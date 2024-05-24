#lang racket
(provide runcode)

(require "parser.rkt")
(require "helpers.rkt")


;; Runs the interpreter on a file with source code. The main method in "class-name" is used
(define (runcode filename)
    (interpret (parser filename)))


;; Root function of interpreter. Takes a parse tree as input and outputs the result of the program execution (assuminging we run main method of "class-name")
(define (interpret tree)
  (call/cc (lambda (return) (interpret-program tree (list empty-layer) return))))


;; Adds all the global variables and functions to the state and then executes the "main" function
;; Hoisting is NOT implemented, therefore the main function must be at the bottom of the program.
(define (interpret-program tree state return)
    (cond
      [(null? tree)   (return (M-call-value (list 'funcall 'main)  ; execution of main
                                            state
                                            (lambda (s) (error 'exception-thrown))))]
      [else                                         (interpret-program
                                                       (cdr tree)
                                                       (call/cc (lambda (next) (M-state (car tree) state return next null null null null))) 
                                                        return)]))

;; ======================================================================
;; STATE UPDATE FUNCTIONS
;; ======================================================================

;; returns the value associated with some variable in the state. Naming conflicts are handled by the layering of the state, i.e. static
;; scoping rules are applied to variable lookups. An error is thrown if variable doesn't exist in state or if the variable hasn't been initialized yet
(define (get-value var state return)
    (cond
      [(null? state)                                                            (error 'using-before-declaring)]
      [(null? (variable-names state))                                           (get-value var (remaining-layers state) return)]
      [(and (eq? (front-name state) var) (eq? 'novalue (front-value state)))    (error 'using-before-assigning)]
      [(eq? (front-name state) var)                                             (return (unbox (front-value state)))]
      [else                                                                     (get-value var (remaining-state state) return)]))


;; returns a reference to some variable in the state, i.e. the box bound to a variable is returned
(define (get-reference var state return)
    (cond
      [(null? state)                                                            (error 'using-before-declaring)]
      [(null? (variable-names state))                                           (get-reference var (remaining-layers state) return)]
      [(eq? (front-name state) var)                                             (return (front-value state))]
      [else                                                                     (get-reference var (remaining-state state) return)]))



;; updates the value of a variable in the state, and returns the newly updated state
;; will throw an error if variable name doesn't exist in the state
(define (update-value var newvalue original-state iter-state return)
    (cond
      [(null? iter-state)                    (error 'using-before-declaring)]
      [(null? (variable-names iter-state))   (update-value var newvalue original-state (remaining-layers iter-state) return)]
      [(eq? (front-name iter-state) var)     (return (begin (set-box! (front-value iter-state) newvalue) original-state))]
      [else                                  (update-value var newvalue original-state (remaining-state iter-state) return)]))


;; adds a binding to the local state
(define (add-binding var value state)
  (cons (list (cons var (variable-names state))
              (cons (box value) (variable-values state)))
        (remaining-layers state)))


;; adds a reference to the local state...identical to "add-binding" but value is not boxed bc it is already a box
(define (add-reference var value state)
  (cons (list (cons var (variable-names state))
              (cons value (variable-values state)))
        (remaining-layers state)))


;; returns true if the variable name exists in the local environment of the state
(define (in-local-state? var state return)
  (cond
    [(null? (variable-names state))   (return #f)]
    [(eq? (front-name state) var)     (return #t)]
    [else                             (in-local-state? var (remaining-state state) return)]))


;; returns true if the variable name exists anywhere in the state
(define (in-state? var state return)
  (cond
    [(null? state)                    (return #f)]
    [(null? (variable-names state))   (in-state? var (remaining-layers state) return)]
    [(eq? (front-name state) var)     (return #t)]
    [else                             (in-state? var (remaining-state state) return)]))


;; bool converter for M-boolean, to ensure the return is 'true or 'false (not #t or #f)
(define (language-bool bool)
    (cond
      [(eq? bool #t)     'true]
      [else              'false]))


;; ======================================================================
;; CLASS RELATED FUNCTIONS
;; ======================================================================

;; creates a new class closure in the following form
;;       (superclass-name ((static method names) (static method closures)) ((method names) (method closures)) ((field names) (field default exprs)) )
;; NOTE: THIS ORGANIZATION WILL CHANGE ONCE MORE FUNCTIONALITY IS IMPLEMENTED
(define (make-class-closure stmt state throw)
    (let* ((super-cc            (optional-get-cc (parent-class stmt) state))

           ; gets instance fields and organizes them in reverse ordering for processing in idx-of
           ; format is  ((field names) (field default exprs))
           (inst-fields         (parse-class-body 'var (class-name stmt) (class-body stmt) clean-return-cont))
           (rev-inst-fields     (list (reverse (variable-names inst-fields))
                                      (reverse (variable-values inst-fields))))

           ; gets methods in form of ((method names) (method closures))
           (static-methods      (parse-class-body 'static-function (class-name stmt) (class-body stmt) clean-return-cont))
           (inst-methods        (parse-class-body 'function (class-name stmt) (class-body stmt) clean-return-cont))
           
           ; appends methods and fields together for processing in body of this function
           (method-field-list   (list static-methods inst-methods rev-inst-fields)))
      (cond
        [(null? super-cc)   (cons 'novalue method-field-list)]

        ; if superclass present, superclass slot is filled and superclass fields are appended to current class field bindings
        [else              (cons (parent-class stmt) (list (method-bindings method-field-list)
                                                           (list (append (variable-names (field-bindings method-field-list)) (variable-names (list (cc-field-bindings super-cc))))
                                                                 (append (variable-values (field-bindings method-field-list)) (variable-values (list (cc-field-bindings super-cc)))))))])))


(define (optional-get-cc class state)
  (cond
    [(eq? class 'novalue)   null]
    [else                  (get-value class state clean-return-cont)]))


(define (optional-get-dec tree)
  (cond
    [(null? tree)   null]
    [else           (car tree)]))


;; parses over the class body and returns a list containing...
;;   1. Method bindings           => ((method-names) (method-closures))
;;   2. Instance names binindgs   => ((instance-field-names) (default-value-expressions))
(define (parse-class-body stmt-type classname tree return)
    (let ((declaration (optional-get-dec tree)))
    (cond
      [(null? declaration)                                       (return (list empty-layer))]

      ; case where the correct dec type is encountered
      [(and (eq? (operator declaration) stmt-type)
            (in-list? stmt-type '(var static-var)))              (parse-class-body stmt-type
                                                                                   classname
                                                                                   (cdr tree)
                                                                                   (lambda (v) (return (list (list (cons (leftoperand declaration) (variable-names v))
                                                                                                                   (cons (rightoperand declaration) (variable-values v)))))))]
      
      [(and (eq? (operator declaration) stmt-type)
            (in-list? stmt-type '(function static-function)))    (parse-class-body stmt-type
                                                                                   classname
                                                                                   (cdr tree)
                                                                                   (lambda (v) (return (list (list (cons (function-name declaration) (variable-names v))
                                                                                                                   (cons (make-func-closure (functio params body current-state)
                                                                                                                         (variable-values v)))))))])))

;; ; will add the implicit "this" to formal parameters only if non static
;; (define add-implicit-for-nonstatic
;;   (lambda (func-name params)
;;     (cond
;;       ((eq? func-name 'main) params)
;;       (else (append params (list 'this))))))  ; have to add to back of params in order for "restore-state" to function correctl



;; ======================================================================
;; FUNCTIONS (METHODS)
;; ======================================================================

;; creates a function closure composed of...
;;     1. a list of formal parameters
;;     2. a body of statements to execute
;;     3. a function that generates the active environment available during function execution (excluding the local scope)
;; The third component is necessary in order to allow for recursion because adding the function closure to the state
;; while we are creating the function closure is impossible
(define (make-func-closure name params body current-state)
    (list params
          body
          (lambda (future-state) (add-binding name
                                   (get-value name future-state clean-return-cont)
                                   current-state))))


;; Takes a list of formal parameters and list of associated argument expressions, evaluates the argument expressions, and
;; adds these bindings to the local state of the function to be executed
(define (bind-parameters params args fstate state throw)
    (cond
      [(and (null? params) (null? args))   fstate]
      [(or (null? params) (null? args))    (error 'mismatched-parameters)]
      [(eq? (car params) '&)               (bind-parameters (cddr params)
                                                            (cdr args)
                                                            (add-reference (cadr params)
                                                                           (get-reference (car args) state clean-return-cont)
                                                                           fstate)
                                                            state
                                                            throw)]
      [else                                (bind-parameters (cdr params)
                                                            (cdr args)
                                                            (add-binding (car params)
                                                                         (M-value (car args) state throw clean-return-cont)
                                                                         fstate)
                                                            state
                                                            throw)]))


; input: a state after executing a function, and a state before the function execution occured
; output: the original state with any updating changes to active bindings after the function was executed
(define (restore-state funcstate state)
    (restore-state-helper funcstate state clean-return-cont))


; helper function for "restore-state"
; the return is a continuation to ensure cps style
(define restore-state-helper
  (lambda (fstate state return)
    (cond
      [(null? state)                                             (return state)]
      [(null? (variable-names state))                            (restore-state-helper fstate (remaining-layers state) return)]
      [(in-state? (front-name state) fstate clean-return-cont)   (restore-state-helper fstate (remaining-state state) return)]
      [else                               (let ((new-state (update-value (front-name fstate)
                                                                         (unbox (front-value fstate))
                                                                         state
                                                                         clean-return-cont)))
                                            (restore-state-helper (remaining-state fstate) new-state return))])))


;; ======================================================================
;; DENOTATIONAL SEMANTICS FUNCTIONS
;; ======================================================================

;; Takes in a single accepted statement from the parse tree, and calls the proper mapping function.
;; Returns the state after the mapping function is applied
(define (M-state stmt state return next continue break throw)
    (cond
      [(eq? (car stmt) 'class)      (M-declare stmt state throw)]
      [(eq? (car stmt) 'var)        (M-declare stmt state throw)]
      [(eq? (car stmt) '=)          (M-assign stmt state throw)]
      [(eq? (car stmt) 'return)     (M-return (leftoperand stmt) state return throw)]
      [(eq? (car stmt) 'begin)      (M-block (cdr stmt) (add-layer state) return next continue break throw)]
      [(eq? (car stmt) 'function)   (M-declare stmt state throw)]
      [(eq? (car stmt) 'funcall)    (M-call-state stmt state next throw)]
      [(eq? (car stmt) 'if)         (M-if stmt state return next continue break throw)]
      [(eq? (car stmt) 'while)      (M-while stmt state return next next throw)]
      [(eq? (car stmt) 'continue)   (continue (remove-layer state))]
      [(eq? (car stmt) 'break)      (break (remove-layer state))]
      [(eq? (car stmt) 'throw)      (M-throw (leftoperand stmt) state throw)]
      [(eq? (car stmt) 'try)        (M-try stmt state return next continue break throw)]
      [(eq? (car stmt) 'finally)    (M-finally stmt state return next continue break throw)]
      [(eq? (caar stmt) 'catch)     (M-catch stmt state return next continue break throw)]))


;; Executes a block of statements enclosed by brackets, and returns the state after execution
(define (M-block stmt-list state return next-outer continue break throw)
    (cond
      [(null? stmt-list)   (next-outer state)]
      [else                (M-block (cdr stmt-list)
                                    (call/cc (lambda (next-inner)
                                               (M-state (car stmt-list) state return next-inner continue break throw)))
                                    return
                                    next-outer
                                    continue
                                    break
                                    throw)]))


; input: a funcall statement, a state before the funcall execution, and two continuations next and throw
; output: the state after executing the funcall in stmt
(define (M-call-state stmt state next throw)
    (let* ((closure (get-value (function-name stmt) state clean-return-cont))
           (fstate1 ((closure-environment closure) state))
           (fstate2 (add-layer fstate1))
           (fstate3 (bind-parameters (closure-params closure)
                                     (function-args stmt)
                                     fstate2
                                     state
                                     throw)))
      (M-block (closure-body closure)
               fstate3
               (lambda (v s) (next state))
               (lambda (s) (next state))
               (lambda (s) (error 'break-not-allowed-outside-loop))
               (lambda (s) (error 'continue-not-allowed-outside-loop))
               (lambda (v s) (M-throw v state throw)))))


;; Executes a function call and returns the value returned by the function call
;;An error is thrown if the function has no return value. 
(define (M-call-value stmt state throw)
    (let* ((closure (get-value (function-name stmt) state clean-return-cont))
           (fstate1 ((closure-environment closure) state))
           (fstate2 (add-layer fstate1))
           (fstate3 (bind-parameters (closure-params closure)
                                     (function-args stmt)
                                     fstate2
                                     state
                                     throw)))
      (call/cc (lambda (return) (M-block (closure-body closure)
                                         fstate3
                                         return
                                         (lambda (s) (error 'return-not-found-when-expected))
                                         (lambda (s) (error 'break-not-allowed-outside-loop))
                                         (lambda (s) (error 'continue-not-allowed-outside-loop))
                                         (lambda (v s) (M-throw v state throw)))))))


;; returns the boolean or integer value that an expression evaluates to
(define (M-value expr state throw return)
    (cond
      ; handling of assignment expression
      [(and (list? expr) (eq? (operator expr) '=))   (return (M-assign-value (leftoperand expr)
                                                                                  (M-value (rightoperand expr) state throw clean-return-cont)
                                                                                  state
                                                                                  clean-return-cont))]
      [(and (list? expr) (eq? (operator expr) 'funcall))   (M-call-value expr state throw)]
      [else                                          (let ((bool-output (M-boolean expr state throw clean-return-cont)))
                                                       (if (eq? bool-output 'error)
                                                           (M-int expr state throw return) 
                                                           (return bool-output)))]))


;; Takes in a declaration statement that may or may not contain a value. If no value is specified, the variable is bound to 'novalue.
;; An error is thrown if a variable has already been declared.
(define (M-declare stmt state throw)
    (let ((in-local-state (in-local-state? (leftoperand stmt) state clean-return-cont)))
      (cond
        [in-local-state                 (error 'redefining-variable)]
        [(null? (var-dec-value stmt))   (add-binding (leftoperand stmt) 'novalue state)]
        [(eq? (car stmt) 'function)     (add-binding (function-name stmt)
                                                     (make-func-closure (function-name stmt) (function-params stmt) (function-body stmt) state)
                                                     state)]
        [(eq? (car stmt) 'class)        (add-binding (class-name stmt)
                                                     (make-class-closure stmt state throw)
                                                     state)]
        [else                           (add-binding (leftoperand stmt) (M-value (rightoperand stmt) state throw clean-return-cont) state)])))


;; Evaluates an assignment statement. The return value of the assignment ISN'T used, so it is ignored and the new state is returned.
;; The new state will  replace the binding on the closest layer in the state
(define (M-assign stmt state throw)
  (update-value (leftoperand stmt)
                (M-value (rightoperand stmt) state throw clean-return-cont)
                state
                state
                clean-return-cont))


;; Evaluates an assignment expression. The return value of the assignment IS used, so the variable reference is updated and the value is returned
;; Identical to the function "update-value", however this functions returns the value being assigned instead of the new state
(define (M-assign-value var newvalue state return)
  (cond
    [(null? state)                    (error 'using-before-declaring)]
    [(null? (variable-names state))   (M-assign-value var newvalue (remaining-layers state) return)]
    [(eq? (front-name state) var)     (return (begin (set-box! (front-value state) newvalue) newvalue))]
    [else                             (M-assign-value var newvalue (remaining-state state) return)]))


;; Takes in an if-statement that has an optional else block, and executes the branch that is determined by the condition.
;; Allows for side effects in the condition statement
(define (M-if stmt state return next continue break throw)
       (cond 
         [(eq? (M-boolean (condition stmt) state throw clean-return-cont) 'true)  (M-state (first-stmt stmt) state return next continue break throw)]
         [(pair? (else-if stmt))                                            (M-state (second-stmt stmt) state return next continue break throw)]
         [else                                                              (next state)]))


;; Takes in a while statement, and executes the loop body repeatedly until condition evaluates to false
;; Allows for side effects in the condition statement
(define (M-while stmt state return next break throw)
      (cond
        [(eq? (M-boolean (condition stmt) state throw clean-return-cont) 'true)  (M-while stmt
                                                                                    (call/cc (lambda (continue) (M-state (loop-body stmt) state return continue continue break throw)))
                                                                                    return
                                                                                    next
                                                                                    break
                                                                                    throw)] 
        [else                                                              (next state)]))


;; Takes in a throw statement and a callback function that may take 1 or 2 arguments.
;; NEED TO COMPLETE
(define (M-throw expr state throw)
  (cond
    [(eq? (procedure-arity throw) 2)   (throw (M-value expr state throw clean-return-cont)
                                               (add-layer (remove-layer state)))]
    [else                              (throw 'exception-thrown-and-not-caught)]))


;; Takes in a return statement and a callback function that may take 1 or 2 arguments.
;; NEED TO COMPLETE COMMENT
(define (M-return expr state return throw)
  (cond
    [(eq? (procedure-arity return) 2)   (return (M-value expr state throw clean-return-cont)
                                                state)]
    [else                               (return (M-value expr state throw clean-return-cont))]))


;; Executes the try-block in a try-catch-finally, where the catch and finally blocks are allowed to be omitted.
;; has same behavior as Java's try-catch-finally
(define (M-try stmts state return next continue break throw)
       ; continuations that define the control flow behavior of try-block
       (let* ((newreturn          (lambda (s) (M-state (finally-from-try stmts) s return return continue break throw)))
              (newbreak           (lambda (s) (M-state (finally-from-try stmts) s return break continue break throw)))
              (newcontinue        (lambda (s) (M-state (finally-from-try stmts) s return continue continue break throw)))
              (newthrow           (lambda (s) (M-state (finally-from-try stmts) s return throw continue break throw)))
              (finallycont        (lambda (s) (M-state (finally-from-try stmts) s return next continue break throw)))  ; for complete execution of try block
              (mythrow1           (lambda (v s) (M-state (catch-and-finally stmts) (add-binding (catch-exception-name stmts) v s) return next continue break throw)))
              (mythrow2           (lambda (v s) (M-state (catch-and-finally stmts) (add-binding (catch-exception-name stmts) v s) newreturn finallycont newbreak newcontinue newthrow))))
         
         (cond
           [(and (null? (catch-only stmts))
                 (null? (finally-from-try stmts)))       (M-block (try-body stmts) (add-layer state) return next continue break throw)]
           [(null? (catch-only stmts))                   (M-block (try-body stmts) (add-layer state) newreturn finallycont newcontinue newbreak newthrow)]
           [(null? (finally-from-try stmts))             (M-block (try-body stmts) (add-layer state) return next continue break mythrow1)]
           [else                                         (M-block (try-body stmts) (add-layer state) newreturn finallycont newcontinue newbreak mythrow2)])))


;; Executes the catch-block in a try-catch-finally, where the finally block is allowed to be omitted.
;; Flow control behavior for continuations is defined in the "M-try" function
(define (M-catch stmts state return next break continue throw)
    (M-block (catch-body stmts) state return next break continue throw))


;; Executes the finally-block in a try-catch-finally.
;; Flow control behavior for continuations is defined in the "M-try" function
(define (M-finally stmts state return next break continue throw)
     (M-block (finally-body stmts) (add-layer state) return next break continue throw))


;; Evaluates an expression through the lens of relational operators/booleans. Returns true, false, or error
(define (M-boolean expr state throw return)
     (cond
       ; expressions with no operators
       [(or (eq? expr 'true) (eq? expr 'false))   (return expr)]
       [(number? expr)                            (return 'error)]
       [(atom? expr)                              (M-boolean (get-value expr state clean-return-cont) state throw return)]
       [(eq? (operator expr) 'funcall)            (M-boolean (M-call-value expr state throw)
                                                             state
                                                             throw
                                                             return)]

       ; unary operators
       [(eq? (operator expr) '!)         (M-boolean (leftoperand expr) state throw
                                           (lambda (v) (return (language-bool (not (eq? v 'true))))))]
       
       ; binary operators
       [(eq? (operator expr) '&&)        (M-boolean (leftoperand expr) state throw
                                           (lambda (v-left) (M-boolean (rightoperand expr) state throw
                                             (lambda (v-right) (return (language-bool (and (eq? v-left 'true) (eq? v-right 'true))))))))]
       
       [(eq? (operator expr) '||)        (M-boolean (leftoperand expr) state throw
                                           (lambda (v-left) (M-boolean (rightoperand expr) state throw
                                             (lambda (v-right) (return (language-bool (or (eq? v-left 'true) (eq? v-right 'true))))))))]
       
       [(eq? (operator expr) '!=)        (M-value (leftoperand expr) state throw
                                           (lambda (v-left) (M-value (rightoperand expr) state throw
                                             (lambda (v-right) (return (language-bool (not (eq? v-left v-right))))))))]
       
       [(eq? (operator expr) '==)        (M-value (leftoperand expr) state throw
                                           (lambda (v-left) (M-value (rightoperand expr) state throw
                                             (lambda (v-right) (return (language-bool (eq? v-left v-right)))))))]
       
       [(eq? (operator expr) '<)         (M-int (leftoperand expr) state throw
                                           (lambda (v-left) (M-int (rightoperand expr) state throw
                                              (lambda (v-right) (return (language-bool (< v-left v-right)))))))]
       
       [(eq? (operator expr) '<=)        (M-int (leftoperand expr) state throw
                                           (lambda (v-left) (M-int (rightoperand expr) state throw
                                             (lambda (v-right) (return (language-bool (<= v-left v-right)))))))]
       
       [(eq? (operator expr) '>)         (M-int (leftoperand expr) state throw
                                           (lambda (v-left) (M-int (rightoperand expr) state throw
                                             (lambda (v-right) (return (language-bool (> v-left v-right)))))))]
       
       [(eq? (operator expr) '>=)        (M-int (leftoperand expr) state throw
                                           (lambda (v-left) (M-int (rightoperand expr) state throw
                                             (lambda (v-right) (return (language-bool (>= v-left v-right)))))))]
       
       [(eq? (operator expr) '=)         (return (M-assign-value (leftoperand expr)
                                                                      (M-value (rightoperand expr) state throw clean-return-cont)
                                                                      state
                                                                      clean-return-cont))]
       [else 'error]))


;; Evaluates an expression through the lens of mathematical operators/integers. Returns an integer or an error.
(define (M-int expr state throw return)
    (cond
      [(number? expr)                           (return expr)]
      [(or (eq? expr 'true) (eq? expr 'false))  (return 'error)]
      [(atom? expr)                             (M-int (get-value expr state clean-return-cont) state throw return)]
      [(eq? (operator expr) 'funcall)           (M-int (M-call-value expr state throw)
                                                           state
                                                           throw
                                                           return)]
      
      [(and (eq? (operator expr) '-)
            (null? (operands-excluding-first expr)))      (M-int (operand expr) state throw
                                                                 (lambda (v) (return (- v))))]
      
      [(eq? (operator expr) '-)                 (M-int (leftoperand expr) state throw
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw
                                                    (lambda (v-right) (return (- v-left v-right))))))]
      
      [(eq? (operator expr) '+)                 (M-int (leftoperand expr) state throw
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw
                                                    (lambda (v-right) (return (+ v-left v-right))))))]
      
      [(eq? (operator expr) '*)                 (M-int (leftoperand expr) state throw
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw
                                                    (lambda (v-right) (return (* v-left v-right))))))]
      
      [(eq? (operator expr) '/)                (M-int (leftoperand expr) state throw
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw
                                                    (lambda (v-right) (return (quotient v-left v-right))))))]
       
      [(eq? (operator expr) '%)                (M-int (leftoperand expr) state throw
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw
                                                    (lambda (v-right) (return (remainder v-left v-right))))))]

       [(eq? (operator expr) '=)         (return (M-assign-value (leftoperand expr)
                                                                      (M-value (rightoperand expr) state throw clean-return-cont)
                                                                      state
                                                                      clean-return-cont))]
      [else                                    (return 'error)]))


; expected output from each of the tests
(define answers '(10 14 45 55 1 115 true 20 24 2 35 error 90 69 87 64 error 125 100 2000400 3421 20332 21))
(define mains   '(A A A A A A C Square Square List List List List))


; function to run the interpreter program on a single test file
; it doesn't automatically compare the output to the expected value, rather it just prints out the return value of the program
(define (test test-number)
  (let ((test-file (string-append "tests/individual-test-cases/oo-tests/test" (number->string test-number) ".txt")))
    (runcode test-file)))


; function to run the interpreter on all tests from 1 to num-tests
; compares the output to the expected return value and prints out a validation message for each individual test
;
; Example usage:
; run-all-tests 20 ; This will run tests from 1 to 20, continuing even if errors occur
(define (run-all-tests num-tests)
  (define (run-and-check-tests test-number)
    (let* ;((class-with-main (expected-main mains test-number))
          ((expected (expected-result answers test-number))
           (actual (with-handlers ([exn? (lambda (e) e)]) 
                            (test test-number))))
      (cond
        [(or (and (exn? actual) (eq? expected 'error)) (equal? actual expected))
               (begin (display (format "Test ~a: Passed\n" test-number)) #t)]
        [else  (begin (display (format "Test ~a: Failed\n" test-number)) #f)])))
  (do ((i 1 (+ i 1)))
      ((> i num-tests))
    (run-and-check-tests i)))

; obtains the expected result for test "test-number"
(define expected-result
  (lambda (list test-number)
    (cond
      [(zero? (- test-number 1)) (car list)]
      (else (expected-result (cdr list) (- test-number 1))))))

; obtains the expected class name for main for test "test-number"
(define expected-main
  (lambda (list test-number)
    (cond
      [(zero? (- test-number 1)) (car list)]
      (else (expected-main (cdr list) (- test-number 1))))))