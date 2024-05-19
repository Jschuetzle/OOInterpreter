#lang racket
(provide runcode)

(require "parser.rkt")
(require "helpers.rkt")


;; Runs the interpreter on a file with source code. The main method in "class-name" is used
(define (runcode filename)
    (interpret (parser filename)))

; Root function of interpreter. Takes a parse tree as input and outputs the result of the program execution (assuminging we run main method of "class-name")
(define (interpret tree)
  (call/cc (lambda (return) (interpret-program tree '((()())) return))))

; helper method for the root function "interpret"
; recurses through all the statements in the parse tree and returns the state after execution of the source program
(define (interpret-program tree state return)
    (cond
      [(null? tree)  (return 'void)]
      [else          (interpret-program (cdr tree)
                                        (call/cc (lambda (next) (M-state (car tree)
                                                                         state
                                                                         return
                                                                         next
                                                                         (lambda (s) (error 'continue-not-allowed))
                                                                         (lambda (s) (error 'break-not-allowed))
                                                                         (lambda (v) (error v)))))
                                        return)]))


; ======================================================================
; STATE UPDATE FUNCTIONS
; ======================================================================

;; returns the value associated with some variable in the state. Naming conflicts are handled by the layering of the state, i.e. static
;; scoping rules are applied to variable lookups. An error is thrown if variable doesn't exist in state or if the variable hasn't been initialized yet
(define (get-value var state return)
    (cond
      [(null? state)                                                            (error 'using-before-declaring)]
      [(null? (variable-names state))                                           (get-value var (remaining-layers state) return)]
      [(and (eq? (front-name state) var) (eq? 'novalue (front-value state)))    (error 'using-before-assigning)]
      [(eq? (front-name state) var)                                             (return (unbox (front-value state)))]
      [else                                                                     (get-value var (remaining-state state) return)]))


;; updates the value of a variable in the state, and returns the newly updated state
;; will throw an error if variable name doesn't exist in the state
(define (update-value var newvalue original-state iter-state return)
    (cond
      [(null? iter-state)                    (error 'using-before-declaring)]
      [(null? (variable-names iter-state))   (update-value var newvalue original-state (remaining-layers iter-state) return)]
      [(eq? (front-name iter-state) var)     (return (begin (set-box! (front-value iter-state) newvalue) original-state))]
      [else                                  (update-value var newvalue original-state (remaining-state iter-state) return)]))


; adds a binding to the state
(define (add-binding var value state)
  (cons (list (cons var (variable-names state))
              (cons (box value) (variable-values state)))
        (remaining-layers state)))


; returns true if the variable name exists in the state
(define (in-state? var state return)
  (cond
    [(null? state)     (return #f)]
    [(null? (variable-names state))   (in-state? var (remaining-layers state) return)]
    [(eq? (front-name state) var)     (return #t)]
    [else                             (in-state? var (remaining-state state) return)]))


; bool converter for M-boolean, to ensure the return is 'true or 'false (not #t or #f)
(define (language-bool bool)
    (cond
      [(eq? bool #t)     'true]
      [else              'false]))



; ======================================================================
; DENOTATIONAL SEMANTICS FUNCTIONS
; ======================================================================

; Takes in a list from the parser that represents a single accepted statement, and calls the proper mapping function.
; Returns the state after the mapping function is applied
(define (M-state stmt state return next continue break throw)
    (cond
      [(eq? (car stmt) 'var)        (M-declare stmt state)]
      [(eq? (car stmt) '=)          (M-assign stmt state)]
      [(eq? (car stmt) 'return)     (return (M-value (leftoperand stmt) state clean-return-cont))]
      [(eq? (car stmt) 'begin)      (M-block (cdr stmt) (add-layer state) return next continue break throw)]
      [(eq? (car stmt) 'if)         (M-if stmt state return next continue break throw)]
      [(eq? (car stmt) 'while)      (M-while stmt state return next next throw)]
      [(eq? (car stmt) 'continue)   (continue (remove-layer state))]
      [(eq? (car stmt) 'break)      (break (remove-layer state))]
      [(eq? (car stmt) 'throw)      (M-throw stmt state throw)]
      [(eq? (car stmt) 'try)        (M-try stmt state return next continue break throw)]
      [(eq? (car stmt) 'finally)    (M-finally stmt state return next continue break throw)]
      [(eq? (caar stmt) 'catch)     (M-catch stmt state return next continue break throw)]))


; Takes in a list of accepted statements that represents a new block of statements.
; This function IS NOT used to execute the statements that in the main scope of the program. Rather it executes only blocks of statements (e.g. while-block, try-catch-finally, etc.)
; Returns the state after execution of the instructions in the block
(define (M-block stmt-list state return next-outer continue break throw)
    (cond
      [(null? stmt-list)   (next-outer (remove-layer state))]
      [else                (M-block (cdr stmt-list)
                                    (call/cc (lambda (next-inner) (M-state (car stmt-list) state return next-inner continue break throw)))
                                    return
                                    next-outer
                                    continue
                                    break
                                    throw)]))


; returns the boolean or integer value that an expression evaluates to
(define (M-value expr state return)
    (cond
      [(and (list? expr) (eq? (operator expr) '=))   (return (M-assign-value (leftoperand expr)
                                                                                  (M-value (rightoperand expr) state clean-return-cont)
                                                                                  state
                                                                                  clean-return-cont))]
      [else                                          (let ((bool-output (M-boolean expr state clean-return-cont)))
                                                       (if (eq? bool-output 'error)
                                                           (M-int expr state return) 
                                                           (return bool-output)))]))


; Takes in list of the form "(var variable)" or "(var variable value)"
; If a "value" is specified, the function returns the a new state with the name/value binding. Otherwise, the function returns the state with the name bound to 'novalue.
(define (M-declare stmt state)
    (let ((in-state (in-state? (leftoperand stmt) state clean-return-cont)))
      (cond
        [in-state                       (error 'redefining-variable)]
        [(null? (var-dec-value stmt))   (add-binding (leftoperand stmt) 'novalue state)]
        [else                           (add-binding (leftoperand stmt) (M-value (rightoperand stmt) state clean-return-cont) state)])))


; Takes in list of the form "(= variable expression)"
; Returns the state after removing the previous name/value binding for "var" (if it existed) and adding the new (variable, value) binding, where value is what expr evaluates to
(define (M-assign stmt state)
  (update-value (leftoperand stmt)
                (M-value (rightoperand stmt) state clean-return-cont)
                state
                state
                clean-return-cont))


;; Updates the value of a variable in the state, and returns the new value
;; Identical to the function "update-value", however this functions returns the value being assigned instead of the new state
(define (M-assign-value var newvalue state return)
  (cond
    [(null? state)                    (error 'using-before-declaring)]
    [(null? (variable-names state))   (M-assign-value var newvalue (remaining-layers state) return)]
    [(eq? (front-name state) var)     (return (begin (set-box! (front-value state) newvalue) newvalue))]
    [else                             (M-assign-value var newvalue (remaining-state state) return)]))


; Takes in list of the form "(if conditional then-statement optional-else-statement)"
; Returns the state after execution of "then-statement" if "conditional" evaluates to 'true. Otherwise, returns state after execution of "optional-else-statement"
(define (M-if stmt state return next continue break throw)
       (cond 
         [(eq? (M-boolean (condition stmt) state clean-return-cont) 'true)  (M-state (first-stmt stmt) state return next continue break throw)]
         [(pair? (else-if stmt))                                            (M-state (second-stmt stmt) state return next continue break throw)]
         [else                                                              (next state)]))


; Takes in list of the form "(while conditional body-statement)"
; If "conditional" evaluates to 'true, the state returned from "body-statement" will be used to evaluate "conditional" again. Once the "conditional" evaluates to 'false,
; the state from the final call to "body-statement" will be returned
(define (M-while stmt state return next break throw)
      (cond
        [(eq? (M-boolean (condition stmt) state clean-return-cont) 'true)  (M-while stmt
                                                                                    (call/cc (lambda (continue) (M-state (loop-body stmt) state return continue continue break throw)))
                                                                                    return
                                                                                    next
                                                                                    break
                                                                                    throw)] 
        [else                                                              (next state)]))


(define (M-throw stmt state throw)
  (cond
    [(eq? (procedure-arity throw) 2)   (throw (M-value (leftoperand stmt) state clean-return-cont)
                                               (add-layer (remove-layer state)))]
    [else                              (throw 'exception-thrown-and-not-caught)]))


; function for execution of the try-block in a try-catch-finally, where catch and finally are allowed to be omitted.
; has similar behavior to Java's try-catch-finally
(define M-try
     (lambda (stmts state return next continue break throw)
       ; new continuations of the form (stmts state return next continue break throw)
       (let* ((newreturn          (lambda (s) (M-state (finally-from-try stmts) s return return continue break throw)))
              (newbreak           (lambda (s) (M-state (finally-from-try stmts) s return break continue break throw)))
              (newcontinue        (lambda (s) (M-state (finally-from-try stmts) s return continue continue break throw)))
              (newthrow           (lambda (s) (M-state (finally-from-try stmts) s return throw continue break throw)))
              (finallycont        (lambda (s) (M-state (finally-from-try stmts) s return next continue break throw)))
              (mythrow1           (lambda (v s) (M-state (catch-and-finally stmts) (add-binding (catch-exception-name stmts) v s) return next continue break throw)))
              (mythrow2           (lambda (v s) (M-state (catch-and-finally stmts) (add-binding (catch-exception-name stmts) v s) newreturn finallycont newbreak newcontinue newthrow))))
         
         (cond
           [(and (null? (catch-only stmts))
                 (null? (finally-from-try stmts)))       (M-block (try-body stmts) (add-layer state) return next continue break throw)]
           [(null? (catch-only stmts))                   (M-block (try-body stmts) (add-layer state) newreturn finallycont newcontinue newbreak newthrow)]
           [(null? (finally-from-try stmts))             (M-block (try-body stmts) (add-layer state) return next continue break mythrow1)]
           [else                                         (M-block (try-body stmts) (add-layer state) newreturn finallycont newcontinue newbreak mythrow2)]))))


; function for execution of the catch-block in a try-catch-finally (if it has been reached)
; In an instance of try-catch-finally, if the catch-block is omitted, then this function won't be called
(define M-catch
  (lambda (stmts state return next break continue throw)
    (cond
      [(null? (finally-from-catch stmts))      (M-block (catch-body stmts) state return next break continue throw)] 
      [else                                    (M-block (catch-body stmts) state return next break continue throw)])))


; function of execution of finally-block in a try-catch-finally
; This function displays the same behavior as M-catch, wherein if the finally-block is empty, then this function won't be called
(define M-finally
  (lambda (stmts state return next break continue throw)
     (M-block (finally-body stmts) (add-layer state) return next break continue throw)))


; Denoational mapping function that evaluates an expression through the lens of relational operators/booleans. Returns true, false, or error
(define (M-boolean expr state return)
     (cond
       ; expressions with no operators
       [(or (eq? expr 'true) (eq? expr 'false))   (return expr)]
       [(number? expr)                            (return 'error)]
       [(and (atom? expr))                        (M-boolean (get-value expr state clean-return-cont) state return)]
       
       ; expressions with operators
       [(eq? (operator expr) '&&)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (and (eq? v-left 'true) (eq? v-right 'true))))))))]
       
       [(eq? (operator expr) '||)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (or (eq? v-left 'true) (eq? v-right 'true))))))))]

       [(eq? (operator expr) '!)         (M-boolean (leftoperand expr) state
                                           (lambda (v) (return (language-bool (not (eq? v 'true))))))]
       
       [(eq? (operator expr) '!=)        (M-value (leftoperand expr) state
                                           (lambda (v-left) (M-value (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (not (eq? v-left v-right))))))))]
       
       [(eq? (operator expr) '==)        (M-value (leftoperand expr) state
                                           (lambda (v-left) (M-value (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (eq? v-left v-right)))))))]
       
       [(eq? (operator expr) '<)         (M-int (leftoperand expr) state
                                           (lambda (v-left) (M-int (rightoperand expr) state
                                              (lambda (v-right) (return (language-bool (< v-left v-right)))))))]
       
       [(eq? (operator expr) '<=)        (M-int (leftoperand expr) state
                                           (lambda (v-left) (M-int (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (<= v-left v-right)))))))]
       
       [(eq? (operator expr) '>)         (M-int (leftoperand expr) state
                                           (lambda (v-left) (M-int (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (> v-left v-right)))))))]
       
       [(eq? (operator expr) '>=)        (M-int (leftoperand expr) state
                                           (lambda (v-left) (M-int (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (>= v-left v-right)))))))]
       
       [(eq? (operator expr) '=)         (return (M-assign-value (leftoperand expr)
                                                                      (M-value (rightoperand expr) state clean-return-cont)
                                                                      state
                                                                      clean-return-cont))]
       [else 'error]))


; evaluates an expression through the lens of mathematical operators/integers
(define (M-int expr state return)
    (cond
      [(number? expr)                           (return expr)]
      [(or (eq? expr 'true) (eq? expr 'false))  (return 'error)]
      [(and (atom? expr))                       (M-int (get-value expr state clean-return-cont) state return)]
      
      [(and (eq? (operator expr) '-)
            (null? (operands-excluding-first expr)))      (M-int (operand expr) state
                                                  (lambda (v) (return (- v))))]
      
      [(eq? (operator expr) '-)                 (M-int (leftoperand expr) state 
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return (- v-left v-right))))))]
      
      [(eq? (operator expr) '+)                 (M-int (leftoperand expr) state 
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return (+ v-left v-right))))))]
      
      [(eq? (operator expr) '*)                 (M-int (leftoperand expr) state
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return (* v-left v-right))))))]
      
      [(eq? (operator expr) '/)                (M-int (leftoperand expr) state 
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return (quotient v-left v-right))))))]
       
      [(eq? (operator expr) '%)                (M-int (leftoperand expr) state 
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return (remainder v-left v-right))))))]

       [(eq? (operator expr) '=)         (return (M-assign-value (leftoperand expr)
                                                                      (M-value (rightoperand expr) state clean-return-cont)
                                                                      state
                                                                      clean-return-cont))]
      [else                                    (return 'error)]))


; expected output from each of the tests
(define answers '(20 164 32 2 error 25 21 6 -1 789 error error error 12 125 110 2000400 101 error 21))
(define mains   '(A A A A A A C Square Square List List List List))


; function to run the interpreter program on a single test file
; it doesn't automatically compare the output to the expected value, rather it just prints out the return value of the program
(define (test test-number)
  (let ((test-file (string-append "tests/individual-test-cases/flow-control-tests/test" (number->string test-number) ".txt")))
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