#lang racket
(provide runcode)

(require "parser.rkt")
(require "helpers.rkt")


;; Runs the interpreter on a file with source code. The main method in "class-name" is used
(define (runcode filename classname)
    (interpret (parser filename) classname))


;; Root function of interpreter. Takes a parse tree as input and outputs the result of the program execution (assuminging we run main method of "class-name")
(define (interpret tree classname)
  (call/cc (lambda (return) (interpret-program tree (list empty-layer) classname return))))


;; Adds all the global variables and functions to the state and then executes the "main" function
;; Hoisting is NOT implemented, therefore the main function must be at the bottom of the program.
(define (interpret-program tree state classname return)
    (cond
      [(null? tree)   (return (dereference (M-call-value (list 'funcall (create-dot-syntax classname 'main))  ; execution of main
                                                         state
                                                         (lambda (s) (error 'exception-thrown))
                                                         classname)))]
      [else                                         (interpret-program (cdr tree)
                                                                       (call/cc (lambda (next) (M-state (car tree) state return next null null null null)))
                                                                       classname
                                                                       return)]))

;; ======================================================================
;; STATE UPDATE FUNCTIONS
;; ======================================================================

;; returns the value associated with some variable in the state. Naming conflicts are handled by the layering of the state, i.e. static
;; scoping rules are applied to variable lookups. An error is thrown if variable doesn't exist in state or if the variable hasn't been initialized yet
(define (get-value var state)
    (cond
      [(null? state)                                                            (error 'using-before-declaring)]
      [(null? (variable-names state))                                           (get-value var (remaining-layers state))]
      [(and (eq? (front-name state) var) (eq? 'novalue (front-value state)))    (error 'using-before-assigning)]
      [(eq? (front-name state) var)                                             (unbox (front-value state))]
      [else                                                                     (get-value var (remaining-state state))]))


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
(define (in-local-state? var state)
  (cond
    [(eq? (length state) 1)           #f]
    [(null? (variable-names state))   (in-local-state? var (remaining-layers state))]
    [(eq? (front-name state) var)     #t]
    [else                             (in-local-state? var (remaining-state state))]))


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

;; checks if a variable is a class. The state argument must only be the global layer of the state
(define (is-class? var state)
  (cond
    [(null? (variable-names state))   #f]
    [(eq? (front-name state) var)     #t]
    [else                             (is-class? var (remaining-state state))]))


;; creates a new class closure in the following form
;;       (superclass-name ((static method names) (static method closures)) ((method names) (method closures)) ((field names) (field default exprs)) )
;; NOTE: THIS ORGANIZATION WILL CHANGE ONCE MORE FUNCTIONALITY IS IMPLEMENTED
(define (make-class-closure stmt state throw)
    (let* ((super-cc            (optional-get-cc (parent-class stmt) state))

           ; gets instance fields and organizes them in reverse ordering for processing in idx-of
           ; format is  ((field names) (field default exprs))
           (inst-fields         (parse-class-body 'var state (class-name stmt) (class-body stmt) clean-return-cont))
           (rev-inst-fields     (list (reverse (variable-names inst-fields))
                                      (reverse (variable-values inst-fields))))

           ; gets methods in form of ((method names) (method closures))
           (static-methods      (strip-list (parse-class-body 'static-function state (class-name stmt) (class-body stmt) clean-return-cont)))
           (inst-methods        (strip-list (parse-class-body 'function state (class-name stmt) (class-body stmt) clean-return-cont)))
           
           ; appends methods and fields together for processing in body of this function
           (method-field-list   (list static-methods inst-methods rev-inst-fields)))
      (cond
        [(null? super-cc)   (cons 'novalue method-field-list)]

        ; if superclass present, superclass slot is filled and superclass fields are appended to current class field bindings
        [else              (cons (parent-class stmt) (list static-methods
                                                           inst-methods
                                                           (list (append (variable-names (list rev-inst-fields)) (variable-names (list (inst-fields-in-cc super-cc))))
                                                                 (append (variable-values (list rev-inst-fields)) (variable-values (list (inst-fields-in-cc super-cc)))))))])))


;; gets the class closure of some class name. If the argument has no name, then return null
;; used when obtaining the super class closure, which may or may not exist
(define (optional-get-cc class state)
  (cond
    [(eq? class 'novalue)   null]
    [else                  (get-value class state)]))


;; obtains the front declaration statement from a list of declarations...used while parsing decs in a class body
(define (optional-get-dec tree)
  (cond
    [(null? tree)   null]
    [else           (car tree)]))


;; parses over the class body and returns a list containing...
;;   1. Method bindings           => ((method-names) (method-closures))
;;   2. Instance names binindgs   => ((instance-field-names) (default-value-expressions))
(define (parse-class-body stmt-type state classname tree return)
    (let ((declaration (optional-get-dec tree)))
    (cond
      [(null? declaration)                                       (return (list empty-layer))]

      ; case where the correct dec type is encountered
      [(and (eq? (operator declaration) stmt-type)
            (in-list? stmt-type '(var static-var)))              (parse-class-body stmt-type
                                                                                   state
                                                                                   classname
                                                                                   (cdr tree)
                                                                                   (lambda (v) (return (list (list (cons (leftoperand declaration) (variable-names v))
                                                                                                                   (opt-add-rightoperand declaration (variable-values v)))))))]
      
      [(and (eq? (operator declaration) stmt-type)
            (in-list? stmt-type '(function static-function)))    (parse-class-body stmt-type
                                                                                   state
                                                                                   classname
                                                                                   (cdr tree)
                                                                                   (lambda (v) (return (list (list (cons (function-name declaration) (variable-names v))
                                                                                                                   (cons (box (make-func-closure state
                                                                                                                                                 (add-implicit-this stmt-type (function-params declaration))
                                                                                                                                                 (function-body declaration)
                                                                                                                                                 classname))
                                                                                                                         (variable-values v)))))))]
      [else                                                     (parse-class-body stmt-type
                                                                                  state
                                                                                  classname
                                                                                  (cdr tree)
                                                                                  return)])))


;; takes in a list of formal parameters and appends the implicit "this" onto the list only if the stmt type isn't a static function
(define (add-implicit-this static-type paramlist)
  (cond
    [(eq? static-type 'static-function)   paramlist]
    [else                                 (append paramlist (list 'this))]))



;; ======================================================================
;; OBJECT (INSTANCE) RELATED FUNCTIONS 
;; ======================================================================

;; creates new instance closure that will hold runtime type and instance field values
(define (make-instance-closure runtime-type state throw)
    (list runtime-type
          (get-default-field-values runtime-type state throw)))


;; evaluates the default field expressions from some class and returns a list of their values
(define (get-default-field-values classname state throw)
  (let ((default-exprs (values (inst-fields-in-cc (get-value classname state)))))
    (reverse (eval-default-exprs default-exprs
                                 state
                                 throw
                                 classname
                                 clean-return-cont))))


;; helper method that does the actual recursion for "get-default-field-values" function
(define (eval-default-exprs exprlist state throw classname return)
  (cond
    [(null? exprlist)   (return exprlist)]
    [else               (eval-default-exprs (cdr exprlist) state throw classname
                          (lambda (v) (return (cons (M-value (car exprlist) state throw classname clean-return-cont) v))))]))


; updates the value of an instance field, given the instance name, field name, and new value
(define (update-inst inst fieldname value state classname)
     (let* ((cc-field-names (names (inst-fields-in-cc (get-value classname state)))))
       
      (idx-of-update (lookup-fields cc-field-names fieldname)
                     value
                     (instance-values inst)
                     clean-return-cont)))


;; given a list of field names, return the current BACK INDEX of argument "name"
;;    BACK INDEX ((length-1) - normal index), which will subsequently be used to find the associated instance value
(define (lookup-fields inst-names name)
    (cond
      [(null? inst-names)            (error 'instance-field-not-valid)]
      [(eq? (car inst-names) name)   (length (cdr inst-names))]
      [else                          (lookup-fields (cdr inst-names) name)]))


;; returns the value at index "n" in list "inst-values"
;; used with the output from the "lookup-fields" function
(define (idx-of n inst-values)
    (cond
      [(null? inst-values)  (error 'field-index-not-possible)]
      [(zero? n)            (car inst-values)]
      [else                 (idx-of (- n 1) (cdr inst-values))]))


; takes the index output from "lookup-fields", and updates the value at that index
(define (idx-of-update n newval inst-values return)
    (cond
      [(null? inst-values)  (error 'field-index-not-possible)]
      [(zero? n)            (return (cons (box newval) (cdr inst-values)))]
      [else                 (idx-of-update (- n 1) newval (cdr inst-values)
                                    (lambda (v) (cons (car inst-values) v)))]))

                                            
;; ======================================================================
;; FUNCTIONS (METHODS)
;; ======================================================================

;; creates a function closure composed of...
;;     1. a list of formal parameters
;;     2. a body of statements to execute
;;     3. a function that generates the active environment available during function execution (excluding the local scope)
;; The third component is necessary in order to allow for recursion because adding the function closure to the state
;; while we are creating the function closure is impossible
(define (make-func-closure current-state params body classname)
    (list params
          body
          ; (lambda (future-state) (add-binding classname (get-value classname future-state) current-state))
          (lambda (future-state) (preserve-classes current-state (class-layer future-state) clean-return-cont))
          classname))


;; when creating the active environment for some function call, classes currently aren't getting hoisted
;; this method will take in a state and replace the highest layer with a complete class layer
(define (preserve-classes state new-layer return)
  (cond
    [(null? state)                      (error 'error-obtaining-function-environment)]
    [(null? (remaining-layers state))   (return new-layer)]
    [else                                       (preserve-classes (remaining-layers state)
                                                                  new-layer
                                                                  (lambda (v) (return (cons (top-layer state) v))))]))


;; Takes a list of formal parameters and list of associated argument expressions, evaluates the argument expressions, and
;; adds these bindings to the local state of the function to be executed
(define (bind-parameters params args fstate state throw classname inst)
    (cond
      [(or (and (null? params) (null? args))
           (eq? (car params) 'error))            fstate]
      [(and (null? (cdr params)) (null? args))   (add-reference (car params) inst fstate)]
      [(or (null? params) (null? args))          (error 'mismatched-parameters)]
      [(eq? (car params) '&)                     (bind-parameters (cddr params)
                                                            (cdr args)
                                                            (add-reference (cadr params)
                                                                           (get-reference (car args) state clean-return-cont)
                                                                           fstate)
                                                            state
                                                            throw
                                                            classname
                                                            inst)]
      
      [else                                (bind-parameters (cdr params)
                                                            (cdr args)
                                                            (add-reference (car params)
                                                                           (M-value (car args) state throw classname clean-return-cont)
                                                                           fstate)
                                                            state
                                                            throw
                                                            classname
                                                            inst)]))


;; obtains the method closure for a static method. If the static method doesn't exist, it examines the parent class's methods (if applicable).
;; If the method doesn't exist at all, an error is thrown.
(define (get-static-func-closure-ref name state cc)
  (get-func-closure-ref name
                    (list (static-methods cc))
                    (superclass cc)
                    state
                    static-methods
                    clean-return-cont))


;; obtains the method closure for an instance method. If the instance method doesn't exist, it examines the parent class's methods (if applicable).
;; If the method doesn't exist at all, an error is thrown.
(define (get-inst-func-closure-ref name state cc)
  (get-func-closure-ref name
                    (list (inst-methods cc))
                    (superclass cc)
                    state
                    inst-methods
                    clean-return-cont))

;; returns either the "get-static-func-closure-ref" function or "get-inst-func-closure-ref" function based on if the input is error
(define (get-closure-type inst-output)
  (cond
    [(eq? inst-output 'error)   get-static-func-closure-ref]
    [else                       get-inst-func-closure-ref]))


;; Looks through a function list that has the form (( (method-names) (method-closures) )) and returns the closures associated with a func name
;; if the name doesn't exist in the funclist and a superclass exists, the same process is done on the superclass's functions
;; nextlist is a function that correctly obtains the function list of the super class (since it may be the static or inst functions).
(define (get-func-closure-ref name funclist super state nextlist return)
  (cond
    [(and (null? (variable-names funclist)) (eq? super 'novalue))   (return 'error)]
    [(null? (variable-names funclist))                              (get-func-closure-ref name
                                                                                      ;; super's functions are put inside a list so the original state functions can be used
                                                                                      (list (nextlist (get-value super state)))
                                                                                      (superclass (get-value super state))
                                                                                      state
                                                                                      nextlist
                                                                                      return)]
    [(eq? (front-name funclist) name)                               (return (front-value funclist))]
    [else                                                           (get-func-closure-ref name (remaining-state funclist) super state nextlist return)]))


;; ======================================================================
;; DENOTATIONAL SEMANTICS FUNCTIONS
;; ======================================================================

;; Takes in a single accepted statement from the parse tree, and calls the proper mapping function.
;; Returns the state after the mapping function is applied
(define (M-state stmt state return next continue break throw classname)
    (cond
      [(or (eq? (car stmt) 'class)
           (eq? (car stmt) 'var)
           (eq? (car stmt) 'function))   (M-declare stmt state throw classname)]
      [(eq? (car stmt) '=)               (M-assign stmt state throw classname)]
      [(eq? (car stmt) 'begin)           (M-block (cdr stmt) (add-layer state) return next continue break throw classname)]
      [(eq? (car stmt) 'funcall)         (M-call-state stmt state next throw classname)]
      [(eq? (car stmt) 'if)              (M-if stmt state return next continue break throw classname)]
      [(eq? (car stmt) 'while)           (M-while stmt state return next next throw classname)]
      [(eq? (car stmt) 'return)          (M-return (leftoperand stmt) state return throw classname)]
      [(eq? (car stmt) 'continue)        (continue (remove-layer state))]
      [(eq? (car stmt) 'break)           (break (remove-layer state))]
      [(eq? (car stmt) 'throw)           (M-throw (leftoperand stmt) state throw classname)]
      [(eq? (car stmt) 'try)             (M-try stmt state return next continue break throw classname)]
      [(eq? (car stmt) 'finally)         (M-finally stmt state return next continue break throw classname)]
      [(eq? (caar stmt) 'catch)          (M-catch stmt state return next continue break throw classname)]))


;; Executes a block of statements enclosed by brackets, and returns the state after execution
(define (M-block stmt-list state return next-outer continue break throw classname)
    (cond
      [(null? stmt-list)   (next-outer state)]
      [else                (M-block (cdr stmt-list)
                                    (call/cc (lambda (next-inner) (M-state (car stmt-list) state return next-inner continue break throw classname)))
                                    return
                                    next-outer
                                    continue
                                    break
                                    throw
                                    classname)]))


; input: a funcall statement, a state before the funcall execution, and two continuations next and throw
; output: the state after executing the funcall in stmt
(define (M-call-state stmt state next throw classname)
    (let* ((dot-syntax (ensure-dot-syntax (leftoperand stmt)))
           (inst-closure-ref (M-inst-ref (leftoperand dot-syntax) state classname throw))
           ;(get-closure (get-closure-type (dereference inst-closure-ref)))
           ;(method-closure (get-closure (M-call-funcname stmt) state (get-value classname state clean-return-cont)))
           (method-closure (M-dot dot-syntax state classname throw))
           (fstate1 ((closure-environment method-closure) state))
           (fstate2 (add-layer fstate1))
           (fstate3 (bind-parameters (closure-params method-closure)
                                     (function-args stmt)
                                     fstate2
                                     state
                                     throw
                                     classname
                                     inst-closure-ref)))
      (M-block (closure-body method-closure)
               fstate3
               (lambda (v s) (next state))
               (lambda (s) (next state))
               (lambda (s) (error 'break-not-allowed-outside-loop))
               (lambda (s) (error 'continue-not-allowed-outside-loop))
               (lambda (v s) (M-throw v state throw classname))
               classname)))


;; determines what class a function call should occur in based on the instance that is used
(define (funcall-execution-location inst-name inst state classname)
  (cond
    [(eq? inst-name 'super)   (superclass (get-value classname state))]
    [(eq? inst 'error)        classname]
    [else                     (runtime-type inst)]))

;; determines what class a field lookup should first occur in based on the instance that is used
(define (field-lookup-location inst-name inst state classname)
  (cond
    [(eq? inst-name 'super)   (superclass (get-value classname state))]
    [(eq? inst-name 'this)    classname]
    [(eq? inst 'error)        classname]
    [else                     (runtime-type inst)]))


;; takes in some identifier and ensures that it is in a dot syntax. Essentially, it adds the implicit 'this' if not already present
(define (ensure-dot-syntax expr)
  (cond
    [(and (list? expr) (eq? (operator expr) 'dot))   expr]
    [else                                            (create-dot-syntax 'this expr)]))

;; Executes a function call and returns the value returned by the function call
;;An error is thrown if the function has no return value. 
(define (M-call-value stmt state throw classname)
    (let* ((dot-syntax (ensure-dot-syntax (leftoperand stmt)))
           (inst-closure-ref (M-inst-ref (leftoperand dot-syntax) state classname throw))
           ;(get-closure (get-closure-type (dereference inst-closure-ref)))
           ;(method-closure (get-closure (M-call-funcname stmt) state (get-value classname state clean-return-cont)))
           (method-closure (M-dot dot-syntax state classname throw))
           (fstate1 ((closure-environment method-closure) state))
           (fstate2 (add-layer fstate1))
           (fstate3 (bind-parameters (closure-params method-closure)
                                     (function-args stmt)
                                     fstate2
                                     state
                                     throw
                                     classname
                                     inst-closure-ref)))
      (call/cc (lambda (return) (M-block (closure-body method-closure)
                                         fstate3
                                         return
                                         (lambda (s) (error 'return-not-found-when-expected))
                                         (lambda (s) (error 'break-not-allowed-outside-loop))
                                         (lambda (s) (error 'continue-not-allowed-outside-loop))
                                         (lambda (v s) (M-throw v state throw classname))
                                         (function-enclosing-class method-closure))))))


;; returns the boolean or integer value that an expression evaluates to
(define (M-value expr state throw classname return)
    (cond
      ; assignment expression
      [(and (list? expr) (eq? (operator expr) '=))         (return (box (M-assign-value (leftoperand expr)
                                                                                        (dereference (M-value (rightoperand expr) state throw classname clean-return-cont))
                                                                                        state
                                                                                        clean-return-cont)))]
      [(and (list? expr) (eq? (operator expr) 'funcall))   (return (M-call-value expr state throw classname))]

      ; instance creation
      [(and (list? expr) (eq? (operator expr) 'new))       (return (box (make-instance-closure (leftoperand expr) state throw)))]

      ; dot operator
      [(and (list? expr) (eq? (operator expr) 'dot))       (return (M-dot-ref expr state classname throw))]

      [(eq? expr 'novalue)                                 (return (box 'novalue))]
      
      [else                                                (let ((bool-output (M-boolean expr state throw classname clean-return-cont)))
                                                            (if (eq? bool-output 'error)
                                                                (let ((int-output (M-int expr state throw classname clean-return-cont)))
                                                                  (if (eq? int-output 'error)
                                                                      (let ((class-output (M-class-ref expr state throw)))
                                                                        (if (eq? class-output 'error)
                                                                            (return (M-inst-ref expr state classname throw))
                                                                            (return class-output)))
                                                                      (return int-output)))
                                                                (return bool-output)))]))


;; obtains a box containing and instance field/method from an instance or a class field/method from a valid class
;; NOTE: this function DOES NOT execute a method, rather it obtains the class closure of the method
(define (M-dot expr state classname throw)
  (dereference (M-dot-ref expr state classname throw)))


;; obtains a box containing and instance field/method from an instance or a class field/method from a valid class
;; NOTE: this function DOES NOT execute a method, rather it obtains the class closure of the method
(define (M-dot-ref expr state classname throw)
    (let* ((reference-closure   (dereference (M-value (leftoperand expr) state throw classname clean-return-cont)))      
           (identifier          (rightoperand expr)))
           ;(cc-field-names (names (inst-fields-in-cc (get-value classname state))))
           ;(inst           (M-inst (leftoperand expr) state classname throw)))
      (cond
        [(eq? (length reference-closure) 4)   (get-static-func-closure-ref identifier state reference-closure)]
        [else                                 (let ((func-closure (get-inst-func-closure-ref identifier
                                                                                         state
                                                                                         (get-value (funcall-execution-location (leftoperand expr)
                                                                                                                                reference-closure
                                                                                                                                state
                                                                                                                                classname)
                                                                                                    state))))
                                                (if (eq? func-closure 'error)
                                                    (idx-of (lookup-fields (names (inst-fields-in-cc (get-value (field-lookup-location (leftoperand expr) reference-closure state classname)
                                                                                                                state)))
                                                                           identifier)
                                                            (instance-values reference-closure))
                                                    func-closure))])))
      
      

;; Takes in a declaration statement that may or may not contain a value. If no value is specified, the variable is bound to 'novalue.
;; An error is thrown if a variable has already been declared.
(define (M-declare stmt state throw classname)
    (let ((in-local-state (in-local-state? (leftoperand stmt) state)))
      (cond
        [in-local-state                 (error 'redefining-variable)]
        [(null? (var-dec-value stmt))   (add-binding (leftoperand stmt) 'novalue state)]
        [(eq? (car stmt) 'function)     (add-binding (function-name stmt)
                                                     (make-func-closure (function-params stmt) (function-body stmt) state)
                                                     state)]
        [(eq? (car stmt) 'class)        (add-binding (class-name stmt)
                                                     (make-class-closure stmt state throw)
                                                     state)]
        [else                           (add-reference (leftoperand stmt) (M-value (rightoperand stmt) state throw classname clean-return-cont) state)])))


;; Evaluates an assignment statement. The return value of the assignment ISN'T used, so it is ignored and the new state is returned.
;; The new state will  replace the binding on the closest layer in the state
(define (M-assign stmt state throw classname)
  (cond
    ; this condition does not work when we update static vars b/c M-inst is error
    [(list? (leftoperand stmt))  (let* ((inst-name (leftoperand (leftoperand stmt)))   ;; this is problematic b/c dot operator nesting
                                        (inst (M-inst inst-name state classname throw)))
                                   (update-value inst-name
                                                 (list (runtime-type inst)
                                                       (update-inst inst
                                                                    (rightoperand (leftoperand stmt))
                                                                    (dereference (M-value (rightoperand stmt) state throw classname clean-return-cont))
                                                                    state
                                                                    (field-lookup-location inst-name inst state classname)))
                                                 state state clean-return-cont))]
                                                                     
  [(in-local-state? (leftoperand stmt) state)   (update-value (leftoperand stmt)
                                                              (dereference (M-value (rightoperand stmt) state throw classname clean-return-cont))
                                                              state
                                                              state
                                                              clean-return-cont)]
  [else                                         (M-assign (list '= (create-dot-syntax 'this (leftoperand stmt)) (rightoperand stmt)) state throw classname)]))


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
(define (M-if stmt state return next continue break throw classname)
       (cond 
         [(eq? (dereference (M-boolean (condition stmt) state throw classname clean-return-cont))
               'true)                                                                              (M-state (first-stmt stmt) state return next continue break throw classname)]
         [(pair? (else-if stmt))                                                                   (M-state (second-stmt stmt) state return next continue break throw classname)]
         [else                                                                                     (next state)]))


;; Takes in a while statement, and executes the loop body repeatedly until condition evaluates to false
;; Allows for side effects in the condition statement
(define (M-while stmt state return next break throw classname)
      (cond
        [(eq? (dereference (M-boolean (condition stmt) state throw classname clean-return-cont))
                           'true)                                                               (M-while stmt
                                                                                                          (call/cc (lambda (continue) (M-state (loop-body stmt) state return continue continue break throw classname)))
                                                                                                          return
                                                                                                          next
                                                                                                          break
                                                                                                          throw
                                                                                                          classname)] 
        [else   (next state)]))


;; Takes in a throw statement and a callback function that may take 1 or 2 arguments.
;; NEED TO COMPLETE
(define (M-throw expr state throw classname)
  (cond
    [(eq? (procedure-arity throw) 2)   (throw (dereference (M-value expr state throw classname clean-return-cont))
                                               (add-layer (remove-layer state)))]
    [else                              (throw 'exception-thrown-and-not-caught)]))


;; Takes in a return statement and a callback function that may take 1 or 2 arguments.
;; NEED TO COMPLETE COMMENT
(define (M-return expr state return throw classname)
  (cond
    [(eq? (procedure-arity return) 2)   (return (M-value expr state throw classname clean-return-cont)
                                                state)]
    [else                               (return (M-value expr state throw classname clean-return-cont))]))


;; Executes the try-block in a try-catch-finally, where the catch and finally blocks are allowed to be omitted.
;; has same behavior as Java's try-catch-finally
(define (M-try stmts state return next continue break throw classname)
       ; continuations that define the control flow behavior of try-block
       (let* ((newreturn          (lambda (s) (M-state (finally-from-try stmts) s return return continue break throw classname)))
              (newbreak           (lambda (s) (M-state (finally-from-try stmts) s return break continue break throw classname)))
              (newcontinue        (lambda (s) (M-state (finally-from-try stmts) s return continue continue break throw classname)))
              (newthrow           (lambda (s) (M-state (finally-from-try stmts) s return throw continue break throw classname)))
              (finallycont        (lambda (s) (M-state (finally-from-try stmts) s return next continue break throw classname)))  ; for complete execution of try block
              (mythrow1           (lambda (v s) (M-state (catch-and-finally stmts) (add-binding (catch-exception-name stmts) v s) return next continue break throw classname)))
              (mythrow2           (lambda (v s) (M-state (catch-and-finally stmts) (add-binding (catch-exception-name stmts) v s) newreturn finallycont newbreak newcontinue newthrow classname))))
         
         (cond
           [(and (null? (catch-only stmts))
                 (null? (finally-from-try stmts)))       (M-block (try-body stmts) (add-layer state) return next continue break throw classname)]
           [(null? (catch-only stmts))                   (M-block (try-body stmts) (add-layer state) newreturn finallycont newcontinue newbreak newthrow classname)]
           [(null? (finally-from-try stmts))             (M-block (try-body stmts) (add-layer state) return next continue break mythrow1 classname)]
           [else                                         (M-block (try-body stmts) (add-layer state) newreturn finallycont newcontinue newbreak mythrow2 classname)])))


;; Executes the catch-block in a try-catch-finally, where the finally block is allowed to be omitted.
;; Flow control behavior for continuations is defined in the "M-try" function
(define (M-catch stmts state return next break continue throw classname)
    (M-block (catch-body stmts) state return next break continue throw classname))


;; Executes the finally-block in a try-catch-finally.
;; Flow control behavior for continuations is defined in the "M-try" function
(define (M-finally stmts state return next break continue throw classname)
     (M-block (finally-body stmts) (add-layer state) return next break continue throw classname))


;; Evaluates an expression through the lens of relational operators/booleans. Returns true, false, or error
(define (M-boolean expr state throw classname return)
     (cond
       ; expressions with no operators
       [(or (eq? expr 'true) (eq? expr 'false))    (return (box expr))]
       [(or (number? expr)
            (eq? expr 'this)
            (eq? expr 'super)
            (is-class? expr (class-layer state)))  (return 'error)]
       
       [(and (atom? expr) (in-local-state? expr state))   (M-boolean (get-value expr state) state throw classname return)]
       [(atom? expr)                                      (M-boolean (dereference (M-value (create-dot-syntax 'this expr) state throw classname clean-return-cont)) state throw classname return)]
       [(eq? (operator expr) 'funcall)            (M-boolean (dereference (M-call-value expr state throw classname))
                                                             state
                                                             throw
                                                             classname
                                                             return)]

       ; unary operators
       [(eq? (operator expr) '!)         (M-boolean (leftoperand expr) state throw classname
                                           (lambda (v) (return (box (language-bool (not (eq? (dereference v) 'true)))))))]
       
       ; binary operators
       [(eq? (operator expr) '&&)        (M-boolean (leftoperand expr) state throw classname
                                           (lambda (v-left) (M-boolean (rightoperand expr) state throw classname
                                             (lambda (v-right) (return (box (language-bool (and (eq? (dereference v-left) 'true) (eq? (dereference v-right) 'true)))))))))]
       
       [(eq? (operator expr) '||)        (M-boolean (leftoperand expr) state throw classname
                                           (lambda (v-left) (M-boolean (rightoperand expr) state throw classname
                                             (lambda (v-right) (return (box (language-bool (or (eq? (dereference v-left) 'true) (eq? (dereference v-right) 'true)))))))))]
       
       [(eq? (operator expr) '!=)        (M-value (leftoperand expr) state throw classname
                                           (lambda (v-left) (M-value (rightoperand expr) state throw classname
                                             (lambda (v-right) (return (box (language-bool (not (eq? (dereference v-left) (dereference v-right))))))))))]
       
       [(eq? (operator expr) '==)        (M-value (leftoperand expr) state throw classname
                                           (lambda (v-left) (M-value (rightoperand expr) state throw classname
                                             (lambda (v-right) (return (box (language-bool (eq? (dereference v-left) (dereference v-right)))))))))]
       
       [(eq? (operator expr) '<)         (M-int (leftoperand expr) state throw classname
                                           (lambda (v-left) (M-int (rightoperand expr) state throw classname
                                              (lambda (v-right) (return (box (language-bool (< (dereference v-left) (dereference v-right)))))))))]
       
       [(eq? (operator expr) '<=)        (M-int (leftoperand expr) state throw classname
                                           (lambda (v-left) (M-int (rightoperand expr) state throw classname
                                             (lambda (v-right) (return (box (language-bool (<= (dereference v-left) (dereference v-right)))))))))]
       
       [(eq? (operator expr) '>)         (M-int (leftoperand expr) state throw classname
                                           (lambda (v-left) (M-int (rightoperand expr) state throw classname
                                             (lambda (v-right) (return (box (language-bool (> (dereference v-left) (dereference v-right)))))))))]
       
       [(eq? (operator expr) '>=)        (M-int (leftoperand expr) state throw classname
                                           (lambda (v-left) (M-int (rightoperand expr) state throw classname
                                             (lambda (v-right) (return (box (language-bool (>= (dereference v-left) (dereference v-right)))))))))]
       
       [(eq? (operator expr) '=)         (return (box (M-assign-value (leftoperand expr)
                                                                      (dereference (M-value (rightoperand expr) state throw classname clean-return-cont))
                                                                      state
                                                                      clean-return-cont)))]
       [else 'error]))


;; Evaluates an expression through the lens of mathematical operators/integers. Returns an integer or an error.
(define (M-int expr state throw classname return)
    (cond
      ; constants
      [(number? expr)                              (return (box expr))]
      [(or (eq? expr 'true)
           (eq? expr 'false)
           (eq? expr 'this)
           (eq? expr 'super)
           (is-class? expr (class-layer state)))   (return 'error)]

      ; variables, fields, and funcalls
      [(and (atom? expr) (in-local-state? expr state))   (M-int (get-value expr state) state throw classname return)]
      [(atom? expr)                                      (M-int (dereference (M-value (create-dot-syntax 'this expr) state throw classname clean-return-cont)) state throw classname return)]
      [(eq? (operator expr) 'funcall)                    (M-int (dereference (M-call-value expr state throw classname))
                                                                             state
                                                                             throw
                                                                             classname
                                                                             return)]
       [(and (list? expr) (eq? (operator expr) 'dot))    (M-int (M-dot expr state classname throw) state throw classname return)]
      
      [(and (eq? (operator expr) '-)
            (null? (operands-excluding-first expr)))     (M-int (operand expr) state throw classname
                                                                (lambda (v) (return (box (- (dereference v))))))]
      
      [(eq? (operator expr) '-)                 (M-int (leftoperand expr) state throw classname
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw classname
                                                    (lambda (v-right) (return (box (- (dereference v-left) (dereference v-right))))))))]
      
      [(eq? (operator expr) '+)                 (M-int (leftoperand expr) state throw classname
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw classname
                                                    (lambda (v-right) (return (box (+ (dereference v-left) (dereference v-right))))))))]
      
      [(eq? (operator expr) '*)                 (M-int (leftoperand expr) state throw classname
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw classname
                                                    (lambda (v-right) (return (box (* (dereference v-left) (dereference v-right))))))))]
      
      [(eq? (operator expr) '/)                (M-int (leftoperand expr) state throw classname
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw classname
                                                    (lambda (v-right) (return (box (quotient (dereference v-left) (dereference v-right))))))))]
       
      [(eq? (operator expr) '%)                (M-int (leftoperand expr) state throw classname
                                                  (lambda (v-left) (M-int (rightoperand expr) state throw classname
                                                    (lambda (v-right) (return (box (remainder (dereference v-left) (dereference v-right))))))))]

       [(eq? (operator expr) '=)         (return (box (M-assign-value (leftoperand expr)
                                                                      (dereference (M-value (rightoperand expr) state throw classname clean-return-cont))
                                                                      state
                                                                      clean-return-cont)))]
      [else                                    (return 'error)]))


;; Evaluates an expression through the lens of a class. Returns a class closure or an error.
(define (M-class expr state throw)
  (dereference (M-class-ref expr state throw)))

;; Evaluates an expression through the lens of a class. Returns a box containing a class closure or an error.
(define (M-class-ref expr state throw)
  (cond
    [(and (list? expr) (eq? (car expr) 'class))   (box (make-class-closure expr state throw))]
    [(not (is-class? expr (class-layer state)))   'error]
    [else                                         (get-reference expr (class-layer state) clean-return-cont)]))
    


;; Evalutes an expression through the lens of an object. Returns an instance closure or an error.
(define (M-inst expr state classname throw)
  (dereference (M-inst-ref expr state classname throw)))


;; Evalutes an expression through the lens of an object reference. Returns a box containing an instance closure or an error.
(define (M-inst-ref expr state classname throw)
    (cond
      [(and (list? expr) (eq? (car expr) 'funcall))                    (M-call-value expr state throw classname)]
      [(and (list? expr) (eq? (car expr) 'new))                        (box (make-instance-closure (leftoperand expr) state throw))]
      [(and (list? expr) (eq? (car expr) 'dot))                        (M-dot-ref expr state classname throw)]

      ; VERIFY...is there ever a case where I'm passing in a class into this function?
      [(is-class? expr (class-layer state))                            'error]
      [(eq? expr 'super)                                               (get-reference 'this state clean-return-cont)]
      [(in-local-state? expr state)                                    (get-reference expr state clean-return-cont)]

      ; this case doesn't work correctly, bc M-dot doesn't return an instance...
      [else                                                            (M-dot-ref (create-dot-syntax 'this expr)
                                                                                  state
                                                                                  classname
                                                                                  throw)]))


; expected output from each of the tests
(define answers '(15 12 125 36 54 110 26 117 32 15 123456 5285 -716 530 66 1026 2045 20 530 615 16 100 420 300 error 417 10 48 1629))
(define mains   '(A A A A A A C Square Square List List List C A B A A A B B Box A A A Circle Circle Square A B A))


; function to run the interpreter program on a single test file
; it doesn't automatically compare the output to the expected value, rather it just prints out the return value of the program
(define (test test-number classname)
  (let ((test-file (string-append "tests/individual-test-cases/oo-tests/test" (number->string test-number) ".txt")))
    (runcode test-file classname)))


; function to run the interpreter on all tests from 1 to num-tests
; compares the output to the expected return value and prints out a validation message for each individual test
;
; Example usage:
; run-all-tests 20 ; This will run tests from 1 to 20, continuing even if errors occur
(define (run-all-tests num-tests)
  (define (run-and-check-tests test-number)
    (let* ((class-with-main (expected-main mains test-number))
           (expected (expected-result answers test-number))
           (actual (with-handlers ([exn? (lambda (e) e)]) 
                            (test test-number class-with-main))))
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