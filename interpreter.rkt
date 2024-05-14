#lang racket
(require "parser.rkt")
(require "helpers.rkt")



; helper method for the root function "interpret"
; recurses through all the statements in the parse tree and returns the state after execution of the source program
(define interpret-program
  (lambda (tree state return-cont)
    (cond
      [(null? tree)  (return-cont 'void)]
      [else          (interpret-program (cdr tree)
                                      (M-state (car tree) state)
                                      return-cont)])))


; Root function of interpreter. Takes a parse tree as input, and passes along this parse tree with an empty state into the helper method "interpret-program"
(define interpret
  (lambda (tree)
    (interpret-program tree '((()())) clean-return-cont)))


; ======================================================================
; STATE UPDATE FUNCTIONS
; ======================================================================

; when the update-value function finds the variable binding, it will cons the new value onto the cdr of the state


; returns the value binded to a valid variable name from the state
(define (lookup var opt-value state action return-cont)
  (cond
    [(null? state)                    (error 'using-before-declaring)]
    [(null? (variable-names state))   (lookup var
                                              (remaining-layers state)
                                              (lambda (v) (return-cont (cons (top-layer state) v))))]
    [(eq? (front-name state) var)     (return-cont (action var opt-value state))]
    [else                             (lookup var
                                              (remaining-state state)
                                              (lambda (v) (return-cont (list (list (cons (front-name state) (variable-names v))
                                                                                   (cons (front-value state) (variable-values v)))
                                                                             (cdr v)))))]))


; takes the current state and removes the current binding of (var, some value)
(define removeBinding-orig
  (lambda (var state)
    (cond
      [(null? (variable-names state))     state]
      [(eq? (front-name state) var)       (remaining-state state)]                                                                                                                     
      [else                               (list (cons (front-name state) (car (removeBinding var (remaining-state state))))
                                             (cons (front-value state) (cadr (removeBinding var (remaining-state state)))))])))

(define removeBinding
  (lambda (var state return)
    (cond
      [(null? state)   (return state)]
      [else (begin (removeBinding var (car state) return) (removeBinding var (cdr state) return))])))




; adds a binding to the state
(define addBinding
  (lambda (var value state)
    (list
     (cons 'return (cons var (remaining-names state)))
     (cons 'novalue (cons value (remaining-values state))))))


; bool converter for M-boolean, to ensure the return is 'true or 'false (not #t or #f)
(define language-bool
  (lambda (bool)
    (cond
      ((eq? bool #t)     'true)
      (else              'false))))



; ======================================================================
; DENOTATIONAL SEMANTICS FUNCTIONS
; ======================================================================

; implements "return" construct by updating part of the state (assuming no previous calls to return have been made)
(define M-return
  (lambda (expr state)
    (cond
      [(eq? 'novalue (get-return state))      (set-return-val expr state)]
      [else                                   state])))


; Checks whether a variable name is currently in the state. If so, the name is returned, otherwise an error is returned
(define M-name
  (lambda (var state)
    (cond
      [(null? (variable-names state))        (error 'using-before-declaring)]
      [(eq? (front-name state) var)          var]
      [else                                  (M-name var (remaining-state state))])))


; evaluates an expression through the lens of relational operators/booleans
(define M-boolean
  (lambda (expr state return)
     (cond
       ; expressions with no operators
       [(eq? expr 'true)                 (return 'true)]
       [(eq? expr 'false)                (return 'false)]
       [(number? expr)                   (return 'error)]
       [(and (atom? expr))               (return (call/cc (lambda (k) (getValue expr state k))))]          
       
       ; expressions with operators
       [(eq? (operator expr) '&&)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (and (eq? v-left 'true) (eq? v-right 'true))))))))]
       
       [(eq? (operator expr) '||)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (or (eq? v-left 'true) (eq? v-right 'true))))))))]

       [(eq? (operator expr) '!)         (M-boolean (leftoperand expr) state
                                           (lambda (v) (return (language-bool (not (eq? v 'true))))))]
       
       [(eq? (operator expr) '!=)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (not (eq? v-right v-left))))))))]
       
       [(eq? (operator expr) '==)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (eq? v-right v-left)))))))]
       
       [(eq? (operator expr) '<)        (M-boolean (leftoperand expr) state
                                          (lambda (v-left) (M-boolean (rightoperand expr) state
                                            (lambda (v-right) (return (language-bool (< v-right v-left)))))))]
       
       [(eq? (operator expr) '<=)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (<= v-right v-left)))))))]
       
       [(eq? (operator expr) '>)        (M-boolean (leftoperand expr) state
                                          (lambda (v-left) (M-boolean (rightoperand expr) state
                                            (lambda (v-right) (return (language-bool (> v-right v-left)))))))]
       
       [(eq? (operator expr) '>=)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return (language-bool (>= v-right v-left)))))))]
       [else 'error])))


; evaluates an expression through the lens of mathematical operators/integers
(define M-int
  (lambda (expr state return)
    (cond
      [(number? expr)    (return expr)]
      [(eq? expr 'true)  (return 'true)]
      [(eq? expr 'false) (return 'error)]
      [(atom? expr)      (return (call/cc (lambda (k) (getValue expr state k))))]
      
      [(and (eq? (operator expr) '-)
            (null? (optional-token expr)))      (M-int (leftoperand expr) state
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
                                                    (lambda (v-right) (return (remainder v-left v-right))))))])))


; returns the boolean or integer value that an expression evaluates to
(define M-value
  (lambda (expr state)
    (cond
      [(eq? 'error (M-boolean expr state))   (M-int expr state)]
      [else                                  (M-boolean expr state)])))


; Takes in list of the form "(var variable)" or "(var variable value)"
; If a "value" is specified, the function returns the a new state with the name/value binding. Otherwise, the function returns the state with the name bound to 'novalue.
(define M-declare
  (lambda (stmt state)
    (cond
      ; need to implement error detection for variable redefining in future
      [(null? (optional-token stmt))     (addBinding (leftoperand stmt) 'novalue state)]
      [else                              (addBinding (leftoperand stmt) (M-value (rightoperand stmt) state) state)])))


; Takes in list of the form "(if conditional then-statement optional-else-statement)"
; Returns the state after execution of "then-statement" if "conditional" evaluates to 'true. Otherwise, returns state after execution of "optional-else-statement"
(define M-if 
   (lambda (stmt state)
      (cond 
        [(eq? (M-boolean (condition stmt) state) 'true)      (M-state (first-stmt stmt) state)] 
        [(pair? (else-if stmt))                              (M-state (second-stmt stmt) state)]
        [else                                                state])))


; Takes in list of the form "(while conditional body-statement)"
; If "conditional" evaluates to 'true, the state returned from "body-statement" will be used to evaluate "conditional" again. Once the "conditional" evaluates to 'false,
; the state from the final call to "body-statement" will be returned
(define M-while
  (lambda (stmt state)
     (cond   
        ; case where return is only statement in the loop
        [(not (eq? (get-return state) 'novalue))                   state]
        [(eq? (M-boolean (condition stmt) state) 'true)            (M-while stmt (M-state (loop-body stmt) state))] 
        [else                                                      state])))


; Takes in list of the form "(= variable expression)"
; Returns the state after removing the previous name/value binding for "var" (if it existed) and adding the new (variable, value) binding, where value is what expr evaluates to
(define M-assign
  (lambda (stmt state)
    (addBinding (M-name (leftoperand stmt) state)
                (M-value (rightoperand stmt) state)
                (removeBinding (M-name (leftoperand stmt) state) state))))
                         

; Takes in a list from the parser that represents a single accepted statement, and calls the proper mapping function.
; Returns the state after the mapping function is applied
(define M-state
  (lambda (stmt state)
    (cond
      [(eq? (car stmt) 'var)        (M-declare stmt state)]
      [(eq? (car stmt) '=)          (M-assign stmt state)]
      [(eq? (car stmt) 'if)         (M-if stmt state)]
      [(eq? (car stmt) 'while)      (M-while stmt state)]
      [else                         (M-return (leftoperand stmt) state)])))