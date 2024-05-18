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
(define (interpret-program tree state return-cont)
    (cond
      [(null? tree)  (return-cont 'void)]
      [else          (interpret-program (cdr tree)
                                      (M-state (car tree) state return-cont)
                                      return-cont)]))


; ======================================================================
; STATE UPDATE FUNCTIONS
; ======================================================================

;; returns the value associated with some variable in the state. Naming conflicts are handled by the layering of the state, i.e. static
;; scoping rules are applied to variable lookups. An error is thrown if variable doesn't exist in state or if the variable hasn't been initialized yet
(define (get-value var state return-cont)
    (cond
      [(null? state)                                                            (error 'using-before-declaring)]
      [(null? (variable-names state))                                           (get-value var (remaining-layers state) return-cont)]
      [(and (eq? (front-name state) var) (eq? 'novalue (front-value state)))    (error 'using-before-assigning)]
      [(eq? (front-name state) var)                                             (return-cont (unbox (front-value state)))]
      [else                                                                     (get-value var (remaining-state state) return-cont)]))


;; updates the value of a variable in the state, and returns the newly updated state
;; will throw an error if variable name doesn't exist in the state
(define (update-value var newvalue original-state iter-state return-cont)
    (cond
      [(null? iter-state)                    (error 'using-before-declaring)]
      [(null? (variable-names iter-state))   (update-value var newvalue original-state (remaining-layers iter-state) return-cont)]
      [(eq? (front-name iter-state) var)     (return-cont (begin (set-box! (front-value iter-state) newvalue) original-state))]
      [else                                  (update-value var newvalue original-state (remaining-state iter-state) return-cont)]))


; adds a binding to the state
(define (addBinding var value state)
  (cons (list (cons var (variable-names state))
              (cons (box value) (variable-values state)))
        (remaining-layers state)))


; returns true if the variable name exists in the state
(define (in-state? var state return-cont)
  (cond
    [(null? state)     (return-cont #f)]
    [(null? (variable-names state))   (in-state? var (remaining-layers state) return-cont)]
    [(eq? (front-name state) var)     (return-cont #t)]
    [else                             (in-state? var (remaining-state state) return-cont)]))


; bool converter for M-boolean, to ensure the return is 'true or 'false (not #t or #f)
(define language-bool
  (lambda (bool)
    (cond
      ((eq? bool #t)     'true)
      (else              'false))))



; ======================================================================
; DENOTATIONAL SEMANTICS FUNCTIONS
; ======================================================================

; Denoational mapping function that evaluates an expression through the lens of relational operators/booleans. Returns true, false, or error
(define M-boolean
  (lambda (expr state return-cont)
     (cond
       ; expressions with no operators
       [(or (eq? expr 'true) (eq? expr 'false))   (return-cont expr)]
       [(number? expr)                            (return-cont 'error)]
       [(and (atom? expr))                        (M-boolean (get-value expr state clean-return-cont) state return-cont)]
       
       ; expressions with operators
       [(eq? (operator expr) '&&)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (and (eq? v-left 'true) (eq? v-right 'true))))))))]
       
       [(eq? (operator expr) '||)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (or (eq? v-left 'true) (eq? v-right 'true))))))))]

       [(eq? (operator expr) '!)         (M-boolean (leftoperand expr) state
                                           (lambda (v) (return-cont (language-bool (not (eq? v 'true))))))]
       
       [(eq? (operator expr) '!=)        (M-value (leftoperand expr) state
                                           (lambda (v-left) (M-value (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (not (eq? v-left v-right))))))))]
       
       [(eq? (operator expr) '==)        (M-value (leftoperand expr) state
                                           (lambda (v-left) (M-value (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (eq? v-left v-right)))))))]
       
       [(eq? (operator expr) '<)         (M-int (leftoperand expr) state
                                           (lambda (v-left) (M-int (rightoperand expr) state
                                              (lambda (v-right) (return-cont (language-bool (< v-left v-right)))))))]
       
       [(eq? (operator expr) '<=)        (M-int (leftoperand expr) state
                                           (lambda (v-left) (M-int (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (<= v-left v-right)))))))]
       
       [(eq? (operator expr) '>)         (M-int (leftoperand expr) state
                                           (lambda (v-left) (M-int (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (> v-left v-right)))))))]
       
       [(eq? (operator expr) '>=)        (M-int (leftoperand expr) state
                                           (lambda (v-left) (M-int (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (>= v-left v-right)))))))]
       
       [(eq? (operator expr) '=)         (return-cont (M-assign-value (leftoperand expr)
                                                                      (M-value (rightoperand expr) state clean-return-cont)
                                                                      state
                                                                      clean-return-cont))]
       [else 'error])))


; evaluates an expression through the lens of mathematical operators/integers
(define M-int
  (lambda (expr state return-cont)
    (cond
      [(number? expr)                           (return-cont expr)]
      [(or (eq? expr 'true) (eq? expr 'false))  (return-cont 'error)]
      [(and (atom? expr))                       (M-int (get-value expr state clean-return-cont) state return-cont)]
      
      [(and (eq? (operator expr) '-)
            (null? (operands-excluding-first expr)))      (M-int (operand expr) state
                                                  (lambda (v) (return-cont (- v))))]
      
      [(eq? (operator expr) '-)                 (M-int (leftoperand expr) state 
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return-cont (- v-left v-right))))))]
      
      [(eq? (operator expr) '+)                 (M-int (leftoperand expr) state 
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return-cont (+ v-left v-right))))))]
      
      [(eq? (operator expr) '*)                 (M-int (leftoperand expr) state
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return-cont (* v-left v-right))))))]
      
      [(eq? (operator expr) '/)                (M-int (leftoperand expr) state 
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return-cont (quotient v-left v-right))))))]
       
      [(eq? (operator expr) '%)                (M-int (leftoperand expr) state 
                                                  (lambda (v-left) (M-int (rightoperand expr) state
                                                    (lambda (v-right) (return-cont (remainder v-left v-right))))))]

       [(eq? (operator expr) '=)         (return-cont (M-assign-value (leftoperand expr)
                                                                      (M-value (rightoperand expr) state clean-return-cont)
                                                                      state
                                                                      clean-return-cont))]
      [else                                    (return-cont 'error)])))


; returns the boolean or integer value that an expression evaluates to
(define M-value
  (lambda (expr state return-cont)
    (cond
      [(and (list? expr) (eq? (operator expr) '=))   (return-cont (M-assign-value (leftoperand expr)
                                                                                  (M-value (rightoperand expr) state clean-return-cont)
                                                                                  state
                                                                                  clean-return-cont))]
      [else                                          (let ((bool-output (M-boolean expr state clean-return-cont)))
                                                       (if (eq? bool-output 'error)
                                                           (M-int expr state return-cont) 
                                                           (return-cont bool-output)))])))


; Takes in list of the form "(var variable)" or "(var variable value)"
; If a "value" is specified, the function returns the a new state with the name/value binding. Otherwise, the function returns the state with the name bound to 'novalue.
(define M-declare
  (lambda (stmt state)
    (let ((in-state (in-state? (leftoperand stmt) state clean-return-cont)))
      (cond
        [in-state                       (error 'redefining-variable)]
        [(null? (var-dec-value stmt))   (addBinding (leftoperand stmt) 'novalue state)]
        [else                           (addBinding (leftoperand stmt) (M-value (rightoperand stmt) state clean-return-cont) state)]))))


; Takes in list of the form "(if conditional then-statement optional-else-statement)"
; Returns the state after execution of "then-statement" if "conditional" evaluates to 'true. Otherwise, returns state after execution of "optional-else-statement"
(define M-if 
   (lambda (stmt state return-cont)
     ;(let ((condition-result (M-boolean (condition stmt) state clean-return-cont))
          ;(side-effected-state (M-state (condition stmt) state clean-return-cont)))
       (cond 
         [(eq? (M-boolean (condition stmt) state clean-return-cont) 'true)  (M-state (first-stmt stmt) state return-cont)]
         [(pair? (else-if stmt))                                            (M-state (second-stmt stmt) state return-cont)]
         [else                                                              state])))


; Takes in list of the form "(while conditional body-statement)"
; If "conditional" evaluates to 'true, the state returned from "body-statement" will be used to evaluate "conditional" again. Once the "conditional" evaluates to 'false,
; the state from the final call to "body-statement" will be returned
(define M-while
  (lambda (stmt state return-cont)
    ;(let ((condition-result (M-boolean (condition stmt) state return-cont))
          ;(side-effected-state (M-state (condition stmt) state return-cont)))
      (cond
        [(eq? (M-boolean (condition stmt) state clean-return-cont) 'true)  (M-while stmt (M-state (loop-body stmt) state return-cont) return-cont)] 
        [else                                                              state])))


;; Updates the value of a variable in the state, and returns the new value
;; Identical to the function "update-value", however this functions returns the value being assigned instead of the new state
(define (M-assign-value var newvalue state return-cont)
  (cond
    [(null? state)                    (error 'using-before-declaring)]
    [(null? (variable-names state))   (M-assign-value var newvalue (remaining-layers state) return-cont)]
    [(eq? (front-name state) var)     (return-cont (begin (set-box! (front-value state) newvalue) newvalue))]
    [else                             (M-assign-value var newvalue (remaining-state state) return-cont)]))


; Takes in list of the form "(= variable expression)"
; Returns the state after removing the previous name/value binding for "var" (if it existed) and adding the new (variable, value) binding, where value is what expr evaluates to
(define (M-assign stmt state)
  (update-value (leftoperand stmt)
                (M-value (rightoperand stmt) state clean-return-cont)
                state
                state
                clean-return-cont))

                         
; Takes in a list from the parser that represents a single accepted statement, and calls the proper mapping function.
; Returns the state after the mapping function is applied
(define M-state
  (lambda (stmt state return-cont)
    (cond
      [(eq? (car stmt) 'var)        (M-declare stmt state)]
      [(eq? (car stmt) '=)          (M-assign stmt state)]
      [(eq? (car stmt) 'if)         (M-if stmt state return-cont)]
      [(eq? (car stmt) 'while)      (M-while stmt state return-cont)]
      [(eq? (car stmt) 'return)     (return-cont (M-value (leftoperand stmt) state clean-return-cont))])))


; expected output from each of the tests
(define answers '(150 -4 10 16 220 5 6 10 5 -39 error error error error true 100 false true 128 12 30 11 1106 12 16 72 21 164))
(define mains   '(A A A A A A C Square Square List List List List))


; function to run the interpreter program on a single test file
; it doesn't automatically compare the output to the expected value, rather it just prints out the return value of the program
(define (test test-number)
  (let ((test-file (string-append "tests/individual-test-cases/simple-tests/test" (number->string test-number) ".txt")))
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