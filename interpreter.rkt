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


;; obtains the location of some variable binding and the portion of the state that precedes it. This function encapsulates behavior that the get, update, and remove
;; functions need. Therefore, it is put into one procedure, and a function argument specifies what happens when the variable is found
(define (lookup var state action return-cont)
  (cond
    [(null? state)                    (error 'using-before-declaring)]
    [(null? (variable-names state))   (lookup var
                                              (remaining-layers state)
                                              (lambda (v) (return-cont (cons (top-layer state) v)))
                                              return-cont)]
    [(eq? (front-name state) var)     (return-cont (action state))]
    [else                             (lookup var
                                              (remaining-state state)
                                              (lambda (v) (return-cont (cons (list (cons (front-name state) (variable-names v))
                                                                                   (cons (front-value state) (variable-values v)))
                                                                             (remaining-layers v))))
                                              return-cont)]))




; adds a binding to the state
(define (addBinding var value state)
  (cons (list (cons var (variable-names state))
              (cons value (variable-values state)))
        (remaining-layers state)))


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
       [(and (atom? expr))                        (M-boolean (lookup expr
                                                                     state
                                                                     (lambda (state) (front-value state))
                                                                     clean-return-cont)
                                                             state
                                                             return-cont)]
       
       ; expressions with operators
       [(eq? (operator expr) '&&)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (and (eq? v-left 'true) (eq? v-right 'true))))))))]
       
       [(eq? (operator expr) '||)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (or (eq? v-left 'true) (eq? v-right 'true))))))))]

       [(eq? (operator expr) '!)         (M-boolean (leftoperand expr) state
                                           (lambda (v) (return-cont (language-bool (not (eq? v 'true))))))]
       
       [(eq? (operator expr) '!=)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (not (eq? v-right v-left))))))))]
       
       [(eq? (operator expr) '==)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (eq? v-right v-left)))))))]
       
       [(eq? (operator expr) '<)        (M-boolean (leftoperand expr) state
                                          (lambda (v-left) (M-boolean (rightoperand expr) state
                                            (lambda (v-right) (return-cont (language-bool (< v-right v-left)))))))]
       
       [(eq? (operator expr) '<=)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (<= v-right v-left)))))))]
       
       [(eq? (operator expr) '>)        (M-boolean (leftoperand expr) state
                                          (lambda (v-left) (M-boolean (rightoperand expr) state
                                            (lambda (v-right) (return-cont (language-bool (> v-right v-left)))))))]
       
       [(eq? (operator expr) '>=)        (M-boolean (leftoperand expr) state
                                           (lambda (v-left) (M-boolean (rightoperand expr) state
                                             (lambda (v-right) (return-cont (language-bool (>= v-right v-left)))))))]
       [else 'error])))


; evaluates an expression through the lens of mathematical operators/integers
(define M-int
  (lambda (expr state return-cont)
    (cond
      [(number? expr)                           (return-cont expr)]
      [(or (eq? expr 'true) (eq? expr 'false))  (return-cont 'error)]
      [(and (atom? expr))                       (M-int (lookup expr
                                                               state
                                                               (lambda (state) (front-value state))
                                                               clean-return-cont)
                                                       state
                                                       return-cont)]
      
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
                                                    (lambda (v-right) (return-cont (remainder v-left v-right))))))])))


; returns the boolean or integer value that an expression evaluates to
(define M-value
  (lambda (expr state return-cont)
    (let ((bool-result (M-boolean expr state clean-return-cont)))
      (cond
        [(eq? bool-result 'error)   (M-int expr state clean-return-cont)]
        [else                       (return-cont bool-result)]))))


; Takes in list of the form "(var variable)" or "(var variable value)"
; If a "value" is specified, the function returns the a new state with the name/value binding. Otherwise, the function returns the state with the name bound to 'novalue.
(define M-declare
  (lambda (stmt state)
    (cond
      ; need to implement error detection for variable redefining in future
      [(null? (var-dec-value stmt))   (addBinding (leftoperand stmt) 'novalue state)]
      [else                           (addBinding (leftoperand stmt) (M-value (rightoperand stmt) state clean-return-cont) state)])))


; Takes in list of the form "(if conditional then-statement optional-else-statement)"
; Returns the state after execution of "then-statement" if "conditional" evaluates to 'true. Otherwise, returns state after execution of "optional-else-statement"
(define M-if 
   (lambda (stmt state return-cont)
     (let ((condition-result (M-boolean (condition stmt) state return-cont))
          (side-effected-state (M-state (condition stmt) state return-cont)))
       (cond 
         [(eq? condition-result 'true)  (M-state (first-stmt stmt) side-effected-state return-cont)]
         [(pair? (else-if stmt))         (M-state (second-stmt stmt) side-effected-state return-cont)]
         [else                           side-effected-state]))))


; Takes in list of the form "(while conditional body-statement)"
; If "conditional" evaluates to 'true, the state returned from "body-statement" will be used to evaluate "conditional" again. Once the "conditional" evaluates to 'false,
; the state from the final call to "body-statement" will be returned
(define M-while
  (lambda (stmt state return-cont)
    (let ((condition-result (M-boolean (condition stmt) state return-cont))
          (side-effected-state (M-state (condition stmt) state return-cont)))
      (cond
        [(eq? condition-result 'true)  (M-while stmt (M-state (loop-body stmt) side-effected-state) return-cont)] 
        [else                          side-effected-state]))))


; Takes in list of the form "(= variable expression)"
; Returns the state after removing the previous name/value binding for "var" (if it existed) and adding the new (variable, value) binding, where value is what expr evaluates to
(define (M-assign stmt state)
  (lookup (leftoperand stmt)
          state
          (lambda (state) (cons (list (cons (leftoperand stmt) (variable-names state))
                                      (cons (M-value (rightoperand stmt) state clean-return-cont) (variable-values state)))
                                (remaining-layers state)))
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
(define answers '(150 -4 10 16 220 5 6 10 5 -39 error error error error true false true 128 12 30 11 1106 12 16 72 21 164))
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