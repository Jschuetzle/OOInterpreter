#lang scheme
(provide (all-defined-out))

; ======================================================================
; ABSTRACTIONS
; ======================================================================

;; return continuation used for better readability
(define clean-return-cont (lambda (v) v))

; for general use
(define (atom? x) (not (or (pair? x) (null? x))))
(define strip-list
  (lambda (expr)
    (cond
      [(null? expr) expr]
      [else         (car expr)])))

(define (in-list? item list)
  (cond
    [(null? list)           #f]
    [(eq? (car list) item)  #t]
    [else                   (in-list? item (cdr list))]))

;; does the same thing as "unbox" but deals with input that could be 'error
(define (dereference opt-box)
  (cond
    [(eq? opt-box 'error)   opt-box]
    [else                   (unbox opt-box)]))

;; the state is stored in the following form
;;          ( ((names) (values)) ... )
;; so these are abstractions for obtaining certain parts of the state
(define top-layer car)
(define remaining-layers cdr)

;; strips everything  but the global layer of a state
(define (class-layer state)
  (cond
    [(null? state)                      (error 'cannot-get-class-layer-on-empty-state)]
    [(null? (remaining-layers state))   state]
    [else                               (class-layer (remaining-layers state))]))

(define variable-names (lambda (state) (car (top-layer state))))
(define variable-values (lambda (state) (cadr (top-layer state))))
(define front-name (lambda (state) (car (variable-names state))))
(define front-value (lambda (state) (car (variable-values state))))
(define remaining-names (lambda (state) (cdr (variable-names state))))
(define remaining-values (lambda (state) (cdr (variable-values state))))
(define remaining-state (lambda (state) (cons (list (remaining-names state) (remaining-values state))
                                                (cdr state))))

;; for manipulating layers
(define empty-layer '(()()))
(define add-layer (lambda (state) (cons empty-layer state)))
(define remove-layer remaining-layers)


;; abstractions for obtaining certain parts of expressions of the following form: (op op1 op2)
(define operator car)
(define operandlist cdr)
(define leftoperand cadr) 
(define operand cadr) ; used for unary operators
(define operands-excluding-first cddr)
(define rightoperand caddr)

; used while processing variable decs in class bodies...needed because we can't add to the program state b/c we are making a custom class state
(define (opt-add-rightoperand stmt list)
  (cond
    [(null? (operands-excluding-first stmt))   (cons 'novalue list)]
    [else                                      (cons (rightoperand stmt) list)]))


; abstractions for stmts
(define var-dec-value cddr)
(define condition     cadr)
(define first-stmt    caddr)
(define else-if       cdddr)
(define second-stmt   cadddr)
(define loop-body     caddr)


; calling from try
(define try-body             cadr)
(define catch-only           caddr)
(define catch-and-finally    cddr)
(define catch-exception-name (lambda (stmt) (caadr (caddr stmt))))
(define finally-from-try     (lambda (stmt) (cadddr stmt)))

; calling from catch
(define catch-body          caddar)
(define finally-from-catch  cadr)

; calling from finally
(define finally-body cadr)


; abstractions for function defs
(define function-name            cadr)
(define function-params          caddr)
(define function-body            cadddr)
(define function-args            cddr)

; abstractions for function closures
(define closure-params           car)
(define closure-body             cadr)
(define closure-environment      caddr)
(define function-enclosing-class cadddr)




; abstractions for class defs
; class definition abstractions
(define class-name    cadr)
(define parent-class (lambda (stmt)
                        (let ((sup (caddr stmt)))
                          (if (null? sup)
                              'novalue
                              (cadr sup)))))
(define class-body    cadddr)

; used while iterating through declarations in a class body
(define declaration-type        caar)   ; the type of declaration is either a (var ...) or a (function ...)
(define binding-name            cadar)
(define binding-expr            (lambda (stmt) (if (eq? (length (car stmt)) 2) 'novalue (caddar stmt))))
(define method-formal-params caddar)
(define method-def-body         (lambda (stmt) (car (cdddar stmt))))


; class closure abstractions
(define superclass       car)
(define static-methods   cadr)
(define inst-methods     caddr)
(define inst-fields-in-cc      cadddr)

; for selecting a specific part of method/field bindings
(define names            car)
(define values           cadr)




; abstractions for instance closures
; instance closure
(define runtime-type    car)
(define instance-values cadr)


; adds the implicit 'this' onto an identifier
(define (create-dot-syntax ref-name identifier)
  (list 'dot ref-name identifier))
