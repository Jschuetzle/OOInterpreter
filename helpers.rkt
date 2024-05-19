#lang scheme
(provide (all-defined-out))

; ======================================================================
; ABSTRACTIONS
; ======================================================================

;; return continuation used for better readability
(define clean-return-cont (lambda (v) v))



; for general use
(define (atom? x) (not (or (pair? x) (null? x))))

;; the state is stored in the following form
;;          ( ((names) (values)) ... )
;; so these are abstractions for obtaining certain parts of the state
(define top-layer car)
(define remaining-layers cdr)
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


; abstractions for stmts
(define var-dec-value cddr)
(define condition     cadr)
(define first-stmt    caddr)
(define else-if       cdddr)
(define second-stmt   cadddr)
(define loop-body     caddr)


; calling from try
(define try-body   (lambda (stmt) (cadr stmt)))
(define catch-only      (lambda (stmt) (caddr stmt)))
(define catch-and-finally (lambda (stmt) (cddr stmt)))
(define catch-exception-name (lambda (stmt) (caadr (caddr stmt))))
(define finally-from-try    (lambda (stmt) (cadddr stmt)))

; calling from catch
(define catch-body     (lambda (stmt) (caddar stmt)))
(define finally-from-catch  (lambda (stmt) (cadr stmt)))

; calling from finally
(define finally-body (lambda (stmt) (cadr stmt)))
(define empty-finally '(()))