#lang scheme
(provide (all-defined-out))

; ======================================================================
; ABSTRACTIONS
; ======================================================================

;; return continuation used for better readability
(define clean-return-cont (lambda (v) v))

(define (update-value var value state)
  (list (list (variable-names state)
              (cons value (remaining-values state)))
        (remaining-layers state)))

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
(define remaining-state (lambda (state) (list (remaining-names state) (remaining-values state))))


;; abstractions for obtaining certain parts of expressions of the following form: (op op1 op2)
(define operator car)
(define leftoperand cadr)
(define operand cadr) ; used for unary operators
(define rightoperand caddr)



; abstractions for stmts
(define condition       (lambda (stmt) (cadr stmt)))
(define first-stmt      (lambda (stmt) (caddr stmt)))
(define else-if         (lambda (stmt) (cdddr stmt)))
(define second-stmt     (lambda (stmt) (cadddr stmt)))
(define loop-body       (lambda (stmt) (caddr stmt)))

(define optional-token (lambda (stmt) (cddr stmt)))