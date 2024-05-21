#lang racket
;;; ======================================================================
;;; ABSTRACTIONS
;;; ======================================================================

; for general use
(define (atom? x) (not (or (pair? x) (null? x))))
(define empty_layer '(()()))

; abstractions for updating the state
(define top_layer         car)
(define remaining_layers  cdr)
(define variable_names    caar)
(define variable_values   cadar)
(define front_name        caaar)
(define front_value       caadar)
(define remaining_names   cdaar)
(define remaining_values  cdadar)
(define remaining_state   (lambda (state) (cons (list (remaining_names state) (remaining_values state))
                                                (cdr state))))

; abstractions for accessing expr operands
(define leftoperand       cadr)
(define rightoperand      caddr)
(define operator          car)


; abstractions for stmts
(define condition         cadr)
(define first_stmt        caddr)
(define else_if           cdddr)
(define second_stmt       cadddr)
(define loop_body         caddr)
(define block_header      caaddr)
(define block_body        cdaddr)


; funcalls
(define function_args cddr)
; if you finish this project then delete the two line below
; (define function_params (lambda (stmt) (caddr stmt)))
; (define function_body (lambda (stmt) (cadddr stmt)))
; (define function_name (lambda (stmt) (car (cddadr stmt))))


; calling from try
(define try_body               cadr)
(define catch_only             caddr)
(define catch_and_finally      cddr)
(define catch_exception_name   caddr)  
(define finally_from_try       cadddr) 

; calling from catch
(define catch_body             caddar)  
(define finally_from_catch     cadr) 

; calling from finally
(define finally_body           cadr)
(define empty_finally          '(()) )


; class definition abstractions
(define class_name              cadr)
(define class_extends             (lambda (stmt)
                                  (let ((sup (caddr stmt)))
                                    (if (null? sup)
                                        'novalue
                                        (cadr sup)))))
(define class_body              cadddr)


; used while iterating through declarations in a class body
(define class_dec_type          caar)   ; the type of declaration is either a (var ...) or a (function ...)
(define binding_name            cadar)
(define binding_expr            (lambda (stmt) (if (eq? (length (car stmt)) 2) 'novalue (caddar stmt))))
(define method_formal_params    caddar)
(define method_def_body         (lambda (stmt) (car (cdddar stmt))))

; used only to create the "method_field_list" that the parse_class_body function generates
(define method_bindings          car) 
(define field_bindings           cdr)


; class closure abstractions
(define superclass               car)
(define cc_method_bindings       cadr)
(define cc_field_bindings      caddr)
(define instance_field_names (lambda (v) (car (cc_field_bindings v))))
(define instance_field_default_exprs (lambda (v) (cadr (cc_field_bindings v))))


; instance closure
(define runtime_type         car)
(define instance_values      cdr)


; method closures
(define closure_params            car)
(define closure_body              cadr)
(define closure_environment       caddr)
(define compiletime_environment   cadddr)
(define get_this_alias            (lambda (stmt) (car (cddddr stmt))))
(define set_this_alias            (lambda (name closure return)
                                    (cond
                                      [(null? closure)    (return '())]
                                      [(and (null? (cdr closure)) (eq? name 'super)) (set_this_alias name (cdr closure) (lambda (v) (return (cons 'this v))))]
                                      [(null? (cdr closure))                         (set_this_alias name (cdr closure) (lambda (v) (return (cons name v))))]
                                      [else                                          (set_this_alias name (cdr closure) (lambda (v) (return (cons (car closure) v))))])))


; bool converter for M_boolean, to ensure the return is 'true or 'false (not #t or #f)
(define language_bool
  (lambda (bool)
    (cond
      ((eq? bool #t)     'true)
      (else              'false))))

(define curr_stmt       (lambda (stmt) (caddr stmt)))
(define next_stmt       (lambda (stmt) (cdr stmt)))

(define optional_token (lambda (stmt) (cddr stmt)))
(define optional_value (lambda (stmt) (caddr stmt)))
