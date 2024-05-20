#lang racket

;; this module implements an object-oriented interpreter

(provide (all-defined-out))

;; ---------------------------------
;; import and implementation section

(require "parser.rkt")
(require "helpers.rkt")
(require "test-cases.rkt")

;;; ======================================================================
;;; FUNCTIONS FOR RUNNING THE INTERPRETER
;;; ======================================================================

;; Runs the interpreter on a file with source code. The main method in "class-name" is used
(define (runcode filename class-name)
    (interpret (parser filename) class-name))

; Root function of interpreter. Takes a parse tree as input and outputs the result of the program execution (assuminging we run main method of "class-name")
(define (interpret tree classname)
    (call/cc (lambda (return) (interpret_global tree classname '((()())) return))))


; ======================================================================
; STATE RELATED FUNCTIONS
; ======================================================================

;; updates the value of a variable in the state in continuation passing style
;; will throw an error if variable name doesn't exist in the state
(define update_value
  (lambda (var value state return)
    (cond
      [(null? state)                                 (error 'using-before-declaring)]
      [(null? (variable_names state))                (update_value var value (remaining_layers state)
                                                       (lambda (v) (return (cons (top_layer state) v))))] 

      [(eq? (front_name state) var)                  (return (begin (set-box! (front_value state) value) state))]

      [else                                          (update_value var value (remaining_state state)
                                                       (lambda (v) (return (cons (list (cons (front_name state) (variable_names v))
                                                                                      (cons (front_value state) (variable_values v))) (cdr v)))))])))


;; returns the value associated with some variable in the state. Naming conflicts are handled by the layering of the state, i.e. static
;; scoping rules are applied to variable lookups. An error is thrown if variable doesn't exist in state or if the variable hasn't been initialized yet
(define get_value
  (lambda (var state return)
    (cond
      [(null? state)                                                            (error 'using-before-declaring)]
      [(null? (variable_names state))                                           (get_value var (remaining_layers state) return)]
      [(and (eq? (front_name state) var) (eq? 'novalue (front_value state)))    (error 'using-before-assigning)]
      [(and (eq? (front_name state) var) (box? (front_value state)))            (return (unbox (front_value state)))]
      [(eq? (front_name state) var)                                             (return (front_value state))]
      [else                                                                     (get_value var (remaining_state state) return)])))


; input: a variable name, a state, and a return continuation (for cps)
; output: an updated state with the binding removed for var. The function only removes the binding of var
;         that is closest to current scope layer. If the name var doesn't exist, the original state is returned
;; removes the closest variable 
(define remove_binding
  (lambda (var state return)
    (cond
      [(null? state)   (return state)]
      [(null? (variable_names state))   (remove_binding var (remaining_layers state)
                                          (lambda (v) (return (cons (top_layer state) v))))]
      [(eq? (front_name state) var)     (return (remaining_state state))]
      [else                             (remove_binding var (remaining_state state)
                                          (lambda (v) (return (cons (list (cons (front_name state) (variable_names v))
                                                                    (cons (front_value state) (variable_values v))) (cdr v)))))])))

; input: a state
; output: the input state with a new empty layer added to the leftmost side of the state
(define add_layer
  (lambda (state)
    (cons empty_layer state)))


; input: a state
; output: the input state with the leftmost layer removed
(define remove_layer
  (lambda (state) (remaining_layers state)))


; input: a variable name, a value, and a state
; output: a state with the new binding (var, value) in the leftmost layer
(define add_binding
  (lambda (var value state)
    (cons
     (list
        (cons var (variable_names state))
        (cons (box value) (variable_values state)))
     (remaining_layers state))))


; given a variable name and a state, this function will return true if the variable name is present in the topmost layer of the state (local layer)
(define in-local-state?
  (lambda (var state)
    (cond
      [(and (null? (variable_names state)) (null? (cdr (remaining_layers state))))  #f]
      [(null? (variable_names state))      (in-local-state? var (remaining_layers state))]
      [(eq? var (front_name state))        #t]
      [else                                (in-local-state? var (remaining_state state))])))



; ======================================================================
; STATE UPDATE FUNCTIONS FOR FUNCTIONS
; ======================================================================

; input: a list of formal parameters, a list of actual parameters, a state directly before execution of the instruction inside
;        a function, and a state before the function execution occured, and a throw continuation if any of the actual parameters happen to be a function call
; output: a state to be used during the execution of a function which binds the values in the actual parameters to the names of the formal parameters
;         
(define bind_parameters
  (lambda (params args fstate state throw classname inst return)
    (cond
      [(and (null? params) (null? args)) fstate]
      
      ; binding the instance to "this"
      [(and (null? (cdr params)) (null? args)) (return (add_binding (car params) inst fstate))]
      [(or (null? params) (null? args)) (error 'mismatched-parameters)]
      [else (bind_parameters (cdr params) (cdr args) fstate state throw classname inst
                              (lambda (v) (return (add_binding (car params) (M_value (car args) state throw (lambda (s) s) classname) v))))])))


; input: a state after executing a function, and a state before the function execution occured
; output: the original state with any updating changes to active bindings after the function was executed
(define restore_state
  (lambda (fstate state this_alias classname)
    (restore_state_helper fstate state (lambda (v) v) this_alias classname)))


; helper function for "restore_state"
; the return is a continuation to ensure cps style
(define restore_state_helper
  (lambda (fstate state return this_alias classname)
    (cond
      [(null? (cdr fstate)) (return (append state fstate))]

      ; finish copying on a layer
      [(null? (variable_names fstate))    (restore_state_helper (remaining_layers fstate) state return this_alias classname)]

      ; copy on the name that "this" was aliasing
      [(eq? (front_name fstate) 'this)    (let ((new_state1 (copy_to_instance_field this_alias (unbox (front_value fstate)) state classname)))
                                            (restore_state_helper (remaining_state fstate) new_state1 return this_alias classname))]

      ; if the variable being copied is an instance...i actually don't think this ever gets utilized
      [(list? (front_value fstate))       (let ((new_state2 (update_value (front_name fstate) (unbox (front_value fstate)) state (lambda (v) v))))
                                            (restore_state_helper (remaining_state fstate) new_state2 return this_alias classname))]

      ; local variable...doesn't get copied
      [else                               (restore_state_helper (remaining_state fstate) state return this_alias classname)])))


(define in-field-bindings?
  (lambda (var bindings)
    (cond
      [(null? (variable_names bindings))   #f]
      [(eq? var (front_name bindings))     #t]
      [else (in-field-bindings? var (cdr bindings))])))

(define copy_to_instance_field
  (lambda (this_alias newval state classname)
    (cond
      [(in-local-state? this_alias state)    (update_value this_alias newval state (lambda (v) v))]

      ; in order to get the instance field names, the compile time type of "this" in the originating class must be found
      ; we can get the class closure with the "classname" argument, which must be representative of the original state, not the function state
      [(in-field-bindings? this_alias (list (cc_field_bindings (get_value classname state (lambda (v) v)))))    (update_value 'this
                                                                                                                              (list (runtime_type (get_value 'this state (lambda (v) v)))
                                                                                                                                    (update_inst_value (list 'dot 'this this_alias)
                                                                                                                                                 newval state classname))
                                                                                                                              state (lambda (v) v))]
      ; then not in the field bindings...rather, could be in the field bindings of an instance in the original field bindings
      [else    (error 'crazy)])))
                                                                                                                            

; ======================================================================
; CLASS CLOSURE MANAGEMENT
; ======================================================================

; creates a new class closure in the following form
;
;       (superclass-name ((method names) (method closures)) ((field names) (field default exprs))
;
(define class_closure
  (lambda (stmt state throw)
    (let* (   (method_field_list    (parse_class_body (class_body stmt) (class-name stmt) (lambda (v) v)))
              (supercc              (if (eq? (class_extends stmt) 'novalue)   ; gets the super class closure if deriving
                                           null
                                           (get_value (class_extends stmt) state (lambda (v) v))))
              (final_mflist           (list
                                       (method_bindings method_field_list)        ; must reverse the natural ordering of field names for processing in idx_of
                                       (list (reverse (caar (field_bindings method_field_list))) (reverse (cadar (field_bindings method_field_list))))))   )
      (cond
        [(null? supercc)   (cons 'novalue final_mflist)]
        [else              (cons (class_extends stmt) (list    ; appending super class fields onto the class closure being generated
                                                         (method_bindings final_mflist)
                                                         (list
                                                             (append (caar (field_bindings final_mflist)) (car (cc_field_bindings supercc)))
                                                             (append (cadar (field_bindings final_mflist)) (cadr (cc_field_bindings supercc))))))]))))


; parses over the class body and returns a list containing...
;   1. Method bindings           => ((method_names) (method_closures))
;   2. Instance names binindgs   => ((instance_field_names) (default_value_expressions))
(define parse_class_body
  (lambda (tree classname return)
    (cond
      [(null? tree)  (return (list empty_layer empty_layer))]

      ; case where a field is encountered
      [(eq? (class_dec_type tree) 'var)   (parse_class_body (cdr tree)
                                                           classname
                                                           (lambda (v) (return (list (method_bindings v)
                                                                                     (list (cons (binding_name tree) (variable_names (field_bindings v)))
                                                                                                 (cons (binding_expr tree) (variable_values (field_bindings v))))))))]
      ; case where a method is encountered
      [else       (parse_class_body (cdr tree)
                                   classname
                                   (lambda (v) (return (list (list (cons (binding_name tree) (variable_names v))
                                                                   (cons (create_method_closure
                                                                             (add_implicit_for_nonstatic (binding_name tree) (method_formal_params tree))
                                                                             (method_def_body tree)
                                                                             classname)
                                                                         (variable_values v)))
                                                             (car (field_bindings v))))))])))


; will add the implicit "this" to formal parameters only if non static
(define add_implicit_for_nonstatic
  (lambda (func_name params)
    (cond
      ((eq? func_name 'main) params)
      (else (append params (list 'this))))))  ; have to add to back of params in order for "restore_state" to function correctly


; ======================================================================
; METHOD CLOSURE MANAGEMENT
; ======================================================================

; creates a method method closure with the following 5 components...
;    1. formal parameters
;    2. method body
;    3. function that generates active environment for method execution
;    4. function that returns the closure of the containing class
;    5. the name of the instance that "this" is an alias for
(define create_method_closure
  (lambda (params body class-name)
    (list
       params
       body
       (lambda (s) (remove_all_layers_but_global s))  ; (lambda (s) (add_binding name (get_value name s (lambda (v) v)) state)) from project 3
       (lambda (s) class-name)
       'novalue)))   ; the name that "this" is an alias for...we need to store this based on how "restore_state" works...by default it isn't loaded


(define remove_all_layers_but_global
  (lambda (state)
    (cond
      [(null? (cdr state))   state]
      [else                  (remove_all_layers_but_global (remove_layer state))])))


; given a method name and a origin class, this will return the method closure of mname if exist in the class
; otherwise, the super class and subsequent ancestory will be searched for the method
(define find_method_closure
  (lambda (mname classname state)
    (let* (   (cc       (get_value classname state (lambda (v) v)))
              (methods              (list (cc_method_bindings cc)))   )

      (find_method_closure_helper mname methods state (superclass cc)))))


; helper for "find_method_closure"...does the actual searching in the method binding list
(define find_method_closure_helper
  (lambda (mname methods state super)
    (cond
      [(and (null? (variable_names methods)) (eq? super 'novalue))   (error 'method-not-found)]
      [(null? (variable_names methods))                              (find_method_closure mname super state)]
      [(eq? (front_name methods) mname)                              (front_value methods)]
      [else                                                          (find_method_closure_helper mname (remaining_state methods) state super)])))


; ======================================================================
; INSTANCE CLOSURE MANAGEMENT
; ======================================================================

; creates new instance closure that will take runtime type and instance field values
(define instance_closure
  (lambda (runtime_type state)
    (list runtime_type (get_default_field_values runtime_type state))))


; given a classname, evaluates the default field expressions and returns their values
(define get_default_field_values
  (lambda (classname state)
    ; if the field generating expressions where actual expressions instead of constants, then this must change
    ; because the expressions would just be returned instead of evaluated
    (reverse (instance_field_default_exprs
                 (get_value classname state (lambda (v) v))))))  ; class closure


; A function that will return the instance closure for some input name
; If argument stmt is an atom, it represents either 1) a variable name, 2) the "this" keyword, or 3) the "super" keyword.
;       There closures can be obtained by simple state lookup functions.
; Otherwise, the argument being passed in is of the form (new class-name), for which we have to generated a new instance closure
(define get_instance
  (lambda (stmt state classname)
    (cond
      [(or (eq? stmt 'this) (eq? stmt 'super))      (get_value 'this state (lambda (v) v))]
      [(and (in-local-state? stmt state) (atom? stmt))    (get_value stmt state (lambda (v) v))]
      [(atom? stmt)                                 (get_inst_value (list 'dot 'this stmt) state classname)]
      [else               (M_value stmt state null (lambda (v) v) classname)])))

; [(eq? stmt 'super)  (get_super_inst (get_value classname)


; obtains the value of some instance field
; input: expr is syntax of the following form...(dot inst_name field_name)
(define get_inst_value
  (lambda (expr state classname)
    (let* (  (inst (get_instance (leftoperand expr) state classname))
             (cc_field_bindings (instance_field_names
                                 (get_value classname state (lambda (v) v))))  )
      
      (idx_of (lookup_fields cc_field_bindings (rightoperand expr))
              (instance_values inst)))))


; given a list of field names, return the current BACK INDEX of argument "name"
;    BACK INDEX ( (length-1) - normal index), which will subsequently be used to find the associated instance value
(define lookup_fields
  (lambda (inst_names name)
    (cond
      [(null? inst_names)            (error 'instance_field_not_valid)]
      [(eq? (car inst_names) name)   (length (cdr inst_names))]
      [else                          (lookup_fields (cdr inst_names) name)]))) 


; takes the index output from "lookup_fields", and returns the value at that index
(define idx_of
  (lambda (n inst_values)
    (cond
      [(null? inst_values)  (error 'field-index-not-possible)]
      [(zero? n)            (car inst_values)]
      [else                 (idx_of (- n 1) (cdr inst_values))])))


; updates the value of an instance field, given the instance name, field name, and new value
(define update_inst_value
  (lambda (expr value state classname)
     (let* (   (inst (get_instance (leftoperand expr) state classname))
               (cc_field_bindings (instance_field_names
                                   (get_value classname state (lambda (v) v))))   )
       
      (idx_of_update (lookup_fields cc_field_bindings (rightoperand expr))
                     value
                     (instance_values inst)
                     (lambda (v) v)))))


; takes the index output from "lookup_fields", and updates the value at that index
(define idx_of_update
  (lambda (n newval inst_values return)
    (cond
      [(null? inst_values)  (error 'field-index-not-possible)]
      [(zero? n)            (return (cons newval (cdr inst_values)))]
      [else                 (idx_of_update (- n 1) newval (cdr inst_values)
                                    (lambda (v) (cons (car inst_values) v)))])))


; ======================================================================
; DENOTATIONAL SEMANTICS FUNCTIONS
; ======================================================================


; Checks whether a variable name is currently in the state. If so, the name is returned, otherwise an error is returned
(define M_name
  (lambda (var state return)
    (cond
      [(null? state)                         (error 'using-before-declaring)]
      [(null? (variable_names state))        (M_name var (remaining_layers state) return)]
      [(eq? (front_name state) var)          (return var)]
      [else                                  (M_name var (remaining_state state) return)])))


; evaluates an expression through the lens of relational operators/booleans
(define M_boolean
  (lambda (expr state throw return classname)
     (cond
       ; expressions with no operators
       [(eq? expr 'true)                 (return 'true)]
       [(eq? expr 'false)                (return 'false)]
       [(number? expr)                   (return 'error)]
       [(and (atom? expr) (in-local-state? expr state))  (M_boolean (get_value expr state (lambda (v) v)) state throw return classname)]
       [(atom? expr)                                     (M_boolean (M_value (list 'dot 'this expr) state throw return classname) state throw return classname)]
       [(and (eq? (operator expr) 'funcall) (list? (leftoperand expr)))        (M_boolean (M_call_value expr state throw classname) state throw return classname)]
       [(eq? (operator expr) 'funcall)                                         (M_boolean (M_call_value (list 'funcall (list 'dot 'this (leftoperand expr))) state throw classname) state throw return classname)]
       
       ; expressions with operators
       [(eq? (operator expr) '&&)        (M_boolean (leftoperand expr) state throw
                                           (lambda (v_left) (M_boolean (rightoperand expr) state throw
                                                                       (lambda (v_right) (return (language_bool (and (eq? v_left 'true) (eq? v_right 'true)))))
                                                                       classname))
                                           classname)]
       
       [(eq? (operator expr) '||)        (M_boolean (leftoperand expr) state throw
                                           (lambda (v_left) (M_boolean (rightoperand expr) state throw
                                                                       (lambda (v_right) (return (language_bool (or (eq? v_left 'true) (eq? v_right 'true)))))
                                                                       classname))
                                           classname)]

       [(eq? (operator expr) '!)         (M_boolean (leftoperand expr) state throw
                                                    (lambda (v) (return (language_bool (not (eq? v 'true)))))
                                                    classname)]
       
       [(eq? (operator expr) '!=)        (M_value (leftoperand expr) state throw
                                           (lambda (v_left) (M_value (rightoperand expr) state throw
                                                                     (lambda (v_right) (return (language_bool (not (eq? v_right v_left)))))
                                                                     classname))
                                           classname)]
       
       [(eq? (operator expr) '==)        (M_value (leftoperand expr) state throw
                                           (lambda (v_left) (M_value (rightoperand expr) state throw
                                                                     (lambda (v_right) (return (language_bool (eq? v_right v_left))))
                                                                     classname))
                                           classname)]
       
       [(eq? (operator expr) '<)        (M_int (leftoperand expr) state throw
                                          (lambda (v_left) (M_int (rightoperand expr) state throw
                                                                  (lambda (v_right) (return (language_bool (< v_left v_right))))
                                                                  classname))
                                          classname)]
       
       [(eq? (operator expr) '<=)        (M_int (leftoperand expr) state throw
                                           (lambda (v_left) (M_int (rightoperand expr) state throw
                                                                   (lambda (v_right) (return (language_bool (<= v_left v_right))))
                                                                   classname))
                                           classname)]
       
       [(eq? (operator expr) '>)        (M_int (leftoperand expr) state throw
                                          (lambda (v_left) (M_int (rightoperand expr) state throw
                                                                  (lambda (v_right) (return (language_bool (> v_left v_right))))
                                                                  classname))
                                          classname)]
       
       [(eq? (operator expr) '>=)        (M_int (leftoperand expr) state throw
                                           (lambda (v_left) (M_int (rightoperand expr) state throw
                                                                   (lambda (v_right) (return (language_bool (>= v_left v_right))))
                                                                   classname))
                                           classname)]
       [else                              (return 'error)])))


; evaluates an expression through the lens of mathematical operators/integers
; (dot a x)
(define M_int
  (lambda (expr state throw return classname)
    (cond
      [(number? expr)                          (return expr)]
      [(or (eq? expr 'true) (eq? expr 'false)) (return 'error)]
      
      ; dealing with single variable
      [(and (atom? expr) (in-local-state? expr state))  (M_int (get_value expr state (lambda (v) v)) state throw return classname)]
      [(atom? expr)                                     (M_int (M_value (list 'dot 'this expr) state throw (lambda (v) v) classname) state throw return classname)]
      [(and (eq? (operator expr) 'funcall) (list? (leftoperand expr)))        (M_int (M_call_value expr state throw classname) state throw return classname)]
      [(eq? (operator expr) 'funcall)                                         (M_int (M_call_value (list 'funcall (list 'dot 'this (leftoperand expr))) state throw classname) state throw return classname)]
      [(eq? (operator expr) 'dot)              (return (get_inst_value expr state classname))]  
      [(and (eq? (operator expr) '-)
            (null? (optional_token expr)))      (M_int (leftoperand expr) state throw
                                                  (lambda (v) (return (- v))) classname)]
      
      [(eq? (operator expr) '-)                 (M_int (leftoperand expr) state throw
                                                  (lambda (v_left) (M_int (rightoperand expr) state throw
                                                                          (lambda (v_right) (return (- v_left v_right))) classname))
                                                  classname)]
      
      [(eq? (operator expr) '+)                 (M_int (leftoperand expr) state throw
                                                  (lambda (v_left) (M_int (rightoperand expr) state throw
                                                                          (lambda (v_right) (return (+ v_left v_right)))
                                                                          classname))
                                                  classname)]
      
      [(eq? (operator expr) '*)                 (M_int (leftoperand expr) state throw
                                                  (lambda (v_left) (M_int (rightoperand expr) state throw
                                                                          (lambda (v_right) (return (* v_left v_right)))
                                                                          classname))
                                                  classname)]
      
      [(eq? (operator expr) '/)                (M_int (leftoperand expr) state throw
                                                  (lambda (v_left) (M_int (rightoperand expr) state throw
                                                                          (lambda (v_right) (return (quotient v_left v_right)))
                                                                          classname))
                                                  classname)]
       
      [(eq? (operator expr) '%)                (M_int (leftoperand expr) state throw
                                                  (lambda (v_left) (M_int (rightoperand expr) state throw
                                                                          (lambda (v_right) (return (remainder v_left v_right)))
                                                                          classname))
                                                  classname)]
      [else                                    (return 'error)])))
 

; Takes in list of the form "(var variable)" or "(var variable value)"
; If a "value" is specified, the function returns the a new state with the name/value binding. Otherwise, the function returns the state with the name bound to 'novalue.
(define M_declare
  (lambda (stmt state throw classname)
    (cond
      [(null? (optional_token stmt))            (add_binding (leftoperand stmt) 'novalue state)]

      ; if you finish this project, then delete this line
      ; [(or (eq? (car stmt) 'function) (eq? (car stmt) 'static-function))   (add_binding (function_name stmt) (method_closure (function_name stmt) (function_params stmt) (function_body stmt) state) state)]
      
      ;;; adds a binding for the class name, and the class closure.
      [(eq? (car stmt) 'class)                  (add_binding (class-name stmt)
                                                             (class_closure stmt state throw)
                                                             state)]
      [(eq? (car stmt) 'var)                     (add_binding (leftoperand stmt) (M_value (rightoperand stmt) state throw (lambda (v) v) classname) state)]
      [else                                     (throw 'error)])))


; M_if 
(define M_if 
   (lambda (stmt state return next break continue throw classname)
      (cond 
        [(eq? (M_boolean (condition stmt) state throw (lambda (v) v) classname) 'true)      (M_state (first_stmt stmt) state return next break continue throw classname)] 
        [(pair? (else_if stmt))                                             (M_state (second_stmt stmt) state return next break continue throw classname)]
        [else                                                               (next state)])))


(define M_while
  (lambda (stmt state return next break throw classname)
     (cond
       [(eq? (M_boolean (condition stmt) state throw (lambda (v) v) classname) 'true) (M_while stmt
                                                                                               (call/cc (lambda (continue)
                                                                                                               (M_state (loop_body stmt) state return continue break continue throw classname)))
                                                                                               return next break throw classname)]
       [else      (next state)])))

       
; Takes in list of the form "(= variable expression)"
; Returns the state after removing the previous name/value binding for "var" (if it existed) and adding the new (variable, value) binding, where value is what expr evaluates to
(define M_assign
  (lambda (stmt state next throw classname)
    (cond
      [(list? (leftoperand stmt))  (update_value (leftoperand (leftoperand stmt))
                                                 (list (runtime_type (get_value (leftoperand (leftoperand stmt)) state (lambda (v) v)))
                                                       (update_inst_value (leftoperand stmt)
                                                            (M_value (rightoperand stmt) state throw (lambda (v) v) classname)
                                                            state classname))
                                                 state (lambda (v) v))]
      [(in-local-state? (leftoperand stmt) state)     (next (update_value (leftoperand stmt)
                                                                    (M_value (rightoperand stmt) state throw (lambda (v) v) classname)
                                                                    state
                                                                    (lambda (v) v)))]
      [else                                     (update_value 'this
                                                              (list (runtime_type (get_value 'this state (lambda (v) v)))
                                                                    (update_inst_value (list 'dot 'this (leftoperand stmt))
                                                                                       (M_value (rightoperand stmt) state throw (lambda (v) v) classname)
                                                                                       state classname))
                                                              state (lambda (v) v))])))


(define M_try
     (lambda (stmts state return next break continue throw classname)
       (let* ((newreturn          (lambda (s) (M_state (finally_from_try stmts) s return return break continue throw classname)))
              (newbreak           (lambda (s) (M_state (finally_from_try stmts) s return break break continue throw classname)))
              (newcontinue        (lambda (s) (M_state (finally_from_try stmts) s return continue break continue throw classname)))
              (newthrow           (lambda (s) (M_state (finally_from_try stmts) s return throw break continue throw classname)))
              (finallycont        (lambda (s) (M_state (finally_from_try stmts) s return next break continue throw classname)))
              (mythrow1           (lambda (v s) (M_state (catch_and_finally stmts) (add_binding (catch_exception_name stmts) v s) return next break continue throw classname)))
              (mythrow2           (lambda (v s) (M_state (catch_and_finally stmts) (add_binding (catch_exception_name stmts) v s) newreturn finallycont newbreak newcontinue newthrow classname))))
         (cond
           [(and (null? (catch_only stmts)) (null? (finally_from_try stmts)))
                                                        (interpret_block (try_body stmts) (add_layer state) return next break continue throw classname)]
           [(null? (catch_only stmts))                  (interpret_block (try_body stmts) (add_layer state) newreturn finallycont newbreak newcontinue newthrow classname)]
           [(null? (finally_from_try stmts))            (interpret_block (try_body stmts) (add_layer state) return next break continue mythrow1 classname)]
           [else                                        (interpret_block (try_body stmts) (add_layer state) newreturn finallycont newbreak newcontinue mythrow2 classname)]))))


(define M_catch
  (lambda (stmts state return next break continue throw classname)
    (cond
      [(null? (finally_from_catch stmts))     (interpret_block (catch_body stmts) state return next break continue throw classname)] 
      [else                                   (interpret_block (catch_body stmts) state return next break continue throw classname)])))


(define M_finally
  (lambda (stmts state return next break continue throw classname)
     (interpret_block (finally_body stmts) (add_layer state) return next break continue throw classname)))
  


; input: a funcall statement, a state before the funcall execution, and two continuations next and throw
; output: the state after executing the funcall in stmt
(define M_call_state
  (lambda (stmt state next throw classname)
    (let* (   (inst (get_instance (leftoperand (leftoperand stmt)) state classname))
              (method (set_this_alias
                         (leftoperand (cadr stmt))
                         (find_method_closure
                              (rightoperand (cadr stmt))
                              (handle_inst_type (leftoperand (cadr stmt)) inst classname state)
                              state)
                         (lambda (v) v)))
              (fstate1 ((closure_environment method) state))
              (fstate2 (add_layer fstate1))
              (fstate3 (bind_parameters (closure_params method) (function_args stmt)
                                     fstate2 state throw classname inst (lambda (v) v)))         )
      ; i'm not sure if the changes made will persist because technically were not keeping closures in a box (unless they come from the state directly
      (interpret_block
         (closure_body method)
         fstate3
         (lambda (v s) (next (restore_state (remove_layer s) state (get_this_alias method) classname)))
         (lambda (s) (next (restore_state s state (get_this_alias method) classname)))
         (lambda (s) (error 'break-out-of-loop))
         (lambda (s) (error 'continue-out-of-loop))
         (lambda (s) (throw (restore_state (remove_layer s) state (get_this_alias method) classname)))
         ((compiletime_environment method) state)))))


; returns the boolean, integer, or instance closure value that an expression evaluates to
(define M_value
  (lambda (expr state throw return classname)
    (cond
      [(and (list? expr) (eq? (operator expr) 'funcall) (list? (leftoperand expr)))  (M_call_value expr state throw classname)]
      [(and (list? expr) (eq? (operator expr) 'funcall))                             (M_call_value (list 'funcall (list 'dot 'this (leftoperand expr)))
                                                                                                   state throw classname)]
      [(and (list? expr) (eq? (operator expr) 'new))                                 (instance_closure (cadr expr) state)]

      ; use the instance (leftoperand expr) to determine the "compile time type"
      ; technically if we ever reach a variable we should be creating a (dot this var) construct instead    but what if it's local?
      [(and (list? expr) (eq? (operator expr) 'dot))      (return (get_inst_value expr state classname))]
      [else                                               (let ((bool_output (M_boolean expr state throw (lambda (v) v) classname)))
                                                            (if (eq? bool_output 'error)
                                                                (let ((int_output (M_int expr state throw (lambda (v) v) classname)))
                                                                  (if (eq? int_output 'error)
                                                                      (return (M_inst expr state classname))
                                                                      (return int_output)))
                                                                (return bool_output)))])))

(define M_inst
  (lambda (expr state classname)
    (cond
      [(in-local-state? expr state)    (get_value expr state (lambda (v) v))]
      [else                      (get_inst_value (list 'dot 'this expr)
                                                 state
                                                 classname)])))
                                                 

(define handle_inst_type
  (lambda (inst_name inst classname state)
    (cond
      [(eq? inst_name 'super)   (superclass (get_value classname state (lambda (v) v)))]
      [else                     (runtime_type inst)])))


; this function takes a stmt of the form (funcall (dot inst name))
(define M_call_value
  (lambda (stmt state throw classname)
    (let* (   (inst (get_instance (leftoperand (cadr stmt)) state classname))
              (method (set_this_alias
                         (leftoperand (cadr stmt))
                         (find_method_closure
                              (rightoperand (cadr stmt))
                              (handle_inst_type (leftoperand (cadr stmt)) inst classname state)
                               state)
                         (lambda (v) v)))   
              (fstate1 ((closure_environment method) state))
              (fstate2 (add_layer fstate1))
              (fstate3 (bind_parameters (closure_params method) (function_args stmt)
                                        fstate2 state throw classname inst (lambda (v) v)))           )
      (call/cc (lambda (return) (interpret_main
                                    (closure_body method)
                                    fstate3
                                    return
                                    (lambda (s) (error 'no-return-statement))
                                    (lambda (s) (error 'break-out-of-loop))
                                    (lambda (s) (error 'continue-out-of-loop))
                                    (lambda (v s) (throw v (restore_state (remove_layer s) state (get_this_alias method) classname)))
                                    ((compiletime_environment method) state)))))))
  

; Takes in a list from the parser that represents a single accepted statement, and calls the proper mapping function.
; Returns the state after the mapping function is applied

;;; M_state will now take another parameter for the classname as its compile time type
;;; add a "class" case where it hits the class, we create the class closure. 
(define M_state
  (lambda (stmt state return next break continue throw classname)
    (cond
      [(null? stmt)                 (next state)]
      [(eq? (car stmt) 'var)        (M_declare stmt state throw classname)]
      [(and (eq? (car stmt) 'return) (eq? (procedure-arity return) 2))    (return
                                                                           (M_value (leftoperand stmt) state throw (lambda (v) v) classname)
                                                                           (remove_layer state))]
      [(eq? (car stmt) 'return)     (return (M_value (leftoperand stmt) state throw (lambda (v) v) classname))]
      [(eq? (car stmt) 'break)      (break (remove_layer state))] 
      [(eq? (car stmt) 'continue)   (continue (remove_layer state))]
      [(and (eq? (car stmt) 'throw) (eq? (procedure-arity throw) 2))      (throw (M_value (leftoperand stmt) state throw (lambda (v) v) classname) (add_layer (remove_layer state)))]
      [(eq? (car stmt) 'throw)                                            (throw 'exception-thrown-and-not-caught)]
      [(eq? (car stmt) '=)          (M_assign stmt state next throw classname)]
      [(eq? (car stmt) 'if)         (M_if stmt state return next break continue throw classname)]
      [(eq? (car stmt) 'while)      (M_while stmt state return next next throw classname)]
      [(eq? (car stmt) 'begin)      (interpret_block (cdr stmt) (add_layer state) return next break continue throw classname)]
      [(eq? (car stmt) 'try)        (M_try stmt state return next break continue throw classname)]
      [(eq? (car stmt) 'finally)    (M_finally stmt state return next break continue throw classname)]
      [(eq? (car stmt) 'function)   (M_declare stmt state throw classname)]  ;; probably need to remove these since M_state doesn't handle function (method) defs anymore
      [(eq? (car stmt) 'static-function) (M_declare stmt state throw classname)]
      [(and (eq? (car stmt) 'funcall) (list? (leftoperand stmt)))  (M_call_state stmt state next throw classname)]
      [(eq? (car stmt) 'funcall)                          (M_call_state (list 'dot 'this stmt) state next throw classname)]
      [(eq? (car stmt) 'class)      (M_declare stmt state throw classname)]  ;;; once it hits here we create a class binding
      [(eq? (caar stmt) 'catch)     (M_catch stmt state return next break continue throw classname)]
      [else                         (return 'error)])))      
      

; recurses through all the statements in the parse tree and returns the state after execution of the source program
;;; possible class-name param may need to be passed here. 
(define interpret_block
  (lambda (tree state return next break continue throw classname)   
    (cond
      [(null? tree)     (next state)]
      [else             (interpret_block
                         (cdr tree)
                         (call/cc (lambda (next) (M_state (car tree) state return next break continue throw classname)))
                         return
                         next
                         break
                         continue
                         throw
                         classname)])))


; helper method for the root function "interpret"
; recurses through all the statements in the parse tree and returns the return value of the block of statements being executed.
; if the block of statements doesn't call return, then 'void is returned

;;; possible class-name param may need to be passed here. 
(define interpret_main
  (lambda (tree state return next break continue throw classname)
    (cond
      [(null? tree)      (return 'void)]
      [else              (interpret_main (cdr tree)
                                         (call/cc (lambda (next)
                                                     (M_state (car tree) state return next break continue throw classname)))
                                         return
                                         next
                                         break
                                         continue
                                         throw
                                         classname)])))


(define interpret_static_main
  (lambda (classname state return)
    (let*  ((main_method_closure  (get_value
                                       'main
                                       (list (cc_method_bindings (get_value classname state (lambda (v) v))))
                                       (lambda (v) v)))
            (fstate1  ((closure_environment main_method_closure) (add_layer state)))
            (fstate2  (add_layer fstate1))
            (fstate3  (bind_parameters (closure_params main_method_closure)
                                       '()
                                       fstate2
                                       state
                                       null
                                       classname
                                       null
                                       (lambda (v) v))))
      (call/cc (lambda (return) (interpret_main (closure_body main_method_closure)
                                                fstate3
                                                return
                                                (lambda (s) (error 'no-return-statement))
                                                (lambda (s) (error 'break-out-of-loop))
                                                (lambda (s) (error 'continue-out-of-loop))
                                                (lambda (s) (error s))
                                                classname))))))

                        
    ;(return (M_call_value (list 'funcall (list 'dot 'this 'main)) state (lambda (s) (error 'exception-thrown)) classname))))
    


; recurses through all the global variable/global functions and adds the bindings to the top layer
; of the state accordingly. After doing so, the instructions inside the 'main' function are executed with the given state

;;; added new continuation here that will take the classname so it can execute the main method on a certain class depending on the name user gives.
;;; need to update the function so that it returns the class closure.
;;; make a function "get_class_closure" that will take the class name and the class body and return the class closure.
(define interpret_global
  (lambda (tree class-name state return)
    (cond
      [(null? tree)   (interpret_static_main class-name state return)]  ;(return (M_call_value (list 'funcall 'main) state (lambda (s) (error 'exception-thrown))))]
      [else                                         (interpret_global
                                                       (cdr tree)
                                                       class-name
                                                       (call/cc (lambda (next) (M_state (car tree) state return next null null null null))) 
                                                        return)])))