;Gehrig Keane
;EECS 662
;Project 3
;Task 2
#lang plai

; Abstract Syntax
(define-type CFWAER
	( num	(n number?) )
	( id	(name symbol?) )
	( op	(operator symbol?) (l CFWAER?) (r CFWAER?) )
	( fun	(param symbol?) (body CFWAER?) )
	( app	(fun-expr CFWAER?) (arg-expr CFWAER?) )
	( if0	(if-body CFWAER?) (then-body CFWAER?) (else-body CFWAER?) )
	( with	(param symbol?) (named-expr CFWAER?) (bound-body CFWAER?) )
	( rec	(param symbol?) (named-expr CFWAER?) (bound-body CFWAER?))
);CFWAER

; Value Construct with boxing beneath
(define-type CFWAER-Value
	( numV (n number?) )
	( closureV (param symbol?) (body CFWAER?) (env Env?))
);CFWAER-Value

; Deferd Sub - Deferred Substitution List
(define-type Env
	( mtSub )
	( aSub (name symbol?) (value CFWAER-Value?) (env Env?) )
	( aRecSub (name symbol?) (value boxed-CFWAER-value?) (env Env?))
);Env

; Boxed Value - type checking
(define boxed-CFWAER-value?
	(lambda (x)
		(and	(box? x) 
				(CFWAER-Value? (unbox x))
		);and
	);lambda
);boxed-CFWAER-value?

; Cyclically-bind-and-interp
(define cyclically-bind-and-interp
	(lambda (bound-id named-expr env)
		(local	(	(define value-holder (box (numV 1729)))
					(define new-env (aRecSub bound-id value-holder env))
					(define named-expr-val (interp-cfwaer named-expr new-env))
				);define
				(begin
					(set-box! value-holder named-expr-val)
					new-env
				);begin
		);local
	);lambda
);cyclically-bind-and-interp

; Binop Record - Lookup table structure
(define-type binop-rec
	( binop (name symbol?) (op procedure?) )
);binop-rec

; Ops - Operator Table
(define ops (list (binop '+ +) (binop '- -) (binop '* *) (binop '/ /)))

; Lookup Operator - Operator Lookup function
(define lookup-ops
	(lambda (op-name op-table)
		(cond ((empty? op-table) (error 'lookup-ops (string-append "Operator not found: " (symbol->string op-name))))
			(else
				(if (symbol=? (binop-name (car op-table)) op-name) (binop-op (car op-table)) (lookup-ops op-name (cdr op-table)))
			);else
		);cond
	);lambda
);lookup-ops

; Lookup Symbol - Deferred Substitution list lookup
(define lookup-sym
	(lambda (n env)
		(type-case Env env
			( mtSub () (error 'lookup-sym (string-append "Identifier not found: " (symbol->string n))) )
			( aSub	(name value next-env)
					(if (symbol=? name n) value (lookup-sym n next-env) )
			);aSub
			( aRecSub (name box-value next-env)
					(if (symbol=? name n) (unbox box-value) (lookup-sym n next-env))
			)
		);type-case
	);lambda
);lookup-sym

; Interp CFWAER - interpret data structure
(define interp-cfwaer
	(lambda (expr env) 
		(type-case CFWAER expr
			( num	(n) (numV n) )
			( id	(name) (lookup-sym name env) )
			( op	(op lhs rhs) (numV ((lookup-ops op ops) (numV-n(interp-cfwaer lhs env)) (numV-n(interp-cfwaer rhs env)))) )
			( if0	(c t e) (if (= (numV-n (interp-cfwaer c env)) 0) (interp-cfwaer t env) (interp-cfwaer e env)) )
			( fun	(param body) (closureV param body env) );Do Nothing! Why??? It's a value! old:( fun	(param body) expr )
			( with	(id expr body) (interp-cfwaer (app (fun id body) expr) env)); bound-id named-expr and bound-body are horrendously long names
			( rec 	(id expr body) (interp-cfwaer body (cyclically-bind-and-interp id expr env)))
			( app	(fun-expr arg-expr)
				(local ((define fun-val (interp-cfwaer fun-expr env)))
					(interp-cfwaer (closureV-body fun-val)
						(aSub	(closureV-param fun-val)
								(interp-cfwaer arg-expr env); Why so Strict! (Removal of interp call is lazy)
								(closureV-env fun-val)); Static scoping - old: just -> env
					);interp-cfwaer
				);local
			);app
		);type-case
	);lambda
);interp-cfwaer

; Parse CFWAER - walks input and produces concrete syntax for CFWAER
(define parse-cfwaer
	(lambda (expr)
		(cond
			( (number? expr) (num expr) )
			( (symbol? expr) (id expr) )
			( (list? expr)
				(case (car expr)
					( (+)		(op `+	(parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))) ) 
					( (-)		(op `-	(parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))) ) 
					( (*)		(op `*	(parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))) ) 
					( (/)		(op `/	(parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))) )
					( (if0)		(if0	(parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr)) (parse-cfwaer (cadddr expr))) )
					( (fun)		(fun	(cadr expr)  (parse-cfwaer (caddr expr))) )
					( (with)	(with	(caadr expr) (parse-cfwaer (cadadr expr)) (parse-cfwaer (caddr expr))) )
					( (rec)		(rec 	(caadr expr) (parse-cfwaer (cadadr expr)) (parse-cfwaer (caddr expr))) )
					( else		(app	(parse-cfwaer (car expr)) (parse-cfwaer (cadr expr))) )
				);case
			);list?
			( else (error 'parse-cfwaer "Parsing Error!") );Silly input, tricks are for kids!
		);cond
	);lambda
);parse-cfwaer

; Eval CFWAER - rope interp, elab, and parse together
(define eval-cfwaer
	(lambda (expr)
		(interp-cfwaer (parse-cfwaer expr) (mtSub))
	);lambda
);eval-cfwaer

; Test Cases provided by Dr. Alexander
(test (eval-cfwaer '{{fun x {+ 1 3}} 1}) (numV 4))
(test (eval-cfwaer '{with {y 1} {{fun x {+ y x}} 3}}) (numV 4))
(test (eval-cfwaer '{with {y 1} {with {f {fun x {+ y x}}} {f 3}}}) (numV 4))
(test (eval-cfwaer '{with {y 1} {with {f {fun x {+ y x}}} {with {y 100} {f 3}}}}) (numV 4))
(test (eval-cfwaer '{rec {fac {fun x {if0 x 1 {* x {fac {- x 1}}}}}} {fac 0}})
(numV 1))
(test (eval-cfwaer '{rec {fac {fun x {if0 x 1 {* x {fac {- x 1}}}}}} {fac 3}})
(numV 6))
(test (eval-cfwaer '{rec {fac {fun x {if0 x 1 {* x {fac {- x 1}}}}}} {fac 5}})
(numV 120))
(test (eval-cfwaer '{rec {ack {fun m {fun n {if0 m {+ n 1} {if0 n {{ack {- m 1}} 1} {{ack {- m 1}} {{ack m} {- n 1}}}}}}}} {{ack 1} 1}})
(numV 3))
(test (eval-cfwaer '{rec {ack {fun m {fun n {if0 m {+ n 1} {if0 n {{ack {- m 1}} 1} {{ack {- m 1}} {{ack m} {- n 1}}}}}}}} {{ack 2} 2}})
(numV 7))
(test (eval-cfwaer '{rec {ack {fun m {fun n {if0 m {+ n 1} {if0 n {{ack {- m 1}} 1} {{ack {- m 1}} {{ack m} {- n 1}}}}}}}} {{ack 3} 3}})
(numV 61))
(test (eval-cfwaer '{rec {ack {fun m {fun n {if0 m {+ n 1} {if0 n {{ack {- m 1}} 1} {{ack {- m 1}} {{ack m} {- n 1}}}}}}}} {{ack 0} 3}})
(numV 4))
(test (eval-cfwaer '{rec {ack {fun m {fun n {if0 m {+ n 1} {if0 n {{ack {- m 1}} 1} {{ack {- m 1}} {{ack m} {- n 1}}}}}}}} {{ack 3} 0}})
(numV 5))
(test (eval-cfwaer '{{fun x {+ 1 3}} 1}) (numV 4))
(test (eval-cfwaer '{rec {y 1} {{fun x {+ y x}} 3}}) (numV 4))
(test (eval-cfwaer '{rec {y 1} {with {f {fun x {+ y x}}} {f 3}}}) (numV 4))
(test (eval-cfwaer '{with {y 1} {rec {f {fun x {+ y x}}} {with {y 100} {f 3}}}}) (numV 4))
(test (eval-cfwaer '{rec {y 1} {rec {f {fun x {+ y x}}} {rec {y 100} {f 3}}}}) (numV 4))