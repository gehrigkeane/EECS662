;Gehrig Keane
;EECS 662
;Project 3
;Task 1
#lang plai

; Abstract Syntax
(define-type CFWAE
	( num	(n number?) )
	( id	(name symbol?) )
	( op	(operator symbol?) (l CFWAE?) (r CFWAE?) )
	( fun	(param symbol?) (body CFWAE?) )
	( app	(fun-expr CFWAE?) (arg-expr CFWAE?) )
	( if0	(if-body CFWAE?) (then-body CFWAE?) (else-body CFWAE?) )
	( with	(param symbol?) (named-expr CFWAE?) (bound-body CFWAE?) )
);CFWAE

; Value Construct
(define-type CFWAE-Value
	( numV (n number?) )
	( closureV (param symbol?) (body CFWAE?) (env DefrdSub?))
);CFWAE-Value

; Deferd Sub - Deferred Substitution List
(define-type DefrdSub
	( mtSub )
	( aSub (name symbol?) (value CFWAE-Value?) (ds DefrdSub?) )
);DefrdSub

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
	(lambda (n ds)
		(type-case DefrdSub ds
			( mtSub () (error 'lookup-sym (string-append "Identifier not found: " (symbol->string n))) )
			( aSub	(name value next-ds)
					(if (symbol=? name n) value (lookup-sym n next-ds) )
			);aSub
		);type-case
	);lambda
);lookup-sym

; Interp CFWAE - interpret data structure
(define interp-cfwae
	(lambda (expr ds) 
		(type-case CFWAE expr
			( num	(n) (numV n) )
			( id	(name) (lookup-sym name ds) )
			( op	(op lhs rhs) (numV ((lookup-ops op ops) (numV-n(interp-cfwae lhs ds)) (numV-n(interp-cfwae rhs ds)))) )
			( if0	(c t e) (if (= (numV-n (interp-cfwae c ds)) 0) (interp-cfwae t ds) (interp-cfwae e ds)) )
			( fun	(param body) (closureV param body ds) );Do Nothing! Why??? It's a value! old:( fun	(param body) expr )
			( with	(id expr body) (interp-cfwae (app (fun id body) expr) ds)); bound-id named-expr and bound-body are horrendously long names
			( app	(fun-expr arg-expr)
				(local ((define fun-val (interp-cfwae fun-expr ds)))
					(interp-cfwae (closureV-body fun-val)
						(aSub	(closureV-param fun-val)
								(interp-cfwae arg-expr ds); Why so Strict! (Removal of interp call is lazy)
								(closureV-env fun-val)); Static scoping - old: just -> ds
					);interp-cfwae
				);local
			);app
		);type-case
	);lambda
);interp-cfwae

; Parse CFWAE - walks input and produces concrete syntax for CFWAE
(define parse-cfwae
	(lambda (expr)
		(cond
			( (number? expr) (num expr) )
			( (symbol? expr) (id expr) )
			( (list? expr)
				(case (car expr)
					( (+)		(op `+	(parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))) ) 
					( (-)		(op `-	(parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))) ) 
					( (*)		(op `*	(parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))) ) 
					( (/)		(op `/	(parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))) )
					( (if0)		(if0	(parse-cfwae (cadr expr)) (parse-cfwae (caddr expr)) (parse-cfwae (cadddr expr))) )
					( (fun)		(fun	(cadr expr) (parse-cfwae (caddr expr))) )
					( (with)	(with	(caadr expr) (parse-cfwae (cadadr expr)) (parse-cfwae (caddr expr))) )
					( else		(app	(parse-cfwae (car expr)) (parse-cfwae (cadr expr))) )             
				);case
			);list?
			( else (error 'parse-cfwae "Parsing Error!") );Silly input, tricks are for kids!
		);cond
	);lambda
);parse-cfwae

; Eval CFWAE - rope interp, elab, and parse together
(define eval-cfwae
	(lambda (expr)
		(interp-cfwae (parse-cfwae expr) (mtSub))
	);lambda
);eval-cfwae

; Test Cases provided by Dr. Alexander (without rec structure)
(test (eval-cfwae '{{fun x {+ 1 3}} 1}) (numV 4))
(test (eval-cfwae '{with {y 1} {{fun x {+ y x}} 3}}) (numV 4))
(test (eval-cfwae '{with {y 1} {with {f {fun x {+ y x}}} {f 3}}}) (numV 4))
(test (eval-cfwae '{with {y 1} {with {f {fun x {+ y x}}} {with {y 100} {f 3}}}}) (numV 4))
(test (eval-cfwae '{{fun x {+ 1 3}} 1}) (numV 4))