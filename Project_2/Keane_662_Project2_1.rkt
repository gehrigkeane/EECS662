;Gehrig Keane
;EECS 662
;Project 2
;Task 1
#lang plai

; Abstract Syntax
(define-type CFAE
	( num	(n number?) )
	( id	(name symbol?) )
	( op	(operator symbol?) (l CFAE?) (r CFAE?) )
	( fun	(param symbol?) (body CFAE?) )
	( app	(fun-expr CFAE?) (arg-expr CFAE?) )
	( if0	(if-body CFAE?) (then-body CFAE?) (else-body CFAE?) )
);CFAE

; Deferd Sub - Deferred Substitution List
(define-type DefrdSub
	( mtSub )
	( aSub (name symbol?) (value CFAE?) (ds DefrdSub?) )
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

; Interp CFAE - interpret data structure
(define interp-cfae
	(lambda (expr ds) 
		(type-case CFAE expr
			( num	(n) (num n) )
			( id	(name) (lookup-sym name ds) )
			( op	(op lhs rhs) (num((lookup-ops op ops) (num-n(interp-cfae lhs ds)) (num-n(interp-cfae rhs ds)))) )
			( if0	(c t e) (if (= (num-n (interp-cfae c ds)) 0) (interp-cfae t ds) (interp-cfae e ds)) )
			( fun	(param body) expr );Do Nothing! Why??? It's a value!
			( app	(fun-expr arg-expr)
				(local ((define fun-val (interp-cfae fun-expr ds)))
					(interp-cfae (fun-body fun-val)
						(aSub	(fun-param fun-val)
								(interp-cfae arg-expr ds); Why so Strict! (Removal of interp call is laxzy)
								ds); Dynamic scoping - star this for later
					);interp-cfae
				);local
			);app
		);type-case
	);lambda
);interp-cfae

; Parse CFAE - walks input and produces concrete syntax for CFAE
(define parse-cfae
	(lambda (expr)
		(cond
			( (number? expr) (num expr) )
			( (symbol? expr) (id expr) )
			( (list? expr)
				(case (car expr)
					( (+)	(op `+ (parse-cfae (cadr expr)) (parse-cfae (caddr expr))) ) 
					( (-)	(op `- (parse-cfae (cadr expr)) (parse-cfae (caddr expr))) ) 
					( (*)	(op `* (parse-cfae (cadr expr)) (parse-cfae (caddr expr))) ) 
					( (/)	(op `/ (parse-cfae (cadr expr)) (parse-cfae (caddr expr))) ) 
					( (if0)	(if0 (parse-cfae (cadr expr)) (parse-cfae (caddr  expr)) (parse-cfae (fourth expr))) )
					( (fun)	(fun (cadr expr) (parse-cfae (caddr expr))) )
					( else	(app (parse-cfae (car expr)) (parse-cfae (cadr expr))) )             
				);case
			);list?
			( else (error 'parse-cfae "Parsing Error!") );Silly input, tricks are for kids!
		);cond
	);lambda
);parse-cfae

; Eval CFWAE - rope interp, elab, and parse together
(define eval-cfae
	(lambda (expr)
		(interp-cfae (parse-cfae expr) (mtSub))
	);lambda
);eval-cfae

; Test Cases provided by Dr. Alexander
(test (eval-cfae '{+ 1 2}) (num 3))
(test (eval-cfae '{+ 2 {* 2 3}}) (num 8))
(test (eval-cfae '{{fun x x} 3}) (num 3))
(test (eval-cfae '{{fun x {+ x 1} } 1}) (num 2))
(test (eval-cfae '{if0 0 1 2}) (num 1))
(test (eval-cfae '{if0 {{fun x {- x 2}} 3} {{fun x {* 2 x}} 10} {{fun x {/ x 2}} 8}}) (num 4))
(test (eval-cfae '{{if0 0 {fun x {+ x 1}} {fun x {+ x 2}}} 0}) (num 1))
(test (eval-cfae '{{fun x {{fun y {+ x y}} 3}} 1}) (num 4))