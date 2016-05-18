;Gehrig Keane
;EECS 662
;Project 2
;Task 2
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

; Abstract Syntax
(define-type CFWAE
	( wnum		(n number?) )
	( wid		(name symbol?) )
	( wop		(operator symbol?) (l CFWAE?) (r CFWAE?) )
	( wif0		(check CFWAE?) (then-body CFWAE?) (else-body CFWAE?) )
	( wwith		(id symbol?) (bound-expr CFWAE?) (bound-body CFWAE?) )
	( wcond0	(branches list?) (base CFWAE?) )
	( wfun		(id symbol?) (body CFWAE?) )
	( wapp		(fun-expr CFWAE?) (expr CFWAE?) )
);CFWAE

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

; Parse CFWAE - walks input and produces concrete syntax for CFAE
(define parse-cfwae
	(lambda (expr)
		(cond
			( (number? expr) (wnum expr) )
			( (symbol? expr) (wid expr ) )
			( (list? expr)
				(case (car expr) 
					( (+)		(wop `+ (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))) )
					( (-)		(wop `- (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))) )
					( (*)		(wop `* (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))) )
					( (/)		(wop `/ (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))) )
					( (if0)		(wif0	(parse-cfwae (cadr expr)) (parse-cfwae (caddr expr)) (parse-cfwae (cadddr expr))) )
					( (with)	(wwith	(car (cadr expr)) (parse-cfwae (cadr (cadr expr)))(parse-cfwae (caddr expr))) )
					( (cond0)	(wcond0	(cascade-cond (reverse (cdr (reverse (cdr expr))))) (parse-cfwae (car (reverse expr)))) )
					( (fun)		(wfun	(cadr expr) (parse-cfwae (caddr expr))) )
					( else		(wapp	(parse-cfwae (car expr)) (parse-cfwae (cadr expr))) )
				);case
			);list?
			( else 'parse-cfwae "parsing failed!" );Silly input, tricks are for kids!
		);cond
	);lambda
);parse-cfwae
								
; Cascade Cond - (similar to previous cascade) interim function for transforming cond arms into CFAE paradigm
(define cascade-cond
	(lambda (armL)
		(cond
			; Base - no more arms
			( (empty? armL) '() )
			; Continue
			( else 
				(cons (list (parse-cfwae (caar armL)) (parse-cfwae (cadar armL))) (cascade-cond (cdr armL)))
			);Continue
		);cond
	);lambda
);cascade-cond

; Elaborate CFWAE - take a CFWAE structure and returns a semantically equivalent CFAE data structure
(define elab-cfwae
	(lambda (expr)
		(type-case CFWAE expr
			( wnum		(n) (num n) )
			( wid		(i) (id i) )
			( wop		(po l r) (op po (elab-cfwae l) (elab-cfwae r)) )
			( wif0		(c t e) (if0 (elab-cfwae c) (elab-cfwae t) (elab-cfwae e)) )
			( wwith		(name named-expr body) (app (fun name (elab-cfwae body)) (elab-cfwae named-expr)) )
			( wcond0	(arms default) (cond-to-if arms (elab-cfwae default)) )
			( wfun		(param body) (fun param (elab-cfwae body)) )
			( wapp		(fun param) (app (elab-cfwae fun) (elab-cfwae param)) )
		);type-case
	);lambda
);elab-cfwae

; Helper function to handle elaborating cond statements
(define cond-to-if
	(lambda (arms default)
		(cond 
			; Base - default case
			( (empty? arms) default)
			; Continue
			( else 
				(if0 (elab-cfwae (caar arms)) (elab-cfwae (cadar arms)) (cond-to-if (cdr arms) default) )
			);Continue
		);cond
	);lambda
);cond-to-if

; Prelude - first class definitions
(define prelude
	(aSub 'pi (num 3.141592653589793)
		(aSub 'area (fun 'r (op '* (id 'pi) (app (fun 'x (op '* (id 'x) (id 'x))) (id 'r))))
			(aSub 'inc (fun 'x (op '+ (id 'x) (num 1))) (mtSub))
		)
	)
);prelude

; Eval CFWAE - rope interp, elab, and parse together
(define eval-cfwae
	(lambda (e)
		(interp-cfae (elab-cfwae (parse-cfwae e)) prelude)
	);lambda
);eval-cfwae

; Test Cases provided by Dr. Alexander
(test (eval-cfwae '{+ 1 2}) (num 3))
(test (eval-cfwae '{+ 2 {* 2 3}}) (num 8))
(test (eval-cfwae '{{fun x x} 3}) (num 3))
(test (eval-cfwae '{{fun x {+ x 1}} 1}) (num 2))
(test (eval-cfwae '{if0 0 1 2}) (num 1))
(test (eval-cfwae '{if0 {{fun x {- x 2}} 3} {{fun x {* 2 x}} 10} {{fun x {/ x 2}} 8}}) (num 4))
(test (eval-cfwae '{{if0 0 {fun x {+ x 1}} {fun x {+ x 2}}} 0}) (num 1))
(test (eval-cfwae '{with {x 10} {+ x 5}}) (num 15))
(test (eval-cfwae '{with {f {fun x {+ x 1}}} {f 2}}) (num 3))
(test (eval-cfwae '{cond0 {1 2} {0 15} 0}) (num 15))
(test (eval-cfwae '{with {add1 {fun x {+ x 1}}} {cond0 {{add1 0} 5} {3 4} {0 {add1 2}} 52} 2}) (num 3))
(test (eval-cfwae '{inc pi}) (num 4.141592653589793))
(test (eval-cfwae '{with {x 2} {with {inc {fun x {+ x 2}}} {inc x}}}) (num 4))
(test (eval-cfwae '{area 2}) (num 12.566370614359172))
(test (eval-cfwae '{{fun x {{fun y {+ x y}} 3}} 1}) (num 4))
(test (eval-cfwae '{with {g {fun f {f 3}}} {g {fun x {+ x 1}}}}) (num 4))
