;Gehrig Keane
;EECS 662
;Project 4
#lang plai

; Abstract Syntax
(define-type CFWAES
	( num		(n number?) )
	( id		(name symbol?) )
	( op		(operator symbol?) (l CFWAES?) (r CFWAES?) )
	( with		(param symbol?) (named-expr CFWAES?) (bound-body CFWAES?) )
	( fun		(param symbol?) (body CFWAES?) )
	( app		(fun-expr CFWAES?) (arg-expr CFWAES?) )
	( if0		(if-body CFWAES?) (then-body CFWAES?) (else-body CFWAES?) )
	( seq		(expr0 CFWAES?) (expr1 CFWAES?) )
	( assign	(x symbol?) (expr CFWAES?) )
);CFWAES

; Value Construct with boxing beneath
(define-type CFWAES-Value
	( numV (n number?) )
	( closureV (param symbol?) (body CFWAES?) (env Env?))
);CFWAES-Value

; Env - Environment
(define-type Env
	( mtEnv )
	( aSub (name symbol?) (loc number?) (env Env?) )
);Env

; Store
(define-type Store
	( mtSto )
	( aSto (loc number?) (value CFWAES-Value?) (sto Store?) )
);Store

; Value X Store - value-store packaging
(define-type ValueXStore
	( vxs (value CFWAES-Value?) (store Store?) )
);ValueXStore

(define next-loc
	(local ((define loc (box 1729) ))
		(lambda ()
			( begin (set-box! loc (+ (unbox loc) 1)) (unbox loc) )
		);lambda
	);local
);next-loc

; Lookup identifier
(define lookup-sto
	(lambda (loc sto total-sto)
		(type-case Store sto
			(mtSto () (error 'lookup-sto "bad id"))
			(aSto	(sto-loc sto-val next-sto)
					(if (equal? sto-loc loc) (vxs sto-val total-sto) (lookup-sto loc next-sto total-sto))
			)
		);type-case
	);lambda
);lookup-sto

; Lookup value
(define lookup-val
	(lambda (name env sto)
		(type-case Env env
			(mtEnv () (error 'lookup-val "bad value"))
			(aSub	(bound-name bound-value next-env)
					(if (symbol=? bound-name name) (lookup-sto bound-value sto sto) (lookup-val name next-env sto))
			)
		);type-case
	);lambda
);lookup-val

; Lookup location
(define lookup-loc
	(lambda (name env)
		(type-case Env env
			(mtEnv () (error 'lookup-loc "bad location"))
			(aSub	(bound-name bound-value next-env)
					(if (symbol=? bound-name name) bound-value (lookup-loc name next-env))
			)
		);type-case
	);lambda
);lookup-loc

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
			( mtEnv () (error 'lookup-sym (string-append "Identifier not found: " (symbol->string n))) )
			( aSub	(name value next-env)
					(if (symbol=? name n) value (lookup-sym n next-env) )
			);aSub
		);type-case
	);lambda
);lookup-sym

; Interp CFWAES - interpret data structure
(define interp-cfwaes
	(lambda (expr env sto) 
		(type-case CFWAES expr
			( num	(n) (vxs (numV n) sto) )
			( id	(name) (lookup-val name env sto) )
			( op	(op lhs rhs)
				(type-case ValueXStore (interp-cfwaes lhs env sto)
					(vxs (lhs-val lhs-sto)
						(type-case ValueXStore (interp-cfwaes rhs env lhs-sto)
							(vxs (rhs-val rhs-sto)
								(vxs (numV ((lookup-ops op ops) (numV-n lhs-val) (numV-n rhs-val))) rhs-sto)
							);vxs
						);type-case
					);vxs
				);type-case
			);op
			( fun	(param body) (vxs (closureV param body env) sto))
			( if0	(c t e)
				(type-case ValueXStore (interp-cfwaes c env sto)
					(vxs (c-val c-sto)
						(if (= (numV-n c-val) 0) (interp-cfwaes t env sto) (interp-cfwaes e env sto) )
					);vxs
				);type-case
			);if0
			( with	(id expr body) (interp-cfwaes (app (fun id body) expr) env sto)); bound-id named-expr and bound-body are horrendously long names
			( assign (id expr)
				(type-case ValueXStore (interp-cfwaes expr env sto)
					(vxs (expr-val expr-sto)
						(vxs expr-val (aSto (lookup-loc id env) expr-val expr-sto) )
					);vxs
				);type-case
			);assign
			( seq (expr1 expr2)
				(type-case ValueXStore (interp-cfwaes expr1 env sto)
					(vxs (expr1-val expr1-sto)
						(interp-cfwaes expr2 env expr1-sto)
					);vxs
				);type-case
			);seq
			( app	(fun-expr arg-expr)
				(type-case ValueXStore (interp-cfwaes fun-expr env sto)
					(vxs (fun-val fun-sto)
						(type-case ValueXStore (interp-cfwaes arg-expr env fun-sto)
							(vxs (arg-val arg-sto)
								(local ((define new-loc (next-loc)))
									(interp-cfwaes (closureV-body fun-val)
										( aSub (closureV-param fun-val) new-loc (closureV-env fun-val) )
										( aSto new-loc arg-val arg-sto )
									);interp-cfwaes
								);local
							);vxs
						);type-case
					);vxs
				);type-case
			);app
		);type-case
	);lambda
);interp-cfwaes

; Parse CFWAES - walks input and produces concrete syntax for CFWAES
(define parse-cfwaes
	(lambda (expr)
		(cond
			( (number? expr) (num expr) )
			( (symbol? expr) (id expr) )
			( (list? expr)
				(case (car expr)
					( (+)		(op `+	(parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))) ) 
					( (-)		(op `-	(parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))) ) 
					( (*)		(op `*	(parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))) ) 
					( (/)		(op `/	(parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))) )
					( (if0)		(if0	(parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr)) (parse-cfwaes (cadddr expr))) )
					( (fun)		(fun	(cadr expr)  (parse-cfwaes (caddr expr))) )
					( (with)	(with	(caadr expr) (parse-cfwaes (cadadr expr)) (parse-cfwaes (caddr expr))) )
					( (assign)	(assign	(cadr expr) (parse-cfwaes (caddr expr))))
					( (seq)		(seq	(parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))) )
					( else		(app	(parse-cfwaes (car expr)) (parse-cfwaes (cadr expr))) )
				);case
			);list?
			( else (error 'parse-cfwaes "Parsing Error!") );Silly input, tricks are for kids!
		);cond
	);lambda
);parse-cfwaes

; Eval CFWAES - rope interp, and parse together
(define eval-cfwaes
	(lambda (expr)
		(vxs-value (interp-cfwaes (parse-cfwaes expr) (mtEnv) (mtSto)) )
	);lambda
);eval-cfwaes

; Test Cases provided by Dr. Alexander
(test (eval-cfwaes '{with {y 0}
                       {with {inc {fun x {+ x 1}}}
                         {seq {seq {assign y {inc y}}
                                   {assign y {inc y}}}
                              {seq {assign y {inc y}}
                                   {assign y {inc y}}}}}}) (numV 4))

(test (eval-cfwaes '{with {y 1}
                       {with {inc {fun x {+ x y}}}
                         {inc 3}}}) (numV 4))

(test (eval-cfwaes '{with {y 1}
                       {with {inc {fun x {+ x y}}}
                         {seq {assign y 2} {inc 3}}}}) (numV 5))

(test (eval-cfwaes '{with {y 1}
                       {with {inc {seq {assign y 2} {fun x {+ x y}}}}
                         {inc 3}}}) (numV 5))

(test (eval-cfwaes '{with {x 3}
                       {seq x {assign x {+ x 1}}}}) (numV 4))

(test (eval-cfwaes '{with {x 3}
                       {seq
                         {assign x {+ x 1}} {assign x {+ x 1}}}}) (numV 5))

(test (eval-cfwaes '{with {x 3}
                       {seq
                        {seq
                         {assign x {+ x 1}} {assign x {+ x 1}}}
                        {assign x {+ x 1}}}}) (numV 6))