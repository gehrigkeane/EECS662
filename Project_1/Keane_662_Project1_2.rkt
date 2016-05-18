;Gehrig Keane
;EECS 662
;Project 1
;Task 2
#lang plai

;Abstract syntax
(define-type WAEE
    ( num (n number?) )
    ( id (name symbol?) )
    ( binp (op symbol?) (l WAEE?) (r WAEE?) )
    ( with (name symbol?) (named-expr WAEE?) (body WAEE?) )
);WAEE

;Eval WAE - rope interp and parse together
(define eval-waee
    (lambda (sxp)
        ( interp-waee (parse-waee sxp) )
    );sxp
);eval

;Interp WAE - interpret data structure
(define interp-waee
    (lambda (e)
        (type-case WAEE e
            ( num (n) n )
            ( binp (op l r) ((lookup op ops) (interp-waee l) (interp-waee r)) )
            ( id (i) (error 'interp-WAE-id (string-append "Free identifier (" (symbol->string i) ")")) )
            ( with (bound-id named-expr bound-body) (interp-waee (subst bound-body bound-id (num (interp-waee named-expr)))) )
        );type-case
    );lambda
);interp

;Parse WAE - walks input and produces concrete syntax for WAE
(define parse-waee
    (lambda (sxp)
        (cond
            ( (number? sxp) (num sxp) )
            ( (symbol? sxp) (id sxp) )
            ( (list? sxp)
                ( case (car sxp)
                    ( (with) (cascade (cadr sxp) (caddr sxp)) )
                    ( else 
                        ( binp (car sxp)
                              (parse-waee (cadr sxp))
                              (parse-waee (caddr sxp))
                        );binp
                    );else
                );case
            );list?
        );cond
    );lambda
);parse

;Cascade - interim function for transforming multiple bindings into nested with structs
(define cascade
    (lambda (biind exxp)
        (cond
            ;Base Cases
            ( (empty? biind) (parse-waee exxp) )
            ( (symbol? (car biind)) (with (car biind) (parse-waee (cadr biind)) (parse-waee exxp)) )
            ;Continue
            ( else 
                ( with (caar biind) (parse-waee (cadar biind)) (cascade (cdr biind) exxp) )
            );continue
        );cond
    );lambda
);cascade  

;Replaces sid with vaal in exxp where it counts
(define subst
    (lambda (exxp sid vaal)
        (type-case WAEE exxp
            ( num (n) exxp )
            ( id (i) (if (symbol=? i sid) vaal exxp) )
            ( binp (op l r) (binp op (subst l sid vaal) (subst r sid vaal)) )
            ( with (bound-id named-expr bound-body)
                (if (symbol=? bound-id sid)
                    (with bound-id (subst named-expr sid vaal) bound-body)
                    (with bound-id (subst named-expr sid vaal) (subst bound-body sid vaal))
                );if
            );with
        );type-case
    );lambda
);subst

;Lookup table implementation
(define-type binop-rec
    (binop (name symbol?) (op procedure?)))

(define lookup
    (lambda (op-name op-table)
        (cond ((empty? op-table) (error 'lookup (string-append "Operator not found: " (symbol->string op-name))))
            (else
                (if (symbol=? (binop-name (car op-table)) op-name)
                    (binop-op (car op-table))
                    (lookup op-name (cdr op-table)))))))

(define ops (list (binop '+ +) (binop '- -) (binop '* *) (binop '/ /)))

;Test Cases:
(test (parse-waee '{+ {- {* 1 {/ 1 1}} 1} 1}) (binp '+ (binp '- (binp '* (num 1) (binp '/ (num 1) (num 1))) (num 1)) (num 1)))
(test (parse-waee '{with {a 1} {+ a {- a {* a {/ a 1}}}}}) (with 'a (num 1) (binp '+ (id 'a) (binp '- (id 'a) (binp '* (id 'a) (binp '/ (id 'a) (num 1)))))))

(test (eval-waee '{+ {- {* 1 {/ 1 1}} 1} 1}) 1)
(test (eval-waee '{with {{a 1} {b 2}} {+ a {with {{c 1} {d 1}} {* c d}}}}) 2)
(test (eval-waee '{with {{a 1} {b 2} {c 3} {d 4}} {+ {* a {/ b {- c d}}} {with {{c 1} {d 1}} {* c d}}}}) -1)

;Provided Tests
(test (eval-waee '1) 1)
(test (eval-waee '{+ 1 1}) 2)
(test (eval-waee '{- 1 1}) 0)
(test (eval-waee '{* 2 2}) 4)
(test (eval-waee '{/ 4 2}) 2)
(test (eval-waee '{with {{x 3}} {+ x x}}) 6)
(test (eval-waee '{with {{x 3} {y 4}} {+ x y}}) 7)
(test (eval-waee '{with {{x 3} {y 4}} {+ x y}}) 7)
(test (eval-waee '{with {{x 3}} {with {{y 4}} {+ x y}}}) 7)
(test (eval-waee '{with {{x 3}} {with {{y {+ x x}}} {+ x y}}}) 9)
(test (eval-waee '{with {{x 3}} {with {{y {+ x x}}} {with {{x 1}} {+ x y}}}}) 7)
(test (eval-waee '{with {{x 1} {y 2}} {with {{z x} {x x}} {with {{z {+ z 1}}} {+ z y}}}}) 4)