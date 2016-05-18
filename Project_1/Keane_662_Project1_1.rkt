;Gehrig Keane
;EECS 662
;Project 1
;Task 1
#lang plai

;Abstract syntax
(define-type WAE
    ( num (n number?) )
    ( id (name symbol?) )
    ( add (l WAE?) (r WAE?) )
    ( sub (l WAE?) (r WAE?) )
    ( with (name symbol?) (named-expr WAE?) (body WAE?) )
);WAE

;Eval WAE - rope interp and parse together
(define eval-wae
    (lambda (sxp)
        ( interp-wae (parse-wae sxp) )
    );lambda
);eval

;Interp WAE - interpret data structure
(define interp-wae
    (lambda (e)
        (type-case WAE e
            ( num (n) n )
            ( add (l r) (+ (interp-wae l) (interp-wae r)) )
            ( sub (l r) (- (interp-wae l) (interp-wae r)) )
            ( id (i) (error 'interp-waeE-id (string-append "Free identifier (" (symbol->string i) ")")) )
            ( with (bound-id named-expr bound-body) (interp-wae (subst bound-body bound-id (num (interp-wae named-expr)))) )
        );type-case
    );lambda
);interp

;Parse WAE - walks input and produces concrete syntax for WAE
(define parse-wae
    (lambda (sxp)
        (cond
            ( (number? sxp) (num sxp) )
            ( (symbol? sxp) (id sxp) )
            ( (list? sxp)
                ( case (car sxp)
                    ( (+) (add (parse-wae (cadr sxp)) (parse-wae (caddr sxp))) )
                    ( (-) (sub (parse-wae (cadr sxp)) (parse-wae (caddr sxp))) )
                    ( (with) (with  (car (cadr sxp))
                                    (parse-wae (cadr (cadr sxp)))
                                    (parse-wae (caddr sxp)))
                    );with
                );case
            );list?
        );cond
    );lambda
);parse

;Replaces sid with vaal in exxp where it counts
(define subst
    (lambda (exxp sid vaal)
        (type-case WAE exxp
            ( num (n) exxp)
            ( id (i) (if (symbol=? i sid) vaal exxp))
            ( add (l r) (add (subst l sid vaal) (subst r sid vaal)))
            ( sub (l r) (sub (subst l sid vaal) (subst r sid vaal)))
            ( with (bound-id named-expr bound-body)
                (if (symbol=? bound-id sid)
                    (with bound-id (subst named-expr sid vaal) bound-body)
                    (with bound-id (subst named-expr sid vaal) (subst bound-body sid vaal))
                );if
            );with
        );type-case
    );lambda
);subst

;Test Cases:
(test (parse-wae '{with {a 1} {+ a {- 0 1}}}) (with 'a (num 1) (add (id 'a) (sub (num 0) (num 1)))))
(test (parse-wae '{with {a {+ 1 1}} {+ a {with {a 0} {+ a 1}}}}) (with 'a (add (num 1) (num 1)) (add (id 'a) (with 'a (num 0) (add (id 'a) (num 1))))))

(test (interp-wae (with 'a (num 1) (add (id 'a) (sub (num 0) (num 1))))) 0)
(test (interp-wae (with 'a (add (num 1) (num 1)) (add (id 'a) (with 'a (num 0) (add (id 'a) (num 1)))))) 3)

(test (eval-wae '{+ {+ {+ {+ {+ 1 1} 1} -1} -1} -1}) 0)
(test (eval-wae '{with {a {with {b 1} {+ b 0}}} {with {b 1} {+ a b}}}) 2)

;Provided Tests
(test (eval-wae '1) 1)
(test (eval-wae '{+ 1 1}) 2)
(test (eval-wae '{- 1 1}) 0)
(test (eval-wae '{with {x 3} {+ x x}}) 6)
(test (eval-wae '{with {x 3} {with {y 4} {+ x y}}}) 7)
(test (eval-wae '{with {x 3} {with {y 4} {+ x y}}}) 7)
(test (eval-wae '{with {x 3} {with {y {+ x x}} {+ x y}}}) 9)
(test (eval-wae '{with {x 3} {with {y {+ x x}} {with {x 1} {+ x y}}}}) 7)
(test (eval-wae '{with {x 1} {with {y 2} {with {z x} {with {x x} {with {z {+ z 1}} {+ z y}}}}}}) 4)