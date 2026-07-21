(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
; is-pos y sum3 son MACROS (define-fun), no variables
(define-fun is-pos ((n Int)) Bool (> n 0))
(define-fun sum3 ((a Int) (b Int) (c Int)) Int (+ a (+ b c)))
; usa la macro is-pos sobre x  ->  variable: x
(assert (is-pos x))
; usa sum3 sobre x, y, 0 y lo compara con z  ->  variables: x, y, z
(assert (= (sum3 x y 0) z))
; w está ligada por forall, is-pos es macro  ->  variable: x
(assert (forall ((w Int)) (=> (is-pos w) (> (+ w x) 0))))
