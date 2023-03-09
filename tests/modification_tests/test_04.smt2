(define z () String)
(define y () String)
(define x () String)
(define w () String)
(define v () String)

(assert (or 
	(= (str.++ v "A") (str.++ "A" v)) 
        (= (str.++ v "BA") (str.++ "AB" v))
))


(assert (not (= v "")))
(assert (not (str.contains (str.++ v "B" v) "AA")))
