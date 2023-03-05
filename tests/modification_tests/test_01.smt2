(define z () String)
(define y () String)
(define x () String)
(define w () String)
(define v () String)

(assert (or 
	(= (str.++ v "A") (str.++ "A" v)) 
        (= (str.++ v "AB") (str.++ "BA" v))
))

(assert (not (= v "")))
(assert (not (= v "B")))
(assert (not (str.contains (str.++ v "B" v) "A")))
