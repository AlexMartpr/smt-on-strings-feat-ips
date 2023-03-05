(define z () String)
(define y () String)
(define x () String)
(define w () String)
(define v () String)

(assert (or 
	(= (str.++ v "A") (str.++ "AB" v)) 
        (not (str.contains (str.++ v "A" v) "A"))
))
