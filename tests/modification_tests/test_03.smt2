(declare-fun z () String)
(declare-fun w () String)
(declare-fun v () String)

(assert (or 
	(= (str.++ v "A") (str.++ "A" v)) 
        (not (str.contains (str.++ v "B" v) "A"))
))

(assert (or 
	(= (str.++ v w "B") (str.++ "B" v w)) 
        (not (str.contains (str.++ w w) "B"))
))

(assert (not (= (str.++ v v) "" ) ) )

(assert (not (= (str.++ w w) "")) )

(assert (= (str.++ v w) (str.++ "AB" z) ) )
