(set-logic QF_SLIA)
(declare-fun z () String)
(declare-fun x () String)

(assert (= (str.++ "ABAA" z "BB") (str.++ "ABA" x "BBA")))