(set-logic QF_SLIA)
(declare-fun z () String)
(declare-fun x () String)


(assert (str.contains (str.++ "ABC" y "BB" z "CA") "ABA")) 