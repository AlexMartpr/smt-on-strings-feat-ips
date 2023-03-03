(set-logic QF_SLIA)
(declare-fun w () String)
(declare-fun y () String)

(assert (= (str.++ w "A") (str.++ y "A" w)))