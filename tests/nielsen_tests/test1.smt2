(set-logic QF_SLIA)
(declare-fun w () String)

(assert (= (str.++ w "A") (str.++ "A" w)))