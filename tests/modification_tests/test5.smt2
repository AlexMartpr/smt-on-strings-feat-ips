(set-logic QF_SLIA)
(declare-fun z () String)
(declare-fun x () String)

(assert (= (str.++ "DC" z y) (str.++ "DA" x)))
(assert (= (str.++  z y "CD") (str.++ x "AD")))
(assert (not (= (str.++  "A" z y "CD") (str.++ "K" x "AD"))))
