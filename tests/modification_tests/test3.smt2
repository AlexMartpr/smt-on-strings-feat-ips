(set-logic QF_SLIA)
(declare-fun z () String)
(declare-fun x () String)
(declare-fun u () String)
(declare-fun v () String)

(assert (not (= (str.++ u v "AB" v "C" x) (str.++ v u y x "C"))))
(assert (= (str.++ x "AB" y x) (str.++ x x) ))
(assert (= (str.++ x z "AB" y x) (str.++ z x w x) )) 