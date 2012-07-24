(set-logic Suraq)


(declare-fun x2 () Value)
(declare-fun x1 () Value)
(declare-fun x3 () Value)



(declare-fun F (Value) Value)
(declare-fun G (Value) Value)



(assert (
	=>
		(= x1 x2)
		(=  (F ( F ( G x1)))  (F ( F ( G x2))))
	)
)