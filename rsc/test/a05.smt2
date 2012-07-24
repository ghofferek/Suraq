(set-logic Suraq)


(declare-fun x2 () Value)
(declare-fun x1 () Value)
(declare-fun x3 () Value)



(declare-fun F (Value Value) Value)
(declare-fun G (Value Value) Value)



(assert (
	=>
		(and
			(= x1 x2)
		)
		(= (F x1 x2)(F x2 x1))
	)
)