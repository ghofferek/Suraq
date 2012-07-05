(set-logic Suraq)


(declare-fun x2 () Value)
(declare-fun x1 () Value)
(declare-fun x3 () Value)



(declare-fun F (Value Value Value) Value)
(declare-fun H (Value) Value)


(assert (
	=>
		(and
			(= x1 x2 x3)
		)
		(= 
			(F (H x1) (H x2) (H x3))
			(F (H x3) (H x2) (H x1))
		)
	)
)