(set-logic Suraq)


(declare-fun x2 () Value)
(declare-fun x1 () Value)
(declare-fun x3 () Value)



(declare-fun f1 (Value) Value)
(declare-fun f2 (Value) Value)



(assert (
	=>
		( and 
			(= x1 ( f1 x1 ))
			(= x1 ( f2 x2 ))
		)
		(= x1 ( f1 ( f2 x2 )))
	)
)

