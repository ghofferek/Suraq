(set-logic Suraq)



(declare-fun x1 () Value)

(declare-fun f (Value) Value)





(assert (
	and
	(= x1 (f x1))
	(not ( = x1 ( f x1)))
	)
)

