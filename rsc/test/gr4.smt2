(set-logic Suraq)



(declare-fun a () Value)
(declare-fun b () Value)
(declare-fun c () Value)
(declare-fun d () Value)
(declare-fun e () Value)


(assert ( =>
		(= a b c)
		(=
			a
			(ite
				(= a b)
				(ite
					(= a c)
					b
					e
				)
				d
			)
		)
	)

)


