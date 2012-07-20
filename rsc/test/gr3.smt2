(set-logic Suraq)



(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Value)
(declare-fun d () Value)


(assert ( =>
		( and
			( = a b)
			( = c d)
		)
		( =
			a
			(and
				b
				( = c d)
			)
		)
	)

)


