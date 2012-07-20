(set-logic Suraq)



(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)


(assert ( =>
		( = a b c d)
		( =
			a
			(and
				b
				( = c d)
			)
		)
	)

)


