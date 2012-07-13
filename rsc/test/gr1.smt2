(set-logic Suraq)



(declare-fun x () Value)
(declare-fun y () Value)
(declare-fun z () Value)
(declare-fun a () Value)
(declare-fun b () Value)
(declare-fun c () Value)

;(declare-fun f (Value) Value)


(assert (
		=>
		(and
			( = x y z)
			( = a b c)
			( = a x)
			( = y x)
		)
		( = z c )
	)

)



;(assert (
;	and
;	(= x1 (f x1))
;	(not ( = x1 ( f x1)))
;	)
;)

