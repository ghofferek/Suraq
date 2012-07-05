(set-logic Suraq)




; Declare variables for inputs

(declare-fun x2 () Value)
(declare-fun x1 () Value)
(declare-fun x3 () Value)



; Declare uninterpreted functions
; Only functions from (Value+) -> Value are supported.
(declare-fun f (Value) Value)


; Equivalence Criterion???



; Use "assert" to state what should actually hold for the synthesized control.
; Multiple assert statements are implicitly conjuncted.

; (x1 != x2) v (F(x1) = F(x2)) v (F(x1) != F(x3))
(assert  
	(or
		(not( = x1 x2 ))
		( = (f x1) (f x2))
		(not( = (f x1) (f x3) ))
	)
)
