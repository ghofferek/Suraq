(set-logic Suraq)


(declare-fun x2 () Value)
(declare-fun x1 () Value)
(declare-fun x3 () Value)



(declare-fun F (Value Value Value) Value)
(declare-fun H (Value) Value)


(assert (
	=>
		(and
			(= x1 (H x1))
			(= x2 (H x2))
			(= x3 (H x3))
		)
		(= 
			(F x1 x2 x3)
			(F (H x1) (H x2) (H x3))
		)
	)
)

;(assert (
;	=>
;		( 
;			and
;			(= (f2 x1) ( f1 x2))
;			(= x1 x2 )
;			;(= (f1 x2) ( f2 x2)) ; should not be nessasary
;			;(= (f1 x1) ( f2 x2))
;			;(= (f1 x2) ( f2 x1))
;		)
;		(=
;			(f1 ( f2 x1))
;			(f2 ( f1 x2))
;		)
;	)
;)



;(assert (
;		and
;		( = x1 x2)
;		( not ( = x1 x2 ) )
;	)
;)


;(assert (
;		and
;		( = x1 (f1 x1))
;		( not ( = x1 (f1 x1 ) ) )
;
;
;		( = x2 (f1 x2))
;		( not ( = x2 (f1 x2 ) ) )
;	)
;)
