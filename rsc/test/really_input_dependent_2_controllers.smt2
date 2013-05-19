(set-logic Suraq)


; input
(declare-fun i_1 () Value)
(declare-fun i_2 () Value)

; outputs
(declare-fun o_1 () Value :no_dependence)
(declare-fun o_2 () Value :no_dependence)

; control signals
(declare-fun c_1 () Control)
(declare-fun c_2 () Control)

; functions
(declare-fun neg (Value) Value)

; predicates
(declare-fun pos (Value) Bool)

; spec
(assert
  (=>
    (and
      (and ; pos/neg properties
        (xor pos(i_1) pos(neg(i_1)))
        (xor pos(i_2) pos(neg(i_2)))
        ;(xor pos(o_1) pos(neg(o_1)))
        ;(xor pos(o_2) pos(neg(o_2)))
      )
      (and ; update
        (ite
          c_1
          (= o_1 i_1)
          (= o_1 neg(i_1))
        )
        (ite
          c_2
          (= o_2 i_2)
          (= o_2 neg(i_2))
        )
      )
    )
    (xor ; desired outcome
      pos(o_1)
      pos(o_2)
    )
  )
)
