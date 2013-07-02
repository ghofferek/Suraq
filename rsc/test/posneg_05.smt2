(set-logic Suraq)


; input
(declare-fun i_1 () Value)
(declare-fun i_2 () Value)
(declare-fun i_3 () Value)
(declare-fun i_4 () Value)
(declare-fun i_5 () Value)

; outputs
(declare-fun o_1 () Value :no_dependence)
(declare-fun o_2 () Value :no_dependence)
(declare-fun o_3 () Value :no_dependence)
(declare-fun o_4 () Value :no_dependence)
(declare-fun o_5 () Value :no_dependence)

; control signals
(declare-fun c_1 () Control)
(declare-fun c_2 () Control)
(declare-fun c_3 () Control)
(declare-fun c_4 () Control)
(declare-fun c_5 () Control)

; functions
(declare-fun neg (Value) Value)

; predicates
(declare-fun pos (Value) Bool)

; spec
(assert
  (=>
    (and
      (and ; pos/neg properties
        (xor (pos i_1) (pos (neg i_1)))
        (xor (pos i_2) (pos (neg i_2)))
        (xor (pos i_3) (pos (neg i_3)))
        (xor (pos i_4) (pos (neg i_4)))
        (xor (pos i_5) (pos (neg i_5)))
      )
      (and ; update
        (ite
          c_1
          (= o_1 i_1)
          (= o_1 (neg i_1))
        )
        (ite
          c_2
          (= o_2 i_2)
          (= o_2 (neg i_2))
        )
        (ite
          c_3
          (= o_3 i_3)
          (= o_3 (neg i_3))
        )
        (ite
          c_4
          (= o_4 i_4)
          (= o_4 (neg i_4))
        )
        (ite
          c_5
          (= o_5 i_5)
          (= o_5 (neg i_5))
        )
      )
    )
    (xor ; desired outcome
      (pos o_1)
      (pos o_2)
      (pos o_3)
      (pos o_4)
      (pos o_5)
    )
  )
)
