(set-logic Suraq)


; input
(declare-fun i_1 () Value)
(declare-fun i_2 () Value)

; outputs
(declare-fun o_1 () Value :no_dependence)
(declare-fun o_2 () Value :no_dependence)

; constants
(declare-fun a () Value)
(declare-fun b () Value)
(declare-fun x () Value)
(declare-fun y () Value)


; control signals
(declare-fun c_1 () Control)
(declare-fun c_2 () Control)

; spec
(assert
  (=>
    (and
      (ite
        c_1
        (=
          o_1
          (ite
            (= i_1 a)
            x
            y
          )
        )
        (=
          o_1
          (ite
            (= i_2 b)
            x
            y
          )
        )
      )
      (ite
        c_2
        (=
          o_2
          (ite
            (= i_2 b)
            x
            y
          )
        )
        (=
          o_2
          (ite
            (= i_1 a)
            x
            y
          )
        )
      )
    )
    (= o_1 o_2)
  )
)
