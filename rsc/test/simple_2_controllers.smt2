(set-logic Suraq)


; input
(declare-fun input () Value)

; outputs
(declare-fun output_1 () Value :no_dependence)
(declare-fun output_2 () Value :no_dependence)

; uninterpreted functions
(declare-fun function_1 (Value) Value)
(declare-fun function_2 (Value) Value)

; control signals
(declare-fun control_1 () Control)
(declare-fun control_2 () Control)

; spec
(assert
  (=>
    (and
      (ite
        control_1
        (=
          output_1
          (function_1 input)
        )
        (=
          output_1
          (function_2 input)
        )
      )
      (ite
        control_2
        (=
          output_2
          (function_1 input)
        )
        (=
          output_2
          (function_2 input)
        )
      )
    )
    (= output_1 output_2)
  )
)
