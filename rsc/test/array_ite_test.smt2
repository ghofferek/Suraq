(set-logic Suraq)


(declare-fun outcome () (Array Value Value) :no_dependence)
(declare-fun correct () (Array Value Value))
(declare-fun wrong   () (Array Value Value))

(declare-fun control () Control)

(assert
  (=>
    (=
      outcome  
      (ite
        control
        correct
        wrong
      )
    )
    (=
      outcome
      correct
    )
  )
)