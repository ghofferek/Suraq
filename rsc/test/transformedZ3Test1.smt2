(set-logic Suraq)
 
(declare-fun x1 () Value)
(declare-fun x2 () Value)
(declare-fun x3 () Value)

(declare-fun f (Value) Value)

(assert
  (or
    (not
      (=
      x1
      x2
      )
    )
    (=
      (f x1)
      (f x2)
    )
    (not
      (=
        (f x1)
        (f x3)      
      )
    
    )
  )
)

