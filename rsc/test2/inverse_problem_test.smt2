(set-logic Suraq)

; Declare variables for inputs

(declare-fun x   () Value)
(declare-fun x_  () Value :no_dependence)
(declare-fun x__ () Value :no_dependence)

(declare-fun ZERO   () Value)

; Declare control variables

(declare-fun c () Control) 

; Declare uninterpreted functions

(declare-fun f    (Value) Value)
(declare-fun finv (Value) Value)
(declare-fun h    (Value) Value)
(declare-fun hinv (Value) Value)

; define-fun macros may be used to abbreviate and structure the input.
; Update function, which describes behavior of circuit

(define-fun update (
  ; parameters
  (x       Value )
  (x_      Value )
  (x__     Value )
  (ZERO    Value )
  (c       Bool  )
  )
  Bool  ; return type
  
  ; main expression  
  (
    and  (= x_
            (ite (= x ZERO) (f x) (h x)))           
         (ite (= x ZERO) (= x (finv (f x))) (= x (hinv (h x))))             
         (= x__
            (ite c (finv x_) (hinv x_)))          
  )    
)

; The whole formula

(define-fun formula (
  ; parameters
  (x       Value            )
  (x_      Value            )
  (x__     Value            )
  (ZERO    Value            )
  (c       Bool             )
  )
  Bool  ; return type
  
  ; main expression
  (=> (update x x_ x__ ZERO c)
      (= x x__)
  )
)

(assert (formula x x_ x__ ZERO c))
