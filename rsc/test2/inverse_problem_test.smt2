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
         (= x__
            (ite c (finv x_) (hinv x_)))
        (= (finv (f x)) x)   
        (= (finv (f x_)) x_)
        (= (finv (f x__)) x__)        
        (= (finv (f ZERO)) ZERO) 
        (= (hinv (h x)) x)   
        (= (hinv (h x_)) x_)
        (= (hinv (h x__)) x__)        
        (= (hinv (h ZERO)) ZERO)         
  )    
)
; 
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
