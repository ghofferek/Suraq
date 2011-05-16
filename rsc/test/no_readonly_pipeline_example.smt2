;(set-option :print-success false)

(set-logic ArraysEx)


; Declare arrays.
; since ' ist not a valid SMTLIB symbol character, _ is used instead
; a ! symbol is appended to variable duplicated for formula expansion

(declare-fun REG      () (Array Int Int))
(declare-fun REGci_   () (Array Int Int))
(declare-fun REGci__  () (Array Int Int))
(declare-fun REGsc_   () (Array Int Int))
(declare-fun REGsc__  () (Array Int Int))

(declare-fun REGci_!  () (Array Int Int))
(declare-fun REGci__! () (Array Int Int))
(declare-fun REGsc_!  () (Array Int Int))
(declare-fun REGsc__! () (Array Int Int))

; Declare variables for pipeline registers

(declare-fun v   () Int)
(declare-fun v_  () Int)
(declare-fun v_! () Int)
(declare-fun w   () Int)


; Declare variables for inputs

(declare-fun s () Int)
(declare-fun dest () Int)


; Declare control variables

(declare-fun x () Bool) 

; Declare uninterpreted functions
(declare-fun ALU (Int) Int)

; Equivalence Criterion

(define-fun equiv ((A (Array Int Int))(B (Array Int Int))) Bool (
  forall (i Int) (
    = (select A i)
      (select B i)
    )
  )
)


; Update function, which describes behavior of circuit
; (in step-complete and complete-ISA branch)

(define-fun update (
  ; parameters
  (REG     (Array Int Int)) 
  (REGci_  (Array Int Int))
  (REGci__ (Array Int Int)) 
  (REGsc_  (Array Int Int))
  (REGsc__ (Array Int Int))
  (v       Int            )
  (v_      Int            )
  (w       Int            )
  (s       Int            )
  (dest    Int            )
  (x       Bool           )
  )
  Bool  ; return type
  
  ; main expression
  (
    and  (= REGci_
            (store REG w (ALU v)))
            
         (= REGci__
            (store REGci_ dest (ALU (select REGci_ s))))
          
         (= REGsc_
            (store REG w (ALU v)))
          
         (= REGsc__
            (store REGsc_ dest (ALU v_)))
          
         (= v_
            (ite x (ALU v) (select REG s)))       
  )
)


; The whole formula
; i.e., (update => equiv)

(define-fun formula (
  ; parameters
  (REG     (Array Int Int)) 
  (REGci_  (Array Int Int))
  (REGci__ (Array Int Int)) 
  (REGsc_  (Array Int Int))
  (REGsc__ (Array Int Int))
  (v       Int            )
  (v_      Int            )
  (w       Int            )
  (s       Int            )
  (dest    Int            )
  (x       Bool           )
  )
  Bool  ; return type
  
  ; main expression
  (=> (update REG REGci_ REGci__ REGsc_ REGsc__ v v_ w s dest x)
      (= REGci__ REGsc__)
  )
)


; assert the negation of the (supposedly valid) main formula, expanded
; over the control signal.

; (assert     
;   (and (not (formula REG REGci_  REGci__  REGsc_  REGsc__  v v_  w s dest true ))
;        (not (formula REG REGci_! REGci__! REGsc_! REGsc__! v v_! w s dest false))
;   )  
; )

; Check if the expected solution (x <=> s=w) is a valid solution

(assert 
  (not (formula REG REGci_  REGci__  REGsc_  REGsc__  v v_  w s dest x))
)
(assert (= x (= s w)))


;(get-assertions)
(check-sat)
(get-info model)
