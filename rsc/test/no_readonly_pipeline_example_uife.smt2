;(set-option :print-success false)


; Check the "no_readonly_pipeline_example" after (manual) reduction to 
; logic with uninterpreted functions and equality.
; I.e., the arrays have been removed by using the corresponding reduction
; technique.
(set-logic QF_LIA)


; Declare functions for "arrays".
; since ' ist not a valid SMTLIB symbol character, _ is used instead
; a ! symbol is appended to variable duplicated for formula expansion
(declare-fun REG      (Int) Int)
(declare-fun REGci_   (Int) Int)
(declare-fun REGci__  (Int) Int)
(declare-fun REGsc_   (Int) Int)
(declare-fun REGsc__  (Int) Int)

(declare-fun REGci_!  (Int) Int)
(declare-fun REGci__! (Int) Int)
(declare-fun REGsc_!  (Int) Int)
(declare-fun REGsc__! (Int) Int)


; Declare variables for pipeline registers
(declare-fun $v   () Int)
(declare-fun $v_  () Int)
(declare-fun $v_! () Int)
(declare-fun $w   () Int)


; Declare variables for inputs
(declare-fun $s () Int)
(declare-fun $dest () Int)


; Declare variable lambda (which is used for reduction of array quantifiers
; to finite conjunction)
(declare-fun $lambda  () Int)
(declare-fun $lambda! () Int)
; Declare control variables
(declare-fun $x () Bool) 


; Declare uninterpreted functions
(declare-fun ALU (Int) Int)


; Equivalence Criterion
(define-fun equiv () Bool (
  and (= (REGsc__ $lambda)(REGci__ $lambda))
      (= (REGsc__ $w     )(REGci__ $w     ))
      (= (REGsc__ $dest  )(REGci__ $dest  ))
      (= (REGsc__ $s     )(REGci__ $s     ))
  )
)

; Equivalence Criterion for duplicated vars
(define-fun equiv! () Bool (
  and (= (REGsc__! $lambda!)(REGci__! $lambda!))
      (= (REGsc__! $w     )(REGci__! $w     ))
      (= (REGsc__! $dest  )(REGci__! $dest  ))
      (= (REGsc__! $s     )(REGci__! $s     ))
  )
)


; Update function, which describes behavior of circuit
; (in step-complete and complete-ISA branch)
(define-fun update (
  ; parameters
  (v       Int )
  (v_      Int )
  (w       Int )
  (s       Int )
  (dest    Int )
  (lambda  Int )
  (x       Bool)
  )
  Bool  ; return type
  
  ; main expression
  (
    and  (= (REGci_  w     )(ALU     v     ))  
         (=> (distinct w lambda)
             (= (REGci_  lambda)(REG     lambda)))     
         (=> (distinct w dest)
             (= (REGci_  dest  )(REG     dest  )))
         (=> (distinct w s) 
             (= (REGci_  s     )(REG     s     )))
        
         (= (REGci__ dest  )(ALU (REGci_ s)))
         (=> (distinct dest lambda)
             (= (REGci__ lambda)(REGci_  lambda)))
         (=> (distinct dest w)
             (= (REGci__ w     )(REGci_  w     )))
         (=> (distinct dest s)
             (= (REGci__ s     )(REGci_  s     )))
          
         (= (REGsc_  w     )(ALU     v     ))
         (=> (distinct w lambda)
             (= (REGsc_  lambda)(REG     lambda)))
         (=> (distinct w dest)
             (= (REGsc_  dest  )(REG     dest  )))
         (=> (distinct w s)
             (= (REGsc_  s     )(REG     s     )))
         
         (= (REGsc__ dest  )(ALU     v_    ))
         (=> (distinct dest lambda)
             (= (REGsc__ lambda)(REGsc_  lambda)))
         (=> (distinct dest w)
             (= (REGsc__ w     )(REGsc_  w     )))
         (=> (distinct dest s)
             (= (REGsc__ s     )(REGsc_  s     )))
            
         (= v_
            (ite x (ALU v) (REG s)))    
  )
)

; Update function, which describes behavior of circuit
; (in step-complete and complete-ISA branch)
; for duplicated variables
(define-fun update! (
  ; parameters
  (v       Int )
  (v_!     Int )
  (w       Int )
  (s       Int )
  (dest    Int )
  (lambda  Int )
  (x       Bool)
  )
  Bool  ; return type
  
  ; main expression
  (
    and  (= (REGci_!  w     )(ALU     v     ))  
         (=> (distinct w lambda)
             (= (REGci_!  lambda)(REG     lambda)))     
         (=> (distinct w dest)
             (= (REGci_!  dest  )(REG     dest  )))
         (=> (distinct w s) 
             (= (REGci_!  s     )(REG     s     )))
        
         (= (REGci__! dest  )(ALU (REGci_! s)))
         (=> (distinct dest lambda)
             (= (REGci__! lambda)(REGci_!  lambda)))
         (=> (distinct dest w)
             (= (REGci__! w     )(REGci_!  w     )))
         (=> (distinct dest s)
             (= (REGci__! s     )(REGci_!  s     )))
          
         (= (REGsc_!  w     )(ALU     v     ))
         (=> (distinct w lambda)
             (= (REGsc_!  lambda)(REG     lambda)))
         (=> (distinct w dest)
             (= (REGsc_!  dest  )(REG     dest  )))
         (=> (distinct w s)
             (= (REGsc_!  s     )(REG     s     )))
         
         (= (REGsc__! dest  )(ALU     v_!    ))
         (=> (distinct dest lambda)
             (= (REGsc__! lambda)(REGsc_!  lambda)))
         (=> (distinct dest w)
             (= (REGsc__! w     )(REGsc_!  w     )))
         (=> (distinct dest s)
             (= (REGsc__! s     )(REGsc_!  s     )))
            
         (= v_!
            (ite x (ALU v) (REG s)))    
  )
)


; Lambda constraints
(define-fun lambda_constraints (
  ; parameters
  (v      Int)
  (w      Int)
  (s      Int)
  (dest   Int)
  (lambda Int)
  )
  Bool ; return type
  
  ; main expression
  (
    and (not (= lambda w   ))
        (not (= lambda s   ))
        (not (= lambda dest))
  )
)

; The whole formula
; i.e., lambda_constraints => (update => equiv)
(define-fun formula (
  ; parameters
  (v       Int )
  (v_      Int )
  (w       Int )
  (s       Int )
  (dest    Int )
  (lambda  Int )
  (x       Bool)
  )
  Bool  ; return type
  
  ; main expression
  (=> (lambda_constraints v w s dest lambda) 
      (=> (update v v_ w s dest lambda x)
          equiv)
  )
)

; The whole formula
; i.e., lambda_constraints => (update => equiv)
; for duplicated variables
(define-fun formula! (
  ; parameters
  (v       Int )
  (v_!     Int )
  (w       Int )
  (s       Int )
  (dest    Int )
  (lambda! Int )
  (x       Bool)
  )
  Bool  ; return type
  
  ; main expression
  (=> (lambda_constraints v w s dest lambda!) 
      (=> (update! v v_! w s dest lambda! x)
          equiv!)
  )
)

; assert the negation of the (supposedly valid) main formula, expanded
; over the control signal.

; (assert 
;   (and (not (formula  $v $v_  $w $s $dest $lambda  true ))
;        (not (formula! $v $v_! $w $s $dest $lambda! false))
;   )
; )

; branches of (negated) main formula:
(assert (not (formula  $v $v_  $w $s $dest $lambda  true )))
(assert (not (formula! $v $v_! $w $s $dest $lambda! false)))


; Check if the expected solution (x <=> s=w) is a valid solution

; (assert (not (formula  $v $v_  $w $s $dest $lambda  $x )))
; (assert (= $x (= $s $w)))
;(get-assertions)
(check-sat)
;(get-info model)
