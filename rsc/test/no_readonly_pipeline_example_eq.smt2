;(set-option :print-success false)


; Check the "no_readonly_pipeline_example" after (manual) reduction to 
; equality logic.
; I.e., the arrays have been removed by using the corresponding reduction
; technique. Also the uninterpreted functions have been removed with Ackermann's
; reduction.
(set-logic QF_LIA)


; Declare (domain) variables.
; since ' ist not a valid SMTLIB symbol character, _ is used instead
; a ! symbol is appended to variable duplicated for formula expansion
(declare-fun $REG_w          () Int)
(declare-fun $REG_dest       () Int)
(declare-fun $REG_s          () Int)
(declare-fun $REG_lambda     () Int)

(declare-fun $REGci_w        () Int)
(declare-fun $REGci_dest     () Int)
(declare-fun $REGci_s        () Int)
(declare-fun $REGci_lambda   () Int)

(declare-fun $REGci__w       () Int)
(declare-fun $REGci__dest    () Int)
(declare-fun $REGci__s       () Int)
(declare-fun $REGci__lambda  () Int)

(declare-fun $REGsc_w        () Int)
(declare-fun $REGsc_dest     () Int)
(declare-fun $REGsc_s        () Int)
(declare-fun $REGsc_lambda   () Int)

(declare-fun $REGsc__w       () Int)
(declare-fun $REGsc__dest    () Int)
(declare-fun $REGsc__s       () Int)
(declare-fun $REGsc__lambda  () Int)

(declare-fun $REGci_w!       () Int)
(declare-fun $REGci_dest!    () Int)
(declare-fun $REGci_s!       () Int)
(declare-fun $REGci_lambda!  () Int)

(declare-fun $REGci__w!      () Int)
(declare-fun $REGci__dest!   () Int)
(declare-fun $REGci__s!      () Int)
(declare-fun $REGci__lambda! () Int)

(declare-fun $REGsc_w!       () Int)
(declare-fun $REGsc_dest!    () Int)
(declare-fun $REGsc_s!       () Int)
(declare-fun $REGsc_lambda!  () Int)

(declare-fun $REGsc__w!      () Int)
(declare-fun $REGsc__dest!   () Int)
(declare-fun $REGsc__s!      () Int)
(declare-fun $REGsc__lambda! () Int)

; Declare variables for pipeline registers
(declare-fun $v   () Int)
(declare-fun $v_  () Int)
(declare-fun $v_! () Int)
(declare-fun $w   () Int)


; Declare variables for inputs
(declare-fun $s    () Int)
(declare-fun $dest () Int)


; Declare variable lambda (which is used for reduction of array quantifiers
; to finite conjunction)
(declare-fun $lambda  () Int)
(declare-fun $lambda! () Int)

; Declare control variables
(declare-fun $x () Bool) 


; Declare uninterpreted functions "results"
(declare-fun $ALU_v        () Int)
(declare-fun $ALU_v_       () Int)
(declare-fun $ALU_REGci_s  () Int)
(declare-fun $ALU_v_!      () Int)
(declare-fun $ALU_REGci_s! () Int)

; Equivalence Criterion
(define-fun equiv (
  ; parameters
  (REGci__w      Int)
  (REGci__dest   Int)
  (REGci__s      Int)
  (REGci__lambda Int)
  (REGsc__w      Int)
  (REGsc__dest   Int)
  (REGsc__s      Int)
  (REGsc__lambda Int)
  )
  Bool ; return type
  (
     and (= REGsc__lambda REGci__lambda)
         (= REGsc__w      REGci__w     )
         (= REGsc__dest   REGci__dest  )
         (= REGsc__s      REGci__s     )
  )
)


; Update function, which describes behavior of circuit
; (in step-complete and complete-ISA branch)
(define-fun update (
  ; parameters
  (REG_w          Int)(REG_dest       Int)(REG_s          Int)(REG_lambda     Int)
  (REGci_w        Int)(REGci_dest     Int)(REGci_s        Int)(REGci_lambda   Int)
  (REGci__w       Int)(REGci__dest    Int)(REGci__s       Int)(REGci__lambda  Int)
  (REGsc_w        Int)(REGsc_dest     Int)(REGsc_s        Int)(REGsc_lambda   Int)
  (REGsc__w       Int)(REGsc__dest    Int)(REGsc__s       Int)(REGsc__lambda  Int)
  (v              Int)(v_             Int)(w              Int)(s              Int)
  (dest           Int)(lambda         Int)
  (ALU_v          Int)(ALU_v_         Int)(ALU_REGci_s    Int)
  (x             Bool)
  )
  Bool  ; return type
  
  ; main expression
  (
    and  (= REGci_w       ALU_v             )  
         (=> (distinct w lambda)
             (= REGci_lambda   REG_lambda  ))     
         (=> (distinct w dest)
             (= REGci_dest     REG_dest    ))
         (=> (distinct w s) 
             (= REGci_s        REG_s       ))
        
         (= REGci__dest  ALU_REGci_s)
         (=> (distinct dest lambda)
             (= REGci__lambda  REGci_lambda))
         (=> (distinct dest w)
             (= REGci__w       REGci_w     ))
         (=> (distinct dest s)
             (= REGci__s       REGci_s     ))
          
         (= REGsc_w     ALU_v               )
         (=> (distinct w lambda)
             (= REGsc_lambda   REG_lambda  ))
         (=> (distinct w dest)
             (= REGsc_dest     REG_dest    ))
         (=> (distinct w s)
             (= REGsc_s        REG_s       ))
         
         (= REGsc__dest  ALU_v_             )
         (=> (distinct dest lambda)
             (= REGsc__lambda  REGsc_lambda))
         (=> (distinct dest w)
             (= REGsc__w       REGsc_w     ))
         (=> (distinct dest s)
             (= REGsc__s       REGsc_s     ))
            
         (= v_
            (ite x ALU_v REG_s))     
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

; Functional constraints (according to Ackermann reduction)
(define-fun functional_constraints (
  ; parameters
  (REG_w          Int)(REG_dest       Int)(REG_s          Int)(REG_lambda     Int)
  (REGci_w        Int)(REGci_dest     Int)(REGci_s        Int)(REGci_lambda   Int)
  (REGci__w       Int)(REGci__dest    Int)(REGci__s       Int)(REGci__lambda  Int)
  (REGsc_w        Int)(REGsc_dest     Int)(REGsc_s        Int)(REGsc_lambda   Int)
  (REGsc__w       Int)(REGsc__dest    Int)(REGsc__s       Int)(REGsc__lambda  Int)
  (v              Int)
  (v_             Int)
  (w              Int)
  (s              Int)
  (dest           Int)
  ;(lambda         Int) ; not needed here
  (ALU_v          Int)(ALU_v_         Int)(ALU_REGci_s    Int)  
  )
  Bool  ; return type
  
  ; main expression
  (
    and (=> (= w dest)
            (and 
              (= REG_w     REG_dest   )
              (= REGci_w   REGci_dest )
              (= REGci__w  REGci__dest)
              (= REGsc_w   REGsc_dest )
              (= REGsc__w  REGsc__dest)
            )
        )
        (=> (= w s)
            (and 
              (= REG_w     REG_s      )
              (= REGci_w   REGci_s    )
              (= REGci__w  REGci__s   )
              (= REGsc_w   REGsc_s    )
              (= REGsc__w  REGsc__s   )
            )
        )
        (=> (= s dest)
            (and 
              (= REG_s     REG_dest   )
              (= REGci_s   REGci_dest )
              (= REGci__s  REGci__dest)
              (= REGsc_s   REGsc_dest )
              (= REGsc__s  REGsc__dest)
            )
        )
        (=> (= v v_)
            (= ALU_v     ALU_v_     )
        )
        (=> (= v REGci_s)
            (= ALU_v     ALU_REGci_s)
        )
        (=> (= v_ REGci_s)
            (= ALU_v_    ALU_REGci_s)
            
        )
  )
)

; The whole formula
; i.e., (functional_constraints => (lambda_constraints => (update => equiv))
(define-fun formula (
  ; parameters
  (REG_w          Int)(REG_dest       Int)(REG_s          Int)(REG_lambda     Int)
  (REGci_w        Int)(REGci_dest     Int)(REGci_s        Int)(REGci_lambda   Int)
  (REGci__w       Int)(REGci__dest    Int)(REGci__s       Int)(REGci__lambda  Int)
  (REGsc_w        Int)(REGsc_dest     Int)(REGsc_s        Int)(REGsc_lambda   Int)
  (REGsc__w       Int)(REGsc__dest    Int)(REGsc__s       Int)(REGsc__lambda  Int)
  (v              Int)(v_             Int)(w              Int)(s              Int)
  (dest           Int)(lambda         Int)
  (ALU_v          Int)(ALU_v_         Int)(ALU_REGci_s    Int)
  (x             Bool)
  )
  Bool  ; return type
  
  ; main expression
  (=> (functional_constraints 
        REG_w    REG_dest    REG_s    REG_lambda
        REGci_w  REGci_dest  REGci_s  REGci_lambda
        REGci__w REGci__dest REGci__s REGci__lambda
        REGsc_w  REGsc_dest  REGsc_s  REGsc_lambda
        REGsc__w REGsc__dest REGsc__s REGsc__lambda
        v v_ w s dest 
        ALU_v    ALU_v_      ALU_REGci_s)      
      (=> (lambda_constraints v w s dest lambda) 
          (=> (update
                REG_w    REG_dest    REG_s    REG_lambda
                REGci_w  REGci_dest  REGci_s  REGci_lambda
                REGci__w REGci__dest REGci__s REGci__lambda
                REGsc_w  REGsc_dest  REGsc_s  REGsc_lambda
                REGsc__w REGsc__dest REGsc__s REGsc__lambda
                v v_ w s dest lambda 
                ALU_v    ALU_v_      ALU_REGci_s
                x)
              (equiv
                REGci__w REGci__dest REGci__s REGci__lambda
                REGsc__w REGsc__dest REGsc__s REGsc__lambda)
          )
      )
  )
)

; assert the negation of the (supposedly valid) main formula, expanded
; over the control signal.

(assert (not (formula
              $REG_w     $REG_dest     $REG_s     $REG_lambda
              $REGci_w   $REGci_dest   $REGci_s   $REGci_lambda
              $REGci__w  $REGci__dest  $REGci__s  $REGci__lambda
              $REGsc_w   $REGsc_dest   $REGsc_s   $REGsc_lambda
              $REGsc__w  $REGsc__dest  $REGsc__s  $REGsc__lambda
              $v  $v_ $w $s  $dest     $lambda
              $ALU_v     $ALU_v_       $ALU_REGci_s
              true )))
            
(assert (not (formula
              $REG_w     $REG_dest     $REG_s     $REG_lambda
              $REGci_w!  $REGci_dest!  $REGci_s!  $REGci_lambda!
              $REGci__w! $REGci__dest! $REGci__s! $REGci__lambda!
              $REGsc_w!  $REGsc_dest!  $REGsc_s!  $REGsc_lambda!
              $REGsc__w! $REGsc__dest! $REGsc__s! $REGsc__lambda!
              $v $v_! $w $s   $dest    $lambda!
              $ALU_v     $ALU_v_!      $ALU_REGci_s!
              false )))            



; Check if the expected solution (x <=> s=w) is a valid solution

; (assert (not (formula
;               $REG_w     $REG_dest     $REG_s     $REG_lambda
;               $REGci_w   $REGci_dest   $REGci_s   $REGci_lambda
;               $REGci__w  $REGci__dest  $REGci__s  $REGci__lambda
;               $REGsc_w   $REGsc_dest   $REGsc_s   $REGsc_lambda
;               $REGsc__w  $REGsc__dest  $REGsc__s  $REGsc__lambda
;               $v  $v_ $w $s  $dest     $lambda
;               $ALU_v     $ALU_v_       $ALU_REGci_s
;               $x )))
; (assert (= $x (= $s $w)))            

;(get-assertions)
(check-sat)
;(get-info model)
