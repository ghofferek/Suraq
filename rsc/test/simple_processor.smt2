(set-logic Suraq)
; (set-option :auto-config false)
; (set-logic QF_AUFLIA)
; (set-option :produce-models true)
; (declare-sort Value 0) 



(declare-fun MEM       () (Array Value Value))
(declare-fun MEMci_    () (Array Value Value) :no_dependence)
(declare-fun MEMci__   () (Array Value Value) :no_dependence)
(declare-fun MEMsc_    () (Array Value Value) :no_dependence)
(declare-fun MEMsc__   () (Array Value Value) :no_dependence)
; (declare-fun MEMci_    () (Array Value Value) )
; (declare-fun MEMci__   () (Array Value Value) )
; (declare-fun MEMsc_    () (Array Value Value) )
; (declare-fun MEMsc__   () (Array Value Value) )


(declare-fun PC        () Value)
(declare-fun PCci_     () Value :no_dependence)
(declare-fun PCci__    () Value :no_dependence)
(declare-fun PCsc_     () Value :no_dependence)
(declare-fun PCsc__    () Value :no_dependence)
; (declare-fun PCci_     () Value )
; (declare-fun PCci__    () Value )
; (declare-fun PCsc_     () Value )
; (declare-fun PCsc__    () Value )


(declare-fun addr_reg           () Value)
(declare-fun addr_regsc_        () Value :no_dependence)
; (declare-fun addr_regsc_        () Value )
(declare-fun alu_reg            () Value)
(declare-fun alu_regsc_         () Value :no_dependence)
; (declare-fun alu_regsc_         () Value )
(declare-fun take_branch_reg    () Bool)
(declare-fun take_branch_regsc_ () Bool :no_dependence)
; (declare-fun take_branch_regsc_ () Bool )

(declare-fun inst-of (Value) Value)
(declare-fun op-a-of (Value) Value)
(declare-fun op-b-of (Value) Value)
(declare-fun addr-of (Value) Value)
(declare-fun incr    (Value) Value)

(declare-fun ALU (Value Value Value) Value)

(declare-fun is-BEQZ (Value) Bool)

(declare-fun ZERO () Value)

(declare-fun forward () Control)
(declare-fun squash  () Control)

; (declare-fun forward () Bool)
; (declare-fun squash  () Bool)

(define-fun r_data (
  (mem    (Array Value Value))
  (r_addr Value)
  )
  Value ; return type
  ; main expression
  (ite 
     (= r_addr ZERO)
     ZERO
     (select mem r_addr)
  )
)

(define-fun w_addr ( 
  (take_branch  Bool)
  (addr        Value)
  )
  Value ; return type
  ; main expression
  (ite
    take_branch
    ZERO
    addr
  )
)


(define-fun update () Bool 
  (and
    
    ; ci path
    
    ; complete
    (ite
      (= ZERO (w_addr take_branch_reg addr_reg))
      (= MEMci_ MEM)
      (= MEMci_ (store MEM (w_addr take_branch_reg addr_reg) alu_reg))
    )
    (= PCci_ (ite take_branch_reg alu_reg PC))
    
    ; instruction
    (ite
      squash
      (and
        (= MEMci__ MEMci_)
        (= PCci__ PCci_)
      )
      (and
        (= 
          MEMci__
          (ite
            (=
              ZERO
              (w_addr 
                (and
                  (is-BEQZ (inst-of (r_data MEMci_ PCci_)))
                  (= ZERO (op-a-of (r_data MEMci_ PCci_)))
                )
                (addr-of (r_data MEMci_ PCci_))
              )
            )
            MEMci_ 
            (store 
              MEMci_ 
              (w_addr 
                (and
                  (is-BEQZ (inst-of (r_data MEMci_ PCci_)))
                  (= ZERO (op-a-of (r_data MEMci_ PCci_)))
                )
                (addr-of (r_data MEMci_ PCci_))
              )
              (ALU
                (inst-of (r_data MEMci_ PCci_))
                (op-a-of (r_data MEMci_ PCci_))
                (op-b-of (r_data MEMci_ PCci_))
              )
            )
          )
        )
        (=
          PCci__
          (ite
            (and
                (is-BEQZ (inst-of (r_data MEMci_ PCci_)))
                (= ZERO (op-a-of (r_data MEMci_ PCci_)))
            )
            (ALU
              (inst-of (r_data MEMci_ PCci_))
              (op-a-of (r_data MEMci_ PCci_))
              (op-b-of (r_data MEMci_ PCci_))
            )
            (incr PCci_)
          )
        )
      )
    )  
    ; sc path
    
    ; step
    (ite
      (= ZERO (w_addr take_branch_reg addr_reg))
      (= MEMsc_ MEM)
      (= MEMsc_ (store MEM (w_addr take_branch_reg addr_reg) alu_reg))
    )
    (= PCsc_ (ite take_branch_reg alu_reg (incr PC)))
    
    (= 
      take_branch_regsc_
      (and
        (is-BEQZ (inst-of (ite forward alu_reg (r_data MEM PC))))
        (= ZERO  (op-a-of (ite forward alu_reg (r_data MEM PC))))
      )
    )
    (= 
      alu_regsc_
      (ALU
        (inst-of (ite forward alu_reg (r_data MEM PC)))
        (op-a-of (ite forward alu_reg (r_data MEM PC)))
        (op-b-of (ite forward alu_reg (r_data MEM PC)))
      )
    )
    (=
      addr_regsc_
      (ite
        squash
        ZERO
        (addr-of (ite forward alu_reg (r_data MEM PC)))
      )
    )
  
    ; complete
    (ite
      (= ZERO (w_addr take_branch_regsc_ addr_regsc_))
      (= MEMsc__ MEMsc_)
      (= MEMsc__ (store MEMsc_ (w_addr take_branch_regsc_ addr_regsc_) alu_regsc_))
    )
    (ite
      squash
      (= PCsc__ PCsc_)
      (= PCsc__ (ite take_branch_regsc_ alu_regsc_ PCsc_))
    )  
  )
)

(define-fun equivalence () Bool 
  (and
    (= MEMci__ MEMsc__)
    (or
      (= PCci__  PCsc__ )
      (and
        (= PCci__ (incr PCsc__))
        take_branch_reg
      )
    )
  )
)

(define-fun main_formula () Bool 
  (=>
    update
    equivalence
  )
)

(assert main_formula)
; (assert (not main_formula))

; (assert (= forward (and (= addr_reg PC) (not (= ZERO PC)) (not take_branch_reg))))
; (assert (= squash take_branch_reg))


; (check-sat)


; (get-model)
; (get-value (equivalence))
; (get-value (update))
; (get-value (main_formula))  
; (get-value ((= PCci__ PCsc__)))
; (get-value ((= MEMci__ MEMsc__)))
; (get-value ((= MEMci_ MEMsc_)))
; (get-value (ZERO))
; (get-value (PC))
; (get-value ((incr PC)))
; (get-value ((incr PCci_)))
; (get-value (PCci_))
; (get-value (PCci__))
; (get-value (PCsc_))
; (get-value (PCsc__))
; (get-value (forward))
; (get-value (squash))
; (get-value (take_branch_reg))
; (get-value (take_branch_regsc_))
; (get-value (
;   (and
;     (is-BEQZ (inst-of (r_data MEMci_ PCci_)))
;     (= ZERO (op-a-of (r_data MEMci_ PCci_)))
;   )))
; (get-value (
;   (and
;     (is-BEQZ (inst-of (ite forward alu_reg (r_data MEM PC))))
;     (= ZERO  (op-a-of (ite forward alu_reg (r_data MEM PC))))
;   )))
; (get-value (
;   (and
;     (is-BEQZ (inst-of (ite forward alu_reg (r_data MEMsc_ PCsc_))))
;     (= ZERO  (op-a-of (ite forward alu_reg (r_data MEMsc_ PCsc_))))
;   )))
; (get-value (alu_regsc_))
; (get-value (
;   (ALU
;     (inst-of (r_data MEM PC))
;     (op-a-of (r_data MEM PC))
;     (op-b-of (r_data MEM PC))
;   )))
; (get-value (
;   (ALU
;     (inst-of (r_data MEMci_ PCci_))
;     (op-a-of (r_data MEMci_ PCci_))
;     (op-b-of (r_data MEMci_ PCci_))
;   )))
; (get-value ((r_data MEMci_ PCci_)))
; (get-value (alu_reg))
; (get-value ((select MEMci_ addr_reg)))
; (get-value ((select MEMci_ PCci_)))
; (get-value ((w_addr take_branch_reg addr_reg)))
; (get-value (addr_reg))
; (get-value ((w_addr take_branch_reg addr_reg)))
