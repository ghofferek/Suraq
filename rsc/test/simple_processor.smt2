;(set-logic Suraq)
(set-logic QF_AUFLIA)
(declare-sort Value 0) 

(declare-fun MEM       () (Array Value Value))
(declare-fun MEMci_    () (Array Value Value) :no_dependence)
(declare-fun MEMci__   () (Array Value Value) :no_dependence)
(declare-fun MEMsc_    () (Array Value Value) :no_dependence)
(declare-fun MEMsc__   () (Array Value Value) :no_dependence)

(declare-fun PC        () Value)
(declare-fun PCci_     () Value :no_dependence)
(declare-fun PCci__    () Value :no_dependence)
(declare-fun PCsc_     () Value :no_dependence)
(declare-fun PCsc__    () Value :no_dependence)

(declare-fun addr_reg           () Value)
(declare-fun addr_regsc_        () Value :no_dependence)
(declare-fun alu_reg            () Value)
(declare-fun alu-regsc_         () Value :no_dependence)
(declare-fun take_branch_reg    () Bool)
(declare-fun take_branch_regsc_ () Bool :no_dependence)

(declare-fun inst-of (Value) Value)
(declare-fun op-a-of (Value) Value)
(declare-fun op-b-of (Value) Value)
(declare-fun addr-of (Value) Value)
(delcare-fun incr    (Value) Value)

(declare-fun ALU (Value Value Value) Value)

(declare-fun is-BEQZ (Value) Bool)

(declare-fun ZERO () Value)

;(declare-fun forward () Control)
;(declare-fun squash  () Control)

(declare-fun forward () Bool)
(declare-fun squash  () Bool)

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
    (= MEMci_ (store MEM (w_addr take_branch_reg addr_reg) alu_reg))
    (= PCci_ (ite take_branch_reg alu_reg (incr PC)))
    
    ; instruction
    (= 
      MEMci__ 
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
          (inst-of (r_data MEMci_ PCci__))
          (op-a-of (r_data MEMci_ PCci_))
          (op-b-of (r_data MEMci_ PCci_))
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
          (inst-of (r_data MEMci_ PCci__))
          (op-a-of (r_data MEMci_ PCci_))
          (op-b-of (r_data MEMci_ PCci_))
        )
        (incr PCci_)
      )
    )
  
    ; sc path
    
    ; step
    (= MEMsc_ (store MEM (w_addr take_branch_reg addr_reg) alu_reg))
    (= PCsc_ (ite take_branch_reg alu_reg (incr PC)))
    
    (= 
      take_branch_regsc_
      (and
        (is-BEQZ (inst-of (ite forward alu_reg (r_data MEMsc_ PCsc_))))
        (= ZERO  (op-a-of (ite forward alu_reg (r_data MEMsc_ PCsc_))))
      )
    )
    (= 
      alu_regsc_
      (ALU
        (inst-of (ite forward alu_reg (r_data MEMsc_ PCsc_)))
        (op-a-of (ite forward alu_reg (r_data MEMsc_ PCsc_)))
        (op-b-of (ite forward alu_reg (r_data MEMsc_ PCsc_)))
      )
    )
    (=
      addr_regsc_
      (ite
        squash
        ZERO
        (addr-of (ite forward alu_reg (r_data MEMsc_ PCsc_)))
      )
    )
  
    ; complete
    (= MEMsc__ (store MEMsc_ (w_addr take_branch_regsc_ addr_regsc_) alu_regsc_))
    (= PCsc__ (ite take_branch_regsc_ alu_regsc_ (incr PCsc_)))  
        
  )
)

(define-fun equiv () Bool 
  (and
    (= MEMci__ MEMsc__)
    (= PCci__  PCsc__ )
  )
)

(define-fun main_formula () Bool 
  (=>
    update
    equiv
  )
)

;(assert main_formula)
(assert (not main_formula))

(assert (= forward (= addr_reg PC)))
(assert (= squash take_branch_reg))
    
  