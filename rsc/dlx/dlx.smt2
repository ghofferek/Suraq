; DLX processor
;
; encoded in SMTLIBv2 format by Georg Hofferek <georg.hofferek@iaik.tugraz.at>

(set-logic Suraq)


; Declare arrays

(declare-fun REGFILE      () (Array Value Value))
(declare-fun REGFILEci1_  () (Array Value Value) :no_dependence)
(declare-fun REGFILEci2_  () (Array Value Value) :no_dependence)
(declare-fun REGFILEci3_  () (Array Value Value) :no_dependence)
(declare-fun REGFILEci4_  () (Array Value Value) :no_dependence)
(declare-fun REGFILEci5_  () (Array Value Value) :no_dependence)
(declare-fun REGFILEsc1_  () (Array Value Value) :no_dependence)
(declare-fun REGFILEsc2_  () (Array Value Value) :no_dependence)
(declare-fun REGFILEsc3_  () (Array Value Value) :no_dependence)
(declare-fun REGFILEsc4_  () (Array Value Value) :no_dependence)
(declare-fun REGFILEsc5_  () (Array Value Value) :no_dependence)

(declare-fun DMEM         () (Array Value Value))
(declare-fun DMEMci1_     () (Array Value Value) :no_dependence)
(declare-fun DMEMci2_     () (Array Value Value) :no_dependence)
(declare-fun DMEMci3_     () (Array Value Value) :no_dependence)
(declare-fun DMEMci4_     () (Array Value Value) :no_dependence)
(declare-fun DMEMci5_     () (Array Value Value) :no_dependence)
(declare-fun DMEMsc1_     () (Array Value Value) :no_dependence)
(declare-fun DMEMsc2_     () (Array Value Value) :no_dependence)
(declare-fun DMEMsc3_     () (Array Value Value) :no_dependence)
(declare-fun DMEMsc4_     () (Array Value Value) :no_dependence)
(declare-fun DMEMsc5_     () (Array Value Value) :no_dependence)

(declare-fun IMEM         () (Array Value Value))  ; IMEM is never written. Thus no need for more copies.


; Declare constants

(declare-fun FOUR () Value)
(declare-fun ZERO () Value)


; Declare single data elements

(declare-fun PC () Value)  ; Program counter


; Declare uninterpreted functions of the datapath

(declare-fun PLUS              (Value Value      )   Value)
(declare-fun ALU               (Value Value Value)   Value)
(declare-fun rf1-of            (Value            )   Value)
(declare-fun rf2-of            (Value            )   Value)
(declare-fun rf3-of            (Value            )   Value)
(declare-fun opcode-of         (Value            )   Value)
(declare-fun short-immed-of    (Value            )   Value)
(declare-fun long-immed-of     (Value            )   Value)
(declare-fun alu-op-of         (Value            )   Value)


; Declare uninterpreted predicates of the datapath

(declare-fun is-load           (Value            )   Bool )
(declare-fun is-store          (Value            )   Bool ) 
(declare-fun is-J              (Value            )   Bool )
(declare-fun is-BEQZ           (Value            )   Bool )
(declare-fun is-alu-immed      (Value            )   Bool )


; Declare pipeline registers

(declare-fun inst-id         () Value)
(declare-fun bubble-id       () Bool )

(declare-fun bubble-ex       () Bool )
(declare-fun short-immed-ex  () Value)
(declare-fun dest-ex         () Value)
(declare-fun opcode-ex       () Value)
(declare-fun operand-a       () Value)
(declare-fun operand-b       () Value)

(declare-fun dest-mem        () Value)
(declare-fun result-mem      () Value)
(declare-fun mar             () Value)
(declare-fun load-flag       () Bool )
(declare-fun store-flag      () Bool )

(declare-fun dest-wb         () Value)
(declare-fun result-wb       () Value)


; Declare "stepped" pipeline registers (values after one step)

(declare-fun inst-id_        () Value :no_dependence)
(declare-fun bubble-id_      () Bool  :no_dependence)

(declare-fun bubble-ex_      () Bool  :no_dependence)
(declare-fun short-immed-ex_ () Value :no_dependence)
(declare-fun dest-ex_        () Value :no_dependence)
(declare-fun opcode-ex_      () Value :no_dependence)
(declare-fun operand-a_      () Value :no_dependence)
(declare-fun operand-b_      () Value :no_dependence)

(declare-fun dest-mem_       () Value :no_dependence)
(declare-fun result-mem_     () Value :no_dependence)
(declare-fun mar_            () Value :no_dependence)
(declare-fun load-flag_      () Bool  :no_dependence)
(declare-fun store-flag_     () Bool  :no_dependence)

(declare-fun dest-wb_        () Value :no_dependence)
(declare-fun result-wb_      () Value :no_dependence)



; Equivalence Criterion:
; The programmer-visible state of the processor is the REGFILE and the DMEM.
; They must be equal after going along the ci and the sc branch.

(define-fun equiv 
  ( ; parameters
    (REGFILEci (Array Value Value))
    (REGFILEsc (Array Value Value))
    (DMEMci    (Array Value Value))
    (DMEMsc    (Array Value Value))
  )
  Bool ; return type of macro
  ; main expression: 
  ( 
    (and (= REGFILEci REGFILEsc)
         (= DMEMci    DMEMsc   )
    )
  )
)


; One instruction in the reference architecture

(define-fun instruction-in-reference
  ( ; parameters
  
    ; "inputs" to macro (state before the instruction)
    (REGFILEi (Array Value Value))
    (DMEMi    (Array Value Value))
    (IMEMi    (Array Value Value))
    (PCi      Value              )
  
    ; "outputs" of macro (state after the instruction)
    (REGFILEo (Array Value Value))
    (DMEMo    (Array Value Value))
    (IMEMo    (Array Value Value))
    (PCo      Value              )
  )
  Bool ; return type of macro
  ; main expression
  (
    (and  ; conjunction over all parts of update expression 
      
      ; IMEM is never written
      (= IMEMo IMEMi)
    
      ; update of PC
      (= PCo
        (ite 
          (is-J (opcode-of (select IMEMi PCi))) 
          (PLUS
            (PLUS PCi FOUR)
            (long-immed-of (select IMEMi PCi)) 
          ) 
          (ite
            (and
              (is-BEQZ (opcode-of (select IMEMi PCi)))
              (= 
                ZERO
                (ite
                  (= ZERO (rf1-of (select IMEMi PCi)))
                  (ZERO)
                  (select REGFILEi (rf1-of (select IMEMi PCi)))
                )
              )
            )
            (PLUS
              (PLUS PCi FOUR)
              (short-immed-of (opcode-of (select IMEMi PCi))) 
            )
            (PLUS PCi FOUR)
          )
        )  
      )
    
      ; update of DMEM
      (ite
        (is-store (opcode-of (select IMEMi PCi))) ; write-enable
        (= 
          DMEMo
          (store
            DMEMi
            (PLUS
              (short-immed-of (select IMEMi PCi))
              (ite
                (= ZERO (rf1-of (select IMEMi PCi)))
                (ZERO)
                (select REGFILEi (rf1-of (select IMEMi PCi)))
              )
            )
            (ite
              (= ZERO (rf2-of (select IMEMi PCi)))
              (ZERO)
              (select REGFILEi (rf2-of (select IMEMi PCi)))
            )
          )
        )
        (= DMEMo DMEMi) ; write-enable == False
      )
    
      ; update of REGFILE
      ( 
      ;TODO
      )
      
    ) ; END conjunction over all parts 
  ) ; END main expression
) ; END instruction-in-reference macro

