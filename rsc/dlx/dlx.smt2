; DLX processor
;
; encoded in SMTLIBv2 format by Georg Hofferek <georg.hofferek@iaik.tugraz.at>
;
;
; Some notes:
;
;
; *) When refering to a "Burch-Dill diagram", a diagram of the following form
;    is ment:
;
;    ISA            O --------- instr -----> O
;                   ^                        ^
;                   |                        |
;                   |                        |
;                complete                complete
;                   |                        |
;                   |                        |
;    Pipeline       O --------- step ------> O
;
; 
; *) For modelling the evolution of data elements during the "ci" and "sc" path,
;    copies of are created, where necessary. The naming convention is as follows:
;    "ci" ("sc", respectively) is added to the name of the variable, followed by
;    a number from 1-5 and a "_". The "_" substitutes the prime "'", which is not
;    a legal symbol for identifiers in SMTLIBv2. The number indicates how many 
;    primes there are. I.e., "PCci3_" should read "PC (program counter) three prime,
;    in path ci."
;
; *) The unprimed names of data elements represent the "original" values. I.e.,
;    the values in the start state (lower left corner in Burch-Dill diagram).
;
; *) The names with 5 primes ("5_") represent the "end state", i.e., the upper
;    right state in the Burch-Dill diagram. The "*ci5_" and the "*sc5_" values
;    are supposed to be equal (programmer visible parts only).
;
; *) In the "sc" path, the names "*sc1_" represent the values after the "step"
;    operation. I.e., the values corresponding to the lower right state in the
;    Burch-Dill diagram.
;
; *) In the "ci" path, the names "*ci4_" correspond to the values before the 
;    ISA instruction. I.e., to the values in the upper left state of the Burch-
;    Dill diagram.
;
; *) The names "*ci1_" to "*ci4" correspond to intermediate values during the
;    completion (left upwards arrow in the Burch-Dill diagram). "*ci4_" are
;    the values for which completion has finished.
;
; *) The names "*sc2_" to "*sc5_" correspond to the intermediate values during
;    the completion (right upwards arrow in the Burch-Dill diagram). "*sc5_" are
;    the values for which completion has finished.
;
; *) The combinational logic of each stage (or the whole ISA model) is modelled 
;    as a separate macro of (return) type Bool. The "inputs" ("outputs", respectively) 
;    of the macros are named by appeding an "i" ("o", respectively) to the name
;    of the signal.
;
; *) Completion is achieved by plugging the aforementioned macros together.
;    The process is illustrated for the sc path. The ci path works analogously.
;    First, the last stage is completed. To do so, the corresponding macro is
;    instantiated with inputs "*sc1_" and outputs "*sc2_". Next, the macros for
;    the second-to-last stage and the last stage are instantiated. The second-to-last
;    stage macro uses inputs "*sc1_" and outputs "*sc2_". This last stage macro 
;    uses "*sc2" as inputs and "*sc3_" as outputs. The remainin completion
;    proceeds analogously. 
;
; *) During completion, forwarding signals from stages that are already completed
;    are set to "no forward". (This is necessary to ensure that only one instance
;    of the control signal occurs in the formula.)



(set-logic Suraq)


; Declare arrays
; (and copies for ci and sc paths)

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
; (and copies for ci and sc paths)

(declare-fun PC     () Value               )  ; Program counter
(declare-fun PCci4_ () Value :no_dependence)  
(declare-fun PCci5_ () Value :no_dependence)
(declare-fun PCsc1_ () Value :no_dependence)  
(declare-fun PCsc5_ () Value :no_dependence)
  

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


; Declare pipeline registers (and copies for stepping and completion)

; ID stage
(declare-fun inst-id             () Value               )
(declare-fun inst-idci4_         () Value :no_dependence)
(declare-fun inst-idsc1_         () Value :no_dependence)
(declare-fun inst-idsc5_         () Value :no_dependence)

(declare-fun bubble-id           () Bool  :no_dependence)
(declare-fun bubble-idci4_       () Bool  :no_dependence)
(declare-fun bubble-idsc1_       () Bool  :no_dependence)
(declare-fun bubble-idsc5_       () Bool  :no_dependence)

; EX stage
(declare-fun bubble-ex           () Bool                )
(declare-fun bubble-exci3_       () Bool  :no_dependence)
(declare-fun bubble-exci4_       () Bool  :no_dependence)
(declare-fun bubble-exsc1_       () Bool  :no_dependence)
(declare-fun bubble-exsc4_       () Bool  :no_dependence)
(declare-fun bubble-exsc5_       () Bool  :no_dependence)

(declare-fun short-immed-ex      () Value               )
(declare-fun short-immed-exci3_  () Value :no_dependence)
(declare-fun short-immed-exci4_  () Value :no_dependence)
(declare-fun short-immed-exsc1_  () Value :no_dependence)
(declare-fun short-immed-exsc4_  () Value :no_dependence)
(declare-fun short-immed-exsc5_  () Value :no_dependence)

(declare-fun dest-ex             () Value               )
(declare-fun dest-exci3_         () Value :no_dependence)
(declare-fun dest-exci4_         () Value :no_dependence)
(declare-fun dest-exsc1_         () Value :no_dependence)
(declare-fun dest-exsc4_         () Value :no_dependence)
(declare-fun dest-exsc5_         () Value :no_dependence)

(declare-fun opcode-ex           () Value               )
(declare-fun opcode-exci3_       () Value :no_dependence)
(declare-fun opcode-exci4_       () Value :no_dependence)
(declare-fun opcode-exsc1_       () Value :no_dependence)
(declare-fun opcode-exsc4_       () Value :no_dependence)
(declare-fun opcode-exsc5_       () Value :no_dependence)

(declare-fun operand-a           () Value               )
(declare-fun operand-aci3_       () Value  :no_dependence)
(declare-fun operand-aci4_       () Value  :no_dependence)
(declare-fun operand-asc1_       () Value  :no_dependence)
(declare-fun operand-asc4_       () Value  :no_dependence)
(declare-fun operand-asc5_       () Value  :no_dependence)

(declare-fun operand-b           () Value               )
(declare-fun operand-bci3_       () Value  :no_dependence)
(declare-fun operand-bci4_       () Value  :no_dependence)
(declare-fun operand-bsc1_       () Value  :no_dependence)
(declare-fun operand-bsc4_       () Value  :no_dependence)
(declare-fun operand-bsc5_       () Value  :no_dependence)

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


; Helper Macros (to shorten main parts of formula)

(define-fun rf1data
  ( ; parameters
    (REGFILE (Array Value Value))
    (IMEM    (Array Value Value))
    (PC      Value              )
  )
  Value ; return type of macro
  ; main expression:
  (
    (ite
      (= ZERO (rf1-of (select IMEM PC)))
      ZERO
      (select REGFILE (rf1-of (select IMEM PC)))
    )
  )
) 

(define-fun rf2data
  ( ; parameters
    (REGFILE (Array Value Value))
    (IMEM    (Array Value Value))
    (PC      Value              )
  )
  Value ; return type of macro
  ; main expression:
  (
    (ite
      (= ZERO (rf2-of (select IMEM PC)))
      ZERO
      (select REGFILE (rf2-of (select IMEM PC)))
    )
  )
) 

(define-fun alu-result
  ( ; parameters
    (operand-a    Value)
    (operand-b    Value)
    (opcode       Value)
    (short-immed  Value)
  )
  Value ; return type of macro
  ; main expression:
  (
    (ite
      (or
        (is-load  opcode)
        (is-store opcode)
      )
      (PLUS short-immed operand-a)
      (ALU (alu-op-of opcode) operand-a operand-b)
    )
  )
) 

(define-fun stall-issue
  ( ; parameters
    (force-stall-issue  Bool )
    (bubble-ex          Bool )
    (dest-ex            Value)
    (bubble-id          Bool )
    (inst-id            Value)
  )
  Bool ; return type of macro
  ; main expression
  (
    (or
      force-stall-issue
      (and
        (or
          (= (rf1-of inst-id) dest-ex)
          (= (rf2-of inst-id) dest-ex)
        )
        (is-load (opcode-of inst-id))
        (not bubble-ex)
        (not bubble-id)
      )
    )
  )
)

(define-fun branch-taken
  ( ; parameters
    (bubble-id          Bool )
    (inst-id            Value)
    (operand-an         Value)
  )
  Bool ; return type of macro
  ; main expression
  (
    (and
      (not bubble-id)
      (or
        (is-J (opcode-of inst-id))
        (and
          (is-BEQZ (opcode of inst-id))
          (= ZERO operand-an)
        )
      )
    )
  )
)

(define-fun TA
  ( ; parameters
    (inst-id Value)
    (PC      Value)
  )
  Value ; return type of macro
  ; main expression
  (
    (ite
      (is-J (opcode-of inst-id))
      (PLUS PC (long-immed-of  inst-id))
      (PLUS PC (short-immed-of inst-id))
    )
  )
)

; ------------------------------------------------------------------------------
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
   ;(IMEMo    (Array Value Value))
    (PCo      Value              )
  )
  Bool ; return type of macro
  ; main expression
  (
    (and  ; conjunction over all parts of update expression 
      
      ; IMEM is never written
      ; (= IMEMo IMEMi)
    
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
                (rf1data REGFILEi IMEMi PCi)
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
              (rf1data REGFILEi IMEMi PCi)
            )
            (rf2data REGFILEi IMEMi PCi)
          )
        )
        (= DMEMo DMEMi) ; write-enable == False
      )
    
      ; update of REGFILE
      (ite 
        (or ; write-enable
          (and
            (distinct ZERO (rf2-of (select IMEMi PCi)))
            (is-load (opcode-of (select IMEMi PCi)))
          )
          (and
            (distinct ZERO (rf2-of (select IMEMi PCi)))
            (is-alu-immed (opcode-of (select IMEMi PCi)))
          )
          (and
            (distinct ZERO (rf3-of (select IMEMi PCi)))
            (and
              (not (is-load       (opcode-of (select IMEMi PCi))))
              (not (is-store      (opcode-of (select IMEMi PCi))))
              (not (is-J          (opcode-of (select IMEMi PCi))))
              (not (is-BEQZ       (opcode-of (select IMEMi PCi))))
              (not (is-alu-immed  (opcode-of (select IMEMi PCi))))
            )
          )
        )   ; END write-enable
        (=  ; write to REGFILE
          REGFILEo
          (store
            REGFILEi
            (ite    ; write address
              (and
                (not (is-load       (opcode-of (select IMEMi PCi))))
                (not (is-store      (opcode-of (select IMEMi PCi))))
                (not (is-J          (opcode-of (select IMEMi PCi))))
                (not (is-BEQZ       (opcode-of (select IMEMi PCi))))
                (not (is-alu-immed  (opcode-of (select IMEMi PCi))))
              )
              (rf3-of (select IMEMi PCi))
              (rf2-of (select IMEMi PCi))
            )       ; END write address
            (ite ; write data
              (is-load (opcode-of (select IMEMi PCi)))
              (select
                DMEMi 
                (PLUS
                  (short-immed-of (select IMEMi PCi))
                  (rf1data REGFILEi IMEMi PCi)
                )
              )
              (ALU
                (alu-op-of (opcode-of (select IMEMi PCi)))
                (rf1data REGFILEi IMEMi PCi)
                (ite
                  (is-alu-immed (opcode-of (select IMEMi PCi)))
                  (short-immed-of (select IMEMi PCi))
                  (rf2data REGFILEi IMEMi PCi)
                )
              )
            )    ; END write data
          )
        )   ; END write to REGFILE
        (= REGFILEi REGFILEo) ; write-enable == False
      )
      
    ) ; END conjunction over all parts 
  ) ; END main expression
) ; END instruction-in-reference macro


; ------------------------------------------------------------------------------
; ------------------------------------------------------------------------------
; Macros for each stage of the pipeline.

(define-fun step-in-REGFILE
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (REGFILEi         (Array Value Value))
    
    (dest-wbi         Value              )
    (result-wbi       Value              )
      
    ; "outputs" of macro (state after the step)
    (REGFILEo         (Array Value Value))
  )
  Bool ; return type
  ; main expression
  (
    (and ; conjunction over all parts
         
      ; update of REGFILE
      (ite
        (distinct ZERO dest-wbi) ; write-enable
        (=
          REGFILEo
          (store REGFILEi dest-wbi result-wbi)
        )
        (= REGFILEo REGFILEi) ; write-enable == False
      )
    ) ; END conjunction over all parts 
  ) ; END main expression
) ; END of step-in-REGFILE macro


; ------------------------------------------------------------------------------
(define-fun step-in-WB
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (DMEMi            (Array Value Value))
    
    (dest-memi        Value              )
    (result-memi      Value              )
    (mari             Value              )
    (load-flagi       Bool               )
    (store-flagi      Bool               )
    
      
    ; "outputs" of macro (state after the step)
    (DMEMo            (Array Value Value))
    
    (dest-wbo         Value              )
    (result-wbo       Value              )
  
  )
  Bool ; return type
  ; main expression
  (
    (and ; conjunction over all parts
      
    
      ; update of DMEM
      (ite
        store-flagi ; write-enable
        (=
          DMEMo
          (store DMEMi mari result-memi)
        )
        (= DMEMo DMEMi) ; write-enable == False
      )
    
      ; update of WB stage registers
      (= dest-wbo dest-memi)
      (= 
        result-wbo
        (ite
          load-flagi
          (select DMEMi mari)
          result-memi
        )
      )
    ) ; END conjunction over all parts 
  ) ; END main expression
) ; END of step-in-WB macro


; ------------------------------------------------------------------------------
(define-fun step-in-MEM
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (inst-idi         Value              )
    (bubble-idi       Bool               )
    
    (bubble-exi       Bool               )
    (short-immed-exi  Value              )
    (dest-exi         Value              )
    (opcode-exi       Value              )
    (operand-ai       Value              )
    (operand-bi       Value              )
    
    (dest-wbi         Value              )
    (result-wbi       Value              )
      
    ; "outputs" of macro (state after the step)
    (dest-memo        Value              )
    (result-memo      Value              )
    (maro             Value              )
    (load-flago       Bool               )
    (store-flago      Bool               )
  )
  Bool ; return type
  ; main expression
  (
    (and ; conjunction over all parts
        
      ; update of MEM stage registers
      (= dest-memo dest-exi)
      (= 
        result-memo
        (ite
          (or (is-load opcode-exi) (is-store opcode-exi))
          (PLUS operand-ai short-immed-exi)
          (alu-result operand-ai operand-bi opcode-exi short-immed-exi)
        )
      )
      (= maro (alu-result operand-ai operand-bi opcode-exi short-immed-exi))
      (= 
        load-flago
        (and (is-load opcode-exi) (not bubble-exi))
      )
      (= 
        store-flago
        (and (is-store opcode-exi) (not bubble-exi))
      )   
    ) ; END conjunction over all parts 
  ) ; END main expression
) ; END of step-in-MEM macro


; ------------------------------------------------------------------------------
(define-fun step-in-EX
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (REGFILEi         (Array Value Value))
    
    (inst-idi         Value              )
    (bubble-idi       Bool               )
    
    (dest-exf         Value              )  ; f = forward
    (result-exf       Value              )
    
    (dest-memf        Value              )
    (result-memf      Value              )
    
    (dest-wbf         Value              )
    (result-wbf       Value              )
      
    ; "outputs" of macro (state after the step)
    
    (bubble-exo       Bool               )
    (short-immed-exo  Value              )
    (dest-exo         Value              )
    (opcode-exo       Value              )
    (operand-ao       Value              )
    (operand-bo       Value              )
    
    ; primary inputs
    (force-stall-issue Bool              )
  )
  Bool ; return type
  ; main expression
  (
    (and ; conjunction over all parts
           
      ; update of EX stage registers
      (=
        bubble-exo
        (or
          (stall-issue force-stall-issue bubble-exi dest-exi bubble-idi inst-idi) 
          bubble-idi
          (is-J    (opcode-of inst-idi))
          (is-BEQZ (opcode-of inst-idi))
        )
      )
      (= short-immed-exo (short-immed-of inst-idi))
      (=
        dest-exo
        (ite
          (or bubble-exo (is-store (opcode-of inst-idi)))
          ZERO
          (ite
            (or
              (is-alu-immed (opcode-of inst-idi))
              (is-load      (opcode-of inst-idi))
            )
            (rf2-of inst-idi)
            (rf3-of inst-idi)
          )
        )
      )
      (= opcode-exo (opcode-of inst-idi))
      (= 
        operand-ao
        (ite ; load from REGFILE[0]? 
          (= ZERO (rf1-of inst-idi))
          ZERO
          (ite ; forward from EX?
            (= (rf1-of inst-idi) dest-exf)
            result-exf
            (ite ; forward from MEM?
              (= (rf1-of inst-idi) dest-memf)
              result-memf
              (ite ; forward from WB?
                (= (rf1-of inst-idi) dest-wbf)
                result-wbf
                (select REGFILEi (rf1-of inst-idi)) ; normal read
              )
            )
          )
        )
      )
      (=
        operand-bo
        (ite ; load immed from inst?
          (is-alu-immed (opcode-of inst-idi))
          (short-immed-of inst-idi)
          (ite ; load from REGFILE[0]?
            (= ZERO (rf2-of inst-idi))
            ZERO
            (ite ; forward from EX?
              (= (rf2-of inst-idi) dest-exf)
              result-exf
              (ite ; forward from MEM?
                (= (rf2-of inst-idi) dest-memf)
                result-memf
                (ite ; forward from WB?
                  (= (rf2-of inst-idi) dest-wbf)
                  result-wbf
                  (select REGFILEi (rf2-of inst-idi)) ; normal read
                )
              )
            )
          )
        )
      )
    ) ; END conjunction over all parts 
  ) ; END main expression
) ; END of step-in-EX macro


; ------------------------------------------------------------------------------

(define-fun step-in-ID
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (IMEMi            (Array Value Value))
    (PCi              Value              )
  
    (inst-idi         Value              )
    (bubble-idi       Bool               )
  
    (bubble-exf       Bool               )
    (dest-exf         Value              )
          
    ; "outputs" of macro (state after the step)
    (PCo              Value              )
    
    (inst-ido         Value              )
    (bubble-ido       Bool               )
      
    ; primary inputs
    (force-stall-issue Bool              )
    (stall             Bool              )
  )
  Bool ; return type
  ; main expression
  (
    (and ; conjunction over all parts
    
      ; update of ID registers
      (= 
        bubble-ido
        (ite
          force-stall-issue
          (ite
            (or (not bubble-idi) stall)
            bubble-idi
            false
          )
          (ite
            (stall-issue force-stall-issue bubble-exf dest-exf bubble-idi inst-idi)
            bubble-idi
            (ite
              stall
              true
              (branch-taken bubble-idi inst-idi operand-ao)
            )
          )
        )
      )
      (=
        inst-ido
        (ite
          force-stall-issue
          (ite
            (or (not bubble-idi) stall)
            inst-idi
            (select IMEMi PCi)
          )
          (ite
            (stall-issue force-stall-issue bubble-exf dest-exf bubble-idi inst-idi)
            inst-idi
            (ite
              stall
              inst-idi
              (select IMEMi PCi)
            )
          )
        )
      )
    
      ; update of PC
      (=
        PCo
        (ite
          force-stall-issue
          (ite
            (or (not bubble-idi) stall)
            PCi
            (PLUS FOUR PCi)
          )
          (ite
            (stall-issue force-stall-issue bubble-exf dest-exf bubble-idi inst-idi)
            PCi
            (ite
              stall
              (ite
                (branch-taken bubble-idi inst-idi operand-ao)
                (TA inst-idi PCi)
                PCi
              )
              (ite
                (branch-taken bubble-idi inst-idi operand-ao)
                (TA inst-idi PCi)
                (PLUS FOUR PCi)
              )
            )
          )
        )
      )
    ) ; END conjunction over all parts 
  ) ; END main expression
) ; END of step-in-ID macro



; ------------------------------------------------------------------------------
; One step in the pipeline architecture

(define-fun step-in-pipeline
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (REGFILEi         (Array Value Value))
    (DMEMi            (Array Value Value))
    (IMEMi            (Array Value Value))
    (PCi              Value              )
  
    (inst-idi         Value              )
    (bubble-idi       Bool               )
    
    (bubble-exi       Bool               )
    (short-immed-exi  Value              )
    (dest-exi         Value              )
    (opcode-exi       Value              )
    (operand-ai       Value              )
    (operand-bi       Value              )
    
    (dest-memi        Value              )
    (result-memi      Value              )
    (mari             Value              )
    (load-flagi       Bool               )
    (store-flagi      Bool               )
    
    (dest-wbi         Value              )
    (result-wbi       Value              )
      
    ; "outputs" of macro (state after the step)
    (REGFILEo         (Array Value Value))
    (DMEMo            (Array Value Value))
   ;(IMEMo            (Array Value Value))
    (PCo              Value              )
    
    (inst-ido         Value              )
    (bubble-ido       Bool               )
    
    (bubble-exo       Bool               )
    (short-immed-exo  Value              )
    (dest-exo         Value              )
    (opcode-exo       Value              )
    (operand-ao       Value              )
    (operand-bo       Value              )
    
    (dest-memo        Value              )
    (result-memo      Value              )
    (maro             Value              )
    (load-flago       Bool               )
    (store-flago      Bool               )
    
    (dest-wbo         Value              )
    (result-wbo       Value              )
  
    ; primary inputs
    (force-stall-issue Bool              )
    (stall             Bool              )
  )
  Bool ; return type
  ; main expression
  (
    (and ; conjunction over all parts
      
      (step-in-REGFILE
        REGFILEi
        dest-wbi
        result-wbi
        REGFILEo
      )
      
      (step-in-WB
        DMEMi      
        dest-memi  
        result-memi
        mari       
        load-flagi 
        store-flagi
        DMEMo        
        dest-wbo  
        result-wbo
      )
    
      (step-in-MEM
        inst-idi   
        bubble-idi 
        bubble-exi      
        short-immed-exi 
        dest-exi        
        opcode-exi       
        operand-ai       
        operand-bi       
        dest-wbi    
        result-wbi  
        dest-memo      
        result-memo    
        maro           
        load-flago     
        store-flago
      )
    
      (step-in-EX
        REGFILEi        
        inst-idi                       
        bubble-idi                      
        dest-exf                       
        result-exf                     
        dest-memf                      
        result-memf                    
        dest-wbf                       
        result-wbf                     
        bubble-exo                      
        short-immed-exo                
        dest-exo                       
        opcode-exo                     
        operand-ao                     
        operand-bo                     
        force-stall-issue                   
      )
      
      (step-in-ID
        IMEMi            
        PCi              
        inst-idi         
        bubble-idi       
        bubble-exf       
        dest-exf         
        PCo              
        inst-ido         
        bubble-ido       
        force-stall-issue 
        stall            
      )   
    ) ; END conjunction over all parts 
  ) ; END main expression
) ; END of step-in-pipeline macro


; ------------------------------------------------------------------------------
(define-fun complete-pipeline
( ; parameters
  
    ; "inputs" to macro (state before the step)
    (REGFILEi         (Array Value Value))
    (DMEMi            (Array Value Value))
    (IMEMi            (Array Value Value))
    (PCi              Value              )
  
    (inst-idi         Value              )
    (bubble-idi       Bool               )
    
    (bubble-exi       Bool               )
    (short-immed-exi  Value              )
    (dest-exi         Value              )
    (opcode-exi       Value              )
    (operand-ai       Value              )
    (operand-bi       Value              )
    
    (dest-memi        Value              )
    (result-memi      Value              )
    (mari             Value              )
    (load-flagi       Bool               )
    (store-flagi      Bool               )
    
    (dest-wbi         Value              )
    (result-wbi       Value              )
      
    ; "outputs" of macro (state after the step)
    (REGFILEo         (Array Value Value))
    (DMEMo            (Array Value Value))
   ;(IMEMo            (Array Value Value))
    (PCo              Value              )
    
    (inst-ido         Value              )
    (bubble-ido       Bool               )
    
    (bubble-exo       Bool               )
    (short-immed-exo  Value              )
    (dest-exo         Value              )
    (opcode-exo       Value              )
    (operand-ao       Value              )
    (operand-bo       Value              )
    
    (dest-memo        Value              )
    (result-memo      Value              )
    (maro             Value              )
    (load-flago       Bool               )
    (store-flago      Bool               )
    
    (dest-wbo         Value              )
    (result-wbo       Value              )
  
    ; primary inputs
    (force-stall-issue Bool              )
    (stall             Bool              )
  )
  Bool ; return type
  ; main expression
  (
    (and ; conjunction over all parts
    
    
    ) ; END conjunction over all parts 
  ) ; END main expression
) ; END of step-in-pipeline macro

