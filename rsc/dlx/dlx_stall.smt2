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
;    uses "*sc2" as inputs and "*sc3_" as outputs. The remaining completion
;    proceeds analogously. 
;
; *) During completion, forwarding signals from stages that are already completed
;    are set to "no forward". (This is necessary to ensure that only one instance
;    of the control signal occurs in the formula.)
;
; *) The macros for stages are named according to their "origin" stage, i.e., the
;    stage from which they read the inputs. E.g., the step-in-WB macro takes as
;    inputs the (current) values of the WB stage registers and produces outputs
;    that should be stored in the register file.


(set-logic Suraq)
; (set-logic QF_AUFLIA)
; (declare-sort Value 0)

; primary inputs
(declare-fun stall             () Bool)
(declare-fun force-stall-issue () Bool)

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
(declare-fun DMEMci2_     () (Array Value Value) :no_dependence)
(declare-fun DMEMci3_     () (Array Value Value) :no_dependence)
(declare-fun DMEMci4_     () (Array Value Value) :no_dependence)
(declare-fun DMEMci5_     () (Array Value Value) :no_dependence)
(declare-fun DMEMsc1_     () (Array Value Value) :no_dependence)
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
(declare-fun inst-idsc1_         () Value :no_dependence)

(declare-fun bubble-id           () Bool                )
(declare-fun bubble-idsc1_       () Bool  :no_dependence)

; EX stage
(declare-fun bubble-ex           () Bool                )
(declare-fun bubble-exci4_       () Bool  :no_dependence)
(declare-fun bubble-exsc1_       () Bool  :no_dependence)
(declare-fun bubble-exsc5_       () Bool  :no_dependence)

(declare-fun short-immed-ex      () Value               )
(declare-fun short-immed-exci4_  () Value :no_dependence)
(declare-fun short-immed-exsc1_  () Value :no_dependence)
(declare-fun short-immed-exsc5_  () Value :no_dependence)

(declare-fun dest-ex             () Value               )
(declare-fun dest-exci4_         () Value :no_dependence)
(declare-fun dest-exsc1_         () Value :no_dependence)
(declare-fun dest-exsc5_         () Value :no_dependence)

(declare-fun opcode-ex           () Value               )
(declare-fun opcode-exci4_       () Value :no_dependence)
(declare-fun opcode-exsc1_       () Value :no_dependence)
(declare-fun opcode-exsc5_       () Value :no_dependence)

(declare-fun operand-a           () Value                )
(declare-fun operand-aci4_       () Value  :no_dependence)
(declare-fun operand-asc1_       () Value  :no_dependence)
(declare-fun operand-asc5_       () Value  :no_dependence)

(declare-fun operand-b           () Value               )
(declare-fun operand-bci4_       () Value  :no_dependence)
(declare-fun operand-bsc1_       () Value  :no_dependence)
(declare-fun operand-bsc5_       () Value  :no_dependence)

; MEM stage
(declare-fun dest-mem        () Value               )
(declare-fun dest-memci3_    () Value :no_dependence)
(declare-fun dest-memci4_    () Value :no_dependence)
(declare-fun dest-memsc1_    () Value :no_dependence)
(declare-fun dest-memsc4_    () Value :no_dependence)
(declare-fun dest-memsc5_    () Value :no_dependence)

(declare-fun result-mem      () Value               )
(declare-fun result-memci3_  () Value :no_dependence)
(declare-fun result-memci4_  () Value :no_dependence)
(declare-fun result-memsc1_  () Value :no_dependence)
(declare-fun result-memsc4_  () Value :no_dependence)
(declare-fun result-memsc5_  () Value :no_dependence)

(declare-fun mar             () Value               )
(declare-fun marci3_         () Value :no_dependence)
(declare-fun marci4_         () Value :no_dependence)
(declare-fun marsc1_         () Value :no_dependence)
(declare-fun marsc4_         () Value :no_dependence)
(declare-fun marsc5_         () Value :no_dependence)

(declare-fun load-flag       () Bool )
(declare-fun load-flagci3_   () Bool :no_dependence)
(declare-fun load-flagci4_   () Bool :no_dependence)
(declare-fun load-flagsc1_   () Bool :no_dependence)
(declare-fun load-flagsc4_   () Bool :no_dependence)
(declare-fun load-flagsc5_   () Bool :no_dependence)

(declare-fun store-flag      () Bool )
(declare-fun store-flagci3_  () Bool :no_dependence)
(declare-fun store-flagci4_  () Bool :no_dependence)
(declare-fun store-flagsc1_  () Bool :no_dependence)
(declare-fun store-flagsc4_  () Bool :no_dependence)
(declare-fun store-flagsc5_  () Bool :no_dependence)


; WB stage
(declare-fun dest-wb         () Value               )
(declare-fun dest-wbci2_     () Value :no_dependence)
(declare-fun dest-wbci3_     () Value :no_dependence)
(declare-fun dest-wbci4_     () Value :no_dependence)
(declare-fun dest-wbsc1_     () Value :no_dependence)
(declare-fun dest-wbsc3_     () Value :no_dependence)
(declare-fun dest-wbsc4_     () Value :no_dependence)
(declare-fun dest-wbsc5_     () Value :no_dependence)

(declare-fun result-wb       () Value               )
(declare-fun result-wbci2_   () Value :no_dependence)
(declare-fun result-wbci3_   () Value :no_dependence)
(declare-fun result-wbci4_   () Value :no_dependence)
(declare-fun result-wbsc1_   () Value :no_dependence)
(declare-fun result-wbsc3_   () Value :no_dependence)
(declare-fun result-wbsc4_   () Value :no_dependence)
(declare-fun result-wbsc5_   () Value :no_dependence)


; Control signals
(declare-fun forward-a-from-ex  () Bool :no_dependence)
(declare-fun forward-a-from-mem () Bool :no_dependence)
(declare-fun forward-a-from-wb  () Bool :no_dependence)

(declare-fun forward-b-from-ex  () Bool :no_dependence)
(declare-fun forward-b-from-mem () Bool :no_dependence)
(declare-fun forward-b-from-wb  () Bool :no_dependence)

(declare-fun do-stall-issue     () Control)
 


; Declare arrays
; (and copies for ci and sc paths)

; (declare-fun REGFILE      () (Array Value Value))
; (declare-fun REGFILEci1_  () (Array Value Value) )
; (declare-fun REGFILEci2_  () (Array Value Value) )
; (declare-fun REGFILEci3_  () (Array Value Value) )
; (declare-fun REGFILEci4_  () (Array Value Value) )
; (declare-fun REGFILEci5_  () (Array Value Value) )
; (declare-fun REGFILEsc1_  () (Array Value Value) )
; (declare-fun REGFILEsc2_  () (Array Value Value) )
; (declare-fun REGFILEsc3_  () (Array Value Value) )
; (declare-fun REGFILEsc4_  () (Array Value Value) )
; (declare-fun REGFILEsc5_  () (Array Value Value) )
; 
; (declare-fun DMEM         () (Array Value Value))
; (declare-fun DMEMci2_     () (Array Value Value) )
; (declare-fun DMEMci3_     () (Array Value Value) )
; (declare-fun DMEMci4_     () (Array Value Value) )
; (declare-fun DMEMci5_     () (Array Value Value) )
; (declare-fun DMEMsc1_     () (Array Value Value) )
; (declare-fun DMEMsc3_     () (Array Value Value) )
; (declare-fun DMEMsc4_     () (Array Value Value) )
; (declare-fun DMEMsc5_     () (Array Value Value) )
; 
; (declare-fun IMEM         () (Array Value Value))  ; IMEM is never written. Thus no need for more copies.
; 
; 
; ; Declare constants
; 
; (declare-fun FOUR () Value)
; (declare-fun ZERO () Value)
; 
; 
; ; Declare single data elements
; ; (and copies for ci and sc paths)
; 
; (declare-fun PC     () Value               )  ; Program counter
; (declare-fun PCci4_ () Value )
; (declare-fun PCci5_ () Value )  
; (declare-fun PCsc1_ () Value )
; (declare-fun PCsc5_ () Value )  
;   
; 
; ; Declare uninterpreted functions of the datapath
; 
; (declare-fun PLUS              (Value Value      )   Value)
; (declare-fun ALU               (Value Value Value)   Value)
; (declare-fun rf1-of            (Value            )   Value)
; (declare-fun rf2-of            (Value            )   Value)
; (declare-fun rf3-of            (Value            )   Value)
; (declare-fun opcode-of         (Value            )   Value)
; (declare-fun short-immed-of    (Value            )   Value)
; (declare-fun long-immed-of     (Value            )   Value)
; (declare-fun alu-op-of         (Value            )   Value)
; 
; 
; ; Declare uninterpreted predicates of the datapath
; 
; (declare-fun is-load           (Value            )   Bool )
; (declare-fun is-store          (Value            )   Bool ) 
; (declare-fun is-J              (Value            )   Bool )
; (declare-fun is-BEQZ           (Value            )   Bool )
; (declare-fun is-alu-immed      (Value            )   Bool )
; 
; 
; ; Declare pipeline registers (and copies for stepping and completion)
; 
; ; ID stage
; (declare-fun inst-id             () Value               )
; (declare-fun inst-idsc1_         () Value )
; 
; (declare-fun bubble-id           () Bool                )
; (declare-fun bubble-idsc1_       () Bool  )
; 
; ; EX stage
; (declare-fun bubble-ex           () Bool                )
; (declare-fun bubble-exci4_       () Bool  )
; (declare-fun bubble-exsc1_       () Bool  )
; (declare-fun bubble-exsc5_       () Bool  )
; 
; (declare-fun short-immed-ex      () Value               )
; (declare-fun short-immed-exci4_  () Value )
; (declare-fun short-immed-exsc1_  () Value )
; (declare-fun short-immed-exsc5_  () Value )
; 
; (declare-fun dest-ex             () Value               )
; (declare-fun dest-exci4_         () Value )
; (declare-fun dest-exsc1_         () Value )
; (declare-fun dest-exsc5_         () Value )
; 
; (declare-fun opcode-ex           () Value               )
; (declare-fun opcode-exci4_       () Value )
; (declare-fun opcode-exsc1_       () Value )
; (declare-fun opcode-exsc5_       () Value )
; 
; (declare-fun operand-a           () Value                )
; (declare-fun operand-aci4_       () Value  )
; (declare-fun operand-asc1_       () Value  )
; (declare-fun operand-asc5_       () Value  )
; 
; (declare-fun operand-b           () Value               )
; (declare-fun operand-bci4_       () Value  )
; (declare-fun operand-bsc1_       () Value  )
; (declare-fun operand-bsc5_       () Value  )
; 
; ; MEM stage
; (declare-fun dest-mem        () Value               )
; (declare-fun dest-memci3_    () Value )
; (declare-fun dest-memci4_    () Value )
; (declare-fun dest-memsc1_    () Value )
; (declare-fun dest-memsc4_    () Value )
; (declare-fun dest-memsc5_    () Value )
; 
; (declare-fun result-mem      () Value               )
; (declare-fun result-memci3_  () Value )
; (declare-fun result-memci4_  () Value )
; (declare-fun result-memsc1_  () Value )
; (declare-fun result-memsc4_  () Value )
; (declare-fun result-memsc5_  () Value )
; 
; (declare-fun mar             () Value               )
; (declare-fun marci3_         () Value )
; (declare-fun marci4_         () Value )
; (declare-fun marsc1_         () Value )
; (declare-fun marsc4_         () Value )
; (declare-fun marsc5_         () Value )
; 
; (declare-fun load-flag       () Bool )
; (declare-fun load-flagci3_   () Bool )
; (declare-fun load-flagci4_   () Bool )
; (declare-fun load-flagsc1_   () Bool )
; (declare-fun load-flagsc4_   () Bool )
; (declare-fun load-flagsc5_   () Bool )
; 
; (declare-fun store-flag      () Bool )
; (declare-fun store-flagci3_  () Bool )
; (declare-fun store-flagci4_  () Bool )
; (declare-fun store-flagsc1_  () Bool )
; (declare-fun store-flagsc4_  () Bool )
; (declare-fun store-flagsc5_  () Bool )
; 
; 
; ; WB stage
; (declare-fun dest-wb         () Value               )
; (declare-fun dest-wbci2_     () Value )
; (declare-fun dest-wbci3_     () Value )
; (declare-fun dest-wbci4_     () Value )
; (declare-fun dest-wbsc1_     () Value )
; (declare-fun dest-wbsc3_     () Value )
; (declare-fun dest-wbsc4_     () Value )
; (declare-fun dest-wbsc5_     () Value )
; 
; (declare-fun result-wb       () Value               )
; (declare-fun result-wbci2_   () Value )
; (declare-fun result-wbci3_   () Value )
; (declare-fun result-wbci4_   () Value )
; (declare-fun result-wbsc1_   () Value )
; (declare-fun result-wbsc3_   () Value )
; (declare-fun result-wbsc4_   () Value )
; (declare-fun result-wbsc5_   () Value )
; 
; 
; ; Control signals
; (declare-fun forward-a-from-ex  () Bool)
; (declare-fun forward-a-from-mem () Bool)
; (declare-fun forward-a-from-wb  () Bool)
; 
; (declare-fun forward-b-from-ex  () Bool)
; (declare-fun forward-b-from-mem () Bool)
; (declare-fun forward-b-from-wb  () Bool)
; 
; (declare-fun do-stall-issue     () Bool)
 



; Properties of is-XXX predicates:
; no more than one is true
; if none of these is true, it is a three-register instruction.
(define-fun is-properties
  ( ; parameters
    (opcode Value)  
  )
  Bool ; return type of macro
  ; main expression:
  (and
    (=>
      (is-load opcode)
      (and
        (not (is-store     opcode))
        (not (is-J         opcode))
        (not (is-BEQZ      opcode))
        (not (is-alu-immed opcode))
      )  
    )
  
    (=>
      (is-store opcode)
      (and
        (not (is-load      opcode))
        (not (is-J         opcode))
        (not (is-BEQZ      opcode))
        (not (is-alu-immed opcode))
      )  
    )
    
    (=>
      (is-J opcode)
      (and
        (not (is-load      opcode))
        (not (is-store     opcode))
        (not (is-BEQZ      opcode))
        (not (is-alu-immed opcode))
      )  
    )
  
    (=>
      (is-BEQZ opcode)
      (and
        (not (is-load      opcode))
        (not (is-store     opcode))       
        (not (is-J         opcode))
        (not (is-alu-immed opcode))
      )  
    )
    
    (=>
      (is-alu-immed opcode)
      (and
        (not (is-load      opcode))
        (not (is-store     opcode))       
        (not (is-J         opcode))
        (not (is-BEQZ      opcode))
      )  
    ) 
  )
)




; Equivalence Criterion:
; The programmer-visible state of the processor is the REGFILE, the DMEM and
; the PC.
; They must be equal after going along the ci and the sc branch.

(define-fun equivalence 
  ( ; parameters
    (REGFILEci (Array Value Value))
    (REGFILEsc (Array Value Value))
    (DMEMci    (Array Value Value))
    (DMEMsc    (Array Value Value))
    (PCci      Value              )
    (PCsc      Value              )
  )
  Bool ; return type of macro
  ; main expression: 
  ( and
     (= REGFILEci REGFILEsc)
     (= DMEMci    DMEMsc   )
     (= PCci      PCsc     )
  )
)


; Helper Macros (to shorten main parts of formula)

; (define-fun rf1data
;   ( ; parameters
;     (REGFILE (Array Value Value))
;     (IMEM    (Array Value Value))
;     (PC      Value              )
;   )
;   Value ; return type of macro
;   ; main expression:
;   (ite
;     (= ZERO (rf1-of (select IMEM PC)))
;     ZERO
;     (select REGFILE (rf1-of (select IMEM PC)))
;   )
; ) 
; 
; (define-fun rf2data
;   ( ; parameters
;     (REGFILE (Array Value Value))
;     (IMEM    (Array Value Value))
;     (PC      Value              )
;   )
;   Value ; return type of macro
;   ; main expression:
;   (ite
;     (= ZERO (rf2-of (select IMEM PC)))
;     ZERO
;     (select REGFILE (rf2-of (select IMEM PC)))
;   )
; ) 

; (define-fun alu-result
;   ( ; parameters
;     (operand-a    Value)
;     (operand-b    Value)
;     (opcode       Value)
;     (short-immed  Value)
;   )
;   Value ; return type of macro
;   ; main expression:
;   (ite
;     (or
;       (is-load  opcode)
;       (is-store opcode)
;     )
;     (PLUS short-immed operand-a)
;     (ALU (alu-op-of opcode) operand-a operand-b)
;   )
; ) 

(define-fun stall-issue
  ( ; parameters
    (force-stall-issue  Bool )
    (bubble-ex          Bool )
    (opcode-ex          Value)
    (dest-ex            Value)
    (bubble-id          Bool )
    (inst-id            Value)
  )
  Bool ; return type of macro
  ; main expression
  (or
    force-stall-issue
    (and
      (or
        (= (rf1-of inst-id) dest-ex)
        (= (rf2-of inst-id) dest-ex)
      )
      (is-load opcode-ex)
      (not bubble-ex)
      (not bubble-id)
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
  (and
    (not bubble-id)
    (or
      (is-J (opcode-of inst-id))
      (and
        (is-BEQZ (opcode-of inst-id))
        (= ZERO operand-an)
      )
    )
  )
)

; (define-fun TA
;   ( ; parameters
;     (inst-id Value)
;     (PC      Value)
;   )
;   Value ; return type of macro
;   ; main expression
;   (ite
;     (is-J (opcode-of inst-id))
;     (PLUS PC (long-immed-of  inst-id))
;     (PLUS PC (short-immed-of inst-id))
;   )
; )

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
  (and  ; conjunction over all parts of update expression 
    
    ; IMEM is never written
    ; (= IMEMo IMEMi)
  
    ; update of PC
    
    (ite 
      (is-J (opcode-of (select IMEMi PCi)))
      (= 
        PCo 
        (PLUS
          (PLUS PCi FOUR)
          (long-immed-of (select IMEMi PCi)) 
        )
      ) 
      (ite
        (and
          (is-BEQZ (opcode-of (select IMEMi PCi)))
          (ite
            (= ZERO (rf1-of (select IMEMi PCi)))
            (= ZERO ZERO)
            (= ZERO (select REGFILEi (rf1-of (select IMEMi PCi))))
          )
        )
        (=
          PCo
          (PLUS
            (PLUS PCi FOUR)
            (short-immed-of (select IMEMi PCi)) 
          )
        )
        (=
          PCo
          (PLUS PCi FOUR)
        )
      )
    )  
  
    ; update of DMEM
    (ite
      (is-store (opcode-of (select IMEMi PCi))) ; write-enable
;       (= 
;         DMEMo
;         (store
;           DMEMi
;           (PLUS
;             (short-immed-of (select IMEMi PCi))
;             (ite
;               (= ZERO (rf1-of (select IMEM PCi)))
;               ZERO
;               (select REGFILEi (rf1-of (select IMEMi PCi)))
;             )
;           )
;           (ite
;             (= ZERO (rf2-of (select IMEMi PCi)))
;             ZERO
;             (select REGFILEi (rf2-of (select IMEMi PCi)))
;           )
;         )
;       )
      (ite 
        (= ZERO (rf1-of (select IMEM PCi)))
        (ite
          (= ZERO (rf2-of (select IMEMi PCi)))
          (=
            DMEMo
            (store
              DMEMi
              (PLUS
                (short-immed-of (select IMEMi PCi))
                ZERO
              )
              ZERO
            )
          )
          (=
            DMEMo
            (store
              DMEMi
              (PLUS
                (short-immed-of (select IMEMi PCi))
                ZERO
              )
              (select REGFILEi (rf2-of (select IMEMi PCi)))
            )
          )
        )
        (ite
          (= ZERO (rf2-of (select IMEMi PCi)))
          (=
            DMEMo
            (store
              DMEMi
              (PLUS
                (short-immed-of (select IMEMi PCi))
                (select REGFILEi (rf1-of (select IMEMi PCi)))
              )
              ZERO
            )
          )
          (=
            DMEMo
            (store
              DMEMi
              (PLUS
                (short-immed-of (select IMEMi PCi))
                (select REGFILEi (rf1-of (select IMEMi PCi)))
              )
              (select REGFILEi (rf2-of (select IMEMi PCi)))
            )
          )
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
      (ite 
        (and
          (not (is-load       (opcode-of (select IMEMi PCi))))
          (not (is-store      (opcode-of (select IMEMi PCi))))
          (not (is-J          (opcode-of (select IMEMi PCi))))
          (not (is-BEQZ       (opcode-of (select IMEMi PCi))))
          (not (is-alu-immed  (opcode-of (select IMEMi PCi))))
        )
        (ite ; 3 register op
          (= ZERO (rf1-of (select IMEM PC)))
          (ite
            (= ZERO (rf2-of (select IMEM PC)))
            (= 
              REGFILEo
              (store
                REGFILEi
                (rf3-of (select IMEMi PCi))
                (ALU
                  (alu-op-of (opcode-of (select IMEMi PCi)))
                  ZERO
                  ZERO
                ) 
              )
            )
            (= 
              REGFILEo
              (store
                REGFILEi
                (rf3-of (select IMEMi PCi))
                (ALU
                  (alu-op-of (opcode-of (select IMEMi PCi)))
                  ZERO
                  (select REGFILEi (rf2-of (select IMEMi PCi)))
                ) 
              )
            )
          )
          (ite
            (= ZERO (rf2-of (select IMEMi PCi)))
            (= 
              REGFILEo
              (store
                REGFILEi
                (rf3-of (select IMEMi PCi))
                (ALU
                  (alu-op-of (opcode-of (select IMEMi PCi)))
                  (select REGFILEi (rf1-of (select IMEMi PCi)))
                  ZERO
                ) 
              )
            )
            (= 
              REGFILEo
              (store
                REGFILEi
                (rf3-of (select IMEMi PCi))
                (ALU
                  (alu-op-of (opcode-of (select IMEMi PCi)))
                  (select REGFILEi (rf1-of (select IMEMi PCi)))
                  (select REGFILEi (rf2-of (select IMEMi PCi)))
                ) 
              )
            )
          )
        ) ; end 3 register op
        (ite
          (is-load (opcode-of (select IMEMi PCi)))
          (ite ; is-load
            (= ZERO (rf1-of (select IMEMi PCi)))
            (ite
              (= ZERO (rf2-of (select IMEMi PCi)))
              (=
                REGFILEo
                REGFILEi
              )
              (=
                REGFILEo
                (store
                  REGFILEi
                  (rf2-of (select IMEMi PCi))
                  (select
                    DMEMi 
                    (PLUS
                      (short-immed-of (select IMEMi PCi))
                      ZERO
                    )
                  )
                )
              )
            )
            (ite
              (= ZERO (rf2-of (select IMEMi PCi)))
              (=
                REGFILEo
                REGFILEi
              )
              (=
                REGFILEo
                (store
                  REGFILEi
                  (rf2-of (select IMEMi PCi))
                  (select
                    DMEMi 
                    (PLUS
                      (short-immed-of (select IMEMi PCi))
                      (select REGFILEi (rf1-of (select IMEMi PCi)))
                    )
                  )
                )
              )
            )
          ) ; end is-load
          (ite
            (is-alu-immed (opcode-of (select IMEMi PCi)))
            (ite ; is-alu-immed
              (= ZERO (rf2-of (select IMEMi PCi)))
              (=
                REGFILEo
                REGFILEi
              )
              (ite
                (= ZERO (rf1-of (select IMEMi PCi)))
                (=
                  REGFILEo
                  (store
                    REGFILEi
                    (rf2-of (select IMEMi PCi))
                    (ALU
                      (alu-op-of (opcode-of (select IMEMi PCi)))
                      ZERO
                      (short-immed-of (select IMEMi PCi))
                    )
                  )
                ) 
                (=
                  REGFILEo
                  (store
                    REGFILEi
                    (rf2-of (select IMEMi PCi))
                    (ALU
                      (alu-op-of (opcode-of (select IMEMi PCi)))
                      (select REGFILEi (rf1-of (select IMEMi PCi)))
                      (short-immed-of (select IMEMi PCi))
                    )
                  )
                ) 
              )
            ) ; end is-alu-immed
            (=
              REGFILEo
              REGFILEi
            )
          )
        )
      )
      (= ; no write enable
        REGFILEo
        REGFILEi
      )
    )
  ) ; END main expression
) ; END instruction-in-reference macro


; ##############################################################################
; ##############################################################################
; ##############################################################################
; ##############################################################################
; ##############################################################################
; ##############################################################################
; ------------------------------------------------------------------------------
; Macros for each stage of the pipeline.

(define-fun step-in-WB
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
  (ite ; update of REGFILE
    (distinct ZERO dest-wbi) ; write-enable
    (=
      REGFILEo
      (store REGFILEi dest-wbi result-wbi)
    )
    (= REGFILEo REGFILEi) ; write-enable == False  
  ) ; END main expression
) ; END of step-in-WB macro


; ------------------------------------------------------------------------------
(define-fun step-in-MEM
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
    
    (ite 
      store-flagi
      (= dest-wbo ZERO)
      (= dest-wbo dest-memi)
    )
    
    (ite
      load-flagi
      (= result-wbo (select DMEMi mari))
      (= result-wbo result-memi)
    )
  ) ; END main expression
) ; END of step-in-MEM macro


; ------------------------------------------------------------------------------
(define-fun step-in-EX
  ( ; parameters
  
    ; "inputs" to macro (state before the step)   
    (bubble-exi       Bool               )
    (short-immed-exi  Value              )
    (dest-exi         Value              )
    (opcode-exi       Value              )
    (operand-ai       Value              )
    (operand-bi       Value              )
          
    ; "outputs" of macro (state after the step)
    (dest-memo        Value              )
    (result-memo      Value              )
    (maro             Value              )
    (load-flago       Bool               )
    (store-flago      Bool               )
  )
  Bool ; return type
  ; main expression
  (and ; conjunction over all parts
      
    ; update of MEM stage registers
    (ite
      (or
        bubble-exi
        (is-store opcode-exi)
      )
      (= dest-memo ZERO)
      (= dest-memo dest-exi)
    )
    
    (ite
      (or (is-load opcode-exi) (is-store opcode-exi))
      (= result-memo operand-bi) 
      (ite
        (or
          (is-load  opcode-exi)
          (is-store opcode-exi)
        )
        (= result-memo (PLUS short-immed-exi operand-ai))
        (= result-memo (ALU (alu-op-of opcode-exi) operand-ai operand-bi))
      )
    )
    
    (ite
      (or
        (is-load  opcode-exi)
        (is-store opcode-exi)
      )
      (= maro (PLUS short-immed-exi operand-ai))
      (= maro (ALU (alu-op-of opcode-exi) operand-ai operand-bi))
    )
    
    (= 
      load-flago
      (and (is-load opcode-exi) (not bubble-exi))
    )
    (= 
      store-flago
      (and (is-store opcode-exi) (not bubble-exi))
    )    
  ) ; END main expression
) ; END of step-in-EX macro


; ------------------------------------------------------------------------------
(define-fun step-in-ID
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (REGFILEi         (Array Value Value))
    
    (inst-idi         Value              )
    (bubble-idi       Bool               )
    
    (bubble-exf       Bool               )  ; f = forward
    (opcode-exf       Value              )
    (dest-exf         Value              )
    
    ;(result-exf       Value              )
    (operand-af       Value)
    (operand-bf       Value)
    (short-immed-exf  Value)
    
    ;(dest-memf        Value              )
    (store-flagf      Bool)
    (dest-memf        Value)
  
    ;(result-memf      Value              )
    (load-flagf       Bool)
    (DMEMf            (Array Value Value))
    (marf             Value)
    (result-memf      Value)
    
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
    
    ; auxiliary signal
    (completion        Bool            )
  )
  Bool ; return type
  ; main expression
  (and ; conjunction over all parts        
      
    ; update of EX stage registers
    (=
      bubble-exo
      (or
        do-stall-issue ; (stall-issue force-stall-issue bubble-exf opcode-exf dest-exf bubble-idi inst-idi) 
        bubble-idi
        (is-J    (opcode-of inst-idi))
        (is-BEQZ (opcode-of inst-idi))
      )
    )
    (= short-immed-exo (short-immed-of inst-idi))
    
    (ite
      (or bubble-exo (is-store (opcode-of inst-idi)))
      (= dest-exo ZERO)
      (ite
        (or
          (is-alu-immed (opcode-of inst-idi))
          (is-load      (opcode-of inst-idi))
        )
        (= dest-exo (rf2-of inst-idi))
        (= dest-exo (rf3-of inst-idi))
      )
    )
    
    (= opcode-exo (opcode-of inst-idi))
    
    (ite ; load from REGFILE[0]? 
      (= ZERO (rf1-of inst-idi))
      (= operand-ao ZERO)
      (ite 
        completion 
        (= operand-ao (select REGFILEi (rf1-of inst-idi))) ; normal read during completion
        (ite ; forward from EX?
          forward-a-from-ex
          (ite
            (or (is-load opcode-exf) (is-store opcode-exf))
            (= operand-ao (PLUS operand-af short-immed-exf))
            (ite
              (or
                (is-load  opcode-exf)
                (is-store opcode-exf)
              )
              (= operand-ao (PLUS short-immed-exf operand-af))
              (= operand-ao (ALU (alu-op-of opcode-exf) operand-af operand-bf))
            )
          )
          (ite ; forward from MEM?
            forward-a-from-mem ; (= (rf1-of inst-idi) dest-memf)
            (ite
              load-flagf
              (= operand-ao (select DMEMf marf))
              (= operand-ao result-memf)
            )
            (ite ; forward from WB?
              forward-a-from-wb ; (= (rf1-of inst-idi) dest-wbf)
              (= operand-ao result-wbf)
              (= operand-ao (select REGFILEi (rf1-of inst-idi))) ; normal read
            )
          )
        )
      )
    )
    
    (ite ; load immed from inst?
      (is-alu-immed (opcode-of inst-idi))
      (= operand-bo (short-immed-of inst-idi))
      (ite ; load from REGFILE[0]?
        (= ZERO (rf2-of inst-idi))
        (= operand-bo ZERO)
        (ite 
          completion 
          (= operand-bo (select REGFILEi (rf2-of inst-idi))) ; normal read during completion
          (ite ; forward from EX?
            forward-b-from-ex
            (ite
              (or (is-load opcode-exf) (is-store opcode-exf))
              (= operand-bo (PLUS operand-af short-immed-exf))
              (ite
                (or
                  (is-load  opcode-exf)
                  (is-store opcode-exf)
                )
                (= operand-bo (PLUS short-immed-exf operand-af))
                (= operand-bo (ALU (alu-op-of opcode-exf) operand-af operand-bf))
              )
            ) 
            (ite ; forward from MEM?
              forward-b-from-mem ; (= (rf2-of inst-idi) dest-memf)
              (ite
                load-flagf
                (= operand-bo (select DMEMf marf))
                (= operand-bo result-memf)
              )
              (ite ; forward from WB?
                forward-b-from-wb ; (= (rf2-of inst-idi) dest-wbf)
                (= operand-bo result-wbf)
                (= operand-bo (select REGFILEi (rf2-of inst-idi))) ; normal read
              )
            )
          )
        )
      )
    )
 
  ) ; END main expression
) ; END of step-in-ID macro


; ------------------------------------------------------------------------------

(define-fun step-in-IF ; necessary for "step" only; not neeeded for completion.
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (IMEMi            (Array Value Value))
    (PCi              Value              )
  
    (inst-idf         Value              )
    (bubble-idf       Bool               )
  
    (bubble-exf       Bool               )
    (opcode-exf       Value              )
    (dest-exf         Value              )
    
    (operand-af       Value              )  ; the value at the *input* (not the output!!) of operand-a register
          
    ; "outputs" of macro (state after the step)
    (inst-ido         Value              )
    (bubble-ido       Bool               )
      
    ; primary inputs
    (force-stall-issue Bool              )
    (stall             Bool              )
  )
  Bool ; return type
  ; main expression
  (and ; conjunction over all parts
  
    ; update of ID registers
    (ite
      force-stall-issue
      (ite
        (or (not bubble-idf) stall)
        (= bubble-ido bubble-idf)
        (= bubble-ido false)
      )
      (ite
        do-stall-issue ; (stall-issue force-stall-issue bubble-exf opcode-exf dest-exf bubble-idf inst-idf)
        (= bubble-ido bubble-idf)
        (ite
          stall
          (= bubble-ido true)
          (= bubble-ido (branch-taken bubble-idf inst-idf operand-af))
        )
      )
    )
    
    (ite
      force-stall-issue
      (ite
        (or (not bubble-idf) stall)
        (= inst-ido inst-idf)
        (= inst-ido (select IMEMi PCi))
      )
      (ite
        do-stall-issue ; (stall-issue force-stall-issue bubble-exf opcode-exf dest-exf bubble-idf inst-idf)
        (= inst-ido inst-idf)
        (ite
          stall
          (= inst-ido inst-idf)
          (= inst-ido (select IMEMi PCi))
        )
      )
    )
    
  ) ; END main expression
) ; END of step-in-IF macro

;-------------------------------------------------------------------------------

(define-fun step-PC ; steps the program counter
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (PCi              Value              )
  
    (inst-idf         Value              )
    (bubble-idf       Bool               )
  
    (bubble-exf       Bool               )
    (opcode-exf       Value              )
    (dest-exf         Value              )
    
    (operand-af       Value              )  ; the value at the *input* (not the output!!) of operand-a register
          
    ; "outputs" of macro (state after the step)
    (PCo              Value              )
      
    ; primary inputs
    (force-stall-issue Bool              )
    (stall             Bool              )
  
    ; auxiliary input indicating that the macro is used for completion and 
    ; thus only jumps and branches should be done (no increment)
    (completion        Bool              )
  )
  Bool ; return type
  ; main expression
  (ite ; update of PC
    completion
    (ite
      (branch-taken bubble-idf inst-idf operand-af)
      (ite
        (is-J (opcode-of inst-idf))
        (= PCo (PLUS PCi (long-immed-of  inst-idf)))
        (= PCo (PLUS PCi (short-immed-of inst-idf)))
      )
      (= PCo PCi)
    )
    (ite
      force-stall-issue
      (ite
        (or (not bubble-idf) stall)
        (= PCo PCi)
        (= PCo (PLUS PCi FOUR))
      )
      (ite
        do-stall-issue ; (stall-issue force-stall-issue bubble-exf opcode-exf dest-exf bubble-idf inst-idf)
        (= PCo PCi)
        (ite
          stall
          (ite
            (branch-taken bubble-idf inst-idf operand-af)
            (ite
              (is-J (opcode-of inst-idf))
              (= PCo (PLUS PCi (long-immed-of  inst-idf)))
              (= PCo (PLUS PCi (short-immed-of inst-idf)))
            )
            (= PCo PCi)
          )
          (ite
            (branch-taken bubble-idf inst-idf operand-af)
            (ite
              (is-J (opcode-of inst-idf))
              (= PCo (PLUS PCi (long-immed-of  inst-idf)))
              (= PCo (PLUS PCi (short-immed-of inst-idf)))
            )
            (= PCo (PLUS PCi FOUR))
          )
        )
      )
    )
  ) ; END main expression
) ; END of step-PC macro


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
  (and ; conjunction over all parts
    
    (step-in-WB
      REGFILEi
      dest-wbi
      result-wbi
      REGFILEo
    )
    
    (step-in-MEM
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
  
    (step-in-EX 
      bubble-exi      
      short-immed-exi 
      dest-exi        
      opcode-exi       
      operand-ai       
      operand-bi         
      dest-memo      
      result-memo    
      maro           
      load-flago     
      store-flago
    )
  
    (step-in-ID
      REGFILEi        
      inst-idi                       
      bubble-idi
      bubble-exi ; forwarded value
      opcode-exi ; forwarded value                      
      dest-exi ; forwarded value
      ; BEGIN result-exi params (only the ones which are not yet listed anyway)
      operand-ai
      operand-bi
      short-immed-exi
      ; END result-exi params                       
;       (ite
;         (or (is-load opcode-exi) (is-store opcode-exi))
;         (PLUS operand-ai short-immed-exi)
;         (alu-result operand-ai operand-bi opcode-exi short-immed-exi)
;       ) ;result-exi ; forwarded value
      ; BEGIN dest-memi params (only the ones which are not yet listed anyway)
      store-flagi
      dest-memi
      ; END dest-memi params                      
;       (ite
;         store-flagi
;         ZERO
;         dest-memi 
;       ) ; dest-memi ; forwarded value
      ; BEGIN result-memi params (only the ones which are not yet listed anyway)
      load-flagi
      DMEMi
      mari
      result-memi
      ; END result-memi params
;       (ite
;         load-flagi
;         (select DMEMi mari)
;         result-memi                      
;       );result-memi ; forwarded value                    
      dest-wbi ; forwarded value                       
      result-wbi ; forwarded value                     
      bubble-exo                      
      short-immed-exo                
      dest-exo                       
      opcode-exo                     
      operand-ao                     
      operand-bo                     
      force-stall-issue     
      false ; completion              
    )
    
    (step-in-IF
      IMEMi            
      PCi              
      inst-idi         
      bubble-idi       
      bubble-exi
      opcode-exi        
      dest-exi
      operand-ao ; the value at the *input* (not the output!!) of operand-a register         
                 ; i.e., the new value for operand-a, as it is outputted by this macro.
                 ; (therefore: operand-ao              
      inst-ido         
      bubble-ido       
      force-stall-issue 
      stall            
    )    
    
    (step-PC
      PCi
      inst-idi
      bubble-idi
      bubble-exi
      opcode-exi
      dest-exi
      operand-ao ; the value at the *input* (not the output!!) of operand-a register         
                 ; i.e., the new value for operand-a, as it is outputted by this macro.
                 ; (therefore: operand-ao              
      PCo
      force-stall-issue
      stall
      
      false ; completion 
    )
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
    (PCo              Value            )
   ;(IMEMo            (Array Value Value))
    
     
     
    ; intermediate ("transient") values
    (REGFILEt1_       (Array Value Value))
    (REGFILEt2_       (Array Value Value))
    (REGFILEt3_       (Array Value Value))
    
    (DMEMt2_          (Array Value Value))
    (DMEMt3_          (Array Value Value))
    
    (bubble-ext4_     Bool               )
    
    (short-immed-ext4_ Value             )
    
    (dest-ext4_       Value              )
     
    (opcode-ext4_     Value              )
    
    (operand-at4_     Value              )
     
    (operand-bt4_     Value              )
     
    (dest-memt3_      Value              )
    (dest-memt4_      Value              )
  
    (result-memt3_    Value              )
    (result-memt4_    Value              )
    
    (mart3_           Value              )
    (mart4_           Value              )
    
    (load-flagt3_     Bool               )
    (load-flagt4_     Bool               )
    
    (store-flagt3_    Bool               )
    (store-flagt4_    Bool               )
  
    (dest-wbt2_       Value              )
    (dest-wbt3_       Value              )
    (dest-wbt4_       Value              )
  
    (result-wbt2_     Value              )
    (result-wbt3_     Value              )
    (result-wbt4_     Value              )
  
    
    ; primary inputs
    (force-stall-issue Bool              )
    (stall             Bool              )
  )
  Bool ; return type
  ; main expression
  (and ; conjunction over all parts
    
    ; "Clearing" WB registers
    (step-in-WB
      REGFILEi
      dest-wbi
      result-wbi
      REGFILEt1_
    )
    ; ----------------------------------
    ; "Clearing" MEM registers
    (step-in-MEM
      DMEMi      
      dest-memi  
      result-memi
      mari       
      load-flagi 
      store-flagi
      DMEMt2_        
      dest-wbt2_  
      result-wbt2_
    )
  
    (step-in-WB
      REGFILEt1_
      dest-wbt2_
      result-wbt2_
      REGFILEt2_
    )
    ; ----------------------------------
    ; "Clearing" EX registers
    (step-in-EX 
      bubble-exi      
      short-immed-exi 
      dest-exi        
      opcode-exi       
      operand-ai       
      operand-bi         
      dest-memt3_      
      result-memt3_    
      mart3_           
      load-flagt3_     
      store-flagt3_
    ) 
    
    (step-in-MEM
      DMEMt2_      
      dest-memt3_  
      result-memt3_
      mart3_       
      load-flagt3_ 
      store-flagt3_
      DMEMt3_        
      dest-wbt3_  
      result-wbt3_
    )
  
    (step-in-WB
      REGFILEt2_
      dest-wbt3_
      result-wbt3_
      REGFILEt3_
    )
    
    ; ----------------------------------
    ; "Clearing" ID registers
    (step-in-ID
      REGFILEt3_        
      inst-idi                       
      bubble-idi
      true ; bubble-exi ; forwarded value                      
      ZERO ; opcode-exi; forwarded value (arbitrary, as bubble-ex is set to true)
      ZERO ; dest-exi ; forwarded value ("invalid" address)
      operand-ai
      operand-bi
      short-immed-exi                       
      ;ZERO ; result-exi ; forwarded value (arbitrary, as bubble-ex is set to true)
      store-flagi                    
      ZERO ; dest-memi ; forwarded value  
      ;ZERO ;result-memi ; forwarded value (arbitrary, as dest-mem is ZERO)
      load-flagi
      DMEMi
      mari
      ZERO                  
      ZERO ; dest-wbi ; forwarded value                       
      ZERO ; result-wbi ; forwarded value (arbitrary, as dest-wb is ZERO)                     
      bubble-ext4_                      
      short-immed-ext4_                
      dest-ext4_                       
      opcode-ext4_                     
      operand-at4_                     
      operand-bt4_                     
      force-stall-issue          
      true ; completion         
    )
  
    (step-in-EX 
      bubble-ext4_      
      short-immed-ext4_ 
      dest-ext4_        
      opcode-ext4_       
      operand-at4_       
      operand-bt4_         
      dest-memt4_      
      result-memt4_    
      mart4_           
      load-flagt4_     
      store-flagt4_
    ) 
    
    (step-in-MEM
      DMEMt3_      
      dest-memt4_  
      result-memt4_
      mart4_       
      load-flagt4_ 
      store-flagt4_
      DMEMo        
      dest-wbt4_  
      result-wbt4_
    )
  
    (step-in-WB
      REGFILEt3_
      dest-wbt4_
      result-wbt4_
      REGFILEo
    ) 
    
    ; ----------------------------------
    ; Updating program counter
    (step-PC
      PCi
      inst-idi
      bubble-idi
      true ; bubble-exi
      ZERO ; opcode-exi ; arbitrary since bubble-ex 
      ZERO ; dest-exi
      operand-at4_ ; The new value that operand-a register would have received
                   ; if this were a normal step (= the one that results from
                   ; clearing the ID stage)
      PCo
      false ;force-stall-issue
      false ;stall 
      
      true ; completion   
    )
    
  ) ; END main expression
) ; END of complete-pipeline macro

; ##############################################################################
; ##############################################################################
; ##############################################################################
; ##############################################################################
; ##############################################################################
; ##############################################################################
; ------------------------------------------------------------------------------
; MAIN FORMULA
; putting everything together
(define-fun main-formula
  ( ; paramters
    ; "p" (for parameter) is prepended to all names to avoid name clashes  
    ; between "local" and "global" variabels
    
    (pstall         Bool)
    (pforce-stall-issue Bool)
    
    (pREGFILE       (Array Value Value))
    (pREGFILEci1_   (Array Value Value))
    (pREGFILEci2_   (Array Value Value))
    (pREGFILEci3_   (Array Value Value))
    (pREGFILEci4_   (Array Value Value))
    (pREGFILEci5_   (Array Value Value))
    (pREGFILEsc1_   (Array Value Value))
    (pREGFILEsc2_   (Array Value Value))
    (pREGFILEsc3_   (Array Value Value))
    (pREGFILEsc4_   (Array Value Value))
    (pREGFILEsc5_   (Array Value Value))
    
    (pDMEM          (Array Value Value))
    (pDMEMci2_      (Array Value Value))
    (pDMEMci3_      (Array Value Value))
    (pDMEMci4_      (Array Value Value))
    (pDMEMci5_      (Array Value Value))
    (pDMEMsc1_      (Array Value Value))
    (pDMEMsc3_      (Array Value Value))
    (pDMEMsc4_      (Array Value Value))
    (pDMEMsc5_      (Array Value Value))
    
    (pIMEM          (Array Value Value))  
    
    (pPC      Value               )  
    (pPCci4_  Value)  
    (pPCci5_  Value)
    (pPCsc1_  Value)
    (pPCsc5_  Value)  
    
    (pinst-id              Value               )
    (pinst-idsc1_          Value)
    
    (pbubble-id            Bool )
    (pbubble-idsc1_        Bool )
    
    (pbubble-ex            Bool                )
    (pbubble-exci4_        Bool )
    (pbubble-exsc1_        Bool )
    (pbubble-exsc5_        Bool )
    
    (pshort-immed-ex       Value               )
    (pshort-immed-exci4_   Value)
    (pshort-immed-exsc1_   Value)
    (pshort-immed-exsc5_   Value)
    
    (pdest-ex              Value               )
    (pdest-exci4_          Value)
    (pdest-exsc1_          Value)
    (pdest-exsc5_          Value)
    
    (popcode-ex            Value               )
    (popcode-exci4_        Value)
    (popcode-exsc1_        Value)
    (popcode-exsc5_        Value)
    
    (poperand-a            Value               )
    (poperand-aci4_        Value )
    (poperand-asc1_        Value )
    (poperand-asc5_        Value )
    
    (poperand-b            Value               )
    (poperand-bci4_        Value )
    (poperand-bsc1_        Value )
    (poperand-bsc5_        Value )
    
    (pdest-mem         Value)
    (pdest-memci3_     Value)
    (pdest-memci4_     Value)
    (pdest-memsc1_     Value)
    (pdest-memsc4_     Value)
    (pdest-memsc5_     Value)
    
    (presult-mem       Value)
    (presult-memci3_   Value)
    (presult-memci4_   Value)
    (presult-memsc1_   Value)
    (presult-memsc4_   Value)
    (presult-memsc5_   Value)
    
    (pmar              Value)
    (pmarci3_          Value)
    (pmarci4_          Value)
    (pmarsc1_          Value)
    (pmarsc4_          Value)
    (pmarsc5_          Value)
    
    (pload-flag        Bool )
    (pload-flagci3_    Bool )
    (pload-flagci4_    Bool )
    (pload-flagsc1_    Bool )
    (pload-flagsc4_    Bool )
    (pload-flagsc5_    Bool )
    
    (pstore-flag       Bool )
    (pstore-flagci3_   Bool )
    (pstore-flagci4_   Bool )
    (pstore-flagsc1_   Bool )
    (pstore-flagsc4_   Bool )
    (pstore-flagsc5_   Bool )
    
    (pdest-wb          Value)
    (pdest-wbci2_      Value)
    (pdest-wbci3_      Value)
    (pdest-wbci4_      Value)
    (pdest-wbsc1_      Value)
    (pdest-wbsc3_      Value)
    (pdest-wbsc4_      Value)
    (pdest-wbsc5_      Value)
    
    (presult-wb        Value)
    (presult-wbci2_    Value)
    (presult-wbci3_    Value)
    (presult-wbci4_    Value)
    (presult-wbsc1_    Value)
    (presult-wbsc3_    Value)
    (presult-wbsc4_    Value)
    (presult-wbsc5_    Value)  
  )
  Bool ; return type of macro
  ; main expression:
  (=> ; properties imply
    (and
      (is-properties (opcode-of (select pIMEM pPCci4_)))
      (is-properties popcode-ex)
      (is-properties popcode-exsc1_)
      (is-properties (opcode-of pinst-id))
      (is-properties (opcode-of pinst-idsc1_))
      (is-properties popcode-exsc5_)
      (is-properties popcode-exci4_)
      ;-------------------------------------------------------------------------------
      ; "implementation" of control signals
      

      ;-------------------------------------------------------------------------------
      ; forward-a-from-ex
      (=
        forward-a-from-ex
        (and
          (= (rf1-of inst-id) dest-ex)
          (not bubble-ex)
          (not (is-store opcode-ex))
        )
      )

      ;-------------------------------------------------------------------------------
      ; forward-a-from-mem
      (=
        forward-a-from-mem
        (and
          (= (rf1-of inst-id) dest-mem)
          (not store-flag)
        )
      )
      
      ;-------------------------------------------------------------------------------
      ; forward-a-from-wb
      (=
        forward-a-from-wb
        (= (rf1-of inst-id) dest-wb)
      )

      ;-------------------------------------------------------------------------------
      ; forward-b-from-ex
      (=
        forward-b-from-ex
        (and
          (= (rf2-of inst-id) dest-ex)
          (not bubble-ex)
          (not (is-store opcode-ex))
        )
      )
      
      ;-------------------------------------------------------------------------------
      ; forward-b-from-mem
      (=
        forward-b-from-mem
        (and
          (= (rf2-of inst-id) dest-mem)
          (not store-flag)
        )
      )
      
      ;-------------------------------------------------------------------------------
      ; forward-b-from-wb
      (=
        forward-b-from-wb
        (= (rf2-of inst-id) dest-wb)
      )
    
    )
    (=> ; update implies
      (and ; main update part
        (complete-pipeline
          ; "inputs" to macro (state before the step)
          pREGFILE
          pDMEM   
          pIMEM   
          pPC     
        
          pinst-id
          pbubble-id
          
          pbubble-ex
          pshort-immed-ex
          pdest-ex
          popcode-ex
          poperand-a
          poperand-b
          
          pdest-mem
          presult-mem
          pmar
          pload-flag
          pstore-flag
          
          pdest-wb
          presult-wb
            
          ; "outputs" of macro (state after the step)
          pREGFILEci4_
          pDMEMci4_
          pPCci4_
           
          ; intermediate ("transient") values
          REGFILEci1_ 
          REGFILEci2_ 
          REGFILEci3_ 
          
          pDMEMci2_ 
          pDMEMci3_ 
          
          pbubble-exci4_
          
          pshort-immed-exci4_
          
          pdest-exci4_
           
          popcode-exci4_
          
          poperand-aci4_
           
          poperand-bci4_
           
          pdest-memci3_
          pdest-memci4_ 
        
          presult-memci3_
          presult-memci4_
          
          pmarci3_
          pmarci4_
          
          pload-flagci3_
          pload-flagci4_
          
          pstore-flagci3_
          pstore-flagci4_
        
          pdest-wbci2_
          pdest-wbci3_
          pdest-wbci4_
        
          presult-wbci2_
          presult-wbci3_
          presult-wbci4_
                   
          ; primary inputs
          pforce-stall-issue
          pstall
        ) ; end complete-pipeline (ci)
      
        (ite
               ; perform ISA step only if the pipeline actually fetched a *new* instruction.
               ; i.e., if not bubble-id after one step and there was no stall-issue;
          (and 
            (not pbubble-idsc1_)
            (not
              do-stall-issue ; (stall-issue
;                 pforce-stall-issue
;                 pbubble-ex
;                 popcode-ex
;                 pdest-ex
;                 pbubble-id
;                 pinst-id
;               )
            )
          ) ; end condition about stalling
   
          (instruction-in-reference ; then-branch (no stalling)
            ; "inputs" to macro (state before the instruction)
            pREGFILEci4_
            pDMEMci4_
            pIMEM
            pPCci4_
          
            ; "outputs" of macro (state after the instruction)
            pREGFILEci5_
            pDMEMci5_
            pPCci5_
          )
          (and ; stall. Keep values
            (= pPCci4_ pPCci5_)
            (= pREGFILEci4_ pREGFILEci5_)
            (= pDMEMci4_ pDMEMci5_)
          )
        ) ; end instruction-in-reference
        
        (step-in-pipeline
          ; "inputs" to macro (state before the step)
          pREGFILE
          pDMEM
          pIMEM
          pPC
        
          pinst-id
          pbubble-id
          
          pbubble-ex
          pshort-immed-ex
          pdest-ex
          popcode-ex
          poperand-a
          poperand-b
          
          pdest-mem
          presult-mem
          pmar
          pload-flag
          pstore-flag
          
          pdest-wb
          presult-wb
            
          ; "outputs" of macro (state after the step)
          pREGFILEsc1_
          pDMEMsc1_
          pPCsc1_
          
          pinst-idsc1_
          pbubble-idsc1_
          
          pbubble-exsc1_
          pshort-immed-exsc1_
          pdest-exsc1_
          popcode-exsc1_
          poperand-asc1_
          poperand-bsc1_
          
          pdest-memsc1_
          presult-memsc1_
          pmarsc1_
          pload-flagsc1_
          pstore-flagsc1_
          
          pdest-wbsc1_
          presult-wbsc1_
        
          ; primary inputs
          pforce-stall-issue
          pstall            
        ) ; end step-in-pipeline
        
        (complete-pipeline  
          ; "inputs" to macro (state before the step)
          pREGFILEsc1_
          pDMEMsc1_
          pIMEM
          pPCsc1_
        
          pinst-idsc1_
          pbubble-idsc1_
          
          pbubble-exsc1_
          pshort-immed-exsc1_
          pdest-exsc1_
          popcode-exsc1_
          poperand-asc1_
          poperand-bsc1_
          
          pdest-memsc1_
          presult-memsc1_
          pmarsc1_
          pload-flagsc1_
          pstore-flagsc1_
          
          pdest-wbsc1_
          presult-wbsc1_
            
          ; "outputs" of macro (state after the step)
          pREGFILEsc5_
          pDMEMsc5_
          pPCsc5_
           
          ; intermediate ("transient") values
          pREGFILEsc2_
          pREGFILEsc3_
          pREGFILEsc4_
          
          pDMEMsc3_
          pDMEMsc4_
          
          pbubble-exsc5_
          
          pshort-immed-exsc5_
          
          pdest-exsc5_
           
          popcode-exsc5_
          
          poperand-asc5_
           
          poperand-bsc5_
           
          pdest-memsc4_
          pdest-memsc5_
        
          presult-memsc4_
          presult-memsc5_
          
          pmarsc4_
          pmarsc5_
          
          pload-flagsc4_
          pload-flagsc5_
          
          pstore-flagsc4_
          pstore-flagsc5_
        
          pdest-wbsc3_
          pdest-wbsc4_
          pdest-wbsc5_
        
          presult-wbsc3_
          presult-wbsc4_
          presult-wbsc5_
        
          
          ; primary inputs
          pforce-stall-issue
          pstall            
        ) ; end complete-pipeline (sc)
      ) ; end conjunction of update parts
      (and
        (equivalence pREGFILEci5_ pREGFILEsc5_ pDMEMci5_ pDMEMsc5_ pPCci5_ pPCsc5_)
        (=> ; liveness. disallow stall if there is a bubble in ID or EX, and stall was not forced.
          (and
            (not pforce-stall-issue)
            (or
              pbubble-id
              pbubble-ex
            )
          )
          (not do-stall-issue)
        )
          true
      )
    ) ; end of update implies 
  ) ; end main expression
) ; end macro main-formula

; ##############################################################################
; ##############################################################################
; ##############################################################################
; ##############################################################################
; ##############################################################################
; ##############################################################################
; ------------------------------------------------------------------------------
;
; The actual assert statement

(assert
;   (not ; for Suraq, we need the valid formula, not the negated unsat one.
    (main-formula
      stall
      false ;force-stall-issue
      
      REGFILE       
      REGFILEci1_   
      REGFILEci2_   
      REGFILEci3_   
      REGFILEci4_   
      REGFILEci5_   
      REGFILEsc1_   
      REGFILEsc2_   
      REGFILEsc3_   
      REGFILEsc4_   
      REGFILEsc5_   
      
      DMEM          
      DMEMci2_      
      DMEMci3_      
      DMEMci4_      
      DMEMci5_      
      DMEMsc1_      
      DMEMsc3_      
      DMEMsc4_      
      DMEMsc5_      
      
      IMEM            
      
      PC       
      PCci4_   
      PCci5_ 
      PCsc1_
      PCsc5_   
      
      inst-id
      inst-idsc1_
      
      bubble-id
      bubble-idsc1_
      
      bubble-ex    
      bubble-exci4_
      bubble-exsc1_
      bubble-exsc5_
      
      short-immed-ex 
      short-immed-exci4_
      short-immed-exsc1_
      short-immed-exsc5_
      
      dest-ex           
      dest-exci4_       
      dest-exsc1_       
      dest-exsc5_       
      
      opcode-ex         
      opcode-exci4_     
      opcode-exsc1_     
      opcode-exsc5_     
      
      operand-a         
      operand-aci4_     
      operand-asc1_     
      operand-asc5_     
      
      operand-b         
      operand-bci4_     
      operand-bsc1_   
      operand-bsc5_   
      
      dest-mem        
      dest-memci3_    
      dest-memci4_    
      dest-memsc1_    
      dest-memsc4_    
      dest-memsc5_    
      
      result-mem      
      result-memci3_  
      result-memci4_  
      result-memsc1_  
      result-memsc4_  
      result-memsc5_  
      
      mar             
      marci3_         
      marci4_         
      marsc1_         
      marsc4_         
      marsc5_         
      
      load-flag       
      load-flagci3_   
      load-flagci4_   
      load-flagsc1_   
      load-flagsc4_   
      load-flagsc5_   
      
      store-flag      
      store-flagci3_  
      store-flagci4_  
      store-flagsc1_  
      store-flagsc4_  
      store-flagsc5_  
      
      dest-wb         
      dest-wbci2_     
      dest-wbci3_     
      dest-wbci4_     
      dest-wbsc1_     
      dest-wbsc3_     
      dest-wbsc4_   
      dest-wbsc5_   
      
      result-wb     
      result-wbci2_ 
      result-wbci3_ 
      result-wbci4_ 
      result-wbsc1_ 
      result-wbsc3_ 
      result-wbsc4_ 
      result-wbsc5_ 
    )
;   ); this parenthesis belongs to the "not" operator that we do not need for Suraq.
)
; 
; ;-------------------------------------------------------------------------------
; ; "implementation" of control signals
; 
; ;-------------------------------------------------------------------------------
; ; forward-a-from-ex
; (assert 
;   (=
;     forward-a-from-ex
;     (and
;       (= (rf1-of inst-id) dest-ex)
;       (not bubble-ex)
;       (not (is-store opcode-ex))
;     )
;   )
; )
; 
; ;-------------------------------------------------------------------------------
; ; forward-a-from-mem
; (assert
;   (=
;     forward-a-from-mem
;     (and
;       (= (rf1-of inst-id) dest-mem)
;       (not store-flag)
;     )
;   )
; )
; 
; ;-------------------------------------------------------------------------------
; ; forward-a-from-wb
; (assert
;   (=
;     forward-a-from-wb
;     (= (rf1-of inst-id) dest-wb)
;   )
; )
; 
; ;-------------------------------------------------------------------------------
; ; forward-b-from-ex
; (assert 
;   (=
;     forward-b-from-ex
;     (and
;       (= (rf2-of inst-id) dest-ex)
;       (not bubble-ex)
;       (not (is-store opcode-ex))
;     )
;   )
; )
; 
; ;-------------------------------------------------------------------------------
; ; forward-b-from-mem
; (assert
;   (=
;     forward-b-from-mem
;     (and
;       (= (rf2-of inst-id) dest-mem)
;       (not store-flag)
;     )
;   )
; )
; 
; ;-------------------------------------------------------------------------------
; ; forward-b-from-wb
; (assert
;   (=
;     forward-b-from-wb
;     (= (rf2-of inst-id) dest-wb)
;   )
; )
; 
; ;-------------------------------------------------------------------------------
; ; do-stall-issue
; (assert
;   (=
;     do-stall-issue
;     (stall-issue
;       force-stall-issue  
;       bubble-ex          
;       opcode-ex          
;       dest-ex            
;       bubble-id          
;       inst-id            
;     )
;   )
; )

; (check-sat)
;(get-model)
; (get-value ((is-load (opcode-of (select IMEM PCci4_)))))
; (get-value ((is-alu-immed (opcode-of (select IMEM PCci4_)))))
; (get-value ((= ZERO (rf1-of (select IMEM PCci4_)))))
; (get-value ((= ZERO (rf2-of (select IMEM PCci4_)))