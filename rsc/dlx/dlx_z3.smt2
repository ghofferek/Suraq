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


(set-option :model-compact true)

(set-logic QF_AUFLIA)

; primary inputs
(declare-fun stall             () Bool)
(declare-fun force-stall-issue () Bool)

; Declare arrays
; (and copies for ci and sc paths)

(declare-fun REGFILE      () (Array Int Int))
(declare-fun REGFILEci1_  () (Array Int Int) )
(declare-fun REGFILEci2_  () (Array Int Int) )
(declare-fun REGFILEci3_  () (Array Int Int) )
(declare-fun REGFILEci4_  () (Array Int Int) )
(declare-fun REGFILEci5_  () (Array Int Int) )
(declare-fun REGFILEsc1_  () (Array Int Int) )
(declare-fun REGFILEsc2_  () (Array Int Int) )
(declare-fun REGFILEsc3_  () (Array Int Int) )
(declare-fun REGFILEsc4_  () (Array Int Int) )
(declare-fun REGFILEsc5_  () (Array Int Int) )

(declare-fun DMEM         () (Array Int Int))
(declare-fun DMEMci2_     () (Array Int Int) )
(declare-fun DMEMci3_     () (Array Int Int) )
(declare-fun DMEMci4_     () (Array Int Int) )
(declare-fun DMEMci5_     () (Array Int Int) )
(declare-fun DMEMsc1_     () (Array Int Int) )
(declare-fun DMEMsc3_     () (Array Int Int) )
(declare-fun DMEMsc4_     () (Array Int Int) )
(declare-fun DMEMsc5_     () (Array Int Int) )

(declare-fun IMEM         () (Array Int Int))  ; IMEM is never written. Thus no need for more copies.


; Declare constants

(declare-fun FOUR () Int)
(declare-fun ZERO () Int)


; Declare single data elements
; (and copies for ci and sc paths)

(declare-fun PC     () Int               )  ; Program counter
(declare-fun PCci4_ () Int )
(declare-fun PCci5_ () Int )  
(declare-fun PCsc1_ () Int )
(declare-fun PCsc5_ () Int )  
  

; Declare uninterpreted functions of the datapath

(declare-fun PLUS              (Int Int      )   Int)
(declare-fun ALU               (Int Int Int)   Int)
(declare-fun rf1-of            (Int            )   Int)
(declare-fun rf2-of            (Int            )   Int)
(declare-fun rf3-of            (Int            )   Int)
(declare-fun opcode-of         (Int            )   Int)
(declare-fun short-immed-of    (Int            )   Int)
(declare-fun long-immed-of     (Int            )   Int)
(declare-fun alu-op-of         (Int            )   Int)


; Declare uninterpreted predicates of the datapath

(declare-fun is-load           (Int            )   Bool )
(declare-fun is-store          (Int            )   Bool ) 
(declare-fun is-J              (Int            )   Bool )
(declare-fun is-BEQZ           (Int            )   Bool )
(declare-fun is-alu-immed      (Int            )   Bool )


; Declare pipeline registers (and copies for stepping and completion)

; ID stage
(declare-fun inst-id             () Int               )
(declare-fun inst-idsc1_         () Int )

(declare-fun bubble-id           () Bool  )
(declare-fun bubble-idsc1_       () Bool  )

; EX stage
(declare-fun bubble-ex           () Bool                )
(declare-fun bubble-exci4_       () Bool  )
(declare-fun bubble-exsc1_       () Bool  )
(declare-fun bubble-exsc5_       () Bool  )

(declare-fun short-immed-ex      () Int               )
(declare-fun short-immed-exci4_  () Int )
(declare-fun short-immed-exsc1_  () Int )
(declare-fun short-immed-exsc5_  () Int )

(declare-fun dest-ex             () Int               )
(declare-fun dest-exci4_         () Int )
(declare-fun dest-exsc1_         () Int )
(declare-fun dest-exsc5_         () Int )

(declare-fun opcode-ex           () Int               )
(declare-fun opcode-exci4_       () Int )
(declare-fun opcode-exsc1_       () Int )
(declare-fun opcode-exsc5_       () Int )

(declare-fun operand-a           () Int               )
(declare-fun operand-aci4_       () Int  )
(declare-fun operand-asc1_       () Int  )
(declare-fun operand-asc5_       () Int  )

(declare-fun operand-b           () Int               )
(declare-fun operand-bci4_       () Int  )
(declare-fun operand-bsc1_       () Int  )
(declare-fun operand-bsc5_       () Int  )

; MEM stage
(declare-fun dest-mem        () Int)
(declare-fun dest-memci3_    () Int)
(declare-fun dest-memci4_    () Int)
(declare-fun dest-memsc1_    () Int)
(declare-fun dest-memsc4_    () Int)
(declare-fun dest-memsc5_    () Int)

(declare-fun result-mem      () Int)
(declare-fun result-memci3_  () Int)
(declare-fun result-memci4_  () Int)
(declare-fun result-memsc1_  () Int)
(declare-fun result-memsc4_  () Int)
(declare-fun result-memsc5_  () Int)

(declare-fun mar             () Int)
(declare-fun marci3_         () Int)
(declare-fun marci4_         () Int)
(declare-fun marsc1_         () Int)
(declare-fun marsc4_         () Int)
(declare-fun marsc5_         () Int)

(declare-fun load-flag       () Bool )
(declare-fun load-flagci3_   () Bool )
(declare-fun load-flagci4_   () Bool )
(declare-fun load-flagsc1_   () Bool )
(declare-fun load-flagsc4_   () Bool )
(declare-fun load-flagsc5_   () Bool )

(declare-fun store-flag      () Bool )
(declare-fun store-flagci3_  () Bool )
(declare-fun store-flagci4_  () Bool )
(declare-fun store-flagsc1_  () Bool )
(declare-fun store-flagsc4_  () Bool )
(declare-fun store-flagsc5_  () Bool )


; WB stage
(declare-fun dest-wb         () Int)
(declare-fun dest-wbci2_     () Int)
(declare-fun dest-wbci3_     () Int)
(declare-fun dest-wbci4_     () Int)
(declare-fun dest-wbsc1_     () Int)
(declare-fun dest-wbsc3_    () Int)
(declare-fun dest-wbsc4_     () Int)
(declare-fun dest-wbsc5_     () Int)

(declare-fun result-wb       () Int)
(declare-fun result-wbci2_   () Int)
(declare-fun result-wbci3_   () Int)
(declare-fun result-wbci4_   () Int)
(declare-fun result-wbsc1_   () Int)
(declare-fun result-wbsc3_   () Int)
(declare-fun result-wbsc4_   () Int)
(declare-fun result-wbsc5_   () Int)


; auxiliary constants to state commutativity and associativity of PLUS
; (declare-fun aux1            () Int )
; (declare-fun aux2            () Int )
; (declare-fun aux3            () Int )
; (declare-fun aux4            () Int )
; (declare-fun aux5            () Int )

; auxiliary constants to state properti4es of the is-XXX predicates
; (declare-fun aux6            () Int )



; Properties of PLUS (commutativity and asscciativity)
; (define-fun plus-properties
;   ( ; parameters
;     (a Int)
;     (b Int)
;     (c Int)
;     (d Int)
;     (e Int)  
;   )
;   Bool ; return type of macro
;   ; main expression:
;   (
;     and
;     (=
;       (PLUS a b)
;       (PLUS b a)
;     )
;     (=
;       (PLUS (PLUS c d) e)
;       (PLUS c (PLUS d e))
;     )
;   )
; )

; Properties of is-XXX predicates
; (always exactly one is true)
(define-fun is-properties
  ( ; parameters
    (opcode Int)  
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
    
;     (or
;       (is-load      opcode)
;       (is-store     opcode)
;       (is-J         opcode)
;       (is-BEQZ      opcode)
;       (is-alu-immed opcode)
;     )

      ; if none of these is true, it is a three-register instruction. 
  )
)




; Equivalence Criterion:
; The programmer-visible state of the processor is the REGFILE, the DMEM and
; the PC.
; They must be equal after going along the ci and the sc branch.

(define-fun equivalence 
  ( ; parameters
    (REGFILEci (Array Int Int))
    (REGFILEsc (Array Int Int))
    (DMEMci    (Array Int Int))
    (DMEMsc    (Array Int Int))
    (PCci      Int              )
    (PCsc      Int              )
  )
  Bool ; return type of macro
  ; main expression: 
;   ( and
;      (= REGFILEci REGFILEsc)
;      (= DMEMci    DMEMsc   )
;      (= PCci      PCsc     )
;   )
    (= PCci      PCsc     )
)


; Helper Macros (to shorten main parts of formula)

(define-fun rf1data
  ( ; parameters
    (REGFILE (Array Int Int))
    (IMEM    (Array Int Int))
    (PC      Int              )
  )
  Int ; return type of macro
  ; main expression:
  (ite
    (= ZERO (rf1-of (select IMEM PC)))
    ZERO
    (select REGFILE (rf1-of (select IMEM PC)))
  )
) 

(define-fun rf2data
  ( ; parameters
    (REGFILE (Array Int Int))
    (IMEM    (Array Int Int))
    (PC      Int              )
  )
  Int ; return type of macro
  ; main expression:
  (ite
    (= ZERO (rf2-of (select IMEM PC)))
    ZERO
    (select REGFILE (rf2-of (select IMEM PC)))
  )
) 

(define-fun alu-result
  ( ; parameters
    (operand-a    Int)
    (operand-b    Int)
    (opcode       Int)
    (short-immed  Int)
  )
  Int ; return type of macro
  ; main expression:
  (ite
    (or
      (is-load  opcode)
      (is-store opcode)
    )
    (PLUS short-immed operand-a)
    (ALU (alu-op-of opcode) operand-a operand-b)
  )
) 

(define-fun stall-issue
  ( ; parameters
    (force-stall-issue  Bool )
    (bubble-ex          Bool )
    (dest-ex            Int)
    (bubble-id          Bool )
    (inst-id            Int)
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
      (is-load (opcode-of inst-id))
      (not bubble-ex)
      (not bubble-id)
    )
  )
)

(define-fun branch-taken
  ( ; parameters
    (bubble-id          Bool )
    (inst-id            Int)
    (operand-an         Int)
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

(define-fun TA
  ( ; parameters
    (inst-id Int)
    (PC      Int)
  )
  Int ; return type of macro
  ; main expression
  (ite
    (is-J (opcode-of inst-id))
    (PLUS PC (long-immed-of  inst-id))
    (PLUS PC (short-immed-of inst-id))
  )
)

; ------------------------------------------------------------------------------
; One instruction in the reference architecture

(define-fun instruction-in-reference
  ( ; parameters
  
    ; "inputs" to macro (state before the instruction)
    (REGFILEi (Array Int Int))
    (DMEMi    (Array Int Int))
    (IMEMi    (Array Int Int))
    (PCi      Int              )
  
    ; "outputs" of macro (state after the instruction)
    (REGFILEo (Array Int Int))
    (DMEMo    (Array Int Int))
   ;(IMEMo    (Array Int Int))
    (PCo      Int              )
  )
  Bool ; return type of macro
  ; main expression
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
    (REGFILEi         (Array Int Int))
    
    (dest-wbi         Int              )
    (result-wbi       Int              )
      
    ; "outputs" of macro (state after the step)
    (REGFILEo         (Array Int Int))
  )
  Bool ; return type
  ; main expression
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
  ) ; END main expression
) ; END of step-in-WB macro


; ------------------------------------------------------------------------------
(define-fun step-in-MEM
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (DMEMi            (Array Int Int))
    
    (dest-memi        Int              )
    (result-memi      Int              )
    (mari             Int              )
    (load-flagi       Bool               )
    (store-flagi      Bool               )
    
      
    ; "outputs" of macro (state after the step)
    (DMEMo            (Array Int Int))
    
    (dest-wbo         Int              )
    (result-wbo       Int              )
  
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
    (= dest-wbo dest-memi)
    (= 
      result-wbo
      (ite
        load-flagi
        (select DMEMi mari)
        result-memi
      )
    )  
  ) ; END main expression
) ; END of step-in-MEM macro


; ------------------------------------------------------------------------------
(define-fun step-in-EX
  ( ; parameters
  
    ; "inputs" to macro (state before the step)   
    (bubble-exi       Bool               )
    (short-immed-exi  Int              )
    (dest-exi         Int              )
    (opcode-exi       Int              )
    (operand-ai       Int              )
    (operand-bi       Int              )
          
    ; "outputs" of macro (state after the step)
    (dest-memo        Int              )
    (result-memo      Int              )
    (maro             Int              )
    (load-flago       Bool               )
    (store-flago      Bool               )
  )
  Bool ; return type
  ; main expression
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
  ) ; END main expression
) ; END of step-in-EX macro


; ------------------------------------------------------------------------------
(define-fun step-in-ID
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (REGFILEi         (Array Int Int))
    
    (inst-idi         Int              )
    (bubble-idi       Bool               )
    
    (bubble-exf       Bool               )  ; f = forward
    (dest-exf         Int              )
    (result-exf       Int              )
    
    (dest-memf        Int              )
    (result-memf      Int              )
    
    (dest-wbf         Int              )
    (result-wbf       Int              )
      
    ; "outputs" of macro (state after the step)
    
    (bubble-exo       Bool               )
    (short-immed-exo  Int              )
    (dest-exo         Int              )
    (opcode-exo       Int              )
    (operand-ao       Int              )
    (operand-bo       Int              )
    
    ; primary inputs
    (force-stall-issue Bool              )
  )
  Bool ; return type
  ; main expression
  (and ; conjunction over all parts        
      
    ; update of EX stage registers
    (=
      bubble-exo
      (or
        (stall-issue force-stall-issue bubble-exf dest-exf bubble-idi inst-idi) 
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
  ) ; END main expression
) ; END of step-in-ID macro


; ------------------------------------------------------------------------------

(define-fun step-in-IF ; necessary for "step" only; not neeeded for completion.
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (IMEMi            (Array Int Int))
    (PCi              Int              )
  
    (inst-idf         Int              )
    (bubble-idf       Bool               )
  
    (bubble-exf       Bool               )
    (dest-exf         Int              )
    
    (operand-af       Int              )  ; the value at the *input* (not the output!!) of operand-a register
          
    ; "outputs" of macro (state after the step)
    (inst-ido         Int              )
    (bubble-ido       Bool               )
      
    ; primary inputs
    (force-stall-issue Bool              )
    (stall             Bool              )
  )
  Bool ; return type
  ; main expression
  (and ; conjunction over all parts
  
    ; update of ID registers
    (= 
      bubble-ido
      (ite
        force-stall-issue
        (ite
          (or (not bubble-idf) stall)
          bubble-idf
          false
        )
        (ite
          (stall-issue force-stall-issue bubble-exf dest-exf bubble-idf inst-idf)
          bubble-idf
          (ite
            stall
            true
            (branch-taken bubble-idf inst-idf operand-af)
          )
        )
      )
    )
    (=
      inst-ido
      (ite
        force-stall-issue
        (ite
          (or (not bubble-idf) stall)
          inst-idf
          (select IMEMi PCi)
        )
        (ite
          (stall-issue force-stall-issue bubble-exf dest-exf bubble-idf inst-idf)
          inst-idf
          (ite
            stall
            inst-idf
            (select IMEMi PCi)
          )
        )
      )
    )
  ) ; END main expression
) ; END of step-in-IF macro

;-------------------------------------------------------------------------------

(define-fun step-PC ; steps the program counter
  ( ; parameters
  
    ; "inputs" to macro (state before the step)
    (PCi              Int              )
  
    (inst-idf         Int              )
    (bubble-idf       Bool               )
  
    (bubble-exf       Bool               )
    (dest-exf         Int              )
    
    (operand-af       Int              )  ; the value at the *input* (not the output!!) of operand-a register
          
    ; "outputs" of macro (state after the step)
    (PCo              Int              )
      
    ; primary inputs
    (force-stall-issue Bool              )
    (stall             Bool              )
  
    ; auxiliary input indicating that the macro is used for completion and 
    ; thus only jumps and branches should be done (no increment)
    (completion        Bool              )
  )
  Bool ; return type
  ; main expression
  (=     ; update of PC
    PCo
    (ite
      completion
      (ite
        (branch-taken bubble-idf inst-idf operand-af)
        (TA inst-idf PCi)
        PCi
      )
      (ite
        force-stall-issue
        (ite
          (or (not bubble-idf) stall)
          PCi
          (PLUS PCi FOUR)
        )
        (ite
          (stall-issue force-stall-issue bubble-exf dest-exf bubble-idf inst-idf)
          PCi
          (ite
            stall
            (ite
              (branch-taken bubble-idf inst-idf operand-af)
              (TA inst-idf PCi)
              PCi
            )
            (ite
              (branch-taken bubble-idf inst-idf operand-af)
              (TA inst-idf PCi)
              (PLUS PCi FOUR)
            )
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
    (REGFILEi         (Array Int Int))
    (DMEMi            (Array Int Int))
    (IMEMi            (Array Int Int))
    (PCi              Int              )
  
    (inst-idi         Int              )
    (bubble-idi       Bool               )
    
    (bubble-exi       Bool               )
    (short-immed-exi  Int              )
    (dest-exi         Int              )
    (opcode-exi       Int              )
    (operand-ai       Int              )
    (operand-bi       Int              )
    
    (dest-memi        Int              )
    (result-memi      Int              )
    (mari             Int              )
    (load-flagi       Bool               )
    (store-flagi      Bool               )
    
    (dest-wbi         Int              )
    (result-wbi       Int              )
      
    ; "outputs" of macro (state after the step)
    (REGFILEo         (Array Int Int))
    (DMEMo            (Array Int Int))
   ;(IMEMo            (Array Int Int))
    (PCo              Int              )
    
    (inst-ido         Int              )
    (bubble-ido       Bool               )
    
    (bubble-exo       Bool               )
    (short-immed-exo  Int              )
    (dest-exo         Int              )
    (opcode-exo       Int              )
    (operand-ao       Int              )
    (operand-bo       Int              )
    
    (dest-memo        Int              )
    (result-memo      Int              )
    (maro             Int              )
    (load-flago       Bool               )
    (store-flago      Bool               )
    
    (dest-wbo         Int              )
    (result-wbo       Int              )
  
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
      dest-exi ; forwarded value                       
      (ite
        (or (is-load opcode-exi) (is-store opcode-exi))
        (PLUS operand-ai short-immed-exi)
        (alu-result operand-ai operand-bi opcode-exi short-immed-exi)
      ) ;result-exi ; forwarded value                     
      dest-memi ; forwarded value                      
      result-memi ; forwarded value                    
      dest-wbi ; forwarded value                       
      result-wbi ; forwarded value                     
      bubble-exo                      
      short-immed-exo                
      dest-exo                       
      opcode-exo                     
      operand-ao                     
      operand-bo                     
      force-stall-issue                   
    )
    
    (step-in-IF
      IMEMi            
      PCi              
      inst-idi         
      bubble-idi       
      bubble-exi       
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
    (REGFILEi         (Array Int Int))
    (DMEMi            (Array Int Int))
    (IMEMi            (Array Int Int))
    (PCi              Int              )
  
    (inst-idi         Int              )
    (bubble-idi       Bool               )
    
    (bubble-exi       Bool               )
    (short-immed-exi  Int              )
    (dest-exi         Int              )
    (opcode-exi       Int              )
    (operand-ai       Int              )
    (operand-bi       Int              )
    
    (dest-memi        Int              )
    (result-memi      Int              )
    (mari             Int              )
    (load-flagi       Bool               )
    (store-flagi      Bool               )
    
    (dest-wbi         Int              )
    (result-wbi       Int              )
      
    ; "outputs" of macro (state after the step)
    (REGFILEo         (Array Int Int))
    (DMEMo            (Array Int Int))
    (PCo              Int            )
   ;(IMEMo            (Array Int Int))
    
     
     
    ; intermediate ("transient") values
    (REGFILEt1_       (Array Int Int))
    (REGFILEt2_       (Array Int Int))
    (REGFILEt3_       (Array Int Int))
    
    (DMEMt2_          (Array Int Int))
    (DMEMt3_          (Array Int Int))
    
    (bubble-ext4_     Bool               )
    
    (short-immed-ext4_ Int             )
    
    (dest-ext4_       Int              )
     
    (opcode-ext4_     Int              )
    
    (operand-at4_     Int              )
     
    (operand-bt4_     Int              )
     
    (dest-memt3_      Int              )
    (dest-memt4_      Int              )
  
    (result-memt3_    Int              )
    (result-memt4_    Int              )
    
    (mart3_           Int              )
    (mart4_           Int              )
    
    (load-flagt3_     Bool               )
    (load-flagt4_     Bool               )
    
    (store-flagt3_    Bool               )
    (store-flagt4_    Bool               )
  
    (dest-wbt2_       Int              )
    (dest-wbt3_       Int              )
    (dest-wbt4_       Int              )
  
    (result-wbt2_     Int              )
    (result-wbt3_     Int              )
    (result-wbt4_     Int              )
  
    
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
      REGFILEi        
      inst-idi                       
      bubble-idi
      bubble-exi ; forwarded value                      
      dest-exi ; forwarded value                       
      (ite
        (or (is-load opcode-exi) (is-store opcode-exi))
        (PLUS operand-ai short-immed-exi)
        (alu-result operand-ai operand-bi opcode-exi short-immed-exi)
      );result-exi ; forwarded value                     
      dest-memi ; forwarded value                      
      result-memi ; forwarded value                    
      dest-wbi ; forwarded value                       
      result-wbi ; forwarded value                     
      bubble-ext4_                      
      short-immed-ext4_                
      dest-ext4_                       
      opcode-ext4_                     
      operand-at4_                     
      operand-bt4_                     
      force-stall-issue                   
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
      bubble-exi
      dest-exi
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
    
    (pREGFILE       (Array Int Int))
    (pREGFILEci1_   (Array Int Int))
    (pREGFILEci2_   (Array Int Int))
    (pREGFILEci3_   (Array Int Int))
    (pREGFILEci4_   (Array Int Int))
    (pREGFILEci5_   (Array Int Int))
    (pREGFILEsc1_   (Array Int Int))
    (pREGFILEsc2_   (Array Int Int))
    (pREGFILEsc3_   (Array Int Int))
    (pREGFILEsc4_   (Array Int Int))
    (pREGFILEsc5_   (Array Int Int))
    
    (pDMEM          (Array Int Int))
    (pDMEMci2_      (Array Int Int))
    (pDMEMci3_      (Array Int Int))
    (pDMEMci4_      (Array Int Int))
    (pDMEMci5_      (Array Int Int))
    (pDMEMsc1_      (Array Int Int))
    (pDMEMsc3_      (Array Int Int))
    (pDMEMsc4_      (Array Int Int))
    (pDMEMsc5_      (Array Int Int))
    
    (pIMEM          (Array Int Int))  
    
    (pPC      Int               )  
    (pPCci4_  Int)  
    (pPCci5_  Int)
    (pPCsc1_  Int)
    (pPCsc5_  Int)  
    
    (pinst-id              Int               )
    (pinst-idsc1_          Int)
    
    (pbubble-id            Bool )
    (pbubble-idsc1_        Bool )
    
    (pbubble-ex            Bool                )
    (pbubble-exci4_        Bool )
    (pbubble-exsc1_        Bool )
    (pbubble-exsc5_        Bool )
    
    (pshort-immed-ex       Int               )
    (pshort-immed-exci4_   Int)
    (pshort-immed-exsc1_   Int)
    (pshort-immed-exsc5_   Int)
    
    (pdest-ex              Int               )
    (pdest-exci4_          Int)
    (pdest-exsc1_          Int)
    (pdest-exsc5_          Int)
    
    (popcode-ex            Int               )
    (popcode-exci4_        Int)
    (popcode-exsc1_        Int)
    (popcode-exsc5_        Int)
    
    (poperand-a            Int               )
    (poperand-aci4_        Int )
    (poperand-asc1_        Int )
    (poperand-asc5_        Int )
    
    (poperand-b            Int               )
    (poperand-bci4_        Int )
    (poperand-bsc1_        Int )
    (poperand-bsc5_        Int )
    
    (pdest-mem         Int)
    (pdest-memci3_     Int)
    (pdest-memci4_     Int)
    (pdest-memsc1_     Int)
    (pdest-memsc4_     Int)
    (pdest-memsc5_     Int)
    
    (presult-mem       Int)
    (presult-memci3_   Int)
    (presult-memci4_   Int)
    (presult-memsc1_   Int)
    (presult-memsc4_   Int)
    (presult-memsc5_   Int)
    
    (pmar              Int)
    (pmarci3_          Int)
    (pmarci4_          Int)
    (pmarsc1_          Int)
    (pmarsc4_          Int)
    (pmarsc5_          Int)
    
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
    
    (pdest-wb          Int)
    (pdest-wbci2_      Int)
    (pdest-wbci3_      Int)
    (pdest-wbci4_      Int)
    (pdest-wbsc1_      Int)
    (pdest-wbsc3_      Int)
    (pdest-wbsc4_      Int)
    (pdest-wbsc5_      Int)
    
    (presult-wb        Int)
    (presult-wbci2_    Int)
    (presult-wbci3_    Int)
    (presult-wbci4_    Int)
    (presult-wbsc1_    Int)
    (presult-wbsc3_    Int)
    (presult-wbsc4_    Int)
    (presult-wbsc5_    Int)
    
    
;     (paux1             Int)
;     (paux2             Int)
;     (paux3             Int)
;     (paux4             Int)
;     (paux5             Int)
;     (paux6             Int)  
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
      ;(plus-properties aux1 aux2 aux3 aux4 aux5)
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
;           (and 
;             (not pstall)
;             (not
;               (stall-issue
;                 force-stall-issue
;                 bubble-ex
;                 dest-ex
;                 bubble-id
;                 inst-id
;               )
;             )
;           ) ; end condition about stalling
           
               ; perform ISA step only if the pipeline actually fetched a *new* instruction.
               ; i.e., if not bubble-id after one step
            (not pbubble-idsc1_)   
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
      (
        equivalence pREGFILEci5_ pREGFILEsc5_ pDMEMci5_ pDMEMsc5_ pPCci5_ pPCsc5_
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
  (not
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
      
;       aux1          
;       aux2          
;       aux3          
;       aux4          
;       aux5          
;       aux6            
    )
  )
)


  
(check-sat)  
(get-info :name)
(get-model)
(get-value ((select IMEM PC)))
(get-value (PC))
(get-value (PCci4_))
(get-value (PCci5_))
(get-value (PCsc1_))
(get-value (PCsc5_))
(get-value ((= PCci5_ PCsc5_)))
(get-value ((equivalence REGFILEci5_ REGFILEsc5_ DMEMci5_ DMEMsc5_ PCci5_ PCsc5_)))