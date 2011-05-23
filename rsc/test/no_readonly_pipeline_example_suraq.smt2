; This file is a "samle" of how input for Suraq should look like.
; It is based on the simple example of the MemoCODE'11 paper.
; Comments provide hints towards generalization of the example.
; A formal standard will be described in the Suraq user's manual at a later time.


; Indicate that this is a Suraq input file.
; This implicitely declares the sorts "Value" for domain values/variables,
; and "Control" for (Boolean) control signals.
(set-logic Suraq)


; Declare arrays.
; since ' ist not a valid SMTLIB symbol character, _ is used instead
; a ! symbol is appended to variable duplicated for formula expansion
;
; Arrays must all be of sort (Array Value Value). Other types of arrays are not
; supported at this time. 

(declare-fun REG      () (Array Value Value))
(declare-fun REGci_   () (Array Value Value))
(declare-fun REGci__  () (Array Value Value))
(declare-fun REGsc_   () (Array Value Value))
(declare-fun REGsc__  () (Array Value Value))

(declare-fun REGci_!  () (Array Value Value))
(declare-fun REGci__! () (Array Value Value))
(declare-fun REGsc_!  () (Array Value Value))
(declare-fun REGsc__! () (Array Value Value))


; Declare variables for pipeline registers
; All (non-control) variables must be of sort Value. Other types are not supported
; at this time. 

(declare-fun v   () Value)
(declare-fun v_  () Value)
(declare-fun v_! () Value)
(declare-fun w   () Value)


; Declare variables for inputs

(declare-fun s () Value)
(declare-fun dest () Value)


; Declare control variables
; The sort "Control" is implicitely compatible with sort "Bool".
; I.e., a something of sort "Control" can be used in a place where something
; of sort "Bool" is expected.
(declare-fun x () Control) 

; Declare uninterpreted functions
; Only functions from (Value+) -> Value are supported.
(declare-fun ALU (Value) Value)



; define-fun macros may be used to abbreviate and structure the input.
; At this point, only define-fun macros of return type Bool are supported.

; Equivalence Criterion

(define-fun equiv ((A (Array Value Value))(B (Array Value Value))) Bool (
  forall (i Value) (
    = (select A i)
      (select B i)
    )
  )
)


; Update function, which describes behavior of circuit
; (in step-complete and complete-ISA branch)

(define-fun update (
  ; parameters
  (REG     (Array Value Value)) 
  (REGci_  (Array Value Value))
  (REGci__ (Array Value Value)) 
  (REGsc_  (Array Value Value))
  (REGsc__ (Array Value Value))
  (v       Value            )
  (v_      Value            )
  (w       Value            )
  (s       Value            )
  (dest    Value            )
  (x       Bool             )
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
  (REG     (Array Value Value)) 
  (REGci_  (Array Value Value))
  (REGci__ (Array Value Value)) 
  (REGsc_  (Array Value Value))
  (REGsc__ (Array Value Value))
  (v       Value            )
  (v_      Value            )
  (w       Value            )
  (s       Value            )
  (dest    Value            )
  (x       Bool           )
  )
  Bool  ; return type
  
  ; main expression
  (=> (update REG REGci_ REGci__ REGsc_ REGsc__ v v_ w s dest x)
      (= REGci__ REGsc__)
  )
)


; Use "assert" to state what should actually hold for the synthesized control.
; Multiple assert statements are implicitly conjuncted.

(assert (formula REG REGci_  REGci__  REGsc_  REGsc__  v v_  w s dest x))
