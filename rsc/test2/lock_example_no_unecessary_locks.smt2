(set-logic Suraq)

(declare-fun ZERO    () Value)
(declare-fun ONE     () Value)
(declare-fun TWO     () Value)
(declare-fun THREE   () Value)
(declare-fun FOUR    () Value)
(declare-fun FIVE    () Value)
(declare-fun SIX     () Value)

(declare-fun pc1_1 () Value :no_dependence)
(declare-fun pc1_2 () Value :no_dependence)
(declare-fun pc1_3 () Value :no_dependence)
(declare-fun pc1_4 () Value :no_dependence)
(declare-fun pc1_5 () Value :no_dependence)
(declare-fun pc1_6 () Value :no_dependence)
(declare-fun pc1_7 () Value :no_dependence)
(declare-fun pc1_8 () Value :no_dependence)
(declare-fun pc1_9 () Value :no_dependence)
(declare-fun pc1_10 () Value :no_dependence)
(declare-fun pc1_11 () Value :no_dependence)
(declare-fun pc1_12 () Value :no_dependence)

(declare-fun pc2_1 () Value :no_dependence)
(declare-fun pc2_2 () Value :no_dependence)
(declare-fun pc2_3 () Value :no_dependence)
(declare-fun pc2_4 () Value :no_dependence)
(declare-fun pc2_5 () Value :no_dependence)
(declare-fun pc2_6 () Value :no_dependence)
(declare-fun pc2_7 () Value :no_dependence)
(declare-fun pc2_8 () Value :no_dependence)
(declare-fun pc2_9 () Value :no_dependence)
(declare-fun pc2_10 () Value :no_dependence)
(declare-fun pc2_11 () Value :no_dependence)
(declare-fun pc2_12 () Value :no_dependence)

(declare-fun pc1_1_no_L1 () Value :no_dependence)
(declare-fun pc1_2_no_L1 () Value :no_dependence)
(declare-fun pc1_3_no_L1 () Value :no_dependence)
(declare-fun pc1_4_no_L1 () Value :no_dependence)
(declare-fun pc1_5_no_L1 () Value :no_dependence)
(declare-fun pc1_6_no_L1 () Value :no_dependence)
(declare-fun pc1_7_no_L1 () Value :no_dependence)
(declare-fun pc1_8_no_L1 () Value :no_dependence)
(declare-fun pc1_9_no_L1 () Value :no_dependence)
(declare-fun pc1_10_no_L1 () Value :no_dependence)
(declare-fun pc1_11_no_L1 () Value :no_dependence)
(declare-fun pc1_12_no_L1 () Value :no_dependence)

(declare-fun pc2_1_no_L1 () Value :no_dependence)
(declare-fun pc2_2_no_L1 () Value :no_dependence)
(declare-fun pc2_3_no_L1 () Value :no_dependence)
(declare-fun pc2_4_no_L1 () Value :no_dependence)
(declare-fun pc2_5_no_L1 () Value :no_dependence)
(declare-fun pc2_6_no_L1 () Value :no_dependence)
(declare-fun pc2_7_no_L1 () Value :no_dependence)
(declare-fun pc2_8_no_L1 () Value :no_dependence)
(declare-fun pc2_9_no_L1 () Value :no_dependence)
(declare-fun pc2_10_no_L1 () Value :no_dependence)
(declare-fun pc2_11_no_L1 () Value :no_dependence)
(declare-fun pc2_12_no_L1 () Value :no_dependence)

(declare-fun pc1_1_no_L2 () Value :no_dependence)
(declare-fun pc1_2_no_L2 () Value :no_dependence)
(declare-fun pc1_3_no_L2 () Value :no_dependence)
(declare-fun pc1_4_no_L2 () Value :no_dependence)
(declare-fun pc1_5_no_L2 () Value :no_dependence)
(declare-fun pc1_6_no_L2 () Value :no_dependence)
(declare-fun pc1_7_no_L2 () Value :no_dependence)
(declare-fun pc1_8_no_L2 () Value :no_dependence)
(declare-fun pc1_9_no_L2 () Value :no_dependence)
(declare-fun pc1_10_no_L2 () Value :no_dependence)
(declare-fun pc1_11_no_L2 () Value :no_dependence)
(declare-fun pc1_12_no_L2 () Value :no_dependence)

(declare-fun pc2_1_no_L2 () Value :no_dependence)
(declare-fun pc2_2_no_L2 () Value :no_dependence)
(declare-fun pc2_3_no_L2 () Value :no_dependence)
(declare-fun pc2_4_no_L2 () Value :no_dependence)
(declare-fun pc2_5_no_L2 () Value :no_dependence)
(declare-fun pc2_6_no_L2 () Value :no_dependence)
(declare-fun pc2_7_no_L2 () Value :no_dependence)
(declare-fun pc2_8_no_L2 () Value :no_dependence)
(declare-fun pc2_9_no_L2 () Value :no_dependence)
(declare-fun pc2_10_no_L2 () Value :no_dependence)
(declare-fun pc2_11_no_L2 () Value :no_dependence)
(declare-fun pc2_12_no_L2 () Value :no_dependence)

(declare-fun MEM () (Array Value Value))

(declare-fun MEM_1 () (Array Value Value)  :no_dependence)
(declare-fun MEM_2 () (Array Value Value)  :no_dependence)
(declare-fun MEM_3 () (Array Value Value)  :no_dependence)
(declare-fun MEM_4 () (Array Value Value)  :no_dependence)
(declare-fun MEM_5 () (Array Value Value)  :no_dependence)
(declare-fun MEM_6 () (Array Value Value)  :no_dependence)
(declare-fun MEM_7 () (Array Value Value)  :no_dependence)
(declare-fun MEM_8 () (Array Value Value)  :no_dependence)
(declare-fun MEM_9 () (Array Value Value)  :no_dependence)
(declare-fun MEM_10 () (Array Value Value)  :no_dependence)
(declare-fun MEM_11 () (Array Value Value)  :no_dependence)
(declare-fun MEM_12 () (Array Value Value)  :no_dependence)

(declare-fun MEM_1_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_2_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_3_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_4_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_5_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_6_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_7_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_8_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_9_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_10_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_11_no_L1 () (Array Value Value) :no_dependence)
(declare-fun MEM_12_no_L1 () (Array Value Value) :no_dependence)

(declare-fun MEM_1_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_2_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_3_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_4_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_5_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_6_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_7_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_8_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_9_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_10_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_11_no_L2 () (Array Value Value) :no_dependence)
(declare-fun MEM_12_no_L2 () (Array Value Value) :no_dependence)

(declare-fun tmp11_0 () Value :no_dependence)
(declare-fun tmp11_1 () Value :no_dependence)
(declare-fun tmp11_2 () Value :no_dependence)
(declare-fun tmp11_3 () Value :no_dependence)
(declare-fun tmp11_4 () Value :no_dependence)
(declare-fun tmp11_5 () Value :no_dependence)
(declare-fun tmp11_6 () Value :no_dependence)
(declare-fun tmp11_7 () Value :no_dependence)
(declare-fun tmp11_8 () Value :no_dependence)
(declare-fun tmp11_9 () Value :no_dependence)
(declare-fun tmp11_10 () Value :no_dependence)
(declare-fun tmp11_11 () Value :no_dependence)
(declare-fun tmp11_12 () Value :no_dependence)

(declare-fun tmp12_0 () Value :no_dependence)
(declare-fun tmp12_1 () Value :no_dependence)
(declare-fun tmp12_2 () Value :no_dependence)
(declare-fun tmp12_3 () Value :no_dependence)
(declare-fun tmp12_4 () Value :no_dependence)
(declare-fun tmp12_5 () Value :no_dependence)
(declare-fun tmp12_6 () Value :no_dependence)
(declare-fun tmp12_7 () Value :no_dependence)
(declare-fun tmp12_8 () Value :no_dependence)
(declare-fun tmp12_9 () Value :no_dependence)
(declare-fun tmp12_10 () Value :no_dependence)
(declare-fun tmp12_11 () Value :no_dependence)
(declare-fun tmp12_12 () Value :no_dependence)

(declare-fun tmp21_0 () Value :no_dependence)
(declare-fun tmp21_1 () Value :no_dependence)
(declare-fun tmp21_2 () Value :no_dependence)
(declare-fun tmp21_3 () Value :no_dependence)
(declare-fun tmp21_4 () Value :no_dependence)
(declare-fun tmp21_5 () Value :no_dependence)
(declare-fun tmp21_6 () Value :no_dependence)
(declare-fun tmp21_7 () Value :no_dependence)
(declare-fun tmp21_8 () Value :no_dependence)
(declare-fun tmp21_9 () Value :no_dependence)
(declare-fun tmp21_10 () Value :no_dependence)
(declare-fun tmp21_11 () Value :no_dependence)
(declare-fun tmp21_12 () Value :no_dependence)

(declare-fun tmp22_0 () Value :no_dependence)
(declare-fun tmp22_1 () Value :no_dependence)
(declare-fun tmp22_2 () Value :no_dependence)
(declare-fun tmp22_3 () Value :no_dependence)
(declare-fun tmp22_4 () Value :no_dependence)
(declare-fun tmp22_5 () Value :no_dependence)
(declare-fun tmp22_6 () Value :no_dependence)
(declare-fun tmp22_7 () Value :no_dependence)
(declare-fun tmp22_8 () Value :no_dependence)
(declare-fun tmp22_9 () Value :no_dependence)
(declare-fun tmp22_10 () Value :no_dependence)
(declare-fun tmp22_11 () Value :no_dependence)
(declare-fun tmp22_12 () Value :no_dependence)

(declare-fun tmp11_0_no_L1 () Value :no_dependence)
(declare-fun tmp11_1_no_L1 () Value :no_dependence)
(declare-fun tmp11_2_no_L1 () Value :no_dependence)
(declare-fun tmp11_3_no_L1 () Value :no_dependence)
(declare-fun tmp11_4_no_L1 () Value :no_dependence)
(declare-fun tmp11_5_no_L1 () Value :no_dependence)
(declare-fun tmp11_6_no_L1 () Value :no_dependence)
(declare-fun tmp11_7_no_L1 () Value :no_dependence)
(declare-fun tmp11_8_no_L1 () Value :no_dependence)
(declare-fun tmp11_9_no_L1 () Value :no_dependence)
(declare-fun tmp11_10_no_L1 () Value :no_dependence)
(declare-fun tmp11_11_no_L1 () Value :no_dependence)
(declare-fun tmp11_12_no_L1 () Value :no_dependence)

(declare-fun tmp12_0_no_L1 () Value :no_dependence)
(declare-fun tmp12_1_no_L1 () Value :no_dependence)
(declare-fun tmp12_2_no_L1 () Value :no_dependence)
(declare-fun tmp12_3_no_L1 () Value :no_dependence)
(declare-fun tmp12_4_no_L1 () Value :no_dependence)
(declare-fun tmp12_5_no_L1 () Value :no_dependence)
(declare-fun tmp12_6_no_L1 () Value :no_dependence)
(declare-fun tmp12_7_no_L1 () Value :no_dependence)
(declare-fun tmp12_8_no_L1 () Value :no_dependence)
(declare-fun tmp12_9_no_L1 () Value :no_dependence)
(declare-fun tmp12_10_no_L1 () Value :no_dependence)
(declare-fun tmp12_11_no_L1 () Value :no_dependence)
(declare-fun tmp12_12_no_L1 () Value :no_dependence)

(declare-fun tmp21_0_no_L1 () Value :no_dependence)
(declare-fun tmp21_1_no_L1 () Value :no_dependence)
(declare-fun tmp21_2_no_L1 () Value :no_dependence)
(declare-fun tmp21_3_no_L1 () Value :no_dependence)
(declare-fun tmp21_4_no_L1 () Value :no_dependence)
(declare-fun tmp21_5_no_L1 () Value :no_dependence)
(declare-fun tmp21_6_no_L1 () Value :no_dependence)
(declare-fun tmp21_7_no_L1 () Value :no_dependence)
(declare-fun tmp21_8_no_L1 () Value :no_dependence)
(declare-fun tmp21_9_no_L1 () Value :no_dependence)
(declare-fun tmp21_10_no_L1 () Value :no_dependence)
(declare-fun tmp21_11_no_L1 () Value :no_dependence)
(declare-fun tmp21_12_no_L1 () Value :no_dependence)

(declare-fun tmp22_0_no_L1 () Value :no_dependence)
(declare-fun tmp22_1_no_L1 () Value :no_dependence)
(declare-fun tmp22_2_no_L1 () Value :no_dependence)
(declare-fun tmp22_3_no_L1 () Value :no_dependence)
(declare-fun tmp22_4_no_L1 () Value :no_dependence)
(declare-fun tmp22_5_no_L1 () Value :no_dependence)
(declare-fun tmp22_6_no_L1 () Value :no_dependence)
(declare-fun tmp22_7_no_L1 () Value :no_dependence)
(declare-fun tmp22_8_no_L1 () Value :no_dependence)
(declare-fun tmp22_9_no_L1 () Value :no_dependence)
(declare-fun tmp22_10_no_L1 () Value :no_dependence)
(declare-fun tmp22_11_no_L1 () Value :no_dependence)
(declare-fun tmp22_12_no_L1 () Value :no_dependence)

(declare-fun tmp11_0_no_L2 () Value :no_dependence)
(declare-fun tmp11_1_no_L2 () Value :no_dependence)
(declare-fun tmp11_2_no_L2 () Value :no_dependence)
(declare-fun tmp11_3_no_L2 () Value :no_dependence)
(declare-fun tmp11_4_no_L2 () Value :no_dependence)
(declare-fun tmp11_5_no_L2 () Value :no_dependence)
(declare-fun tmp11_6_no_L2 () Value :no_dependence)
(declare-fun tmp11_7_no_L2 () Value :no_dependence)
(declare-fun tmp11_8_no_L2 () Value :no_dependence)
(declare-fun tmp11_9_no_L2 () Value :no_dependence)
(declare-fun tmp11_10_no_L2 () Value :no_dependence)
(declare-fun tmp11_11_no_L2 () Value :no_dependence)
(declare-fun tmp11_12_no_L2 () Value :no_dependence)

(declare-fun tmp12_0_no_L2 () Value :no_dependence)
(declare-fun tmp12_1_no_L2 () Value :no_dependence)
(declare-fun tmp12_2_no_L2 () Value :no_dependence)
(declare-fun tmp12_3_no_L2 () Value :no_dependence)
(declare-fun tmp12_4_no_L2 () Value :no_dependence)
(declare-fun tmp12_5_no_L2 () Value :no_dependence)
(declare-fun tmp12_6_no_L2 () Value :no_dependence)
(declare-fun tmp12_7_no_L2 () Value :no_dependence)
(declare-fun tmp12_8_no_L2 () Value :no_dependence)
(declare-fun tmp12_9_no_L2 () Value :no_dependence)
(declare-fun tmp12_10_no_L2 () Value :no_dependence)
(declare-fun tmp12_11_no_L2 () Value :no_dependence)
(declare-fun tmp12_12_no_L2 () Value :no_dependence)

(declare-fun tmp21_0_no_L2 () Value :no_dependence)
(declare-fun tmp21_1_no_L2 () Value :no_dependence)
(declare-fun tmp21_2_no_L2 () Value :no_dependence)
(declare-fun tmp21_3_no_L2 () Value :no_dependence)
(declare-fun tmp21_4_no_L2 () Value :no_dependence)
(declare-fun tmp21_5_no_L2 () Value :no_dependence)
(declare-fun tmp21_6_no_L2 () Value :no_dependence)
(declare-fun tmp21_7_no_L2 () Value :no_dependence)
(declare-fun tmp21_8_no_L2 () Value :no_dependence)
(declare-fun tmp21_9_no_L2 () Value :no_dependence)
(declare-fun tmp21_10_no_L2 () Value :no_dependence)
(declare-fun tmp21_11_no_L2 () Value :no_dependence)
(declare-fun tmp21_12_no_L2 () Value :no_dependence)

(declare-fun tmp22_0_no_L2 () Value :no_dependence)
(declare-fun tmp22_1_no_L2 () Value :no_dependence)
(declare-fun tmp22_2_no_L2 () Value :no_dependence)
(declare-fun tmp22_3_no_L2 () Value :no_dependence)
(declare-fun tmp22_4_no_L2 () Value :no_dependence)
(declare-fun tmp22_5_no_L2 () Value :no_dependence)
(declare-fun tmp22_6_no_L2 () Value :no_dependence)
(declare-fun tmp22_7_no_L2 () Value :no_dependence)
(declare-fun tmp22_8_no_L2 () Value :no_dependence)
(declare-fun tmp22_9_no_L2 () Value :no_dependence)
(declare-fun tmp22_10_no_L2 () Value :no_dependence)
(declare-fun tmp22_11_no_L2 () Value :no_dependence)
(declare-fun tmp22_12_no_L2 () Value :no_dependence)

(declare-fun idx1 () Value)
(declare-fun idx2 () Value)
(declare-fun idx3 () Value)
(declare-fun idx4 () Value)

(declare-fun free       () Value )
(declare-fun hold_by_t1 () Value )
(declare-fun hold_by_t2 () Value )

(declare-fun lock_1  () Value :no_dependence)
(declare-fun lock_2  () Value :no_dependence)
(declare-fun lock_3  () Value :no_dependence)
(declare-fun lock_4  () Value :no_dependence)
(declare-fun lock_5  () Value :no_dependence)
(declare-fun lock_6  () Value :no_dependence)
(declare-fun lock_7  () Value :no_dependence)
(declare-fun lock_8  () Value :no_dependence)
(declare-fun lock_9  () Value :no_dependence)
(declare-fun lock_10  () Value :no_dependence)
(declare-fun lock_11  () Value :no_dependence)
(declare-fun lock_12  () Value :no_dependence)

(declare-fun lock_1_no_L1  () Value :no_dependence)
(declare-fun lock_2_no_L1  () Value :no_dependence)
(declare-fun lock_3_no_L1  () Value :no_dependence)
(declare-fun lock_4_no_L1  () Value :no_dependence)
(declare-fun lock_5_no_L1  () Value :no_dependence)
(declare-fun lock_6_no_L1  () Value :no_dependence)
(declare-fun lock_7_no_L1  () Value :no_dependence)
(declare-fun lock_8_no_L1  () Value :no_dependence)
(declare-fun lock_9_no_L1  () Value :no_dependence)
(declare-fun lock_10_no_L1  () Value :no_dependence)
(declare-fun lock_11_no_L1  () Value :no_dependence)
(declare-fun lock_12_no_L1  () Value :no_dependence)

(declare-fun lock_1_no_L2  () Value :no_dependence)
(declare-fun lock_2_no_L2 () Value :no_dependence)
(declare-fun lock_3_no_L2  () Value :no_dependence)
(declare-fun lock_4_no_L2  () Value :no_dependence)
(declare-fun lock_5_no_L2  () Value :no_dependence)
(declare-fun lock_6_no_L2  () Value :no_dependence)
(declare-fun lock_7_no_L2  () Value :no_dependence)
(declare-fun lock_8_no_L2  () Value :no_dependence)
(declare-fun lock_9_no_L2  () Value :no_dependence)
(declare-fun lock_10_no_L2  () Value :no_dependence)
(declare-fun lock_11_no_L2  () Value :no_dependence)
(declare-fun lock_12_no_L2  () Value :no_dependence)

(declare-fun c_lock1 () Control)    
(declare-fun c_lock2 () Control) 
(declare-fun c_unlock1 () Control) 
(declare-fun c_unlock2 () Control)

(declare-fun tmp_1_s_t1t2 () Value :no_dependence)
(declare-fun tmp_2_s_t1t2 () Value :no_dependence)
(declare-fun tmp_3_s_t1t2 () Value :no_dependence)
(declare-fun tmp_4_s_t1t2 () Value :no_dependence)

(declare-fun tmp_1_s_t2t1 () Value :no_dependence)
(declare-fun tmp_2_s_t2t1 () Value :no_dependence)
(declare-fun tmp_3_s_t2t1 () Value :no_dependence)
(declare-fun tmp_4_s_t2t1 () Value :no_dependence)

(declare-fun MEM_1_s_t1t2 () (Array Value Value)  :no_dependence)
(declare-fun MEM_2_s_t1t2 () (Array Value Value)  :no_dependence)
(declare-fun MEM_3_s_t1t2 () (Array Value Value)  :no_dependence)
(declare-fun MEM_4_s_t1t2 () (Array Value Value)  :no_dependence)

(declare-fun MEM_1_s_t2t1 () (Array Value Value)  :no_dependence)
(declare-fun MEM_2_s_t2t1 () (Array Value Value)  :no_dependence)
(declare-fun MEM_3_s_t2t1 () (Array Value Value)  :no_dependence)
(declare-fun MEM_4_s_t2t1 () (Array Value Value)  :no_dependence)

(declare-fun op  (Value) Value)

(define-fun distinct1 ( (ZERO Value) (ONE Value) (TWO Value) (THREE Value) 
                        (FOUR Value) (FIVE Value) (SIX Value)) Bool    
  ( and  
    (not (= ZERO ONE))
    (not (= ZERO TWO))
    (not (= ZERO THREE))
    (not (= ZERO FOUR))
    (not (= ZERO FIVE))
    (not (= ZERO SIX))

    (not (= ONE TWO))
    (not (= ONE THREE))
    (not (= ONE FOUR))
    (not (= ONE FIVE))
    (not (= ONE SIX))
  
    (not (= TWO THREE))
    (not (= TWO FOUR))
    (not (= TWO FIVE))
    (not (= TWO SIX))
    
    (not (= THREE FOUR))
    (not (= THREE FIVE))
    (not (= THREE SIX))
  
    (not (= FOUR FIVE))
    (not (= FOUR SIX))
  
    (not (= FIVE SIX))         
  )    
)

(define-fun distinct2  ( (a Value) (b Value) (c Value)) Bool
  ( and
     (not (= a b))
     (not (= a c))
     (not (= b c))
  )  
)

(define-fun select_index ((index Value) (a Value) (b Value) (c Value) (d Value))
Bool    
  ( or  
      (and (= index a) (not (= index b)) (not (= index c)) (not (= index d)))
      (and (= index b) (not (= index a)) (not (= index c)) (not (= index d)))
      (and (= index c) (not (= index a)) (not (= index b)) (not (= index d)))
      (and (= index d) (not (= index a)) (not (= index b)) (not (= index c)))      
  )    
)

 ;one step in T1||T2
(define-fun step  ((pc1 Value)(pc1_n Value)(pc2 Value)(pc2_n Value)(MEM (Array Value Value))(MEM_n (Array Value Value))
                   (tmp11 Value)(tmp11_n Value)(tmp12 Value)(tmp12_n Value) (tmp21 Value)(tmp21_n Value)(tmp22 Value)(tmp22_n Value)
                   (idx1 Value)(idx2 Value)(idx3 Value)(idx4 Value)(lock Value)(lock_n Value)
                   (c_lock1 Bool)(c_lock2 Bool)(c_unlock1 Bool)(c_unlock2 Bool)) Bool 
                   
  (or
      (and
        (=> (= pc1 ZERO) (ite c_lock1 
                              (ite (= lock hold_by_t2) 
                                    (and  (= pc1_n pc1)(= pc2_n pc2)(= tmp11_n tmp11)(= tmp12_n tmp12) (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM) (= lock_n lock))
                                    (and  (= pc1_n ONE)(= pc2_n pc2)(= tmp11_n tmp11)(= tmp12_n tmp12) (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM) (= lock_n hold_by_t1)))
                              (and  (= pc1_n ONE)(= pc2_n pc2)(= tmp11_n tmp11)(= tmp12_n tmp12) (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM) (= lock_n lock))
                          ) 
        ) 
        (=> (= pc1 ONE)  (and  (= pc1_n TWO)    (= pc2_n pc2)(= tmp11_n (op (select MEM idx1)))(= tmp12_n tmp12)                  (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM)                   (= lock_n lock)) ) 
        (=> (= pc1 TWO)  (and  (= pc1_n THREE)  (= pc2_n pc2)(= tmp11_n tmp11)                 (= tmp12_n (op (select MEM idx2))) (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM)                   (= lock_n lock)) )
        (=> (= pc1 THREE)(and  (= pc1_n FOUR)   (= pc2_n pc2)(= tmp11_n tmp11)                 (= tmp12_n tmp12)                  (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n (store MEM idx1 tmp12)) (= lock_n lock)) )
        (=> (= pc1 FOUR) (and  (= pc1_n FIVE)   (= pc2_n pc2)(= tmp11_n tmp11)                 (= tmp12_n tmp12)                  (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n (store MEM idx2 tmp11)) (= lock_n lock)) )
        
        (=> (= pc1 FIVE) (and  (ite c_unlock1 (= lock_n free) (= lock_n lock)) 
                              (and (= pc1_n SIX)   (= pc2_n pc2)(= tmp11_n tmp11)                 (= tmp12_n tmp12)                 (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM)) ) )
      
        (=> (= pc1 SIX)  (and  (= pc1_n pc1)(= pc2_n pc2)(= tmp11_n tmp11)(= tmp12_n tmp12) (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM) (= lock_n lock)))
        ;no unnecessary unlocks
        (=> (= lock free) (not c_unlock1))         
      )                                                                                                                                                   
      (and
        (=> (= pc2 ZERO) (ite c_lock2
                              (ite (= lock hold_by_t1) 
                                    (and  (= pc1_n pc1)(= pc2_n pc2)(= tmp11_n tmp11)(= tmp12_n tmp12) (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM) (= lock_n lock))
                                    (and  (= pc2_n ONE)(= pc1_n pc1)(= tmp11_n tmp11)(= tmp12_n tmp12) (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM) (= lock_n hold_by_t2)))
                              (and  (= pc2_n ONE)(= pc1_n pc1)(= tmp11_n tmp11)(= tmp12_n tmp12) (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM) (= lock_n lock))
                          ) 
        ) 
        (=> (= pc2 ONE)  (and  (= pc2_n TWO)    (= pc1_n pc1)(= tmp21_n (op (select MEM idx3))) (= tmp22_n tmp22)                 (= tmp12_n tmp12) (= tmp11_n tmp11) (= MEM_n MEM)                   (= lock_n lock)) ) 
        (=> (= pc2 TWO)  (and  (= pc2_n THREE)  (= pc1_n pc1)(= tmp21_n tmp21)                  (= tmp22_n (op (select MEM idx4)))    (= tmp12_n tmp12) (= tmp11_n tmp11) (= MEM_n MEM)                   (= lock_n lock)) )
        (=> (= pc2 THREE)(and  (= pc2_n FOUR)   (= pc1_n pc1)(= tmp21_n tmp21)                  (= tmp22_n tmp22)                 (= tmp12_n tmp12) (= tmp11_n tmp11) (= MEM_n(store MEM idx3 tmp22)) (= lock_n lock)) )
        (=> (= pc2 FOUR) (and  (= pc2_n FIVE)   (= pc1_n pc1)(= tmp21_n tmp21)                  (= tmp22_n tmp22)                 (= tmp12_n tmp12) (= tmp11_n tmp11) (= MEM_n(store MEM idx4 tmp21)) (= lock_n lock)) )
        
        (=> (= pc2 FIVE) (and  (ite c_unlock2 (= lock_n free) (= lock_n lock)) 
                              (and (= pc2_n SIX)   (= pc1_n pc1)(= tmp21_n tmp21)                 (= tmp22_n tmp22)                 (= tmp12_n tmp12) (= tmp11_n tmp11) (= MEM_n MEM)) ) )
      
        (=> (= pc2 SIX)  (and  (= pc1_n pc1)(= pc2_n pc2)(= tmp11_n tmp11)(= tmp12_n tmp12) (= tmp21_n tmp21) (= tmp22_n tmp22) (= MEM_n MEM) (= lock_n lock)))
        ;no unnecessary unlocks
        (=> (= lock free) (not c_unlock2))         
      )
  )                
)         

;T1||T2 
(define-fun parallel 
 ( (pc1_0 Value) (pc1_1 Value) (pc1_2 Value) (pc1_3  Value) (pc1_4 Value) (pc1_5 Value) (pc1_6 Value) (pc1_7 Value) (pc1_8 Value) (pc1_9 Value) (pc1_10  Value) (pc1_11 Value) (pc1_12 Value) 
   (pc2_0 Value) (pc2_1 Value) (pc2_2 Value) (pc2_3  Value) (pc2_4 Value) (pc2_5 Value) (pc2_6 Value) (pc2_7 Value) (pc2_8 Value) (pc2_9 Value) (pc2_10  Value) (pc2_11 Value) (pc2_12 Value)
   (MEM (Array Value Value))(MEM_1 (Array Value Value))(MEM_2 (Array Value Value))(MEM_3 (Array Value Value))(MEM_4 (Array Value Value))(MEM_5 (Array Value Value))(MEM_6 (Array Value Value))(MEM_7 (Array Value Value))(MEM_8 (Array Value Value))(MEM_9 (Array Value Value))(MEM_10 (Array Value Value))(MEM_11 (Array Value Value))(MEM_12(Array Value Value))
   (tmp11_0  Value) (tmp11_1  Value) (tmp11_2  Value) (tmp11_3  Value) (tmp11_4  Value) (tmp11_5  Value) (tmp11_6  Value) (tmp11_7  Value) (tmp11_8  Value) (tmp11_9  Value) (tmp11_10  Value) (tmp11_11  Value) (tmp11_12  Value) 
   (tmp12_0  Value) (tmp12_1  Value) (tmp12_2  Value) (tmp12_3  Value) (tmp12_4  Value) (tmp12_5  Value) (tmp12_6  Value) (tmp12_7  Value) (tmp12_8  Value) (tmp12_9  Value) (tmp12_10  Value) (tmp12_11  Value) (tmp12_12  Value)
   (tmp21_0  Value) (tmp21_1  Value) (tmp21_2  Value) (tmp21_3  Value) (tmp21_4  Value) (tmp21_5  Value) (tmp21_6  Value) (tmp21_7  Value) (tmp21_8  Value) (tmp21_9  Value) (tmp21_10  Value) (tmp21_11  Value) (tmp21_12  Value)
   (tmp22_0  Value) (tmp22_1  Value) (tmp22_2  Value) (tmp22_3  Value) (tmp22_4  Value) (tmp22_5  Value) (tmp22_6  Value) (tmp22_7  Value) (tmp22_8  Value) (tmp22_9  Value) (tmp22_10  Value) (tmp22_11  Value) (tmp22_12  Value) 
   (idx1 Value)(idx2 Value) (idx3 Value) (idx4 Value)
   (lock_0 Value)(lock_1 Value)(lock_2 Value)(lock_3 Value)(lock_4 Value)(lock_5 Value)(lock_6 Value)(lock_7 Value)(lock_8 Value)(lock_9 Value)(lock_10 Value)(lock_11 Value)(lock_12 Value)
   (c_lock1 Bool)(c_lock2 Bool)(c_unlock1 Bool)(c_unlock2 Bool) 
) Bool
  (and
    (step pc1_0 pc1_1 pc2_0 pc2_1 MEM   MEM_1 tmp11_0 tmp11_1 tmp12_0 tmp12_1 tmp21_0 tmp21_1 tmp22_0 tmp22_1 idx1 idx2 idx3 idx4 lock_0 lock_1 c_lock1 c_lock2 c_unlock1 c_unlock2)
    (step pc1_1 pc1_2 pc2_1 pc2_2 MEM_1 MEM_2 tmp11_1 tmp11_2 tmp12_1 tmp12_2 tmp21_1 tmp21_2 tmp22_1 tmp22_2 idx1 idx2 idx3 idx4 lock_1 lock_2 c_lock1 c_lock2 c_unlock1 c_unlock2)
    (step pc1_2 pc1_3 pc2_2 pc2_3 MEM_2 MEM_3 tmp11_2 tmp11_3 tmp12_2 tmp12_3 tmp21_2 tmp21_3 tmp22_2 tmp22_3 idx1 idx2 idx3 idx4 lock_2 lock_3 c_lock1 c_lock2 c_unlock1 c_unlock2)
    (step pc1_3 pc1_4 pc2_3 pc2_4 MEM_3 MEM_4 tmp11_3 tmp11_4 tmp12_3 tmp12_4 tmp21_3 tmp21_4 tmp22_3 tmp22_4 idx1 idx2 idx3 idx4 lock_3 lock_4 c_lock1 c_lock2 c_unlock1 c_unlock2)
    (step pc1_4 pc1_5 pc2_4 pc2_5 MEM_4 MEM_5 tmp11_4 tmp11_5 tmp12_4 tmp12_5 tmp21_4 tmp21_5 tmp22_4 tmp22_5 idx1 idx2 idx3 idx4 lock_4 lock_5 c_lock1 c_lock2 c_unlock1 c_unlock2)
    (step pc1_5 pc1_6 pc2_5 pc2_6 MEM_5 MEM_6 tmp11_5 tmp11_6 tmp12_5 tmp12_6 tmp21_5 tmp21_6 tmp22_5 tmp22_6 idx1 idx2 idx3 idx4 lock_5 lock_6 c_lock1 c_lock2 c_unlock1 c_unlock2)
        
    (step pc1_6  pc1_7  pc2_6  pc2_7  MEM_6  MEM_7  tmp11_6  tmp11_7  tmp12_6  tmp12_7  tmp21_6  tmp21_7  tmp22_6  tmp22_7  idx1 idx2 idx3 idx4 lock_6  lock_7  c_lock1 c_lock2 c_unlock1 c_unlock2)
    (step pc1_7  pc1_8  pc2_7  pc2_8  MEM_7  MEM_8  tmp11_7  tmp11_8  tmp12_7  tmp12_8  tmp21_7  tmp21_8  tmp22_7  tmp22_8  idx1 idx2 idx3 idx4 lock_7  lock_8  c_lock1 c_lock2 c_unlock1 c_unlock2)
    (step pc1_8  pc1_9  pc2_8  pc2_9  MEM_8  MEM_9  tmp11_8  tmp11_9  tmp12_8  tmp12_9  tmp21_8  tmp21_9  tmp22_8  tmp22_9  idx1 idx2 idx3 idx4 lock_8  lock_9  c_lock1 c_lock2 c_unlock1 c_unlock2)
    (step pc1_9  pc1_10 pc2_9  pc2_10 MEM_9  MEM_10 tmp11_9  tmp11_10 tmp12_9  tmp12_10 tmp21_9  tmp21_10 tmp22_9  tmp22_10 idx1 idx2 idx3 idx4 lock_9  lock_10 c_lock1 c_lock2 c_unlock1 c_unlock2) 
    (step pc1_10 pc1_11 pc2_10 pc2_11 MEM_10 MEM_11 tmp11_10 tmp11_11 tmp12_10 tmp12_11 tmp21_10 tmp21_11 tmp22_10 tmp22_11 idx1 idx2 idx3 idx4 lock_10 lock_11 c_lock1 c_lock2 c_unlock1 c_unlock2)
    (step pc1_11 pc1_12 pc2_11 pc2_12 MEM_11 MEM_12 tmp11_11 tmp11_12 tmp12_11 tmp12_12 tmp21_11 tmp21_12 tmp22_11 tmp22_12 idx1 idx2 idx3 idx4 lock_11 lock_12 c_lock1 c_lock2 c_unlock1 c_unlock2)                       
  )     
)          

;(T1.T2)
(define-fun sequential_t1t2 ( (tmp_1_s Value) (tmp_2_s Value) (tmp_3_s Value) (tmp_4_s Value)(MEM (Array Value Value)) (MEM_1_s (Array Value Value)) (MEM_2_s (Array Value Value)) (MEM_3_s (Array Value Value)) (MEM_4_s (Array Value Value)) 
                        (idx1 Value) (idx2 Value) (idx3 Value) (idx4 Value) )  Bool  
  (and  
      (= tmp_1_s  (op (select MEM idx1)))
      (= tmp_2_s  (op (select MEM idx2)))
      (= MEM_1_s (store MEM idx1 tmp_2_s))
      (= MEM_2_s (store MEM_1_s idx2 tmp_1_s))
      
      (= tmp_3_s  (op (select MEM_2_s idx3)))
      (= tmp_4_s  (op (select MEM_2_s idx4)))
      (= MEM_3_s (store MEM_2_s idx3 tmp_4_s))
      (= MEM_4_s (store MEM_3_s idx4 tmp_3_s))        
  )    
)

;(T2.T1)
(define-fun sequential_t2t1 ( (tmp_1_s Value) (tmp_2_s Value) (tmp_3_s Value) (tmp_4_s Value)(MEM (Array Value Value)) (MEM_1_s (Array Value Value)) (MEM_2_s (Array Value Value)) (MEM_3_s (Array Value Value)) (MEM_4_s (Array Value Value)) 
                        (idx1 Value) (idx2 Value) (idx3 Value) (idx4 Value) )  Bool  
  (and  
      (= tmp_1_s  (op (select MEM idx3)))
      (= tmp_2_s  (op (select MEM idx4)))
      (= MEM_1_s  (store MEM idx3 tmp_2_s))
      (= MEM_2_s  (store MEM_1_s idx4 tmp_1_s))
      
      (= tmp_3_s  (op (select MEM_2_s idx1)))
      (= tmp_4_s  (op (select MEM_2_s idx2)))
      (= MEM_3_s  (store MEM_2_s idx1 tmp_4_s))
      (= MEM_4_s  (store MEM_3_s idx2 tmp_3_s))        
  )    
)

;T1||T2 AND T1.T2 -> MEM_4_s_t1t2 = MEM_12 
(define-fun phi_t1t2 
 ( (pc1_0 Value) (pc1_1 Value) (pc1_2 Value) (pc1_3  Value) (pc1_4 Value) (pc1_5 Value) (pc1_6 Value) (pc1_7 Value) (pc1_8 Value) (pc1_9 Value) (pc1_10  Value) (pc1_11 Value) (pc1_12 Value) 
   (pc2_0 Value) (pc2_1 Value) (pc2_2 Value) (pc2_3  Value) (pc2_4 Value) (pc2_5 Value) (pc2_6 Value) (pc2_7 Value) (pc2_8 Value) (pc2_9 Value) (pc2_10  Value) (pc2_11 Value) (pc2_12 Value)
   (MEM (Array Value Value))(MEM_1 (Array Value Value))(MEM_2 (Array Value Value))(MEM_3 (Array Value Value))(MEM_4 (Array Value Value))(MEM_5 (Array Value Value))(MEM_6 (Array Value Value))(MEM_7 (Array Value Value))(MEM_8 (Array Value Value))(MEM_9 (Array Value Value))(MEM_10 (Array Value Value))(MEM_11 (Array Value Value))(MEM_12(Array Value Value))
   (tmp11_0  Value) (tmp11_1  Value) (tmp11_2  Value) (tmp11_3  Value) (tmp11_4  Value) (tmp11_5  Value) (tmp11_6  Value) (tmp11_7  Value) (tmp11_8  Value) (tmp11_9  Value) (tmp11_10  Value) (tmp11_11  Value) (tmp11_12  Value) 
   (tmp12_0  Value) (tmp12_1  Value) (tmp12_2  Value) (tmp12_3  Value) (tmp12_4  Value) (tmp12_5  Value) (tmp12_6  Value) (tmp12_7  Value) (tmp12_8  Value) (tmp12_9  Value) (tmp12_10  Value) (tmp12_11  Value) (tmp12_12  Value)
   (tmp21_0  Value) (tmp21_1  Value) (tmp21_2  Value) (tmp21_3  Value) (tmp21_4  Value) (tmp21_5  Value) (tmp21_6  Value) (tmp21_7  Value) (tmp21_8  Value) (tmp21_9  Value) (tmp21_10  Value) (tmp21_11  Value) (tmp21_12  Value)
   (tmp22_0  Value) (tmp22_1  Value) (tmp22_2  Value) (tmp22_3  Value) (tmp22_4  Value) (tmp22_5  Value) (tmp22_6  Value) (tmp22_7  Value) (tmp22_8  Value) (tmp22_9  Value) (tmp22_10  Value) (tmp22_11  Value) (tmp22_12  Value) 
   (idx1 Value)(idx2 Value) (idx3 Value) (idx4 Value)
   (lock_0 Value)(lock_1 Value)(lock_2 Value)(lock_3 Value)(lock_4 Value)(lock_5 Value)(lock_6 Value)(lock_7 Value)(lock_8 Value)(lock_9 Value)(lock_10 Value)(lock_11 Value)(lock_12 Value)
   (c_lock1 Bool)(c_lock2 Bool)(c_unlock1 Bool)(c_unlock2 Bool)  
   
   (tmp_1_s_t1t2 Value) (tmp_2_s_t1t2 Value) (tmp_3_s_t1t2 Value) (tmp_4_s_t1t2 Value) (MEM_1_s_t1t2 (Array Value Value))(MEM_2_s_t1t2 (Array Value Value))(MEM_3_s_t1t2 (Array Value Value))(MEM_4_s_t1t2(Array Value Value))  
 ) Bool
 (=> 
  (and
      (parallel
        ZERO pc1_1	pc1_2	pc1_3	pc1_4	pc1_5	pc1_6	pc1_7	pc1_8	pc1_9	pc1_10	pc1_11	pc1_12
        ZERO pc2_1	pc2_2	pc2_3	pc2_4	pc2_5	pc2_6	pc2_7	pc2_8	pc2_9	pc2_10	pc2_11	pc2_12
        MEM	MEM_1	MEM_2	MEM_3	MEM_4	MEM_5	MEM_6	MEM_7	MEM_8	MEM_9	MEM_10	MEM_11	MEM_12
        tmp11_0	tmp11_1	tmp11_2	tmp11_3	tmp11_4	tmp11_5	tmp11_6	tmp11_7	tmp11_8	tmp11_9	tmp11_10	tmp11_11	tmp11_12
        tmp12_0	tmp12_1	tmp12_2	tmp12_3	tmp12_4	tmp12_5	tmp12_6	tmp12_7	tmp12_8	tmp12_9	tmp12_10	tmp12_11	tmp12_12
        tmp21_0	tmp21_1	tmp21_2	tmp21_3	tmp21_4	tmp21_5	tmp21_6	tmp21_7	tmp21_8	tmp21_9	tmp21_10	tmp21_11	tmp21_12
        tmp22_0	tmp22_1	tmp22_2	tmp22_3	tmp22_4	tmp22_5	tmp22_6	tmp22_7	tmp22_8	tmp22_9	tmp22_10	tmp22_11	tmp22_12
        idx1 idx2 idx3 idx4
        free	lock_1	lock_2	lock_3	lock_4	lock_5	lock_6	lock_7	lock_8	lock_9	lock_10	lock_11	lock_12
        c_lock1 c_lock2 c_unlock1 c_unlock2            
      )
      ( sequential_t1t2 tmp_1_s_t1t2 tmp_2_s_t1t2 tmp_3_s_t1t2 tmp_4_s_t1t2 MEM MEM_1_s_t1t2 MEM_2_s_t1t2 MEM_3_s_t1t2 MEM_4_s_t1t2 idx1 idx2 idx3 idx4    )
      (= pc1_12 SIX)
      (= pc2_12 SIX)          
  )
  (
     = MEM_4_s_t1t2 MEM_12
  )     
 )
)

;T1||T2 AND T1.T2 -> MEM_4_s_t2t1 = MEM_12 
(define-fun phi_t2t1 
 ( (pc1_0 Value) (pc1_1 Value) (pc1_2 Value) (pc1_3  Value) (pc1_4 Value) (pc1_5 Value) (pc1_6 Value) (pc1_7 Value) (pc1_8 Value) (pc1_9 Value) (pc1_10  Value) (pc1_11 Value) (pc1_12 Value) 
   (pc2_0 Value) (pc2_1 Value) (pc2_2 Value) (pc2_3  Value) (pc2_4 Value) (pc2_5 Value) (pc2_6 Value) (pc2_7 Value) (pc2_8 Value) (pc2_9 Value) (pc2_10  Value) (pc2_11 Value) (pc2_12 Value)
   (MEM (Array Value Value))(MEM_1 (Array Value Value))(MEM_2 (Array Value Value))(MEM_3 (Array Value Value))(MEM_4 (Array Value Value))(MEM_5 (Array Value Value))(MEM_6 (Array Value Value))(MEM_7 (Array Value Value))(MEM_8 (Array Value Value))(MEM_9 (Array Value Value))(MEM_10 (Array Value Value))(MEM_11 (Array Value Value))(MEM_12(Array Value Value))
   (tmp11_0  Value) (tmp11_1  Value) (tmp11_2  Value) (tmp11_3  Value) (tmp11_4  Value) (tmp11_5  Value) (tmp11_6  Value) (tmp11_7  Value) (tmp11_8  Value) (tmp11_9  Value) (tmp11_10  Value) (tmp11_11  Value) (tmp11_12  Value) 
   (tmp12_0  Value) (tmp12_1  Value) (tmp12_2  Value) (tmp12_3  Value) (tmp12_4  Value) (tmp12_5  Value) (tmp12_6  Value) (tmp12_7  Value) (tmp12_8  Value) (tmp12_9  Value) (tmp12_10  Value) (tmp12_11  Value) (tmp12_12  Value)
   (tmp21_0  Value) (tmp21_1  Value) (tmp21_2  Value) (tmp21_3  Value) (tmp21_4  Value) (tmp21_5  Value) (tmp21_6  Value) (tmp21_7  Value) (tmp21_8  Value) (tmp21_9  Value) (tmp21_10  Value) (tmp21_11  Value) (tmp21_12  Value)
   (tmp22_0  Value) (tmp22_1  Value) (tmp22_2  Value) (tmp22_3  Value) (tmp22_4  Value) (tmp22_5  Value) (tmp22_6  Value) (tmp22_7  Value) (tmp22_8  Value) (tmp22_9  Value) (tmp22_10  Value) (tmp22_11  Value) (tmp22_12  Value) 
   (idx1 Value)(idx2 Value) (idx3 Value) (idx4 Value)
   (lock_0 Value)(lock_1 Value)(lock_2 Value)(lock_3 Value)(lock_4 Value)(lock_5 Value)(lock_6 Value)(lock_7 Value)(lock_8 Value)(lock_9 Value)(lock_10 Value)(lock_11 Value)(lock_12 Value)
   (c_lock1 Bool)(c_lock2 Bool)(c_unlock1 Bool)(c_unlock2 Bool)  
   
   (tmp_1_s_t2t1 Value) (tmp_2_s_t2t1 Value) (tmp_3_s_t2t1 Value) (tmp_4_s_t2t1 Value) (MEM_1_s_t2t1 (Array Value Value))(MEM_2_s_t2t1 (Array Value Value))(MEM_3_s_t2t1 (Array Value Value))(MEM_4_s_t2t1(Array Value Value))  
 ) Bool
 (=> 
  (and
      (parallel
        ZERO pc1_1	pc1_2	pc1_3	pc1_4	pc1_5	pc1_6	pc1_7	pc1_8	pc1_9	pc1_10	pc1_11	pc1_12
        ZERO pc2_1	pc2_2	pc2_3	pc2_4	pc2_5	pc2_6	pc2_7	pc2_8	pc2_9	pc2_10	pc2_11	pc2_12
        MEM	MEM_1	MEM_2	MEM_3	MEM_4	MEM_5	MEM_6	MEM_7	MEM_8	MEM_9	MEM_10	MEM_11	MEM_12
        tmp11_0	tmp11_1	tmp11_2	tmp11_3	tmp11_4	tmp11_5	tmp11_6	tmp11_7	tmp11_8	tmp11_9	tmp11_10	tmp11_11	tmp11_12
        tmp12_0	tmp12_1	tmp12_2	tmp12_3	tmp12_4	tmp12_5	tmp12_6	tmp12_7	tmp12_8	tmp12_9	tmp12_10	tmp12_11	tmp12_12
        tmp21_0	tmp21_1	tmp21_2	tmp21_3	tmp21_4	tmp21_5	tmp21_6	tmp21_7	tmp21_8	tmp21_9	tmp21_10	tmp21_11	tmp21_12
        tmp22_0	tmp22_1	tmp22_2	tmp22_3	tmp22_4	tmp22_5	tmp22_6	tmp22_7	tmp22_8	tmp22_9	tmp22_10	tmp22_11	tmp22_12
        idx1 idx2 idx3 idx4
        free	lock_1	lock_2	lock_3	lock_4	lock_5	lock_6	lock_7	lock_8	lock_9	lock_10	lock_11	lock_12  
        c_lock1 c_lock2 c_unlock1 c_unlock2          
      )
      ( sequential_t2t1 tmp_1_s_t2t1 tmp_2_s_t2t1 tmp_3_s_t2t1 tmp_4_s_t2t1 MEM MEM_1_s_t2t1 MEM_2_s_t2t1 MEM_3_s_t2t1 MEM_4_s_t2t1 idx1 idx2 idx3 idx4    )
      (= pc1_12 SIX)
      (= pc2_12 SIX)          
  )
  (
     = MEM_4_s_t2t1 MEM_12  
  )     
 )
)

;T1||T2 AND T1.T2 AND MEM_4_s_t1t2 = MEM_12 
(define-fun psi_t1t2 
 ( (pc1_0 Value) (pc1_1 Value) (pc1_2 Value) (pc1_3  Value) (pc1_4 Value) (pc1_5 Value) (pc1_6 Value) (pc1_7 Value) (pc1_8 Value) (pc1_9 Value) (pc1_10  Value) (pc1_11 Value) (pc1_12 Value) 
   (pc2_0 Value) (pc2_1 Value) (pc2_2 Value) (pc2_3  Value) (pc2_4 Value) (pc2_5 Value) (pc2_6 Value) (pc2_7 Value) (pc2_8 Value) (pc2_9 Value) (pc2_10  Value) (pc2_11 Value) (pc2_12 Value)
   (MEM (Array Value Value))(MEM_1 (Array Value Value))(MEM_2 (Array Value Value))(MEM_3 (Array Value Value))(MEM_4 (Array Value Value))(MEM_5 (Array Value Value))(MEM_6 (Array Value Value))(MEM_7 (Array Value Value))(MEM_8 (Array Value Value))(MEM_9 (Array Value Value))(MEM_10 (Array Value Value))(MEM_11 (Array Value Value))(MEM_12(Array Value Value))
   (tmp11_0  Value) (tmp11_1  Value) (tmp11_2  Value) (tmp11_3  Value) (tmp11_4  Value) (tmp11_5  Value) (tmp11_6  Value) (tmp11_7  Value) (tmp11_8  Value) (tmp11_9  Value) (tmp11_10  Value) (tmp11_11  Value) (tmp11_12  Value) 
   (tmp12_0  Value) (tmp12_1  Value) (tmp12_2  Value) (tmp12_3  Value) (tmp12_4  Value) (tmp12_5  Value) (tmp12_6  Value) (tmp12_7  Value) (tmp12_8  Value) (tmp12_9  Value) (tmp12_10  Value) (tmp12_11  Value) (tmp12_12  Value)
   (tmp21_0  Value) (tmp21_1  Value) (tmp21_2  Value) (tmp21_3  Value) (tmp21_4  Value) (tmp21_5  Value) (tmp21_6  Value) (tmp21_7  Value) (tmp21_8  Value) (tmp21_9  Value) (tmp21_10  Value) (tmp21_11  Value) (tmp21_12  Value)
   (tmp22_0  Value) (tmp22_1  Value) (tmp22_2  Value) (tmp22_3  Value) (tmp22_4  Value) (tmp22_5  Value) (tmp22_6  Value) (tmp22_7  Value) (tmp22_8  Value) (tmp22_9  Value) (tmp22_10  Value) (tmp22_11  Value) (tmp22_12  Value) 
   (idx1 Value)(idx2 Value) (idx3 Value) (idx4 Value)
   (lock_0 Value)(lock_1 Value)(lock_2 Value)(lock_3 Value)(lock_4 Value)(lock_5 Value)(lock_6 Value)(lock_7 Value)(lock_8 Value)(lock_9 Value)(lock_10 Value)(lock_11 Value)(lock_12 Value)
   (c_lock1 Bool)(c_lock2 Bool)(c_unlock1 Bool)(c_unlock2 Bool)  
   
   (tmp_1_s_t1t2 Value) (tmp_2_s_t1t2 Value) (tmp_3_s_t1t2 Value) (tmp_4_s_t1t2 Value) (MEM_1_s_t1t2 (Array Value Value))(MEM_2_s_t1t2 (Array Value Value))(MEM_3_s_t1t2 (Array Value Value))(MEM_4_s_t1t2(Array Value Value))  
 ) Bool
 (=> 
  (and
      (parallel
        ZERO pc1_1	pc1_2	pc1_3	pc1_4	pc1_5	pc1_6	pc1_7	pc1_8	pc1_9	pc1_10	pc1_11	pc1_12
        ZERO pc2_1	pc2_2	pc2_3	pc2_4	pc2_5	pc2_6	pc2_7	pc2_8	pc2_9	pc2_10	pc2_11	pc2_12
        MEM	MEM_1	MEM_2	MEM_3	MEM_4	MEM_5	MEM_6	MEM_7	MEM_8	MEM_9	MEM_10	MEM_11	MEM_12
        tmp11_0	tmp11_1	tmp11_2	tmp11_3	tmp11_4	tmp11_5	tmp11_6	tmp11_7	tmp11_8	tmp11_9	tmp11_10	tmp11_11	tmp11_12
        tmp12_0	tmp12_1	tmp12_2	tmp12_3	tmp12_4	tmp12_5	tmp12_6	tmp12_7	tmp12_8	tmp12_9	tmp12_10	tmp12_11	tmp12_12
        tmp21_0	tmp21_1	tmp21_2	tmp21_3	tmp21_4	tmp21_5	tmp21_6	tmp21_7	tmp21_8	tmp21_9	tmp21_10	tmp21_11	tmp21_12
        tmp22_0	tmp22_1	tmp22_2	tmp22_3	tmp22_4	tmp22_5	tmp22_6	tmp22_7	tmp22_8	tmp22_9	tmp22_10	tmp22_11	tmp22_12
        idx1 idx2 idx3 idx4
        free	lock_1	lock_2	lock_3	lock_4	lock_5	lock_6	lock_7	lock_8	lock_9	lock_10	lock_11	lock_12
        c_lock1 c_lock2 c_unlock1 c_unlock2            
      )
      ( sequential_t1t2 tmp_1_s_t1t2 tmp_2_s_t1t2 tmp_3_s_t1t2 tmp_4_s_t1t2 MEM MEM_1_s_t1t2 MEM_2_s_t1t2 MEM_3_s_t1t2 MEM_4_s_t1t2 idx1 idx2 idx3 idx4    )
      (= pc1_12 SIX)
      (= pc2_12 SIX)          
  )
  (
     = MEM_4_s_t1t2 MEM_12
  )     
 )
)

;T1||T2 AND T1.T2 AND MEM_4_s_t2t1 = MEM_12 
(define-fun psi_t2t1 
 ( (pc1_0 Value) (pc1_1 Value) (pc1_2 Value) (pc1_3  Value) (pc1_4 Value) (pc1_5 Value) (pc1_6 Value) (pc1_7 Value) (pc1_8 Value) (pc1_9 Value) (pc1_10  Value) (pc1_11 Value) (pc1_12 Value) 
   (pc2_0 Value) (pc2_1 Value) (pc2_2 Value) (pc2_3  Value) (pc2_4 Value) (pc2_5 Value) (pc2_6 Value) (pc2_7 Value) (pc2_8 Value) (pc2_9 Value) (pc2_10  Value) (pc2_11 Value) (pc2_12 Value)
   (MEM (Array Value Value))(MEM_1 (Array Value Value))(MEM_2 (Array Value Value))(MEM_3 (Array Value Value))(MEM_4 (Array Value Value))(MEM_5 (Array Value Value))(MEM_6 (Array Value Value))(MEM_7 (Array Value Value))(MEM_8 (Array Value Value))(MEM_9 (Array Value Value))(MEM_10 (Array Value Value))(MEM_11 (Array Value Value))(MEM_12(Array Value Value))
   (tmp11_0  Value) (tmp11_1  Value) (tmp11_2  Value) (tmp11_3  Value) (tmp11_4  Value) (tmp11_5  Value) (tmp11_6  Value) (tmp11_7  Value) (tmp11_8  Value) (tmp11_9  Value) (tmp11_10  Value) (tmp11_11  Value) (tmp11_12  Value) 
   (tmp12_0  Value) (tmp12_1  Value) (tmp12_2  Value) (tmp12_3  Value) (tmp12_4  Value) (tmp12_5  Value) (tmp12_6  Value) (tmp12_7  Value) (tmp12_8  Value) (tmp12_9  Value) (tmp12_10  Value) (tmp12_11  Value) (tmp12_12  Value)
   (tmp21_0  Value) (tmp21_1  Value) (tmp21_2  Value) (tmp21_3  Value) (tmp21_4  Value) (tmp21_5  Value) (tmp21_6  Value) (tmp21_7  Value) (tmp21_8  Value) (tmp21_9  Value) (tmp21_10  Value) (tmp21_11  Value) (tmp21_12  Value)
   (tmp22_0  Value) (tmp22_1  Value) (tmp22_2  Value) (tmp22_3  Value) (tmp22_4  Value) (tmp22_5  Value) (tmp22_6  Value) (tmp22_7  Value) (tmp22_8  Value) (tmp22_9  Value) (tmp22_10  Value) (tmp22_11  Value) (tmp22_12  Value) 
   (idx1 Value)(idx2 Value) (idx3 Value) (idx4 Value)
   (lock_0 Value)(lock_1 Value)(lock_2 Value)(lock_3 Value)(lock_4 Value)(lock_5 Value)(lock_6 Value)(lock_7 Value)(lock_8 Value)(lock_9 Value)(lock_10 Value)(lock_11 Value)(lock_12 Value)
   (c_lock1 Bool)(c_lock2 Bool)(c_unlock1 Bool)(c_unlock2 Bool)  
   
   (tmp_1_s_t2t1 Value) (tmp_2_s_t2t1 Value) (tmp_3_s_t2t1 Value) (tmp_4_s_t2t1 Value) (MEM_1_s_t2t1 (Array Value Value))(MEM_2_s_t2t1 (Array Value Value))(MEM_3_s_t2t1 (Array Value Value))(MEM_4_s_t2t1(Array Value Value))  
 ) Bool
 (=> 
  (and
      (parallel
        ZERO pc1_1	pc1_2	pc1_3	pc1_4	pc1_5	pc1_6	pc1_7	pc1_8	pc1_9	pc1_10	pc1_11	pc1_12
        ZERO pc2_1	pc2_2	pc2_3	pc2_4	pc2_5	pc2_6	pc2_7	pc2_8	pc2_9	pc2_10	pc2_11	pc2_12
        MEM	MEM_1	MEM_2	MEM_3	MEM_4	MEM_5	MEM_6	MEM_7	MEM_8	MEM_9	MEM_10	MEM_11	MEM_12
        tmp11_0	tmp11_1	tmp11_2	tmp11_3	tmp11_4	tmp11_5	tmp11_6	tmp11_7	tmp11_8	tmp11_9	tmp11_10	tmp11_11	tmp11_12
        tmp12_0	tmp12_1	tmp12_2	tmp12_3	tmp12_4	tmp12_5	tmp12_6	tmp12_7	tmp12_8	tmp12_9	tmp12_10	tmp12_11	tmp12_12
        tmp21_0	tmp21_1	tmp21_2	tmp21_3	tmp21_4	tmp21_5	tmp21_6	tmp21_7	tmp21_8	tmp21_9	tmp21_10	tmp21_11	tmp21_12
        tmp22_0	tmp22_1	tmp22_2	tmp22_3	tmp22_4	tmp22_5	tmp22_6	tmp22_7	tmp22_8	tmp22_9	tmp22_10	tmp22_11	tmp22_12
        idx1 idx2 idx3 idx4
        free	lock_1	lock_2	lock_3	lock_4	lock_5	lock_6	lock_7	lock_8	lock_9	lock_10	lock_11	lock_12  
        c_lock1 c_lock2 c_unlock1 c_unlock2          
      )
      ( sequential_t2t1 tmp_1_s_t2t1 tmp_2_s_t2t1 tmp_3_s_t2t1 tmp_4_s_t2t1 MEM MEM_1_s_t2t1 MEM_2_s_t2t1 MEM_3_s_t2t1 MEM_4_s_t2t1 idx1 idx2 idx3 idx4    )     
      (= pc1_12 SIX)
      (= pc2_12 SIX)       
  )
  (
     = MEM_4_s_t2t1 MEM_12  
  )     
 )
)

(assert
  (=>
   (and
     (distinct1 ZERO ONE TWO THREE FOUR FIVE SIX)
     (distinct2 free hold_by_t1 hold_by_t2)
  
     ;indices can have global or local values 
     (select_index idx1 ZERO ONE TWO THREE)
     (select_index idx2 ZERO ONE TWO THREE)
     (select_index idx3 TWO THREE FOUR FIVE)
     (select_index idx4 TWO THREE FOUR FIVE)
    )
    (and 
      (or 
        ;phi_t1_t2(c_lock1, c_lock2)
        (phi_t1t2  
          ZERO pc1_1	pc1_2	pc1_3	pc1_4	pc1_5	pc1_6	pc1_7	pc1_8	pc1_9	pc1_10	pc1_11	pc1_12
          ZERO pc2_1	pc2_2	pc2_3	pc2_4	pc2_5	pc2_6	pc2_7	pc2_8	pc2_9	pc2_10	pc2_11	pc2_12
          MEM	MEM_1	MEM_2	MEM_3	MEM_4	MEM_5	MEM_6	MEM_7	MEM_8	MEM_9	MEM_10	MEM_11	MEM_12
          tmp11_0	tmp11_1	tmp11_2	tmp11_3	tmp11_4	tmp11_5	tmp11_6	tmp11_7	tmp11_8	tmp11_9	tmp11_10	tmp11_11	tmp11_12
          tmp12_0	tmp12_1	tmp12_2	tmp12_3	tmp12_4	tmp12_5	tmp12_6	tmp12_7	tmp12_8	tmp12_9	tmp12_10	tmp12_11	tmp12_12
          tmp21_0	tmp21_1	tmp21_2	tmp21_3	tmp21_4	tmp21_5	tmp21_6	tmp21_7	tmp21_8	tmp21_9	tmp21_10	tmp21_11	tmp21_12
          tmp22_0	tmp22_1	tmp22_2	tmp22_3	tmp22_4	tmp22_5	tmp22_6	tmp22_7	tmp22_8	tmp22_9	tmp22_10	tmp22_11	tmp22_12
          idx1 idx2 idx3 idx4
          free	lock_1	lock_2	lock_3	lock_4	lock_5	lock_6	lock_7	lock_8	lock_9	lock_10	lock_11	lock_12
          c_lock1 c_lock2 c_unlock1 c_unlock2
                
          tmp_1_s_t1t2 tmp_2_s_t1t2 tmp_3_s_t1t2 tmp_4_s_t1t2 MEM_1_s_t1t2 MEM_2_s_t1t2 MEM_3_s_t1t2 MEM_4_s_t1t2
        )  
        ;phi_t2t1(c_lock1, c_lock2)
        (phi_t2t1  
          ZERO pc1_1	pc1_2	pc1_3	pc1_4	pc1_5	pc1_6	pc1_7	pc1_8	pc1_9	pc1_10	pc1_11	pc1_12
          ZERO pc2_1	pc2_2	pc2_3	pc2_4	pc2_5	pc2_6	pc2_7	pc2_8	pc2_9	pc2_10	pc2_11	pc2_12
          MEM	MEM_1	MEM_2	MEM_3	MEM_4	MEM_5	MEM_6	MEM_7	MEM_8	MEM_9	MEM_10	MEM_11	MEM_12
          tmp11_0	tmp11_1	tmp11_2	tmp11_3	tmp11_4	tmp11_5	tmp11_6	tmp11_7	tmp11_8	tmp11_9	tmp11_10	tmp11_11	tmp11_12
          tmp12_0	tmp12_1	tmp12_2	tmp12_3	tmp12_4	tmp12_5	tmp12_6	tmp12_7	tmp12_8	tmp12_9	tmp12_10	tmp12_11	tmp12_12
          tmp21_0	tmp21_1	tmp21_2	tmp21_3	tmp21_4	tmp21_5	tmp21_6	tmp21_7	tmp21_8	tmp21_9	tmp21_10	tmp21_11	tmp21_12
          tmp22_0	tmp22_1	tmp22_2	tmp22_3	tmp22_4	tmp22_5	tmp22_6	tmp22_7	tmp22_8	tmp22_9	tmp22_10	tmp22_11	tmp22_12
          idx1 idx2 idx3 idx4
          free	lock_1	lock_2	lock_3	lock_4	lock_5	lock_6	lock_7	lock_8	lock_9	lock_10	lock_11	lock_12
          c_lock1 c_lock2 c_unlock1 c_unlock2
                
          tmp_1_s_t2t1 tmp_2_s_t2t1 tmp_3_s_t2t1 tmp_4_s_t2t1 MEM_1_s_t2t1 MEM_2_s_t2t1 MEM_3_s_t2t1 MEM_4_s_t2t1
        ) 
      )
 
      ;phi_t1t2(c_lock2)|~c_lock1-> nicht c_lock1    no unnecessary locks
       (=>
        (psi_t1t2  
         ZERO pc1_1_no_L1	pc1_2_no_L1	pc1_3_no_L1	pc1_4_no_L1	pc1_5_no_L1	pc1_6_no_L1	pc1_7_no_L1	pc1_8_no_L1	pc1_9_no_L1	pc1_10_no_L1	pc1_11_no_L1	pc1_12_no_L1
         ZERO pc2_1_no_L1	pc2_2_no_L1	pc2_3_no_L1	pc2_4_no_L1	pc2_5_no_L1	pc2_6_no_L1	pc2_7_no_L1	pc2_8_no_L1	pc2_9_no_L1	pc2_10_no_L1	pc2_11_no_L1	pc2_12_no_L1
         MEM	MEM_1_no_L1	MEM_2_no_L1	MEM_3_no_L1	MEM_4_no_L1	MEM_5_no_L1	MEM_6_no_L1	MEM_7_no_L1	MEM_8_no_L1	MEM_9_no_L1	MEM_10_no_L1	MEM_11_no_L1	MEM_12_no_L1
         tmp11_0_no_L1	tmp11_1_no_L1	tmp11_2_no_L1	tmp11_3_no_L1	tmp11_4_no_L1	tmp11_5_no_L1	tmp11_6_no_L1	tmp11_7_no_L1	tmp11_8_no_L1	tmp11_9_no_L1	tmp11_10_no_L1	tmp11_11_no_L1	tmp11_12_no_L1
         tmp12_0_no_L1	tmp12_1_no_L1	tmp12_2_no_L1	tmp12_3_no_L1	tmp12_4_no_L1	tmp12_5_no_L1	tmp12_6_no_L1	tmp12_7_no_L1	tmp12_8_no_L1	tmp12_9_no_L1	tmp12_10_no_L1	tmp12_11_no_L1	tmp12_12_no_L1
         tmp21_0_no_L1	tmp21_1_no_L1	tmp21_2_no_L1	tmp21_3_no_L1	tmp21_4_no_L1	tmp21_5_no_L1	tmp21_6_no_L1	tmp21_7_no_L1	tmp21_8_no_L1	tmp21_9_no_L1	tmp21_10_no_L1	tmp21_11_no_L1	tmp21_12_no_L1
         tmp22_0_no_L1	tmp22_1_no_L1	tmp22_2_no_L1	tmp22_3_no_L1	tmp22_4_no_L1	tmp22_5_no_L1	tmp22_6_no_L1	tmp22_7_no_L1	tmp22_8_no_L1	tmp22_9_no_L1	tmp22_10_no_L1	tmp22_11_no_L1	tmp22_12_no_L1
         idx1 idx2 idx3 idx4
         free	lock_1_no_L1	lock_2_no_L1	lock_3_no_L1	lock_4_no_L1	lock_5_no_L1	lock_6_no_L1	lock_7_no_L1	lock_8_no_L1	lock_9_no_L1	lock_10_no_L1	lock_11_no_L1	lock_12_no_L1
         false c_lock2 c_unlock1 c_unlock2
                
         tmp_1_s_t1t2 tmp_2_s_t1t2 tmp_3_s_t1t2 tmp_4_s_t1t2 MEM_1_s_t1t2 MEM_2_s_t1t2 MEM_3_s_t1t2 MEM_4_s_t1t2
        ) 
        (
          = c_lock1 false
        )
       ) 
       ;phi_t2t1(c_lock2)|~c_lock1-> nicht c_lock1    no unnecessary locks
       (=>
        (psi_t2t1  
         ZERO pc1_1_no_L1	pc1_2_no_L1	pc1_3_no_L1	pc1_4_no_L1	pc1_5_no_L1	pc1_6_no_L1	pc1_7_no_L1	pc1_8_no_L1	pc1_9_no_L1	pc1_10_no_L1	pc1_11_no_L1	pc1_12_no_L1
         ZERO pc2_1_no_L1	pc2_2_no_L1	pc2_3_no_L1	pc2_4_no_L1	pc2_5_no_L1	pc2_6_no_L1	pc2_7_no_L1	pc2_8_no_L1	pc2_9_no_L1	pc2_10_no_L1	pc2_11_no_L1	pc2_12_no_L1
         MEM	MEM_1_no_L1	MEM_2_no_L1	MEM_3_no_L1	MEM_4_no_L1	MEM_5_no_L1	MEM_6_no_L1	MEM_7_no_L1	MEM_8_no_L1	MEM_9_no_L1	MEM_10_no_L1	MEM_11_no_L1	MEM_12_no_L1
         tmp11_0_no_L1	tmp11_1_no_L1	tmp11_2_no_L1	tmp11_3_no_L1	tmp11_4_no_L1	tmp11_5_no_L1	tmp11_6_no_L1	tmp11_7_no_L1	tmp11_8_no_L1	tmp11_9_no_L1	tmp11_10_no_L1	tmp11_11_no_L1	tmp11_12_no_L1
         tmp12_0_no_L1	tmp12_1_no_L1	tmp12_2_no_L1	tmp12_3_no_L1	tmp12_4_no_L1	tmp12_5_no_L1	tmp12_6_no_L1	tmp12_7_no_L1	tmp12_8_no_L1	tmp12_9_no_L1	tmp12_10_no_L1	tmp12_11_no_L1	tmp12_12_no_L1
         tmp21_0_no_L1	tmp21_1_no_L1	tmp21_2_no_L1	tmp21_3_no_L1	tmp21_4_no_L1	tmp21_5_no_L1	tmp21_6_no_L1	tmp21_7_no_L1	tmp21_8_no_L1	tmp21_9_no_L1	tmp21_10_no_L1	tmp21_11_no_L1	tmp21_12_no_L1
         tmp22_0_no_L1	tmp22_1_no_L1	tmp22_2_no_L1	tmp22_3_no_L1	tmp22_4_no_L1	tmp22_5_no_L1	tmp22_6_no_L1	tmp22_7_no_L1	tmp22_8_no_L1	tmp22_9_no_L1	tmp22_10_no_L1	tmp22_11_no_L1	tmp22_12_no_L1
         idx1 idx2 idx3 idx4
         free	lock_1_no_L1	lock_2_no_L1	lock_3_no_L1	lock_4_no_L1	lock_5_no_L1	lock_6_no_L1	lock_7_no_L1	lock_8_no_L1	lock_9_no_L1	lock_10_no_L1	lock_11_no_L1	lock_12_no_L1          false c_lock2 c_unlock1 c_unlock2
                
        tmp_1_s_t2t1 tmp_2_s_t2t1 tmp_3_s_t2t1 tmp_4_s_t2t1 MEM_1_s_t2t1 MEM_2_s_t2t1 MEM_3_s_t2t1 MEM_4_s_t2t1
        )
        (
          = c_lock1 false
        )
      )
    
 
      ;phi_t1t2(c_lock1)|~c_lock2-> nicht c_lock2    no unnecessary locks
      (=>
       (psi_t1t2  
         ZERO pc1_1_no_L2	pc1_2_no_L2	pc1_3_no_L2	pc1_4_no_L2	pc1_5_no_L2	pc1_6_no_L2	pc1_7_no_L2	pc1_8_no_L2	pc1_9_no_L2	pc1_10_no_L2	pc1_11_no_L2	pc1_12_no_L2
         ZERO pc2_1_no_L2	pc2_2_no_L2	pc2_3_no_L2	pc2_4_no_L2	pc2_5_no_L2	pc2_6_no_L2	pc2_7_no_L2	pc2_8_no_L2	pc2_9_no_L2	pc2_10_no_L2	pc2_11_no_L2	pc2_12_no_L2
         MEM	MEM_1_no_L2	MEM_2_no_L2	MEM_3_no_L2	MEM_4_no_L2	MEM_5_no_L2	MEM_6_no_L2	MEM_7_no_L2	MEM_8_no_L2	MEM_9_no_L2	MEM_10_no_L2	MEM_11_no_L2	MEM_12_no_L2
         tmp11_0_no_L2	tmp11_1_no_L2	tmp11_2_no_L2	tmp11_3_no_L2	tmp11_4_no_L2	tmp11_5_no_L2	tmp11_6_no_L2	tmp11_7_no_L2	tmp11_8_no_L2	tmp11_9_no_L2	tmp11_10_no_L2	tmp11_11_no_L2	tmp11_12_no_L2
         tmp12_0_no_L2	tmp12_1_no_L2	tmp12_2_no_L2	tmp12_3_no_L2	tmp12_4_no_L2	tmp12_5_no_L2	tmp12_6_no_L2	tmp12_7_no_L2	tmp12_8_no_L2	tmp12_9_no_L2	tmp12_10_no_L2	tmp12_11_no_L2	tmp12_12_no_L2
         tmp21_0_no_L2	tmp21_1_no_L2	tmp21_2_no_L2	tmp21_3_no_L2	tmp21_4_no_L2	tmp21_5_no_L2	tmp21_6_no_L2	tmp21_7_no_L2	tmp21_8_no_L2	tmp21_9_no_L2	tmp21_10_no_L2	tmp21_11_no_L2	tmp21_12_no_L2
         tmp22_0_no_L2	tmp22_1_no_L2	tmp22_2_no_L2	tmp22_3_no_L2	tmp22_4_no_L2	tmp22_5_no_L2	tmp22_6_no_L2	tmp22_7_no_L2	tmp22_8_no_L2	tmp22_9_no_L2	tmp22_10_no_L2	tmp22_11_no_L2	tmp22_12_no_L2
         idx1 idx2 idx3 idx4
         free	lock_1_no_L2	lock_2_no_L2	lock_3_no_L2	lock_4_no_L2	lock_5_no_L2	lock_6_no_L2	lock_7_no_L2	lock_8_no_L2	lock_9_no_L2	lock_10_no_L2	lock_11_no_L2	lock_12_no_L2
         c_lock1 false c_unlock1 c_unlock2
                
         tmp_1_s_t1t2 tmp_2_s_t1t2 tmp_3_s_t1t2 tmp_4_s_t1t2 MEM_1_s_t1t2 MEM_2_s_t1t2 MEM_3_s_t1t2 MEM_4_s_t1t2
        ) 
        (
          = c_lock2 false          
        ) 
      )
       ;phi_t2t1(c_lock1)|~c_lock2-> nicht c_lock2    no unnecessary locks
       (=>
        (psi_t2t1  
         ZERO pc1_1_no_L2	pc1_2_no_L2	pc1_3_no_L2	pc1_4_no_L2	pc1_5_no_L2	pc1_6_no_L2	pc1_7_no_L2	pc1_8_no_L2	pc1_9_no_L2	pc1_10_no_L2	pc1_11_no_L2	pc1_12_no_L2
         ZERO pc2_1_no_L2	pc2_2_no_L2	pc2_3_no_L2	pc2_4_no_L2	pc2_5_no_L2	pc2_6_no_L2	pc2_7_no_L2	pc2_8_no_L2	pc2_9_no_L2	pc2_10_no_L2	pc2_11_no_L2	pc2_12_no_L2
         MEM	MEM_1_no_L2	MEM_2_no_L2	MEM_3_no_L2	MEM_4_no_L2	MEM_5_no_L2	MEM_6_no_L2	MEM_7_no_L2	MEM_8_no_L2	MEM_9_no_L2	MEM_10_no_L2	MEM_11_no_L2	MEM_12_no_L2
         tmp11_0_no_L2	tmp11_1_no_L2	tmp11_2_no_L2	tmp11_3_no_L2	tmp11_4_no_L2	tmp11_5_no_L2	tmp11_6_no_L2	tmp11_7_no_L2	tmp11_8_no_L2	tmp11_9_no_L2	tmp11_10_no_L2	tmp11_11_no_L2	tmp11_12_no_L2
         tmp12_0_no_L2	tmp12_1_no_L2	tmp12_2_no_L2	tmp12_3_no_L2	tmp12_4_no_L2	tmp12_5_no_L2	tmp12_6_no_L2	tmp12_7_no_L2	tmp12_8_no_L2	tmp12_9_no_L2	tmp12_10_no_L2	tmp12_11_no_L2	tmp12_12_no_L2
         tmp21_0_no_L2	tmp21_1_no_L2	tmp21_2_no_L2	tmp21_3_no_L2	tmp21_4_no_L2	tmp21_5_no_L2	tmp21_6_no_L2	tmp21_7_no_L2	tmp21_8_no_L2	tmp21_9_no_L2	tmp21_10_no_L2	tmp21_11_no_L2	tmp21_12_no_L2
         tmp22_0_no_L2	tmp22_1_no_L2	tmp22_2_no_L2	tmp22_3_no_L2	tmp22_4_no_L2	tmp22_5_no_L2	tmp22_6_no_L2	tmp22_7_no_L2	tmp22_8_no_L2	tmp22_9_no_L2	tmp22_10_no_L2	tmp22_11_no_L2	tmp22_12_no_L2
         idx1 idx2 idx3 idx4
         free	lock_1_no_L2	lock_2_no_L2	lock_3_no_L2	lock_4_no_L2	lock_5_no_L2	lock_6_no_L2	lock_7_no_L2	lock_8_no_L2	lock_9_no_L2	lock_10_no_L2	lock_11_no_L2	lock_12_no_L2
         c_lock1 false c_unlock1 c_unlock2
                
         tmp_1_s_t2t1 tmp_2_s_t2t1 tmp_3_s_t2t1 tmp_4_s_t2t1 MEM_1_s_t2t1 MEM_2_s_t2t1 MEM_3_s_t2t1 MEM_4_s_t2t1
        ) 
        (
           = c_lock2 false         
        )
   
     )
    )
    )
)      
