% =========================================================================== %
% FILE          : strong_sem.ml                                               %
% DESCRIPTION   : Operational definition of strong equivalence for CCS        %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 25 October 1991                                             %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `strong_sem`;;

% --------------------------------------------------------------------------- %
% Define the strong bisimulation relation on CCS processes.                   %
% --------------------------------------------------------------------------- %
let STRONG_BISIM =
     new_definition
      (`STRONG_BISIM`,
       "STRONG_BISIM (Bsm: CCS -> CCS -> bool) =
        (!E E'.
         (Bsm E E' ==>
          (!u.
           (!E1. TRANS E u E1 ==> 
                 (?E2. TRANS E' u E2 /\ Bsm E1 E2)) /\
           (!E2. TRANS E' u E2 ==> 
                 (?E1. TRANS E u E1 /\ Bsm E1 E2)))))");;

% --------------------------------------------------------------------------- %
% The identity relation is a strong bisimulation.                       (106) %
% --------------------------------------------------------------------------- %
let IDENTITY_STRONG_BISIM =
     prove_thm
      (`IDENTITY_STRONG_BISIM`,
       "STRONG_BISIM (\x y. x = y)",
       PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN  
       REPEAT STRIP_TAC THENL
       [ASSUME_TAC (REWRITE_RULE [ASSUME "E: CCS = E'"]
                           (ASSUME "TRANS E u E1")) THEN
        EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] ;    
        PURE_ONCE_ASM_REWRITE_TAC[] THEN 
        EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] ]);;    

% --------------------------------------------------------------------------- %
% The converse of a strong bisimulation is a strong bisimulation.       (291) %
% --------------------------------------------------------------------------- %
let CONVERSE_STRONG_BISIM =
     prove_thm
      (`CONVERSE_STRONG_BISIM`,
       "!Bsm. STRONG_BISIM Bsm ==> STRONG_BISIM (\x y. Bsm y x)",
       GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN     
       REPEAT STRIP_TAC THEN RES_TAC THENL 
       [EXISTS_TAC "E1': CCS"; EXISTS_TAC "E2':CCS"] THEN ASM_REWRITE_TAC[]);;  

% --------------------------------------------------------------------------- %
% The composition of two strong bisimulations is a strong bisimulation.  (402)%
% --------------------------------------------------------------------------- % 
let COMP_STRONG_BISIM =
     prove_thm
      (`COMP_STRONG_BISIM`,
       "!Bsm1 Bsm2. 
         STRONG_BISIM Bsm1 /\ STRONG_BISIM Bsm2 ==>
         STRONG_BISIM (\x z. ?y. Bsm1 x y /\ Bsm2 y z)",
       REPEAT GEN_TAC THEN  
       PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN   
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC 
        (MP (SPECL ["E: CCS"; "y: CCS"] 
            (ASSUME 
             "!E E'.
               Bsm1 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm1 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm1 E1 E2)))"))
        (ASSUME "(Bsm1: CCS -> CCS -> bool) E y")) THEN 
        IMP_RES_TAC 
        (MP (SPECL ["y: CCS"; "E': CCS"] 
            (ASSUME 
             "!E E'.
               Bsm2 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm2 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm2 E1 E2)))"))
        (ASSUME "(Bsm2: CCS -> CCS -> bool) y E'")) THEN  
        EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]  
        ;
        IMP_RES_TAC
        (MP (SPECL ["y: CCS"; "E': CCS"]
            (ASSUME 
             "!E E'.
               Bsm2 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm2 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm2 E1 E2)))"))
        (ASSUME "(Bsm2: CCS -> CCS -> bool) y E'")) THEN 
        IMP_RES_TAC
        (MP (SPECL ["E: CCS"; "y: CCS"]
            (ASSUME 
             "!E E'.
               Bsm1 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm1 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm1 E1 E2)))"))
        (ASSUME "(Bsm1: CCS -> CCS -> bool) E y")) THEN 
        EXISTS_TAC "E1': CCS" THEN ASM_REWRITE_TAC[] THEN 
        EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] ]);;    

% --------------------------------------------------------------------------- %
% The union of two strong bisimulations is a strong bisimulation.       (700) %
% --------------------------------------------------------------------------- %
let UNION_STRONG_BISIM =
     prove_thm
      (`UNION_STRONG_BISIM`,
       "!Bsm1 Bsm2. 
         STRONG_BISIM Bsm1 /\ STRONG_BISIM Bsm2 ==>  
         STRONG_BISIM (\x y. Bsm1 x y \/ Bsm2 x y)",  
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN  
       REPEAT STRIP_TAC THEN RES_TAC THENL 
       [EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS"; 
        EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS"] THEN ASM_REWRITE_TAC[]);; 
 
% --------------------------------------------------------------------------- %
% Define the strong equivalence relation for CCS processes.                   %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV =
     new_definition
      (`STRONG_EQUIV`,
       "STRONG_EQUIV E E' = (?Bsm. Bsm E E' /\ STRONG_BISIM Bsm)");;

% --------------------------------------------------------------------------- %
% Strong equivalence is an equivalence relation.                              %
% --------------------------------------------------------------------------- %
% --------------------------------------------------------------------------- %
% Strong equivalence is a reflexive relation.                            (28) %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_REFL =
     prove_thm
      (`STRONG_EQUIV_REFL`,
       "!E. STRONG_EQUIV E E",
       GEN_TAC THEN PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC "\x y: CCS. x = y" THEN BETA_TAC THEN
       REWRITE_TAC [IDENTITY_STRONG_BISIM] );;  

% --------------------------------------------------------------------------- %
% Strong equivalence is a symmetric relation.                            (57) %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_SYM =
     prove_thm
      (`STRONG_EQUIV_SYM`,
       "!E E'. STRONG_EQUIV E E' ==> STRONG_EQUIV E' E",
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN REPEAT STRIP_TAC THEN
       EXISTS_TAC "\x y. (Bsm: CCS -> CCS -> bool) y x" THEN BETA_TAC THEN 
       IMP_RES_TAC CONVERSE_STRONG_BISIM THEN ASM_REWRITE_TAC[]);;     

% --------------------------------------------------------------------------- %
% Strong equivalence is a transitive relation.                          (147) %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_TRANS =
     prove_thm
      (`STRONG_EQUIV_TRANS`,
       "!E E' E''. 
         STRONG_EQUIV E E' /\ STRONG_EQUIV E' E'' ==> STRONG_EQUIV E E''", 
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN REPEAT STRIP_TAC THEN
       EXISTS_TAC "\x z. ?y. (Bsm: CCS -> CCS -> bool) x y /\
                             (Bsm': CCS -> CCS -> bool) y z" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "E': CCS" THEN ASM_REWRITE_TAC[] ; 
        IMP_RES_TAC COMP_STRONG_BISIM ]);;

% --------------------------------------------------------------------------- %
% Syntactic equivalence implies strong equivalence.                      (17) %
% --------------------------------------------------------------------------- %
let EQUAL_IMP_STRONG_EQUIV =
     prove_thm
      (`EQUAL_IMP_STRONG_EQUIV`,
       "!E E'. (E = E') ==> STRONG_EQUIV E E'",
       REPEAT STRIP_TAC THEN PURE_ASM_REWRITE_TAC [STRONG_EQUIV_REFL]);;

% --------------------------------------------------------------------------- %
% Definition 3, page 91 in Milner's book.                                     %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV' = 
     new_definition 
      (`STRONG_EQUIV'`, 
       "STRONG_EQUIV' E E' = 
        (!u.
         (!E1. TRANS E u E1 ==> 
               (?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2)) /\
         (!E2. TRANS E' u E2 ==> 
               (?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2)))");; 

% --------------------------------------------------------------------------- %
% Strong equivalence implies the new relation.                          (241) % 
% --------------------------------------------------------------------------- %
let STR_EQUIV_IMP_STR_EQUIV' =    
     prove_thm 
      (`STR_EQUIV_IMP_STR_EQUIV'`, 
       "!E E'. STRONG_EQUIV E E' ==> STRONG_EQUIV' E E'", 
       REPEAT GEN_TAC THEN 
       REWRITE_TAC [STRONG_EQUIV'; STRONG_EQUIV] THEN
       REPEAT STRIP_TAC THEN    
       IMP_RES_TAC
       (MP(SPEC_ALL
           (EQ_MP(SPEC "Bsm: CCS -> CCS -> bool" STRONG_BISIM)
                 (ASSUME "STRONG_BISIM Bsm")))
          (ASSUME "(Bsm: CCS -> CCS -> bool) E E'")) THENL  
        [EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS"] THEN  
        ASM_REWRITE_TAC[] THEN 
        EXISTS_TAC "Bsm: CCS -> CCS -> bool" THEN ASM_REWRITE_TAC[]);; 
          
% --------------------------------------------------------------------------- %
% Lemma 3, page 91 in Milner's book:                                    (160) %
% the new relation STRONG_EQUIV' is a strong bisimulation.                    %
% --------------------------------------------------------------------------- % 
let Lemma3 =              
     prove_thm 
      (`Lemma3`, 
       "STRONG_BISIM STRONG_EQUIV'", 
       PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN REPEAT STRIP_TAC THEN
       IMP_RES_TAC 
       (EQ_MP (SPECL ["E: CCS"; "E': CCS"] STRONG_EQUIV') 
              (ASSUME "STRONG_EQUIV' E E'")) THENL 
       [EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS"] THEN
       IMP_RES_TAC STR_EQUIV_IMP_STR_EQUIV' THEN ASM_REWRITE_TAC[]);;   

% --------------------------------------------------------------------------- %
% The new relation implies strong equivalence.                           (25) %
% --------------------------------------------------------------------------- %
let STR_EQUIV'_IMP_STR_EQUIV =         
     prove_thm 
      (`STR_EQUIV'_IMP_STR_EQUIV`, 
       "!E E'. STRONG_EQUIV' E E' ==> STRONG_EQUIV E E'",   
       REPEAT STRIP_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN 
       EXISTS_TAC "STRONG_EQUIV'" THEN ASM_REWRITE_TAC [Lemma3]);;

% --------------------------------------------------------------------------- %
% Prop. 4, page 91: strong equivalence satisfies property (*).           (50) %
% --------------------------------------------------------------------------- %
let PROPERTY_STAR =              
     prove_thm 
      (`PROPERTY_STAR`,    
       "!E E'. STRONG_EQUIV E E' = 
         (!u.
           (!E1. TRANS E u E1 ==>
                 (?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2)) /\
           (!E2. TRANS E' u E2 ==>
                 (?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2)))",    
       REPEAT GEN_TAC THEN EQ_TAC THENL     
       [PURE_ONCE_REWRITE_TAC 
            [ONCE_REWRITE_RULE [STRONG_EQUIV'] STR_EQUIV_IMP_STR_EQUIV'] ; 
        PURE_ONCE_REWRITE_TAC 
            [ONCE_REWRITE_RULE [STRONG_EQUIV'] STR_EQUIV'_IMP_STR_EQUIV] ]);; 

let PROPERTY_STAR_LR = save_thm(`PROPERTY_STAR_LR`, EQ_IMP_LR PROPERTY_STAR);;
 
% --------------------------------------------------------------------------- %
% Strong equivalence is substitutive under prefix operator.             (158) %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_SUBST_PREFIX =    
     prove_thm 
      (`STRONG_EQUIV_SUBST_PREFIX`, 
       "!E E'. 
         STRONG_EQUIV E E' ==> !u. STRONG_EQUIV (prefix u E) (prefix u E')",  
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC 
           [SPECL ["prefix u E"; "prefix u E'"] PROPERTY_STAR] THEN     
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC TRANS_PREFIX THENL
       [EXISTS_TAC "E': CCS" ; EXISTS_TAC "E: CCS"] THEN
       ASM_REWRITE_TAC [PREFIX]);;

% --------------------------------------------------------------------------- %
% Strong equivalence is preserved by binary summation.                  (683) %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_PRESD_BY_SUM =
     prove_thm
      (`STRONG_EQUIV_PRESD_BY_SUM`,
       "!E1 E1' E2 E2'.
         STRONG_EQUIV E1 E1' /\ STRONG_EQUIV E2 E2' ==>
         STRONG_EQUIV (sum E1 E2) (sum E1' E2')",
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [PROPERTY_STAR] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC TRANS_SUM THEN
        RES_TAC THEN EXISTS_TAC "E2'': CCS" THEN ASM_REWRITE_TAC[]
        THENL [SUM1_TAC; SUM2_TAC] THEN ASM_REWRITE_TAC[]
        ;
        IMP_RES_TAC TRANS_SUM THEN
        RES_TAC THEN EXISTS_TAC "E1'': CCS" THEN ASM_REWRITE_TAC[]
        THENL [SUM1_TAC; SUM2_TAC] THEN ASM_REWRITE_TAC[] ]);;

% --------------------------------------------------------------------------- %
% Strong equivalence is substitutive under summation operator on the right.   %
%  |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV(sum E E'')(sum E' E''))%
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_SUBST_SUM_R = 
     save_thm
      (`STRONG_EQUIV_SUBST_SUM_R`,
       GEN_ALL
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM 
             (CONJ (ASSUME "STRONG_EQUIV E E'")
                   (ASSUME "STRONG_EQUIV E'' E''")))))))));;

% --------------------------------------------------------------------------- %
% Strong equivalence is substitutive under summation operator on the left.    %
%  |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV(sum E'' E)(sum E'' E'))%
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_SUBST_SUM_L =
     save_thm
      (`STRONG_EQUIV_SUBST_SUM_L`,
       GEN_ALL
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM 
             (CONJ (ASSUME "STRONG_EQUIV E'' E''")
                   (ASSUME "STRONG_EQUIV E E'")))))))));;

% --------------------------------------------------------------------------- %
% Strong equivalence is preserved by parallel composition.             (1848) %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_PRESD_BY_PAR =
     prove_thm
      (`STRONG_EQUIV_PRESD_BY_PAR`,
       "!E1 E1' E2 E2'.
         STRONG_EQUIV E1 E1' /\ STRONG_EQUIV E2 E2' ==>
         STRONG_EQUIV (par E1 E2) (par E1' E2')",
       REPEAT STRIP_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y.
         (?F1 F2 F3 F4.
           (x = par F1 F3) /\ (y = par F2 F4) /\
           STRONG_EQUIV F1 F2 /\ STRONG_EQUIV F3 F4)" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "E1: CCS" THEN EXISTS_TAC "E1': CCS" THEN
        EXISTS_TAC "E2: CCS" THEN EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[]
        ;
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E = par F1 F3"]
                            (ASSUME "TRANS E u E1''")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                       (ASSUME "STRONG_EQUIV F1 F2")) THEN
          EXISTS_TAC "par E2'' F4" THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
          [PAR1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2'': CCS" THEN 
           EXISTS_TAC "F3: CCS" THEN EXISTS_TAC "F4: CCS" THEN 
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                       (ASSUME "STRONG_EQUIV F3 F4")) THEN    
          EXISTS_TAC "par F2 E2''" THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
          [PAR2_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "F1: CCS" THEN EXISTS_TAC "F2: CCS" THEN
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2'': CCS" THEN
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                       (ASSUME "STRONG_EQUIV F1 F2")) THEN
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                       (ASSUME "STRONG_EQUIV F3 F4")) THEN
          EXISTS_TAC "par E2''' E2''''" THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
          [PAR3_TAC THEN EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2''': CCS" THEN
           EXISTS_TAC "E2'': CCS" THEN EXISTS_TAC "E2'''': CCS" THEN
           ASM_REWRITE_TAC[] ] ] 
         ;
         ASSUME_TAC
         (REWRITE_RULE [ASSUME "E' = par F2 F4"]
                 (ASSUME "TRANS E' u E2''")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                       (ASSUME "STRONG_EQUIV F1 F2")) THEN
          EXISTS_TAC "par E1''' F3" THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
          [PAR1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E1'': CCS" THEN 
           EXISTS_TAC "F3: CCS" THEN EXISTS_TAC "F4: CCS" THEN 
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                       (ASSUME "STRONG_EQUIV F3 F4")) THEN
          EXISTS_TAC "par F1 E1'''" THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
          [PAR2_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "F1: CCS" THEN EXISTS_TAC "F2: CCS" THEN
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E1'': CCS" THEN
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR
                       (ASSUME "STRONG_EQUIV F1 F2")) THEN
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                       (ASSUME "STRONG_EQUIV F3 F4")) THEN
          EXISTS_TAC "par E1''' E1''''" THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
          [PAR3_TAC THEN EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E1'': CCS" THEN
           EXISTS_TAC "E1'''': CCS" THEN EXISTS_TAC "E2''': CCS" THEN 
           ASM_REWRITE_TAC[] ] ] ]]);;

% --------------------------------------------------------------------------- %
% Strong equivalence is substitutive under parallel operator on the right:    %
%  |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV(par E E'')(par E' E''))%
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_SUBST_PAR_R =
     save_thm
      (`STRONG_EQUIV_SUBST_PAR_R`,
       GEN_ALL
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_PAR
             (CONJ (ASSUME "STRONG_EQUIV E E'")
                   (ASSUME "STRONG_EQUIV E'' E''")))))))));;

% --------------------------------------------------------------------------- %
% Strong equivalence is substitutive under parallel operator on the left:     %
%  |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV(par E'' E)(par E'' E'))%
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_SUBST_PAR_L =
     save_thm
      (`STRONG_EQUIV_SUBST_PAR_L`,
       GEN_ALL
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_PAR 
             (CONJ (ASSUME "STRONG_EQUIV E'' E''")
                   (ASSUME "STRONG_EQUIV E E'")))))))));;

% --------------------------------------------------------------------------- %
% Strong equivalence is substitutive under restriction operator.        (943) %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_SUBST_RESTR =
     prove_thm
      (`STRONG_EQUIV_SUBST_RESTR`,
       "!E E'. 
         STRONG_EQUIV E E' ==> 
         (!L. STRONG_EQUIV (restr E L) (restr E' L))",   
       REPEAT STRIP_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN 
       EXISTS_TAC "\x y. ?E1 E2 L'. (x = restr E1 L') /\ (y = restr E2 L') /\ 
                                    STRONG_EQUIV E1 E2" THEN 
       CONJ_TAC THENL 
       [BETA_TAC THEN EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E': CCS" THEN 
        EXISTS_TAC "L: (Label)set" THEN ASM_REWRITE_TAC[]  
        ; 
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN 
        REPEAT STRIP_TAC THENL 
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E'' = restr E1 L'"]
                            (ASSUME "TRANS E'' u E1'")) THEN 
         IMP_RES_TAC TRANS_RESTR THENL 
         [IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
                       (ASSUME "STRONG_EQUIV E1 E2")) THEN 
          EXISTS_TAC "restr E2' L'" THEN  
          CONJ_TAC THENL 
          [ASM_REWRITE_TAC[] THEN RESTR_TAC THEN   
           REWRITE_TAC [REWRITE_RULE [ASSUME "u = tau"] 
                               (ASSUME "TRANS E2 u E2'")]  
           ; 
           EXISTS_TAC "E'''': CCS" THEN EXISTS_TAC "E2': CCS" THEN 
           EXISTS_TAC "L': (Label)set" THEN ASM_REWRITE_TAC[] ]  
          ; 
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
                       (ASSUME "STRONG_EQUIV E1 E2")) THEN 
          EXISTS_TAC "restr E2' L'" THEN 
          CONJ_TAC THENL 
          [ASM_REWRITE_TAC[] THEN RESTR_TAC THEN EXISTS_TAC "l: Label" THEN 
           ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "u = label l"] 
                                   (ASSUME "TRANS E2 u E2'")]  
           ; 
           EXISTS_TAC "E'''': CCS" THEN EXISTS_TAC "E2': CCS" THEN    
           EXISTS_TAC "L': (Label)set" THEN ASM_REWRITE_TAC[]  ] ]  
          ; 
          ASSUME_TAC (REWRITE_RULE [ASSUME "E''' = restr E2 L'"]
                             (ASSUME "TRANS E''' u E2'")) THEN 
          IMP_RES_TAC TRANS_RESTR THENL 
          [IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
                        (ASSUME "STRONG_EQUIV E1 E2")) THEN 
           EXISTS_TAC "restr E1' L'" THEN 
           CONJ_TAC THENL 
           [ASM_REWRITE_TAC[] THEN RESTR_TAC THEN  
            REWRITE_TAC [REWRITE_RULE [ASSUME "u = tau"] 
                                (ASSUME "TRANS E1 u E1'")]  
            ; 
            EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E'''': CCS" THEN   
            EXISTS_TAC "L': (Label)set" THEN ASM_REWRITE_TAC[] ]  
           ; 
           IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
                        (ASSUME "STRONG_EQUIV E1 E2")) THEN 
           EXISTS_TAC "restr E1' L'" THEN 
           CONJ_TAC THENL 
           [ASM_REWRITE_TAC[] THEN RESTR_TAC THEN EXISTS_TAC "l: Label" THEN
            ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "u = label l"] 
                                    (ASSUME "TRANS E1 u E1'")]  
            ; 
            EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E'''': CCS" THEN 
            EXISTS_TAC "L': (Label)set" THEN ASM_REWRITE_TAC[] ] ]]]);;

% --------------------------------------------------------------------------- %
% Strong equivalence is substitutive under relabelling operator.        (545) %
% --------------------------------------------------------------------------- %
let STRONG_EQUIV_SUBST_RELAB =
     prove_thm
      (`STRONG_EQUIV_SUBST_RELAB`,
       "!E E'. 
         STRONG_EQUIV E E' ==> 
         (!rf. STRONG_EQUIV (relab E rf) (relab E' rf))",   
       REPEAT STRIP_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN 
       EXISTS_TAC "\x y. ?E1 E2 rf'. (x = relab E1 rf') /\ (y = relab E2 rf') /\
                                     STRONG_EQUIV E1 E2" THEN  
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E': CCS" THEN 
        EXISTS_TAC "rf: Relabelling" THEN ASM_REWRITE_TAC[]  
        ; 
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E'' = relab E1 rf'"] 
                            (ASSUME "TRANS E'' u E1'")) THEN 
         IMP_RES_TAC TRANS_RELAB THEN 
         IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
                      (ASSUME "STRONG_EQUIV E1 E2")) THEN 
         EXISTS_TAC "relab E2' rf'" THEN CONJ_TAC THENL 
         [ASM_REWRITE_TAC[] THEN RELAB_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]  
          ; 
          EXISTS_TAC "E'''': CCS" THEN EXISTS_TAC "E2': CCS" THEN
          EXISTS_TAC "rf': Relabelling" THEN ASM_REWRITE_TAC[] ]  
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E''' = relab E2 rf'"]
                            (ASSUME "TRANS E''' u E2'")) THEN
         IMP_RES_TAC TRANS_RELAB THEN 
         IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
                      (ASSUME "STRONG_EQUIV E1 E2")) THEN 
         EXISTS_TAC "relab E1' rf'" THEN CONJ_TAC THENL 
         [ASM_REWRITE_TAC[] THEN RELAB_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] 
          ; 
          EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E'''': CCS" THEN 
          EXISTS_TAC "rf': Relabelling" THEN ASM_REWRITE_TAC[] ] ]]);;  
 
% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

