% =========================================================================== %
% FILE          : obseq_sem.ml                                                %
% DESCRIPTION   : Operational definition of observation equivalence for CCS   %
%                 and related properties                                      %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 14 November 1991                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `obseq_sem`;;

% --------------------------------------------------------------------------- %
% Define the epsilon transition relation, as the reflexive-transitive   (106) %
% closure of tau-transition.                                                  %
% --------------------------------------------------------------------------- %
let (eps_rules, eps_ind) =

    let EPS = "EPS: CCS -> CCS -> bool" in

    new_inductive_definition false `EPS_DEF` ("^EPS E E'", [])

     [ [ "TRANS E tau E'" ],
      % ------------------ %
           "^EPS E E'";

       [             ],
      % ------------- %
         "^EPS E E";

       [ "^EPS E E1"; "^EPS E1 E'" ],
      % --------------------------- %
               "^EPS E E'"         ];;

let [ONE_TAU; EPS_REFL; EPS_TRANS] = eps_rules;;

let [ONE_TAU_TAC; EPS_REFL_TAC; EPS_TRANS_TAC] = map RULE_TAC eps_rules;;

let EPS_INDUCT_TAC = RULE_INDUCT_THEN eps_ind ASSUME_TAC ASSUME_TAC;; 

% --------------------------------------------------------------------------- %
% Backward case analysis theorem (equational version).                  (456) %
% --------------------------------------------------------------------------- %
let EPS_cases = derive_cases_thm (eps_rules, eps_ind);;

% --------------------------------------------------------------------------- %
% Define the weak transition relation (double arrow transition).              %
% --------------------------------------------------------------------------- %
let WEAK_TRANS =
     new_definition
      (`WEAK_TRANS`,
       "WEAK_TRANS E u E' =
        ?E1 E2. EPS E E1 /\ TRANS E1 u E2 /\ EPS E2 E'");;

% --------------------------------------------------------------------------- %
% A transition is a particular weak transition.                          (39) %
% --------------------------------------------------------------------------- %
let TRANS_IMP_WEAK_TRANS =
     prove_thm
      (`TRANS_IMP_WEAK_TRANS`,
       "!E u E'. TRANS E u E' ==> WEAK_TRANS E u E'",
       REPEAT STRIP_TAC THEN
       PURE_ONCE_REWRITE_TAC [WEAK_TRANS] THEN
       EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E': CCS" THEN
       ASM_REWRITE_TAC [EPS_REFL]);;

% --------------------------------------------------------------------------- %
% A weak transition on tau implies the epsilon relation.                 (86) %
% --------------------------------------------------------------------------- %
let WEAK_TRANS_TAU =
     prove_thm 
      (`WEAK_TRANS_TAU`, 
       "!E E'. WEAK_TRANS E tau E' ==> EPS E E'", 
       PURE_ONCE_REWRITE_TAC [WEAK_TRANS] THEN REPEAT STRIP_TAC THEN 
       EPS_TRANS_TAC THEN EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] THEN 
       EPS_TRANS_TAC THEN EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] THEN 
       ONE_TAU_TAC THEN ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------------- %
%  EPS_AND_WEAK:                                                         (88) %
%    |- !E E1 u E2 E'.                                                        %
%        EPS E E1 /\ WEAK_TRANS E1 u E2 /\ EPS E2 E' ==> WEAK_TRANS E u E'    %
% --------------------------------------------------------------------------- % 
let EPS_AND_WEAK =
     prove_thm
      (`EPS_AND_WEAK`,
       "!E E1 u E2 E'.
         EPS E E1 /\ WEAK_TRANS E1 u E2 /\ EPS E2 E' ==> WEAK_TRANS E u E'",
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [WEAK_TRANS] THEN STRIP_TAC THEN 
       EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E2': CCS" THEN 
       ASM_REWRITE_TAC 
       [MATCH_MP  
        EPS_TRANS  
        (EXISTS ("?E1. EPS E E1 /\ EPS E1 E1'", "E1: CCS")  
                (CONJ (ASSUME "EPS E E1") (ASSUME "EPS E1 E1'"))); 
        MATCH_MP 
        EPS_TRANS
        (EXISTS ("?E1. EPS E2' E1 /\ EPS E1 E'", "E2: CCS")
                (CONJ (ASSUME "EPS E2' E2") (ASSUME "EPS E2 E'")))]);;

% --------------------------------------------------------------------------- %
% Define the weak bisimulation relation over CCS agent expressions.           %
% --------------------------------------------------------------------------- %
let WEAK_BISIM =
     new_definition
      (`WEAK_BISIM`,
       "WEAK_BISIM (Wbsm: CCS -> CCS -> bool) =
        (!E E' .
         (Wbsm E E' ==>
          (!l.
           (!E1. TRANS E (label l) E1 ==>
                 (?E2. WEAK_TRANS E' (label l) E2 /\ Wbsm E1 E2)) /\
           (!E2. TRANS E' (label l) E2 ==>
                 (?E1. WEAK_TRANS E (label l) E1 /\ Wbsm E1 E2))) /\
           (!E1. TRANS E tau E1 ==>
                 (?E2. EPS E' E2 /\ Wbsm E1 E2)) /\
           (!E2. TRANS E' tau E2 ==>
                 (?E1. EPS E E1 /\ Wbsm E1 E2))))");;

% --------------------------------------------------------------------------- %
% The identity relation is a weak bisimulation.                         (259) %
% --------------------------------------------------------------------------- %
let IDENTITY_WEAK_BISIM =
     prove_thm
      (`IDENTITY_WEAK_BISIM`,
       "WEAK_BISIM (\x y. x = y)",
       PURE_ONCE_REWRITE_TAC [WEAK_BISIM] THEN BETA_TAC THEN    
       REPEAT STRIP_TAC THENL
       [ASSUME_TAC (REWRITE_RULE [ASSUME "E: CCS = E'"] 
                           (ASSUME "TRANS E(label l)E1")) THEN 
        IMP_RES_TAC TRANS_IMP_WEAK_TRANS THEN 
        EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[]        
        ; 
        IMP_RES_TAC TRANS_IMP_WEAK_TRANS THEN 
        EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]      
        ;  
        ASSUME_TAC (REWRITE_RULE [ASSUME "E: CCS = E'"]
                           (ASSUME "TRANS E tau E1")) THEN 
        IMP_RES_TAC ONE_TAU THEN 
        EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] 
        ; 
        IMP_RES_TAC ONE_TAU THEN 
        EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] ]);;     

% --------------------------------------------------------------------------- %
% The converse of a weak bisimulation is a weak bisimulation.           (805) %
% --------------------------------------------------------------------------- %
let CONVERSE_WEAK_BISIM =
     prove_thm
      (`CONVERSE_WEAK_BISIM`,
       "!Wbsm. WEAK_BISIM Wbsm ==> WEAK_BISIM (\x y. Wbsm y x)",
       GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [WEAK_BISIM] THEN BETA_TAC THEN   
       REPEAT STRIP_TAC THEN RES_TAC THENL
       [EXISTS_TAC "E1': CCS" ;
        EXISTS_TAC "E2': CCS" ;
        EXISTS_TAC "E1': CCS" ;
        EXISTS_TAC "E2': CCS"] THEN ASM_REWRITE_TAC[]);;   

% --------------------------------------------------------------------------- %
% Some auxiliary results for proving that the composition of two weak         %
% bisimulations is a weak bisimulation.                                       %
% --------------------------------------------------------------------------- %

% --------------------------------------------------------------------------- %
% EPS_TRANS_AUX: different formulation of case 1 in Milner's proof.     (310) %
% --------------------------------------------------------------------------- %
let EPS_TRANS_AUX =    
     prove_thm 
      (`EPS_TRANS_AUX`, 
       "!E E1. 
         EPS E E1 ==> 
         (!Wbsm E'. 
           WEAK_BISIM Wbsm /\ Wbsm E E' ==> (?E2. EPS E' E2 /\ Wbsm E1 E2))", 
       EPS_INDUCT_TAC THENL    
       [REPEAT STRIP_TAC THEN 
        IMP_RES_TAC 
        (CONJUNCT2 
         (MATCH_MP (EQ_MP (SPEC_ALL WEAK_BISIM) (ASSUME "WEAK_BISIM Wbsm")) 
          (ASSUME "(Wbsm: CCS -> CCS -> bool) E E''"))) THEN 
        EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
        ; 
        REPEAT STRIP_TAC THEN EXISTS_TAC "E': CCS" THEN 
        ASM_REWRITE_TAC [EPS_REFL] 
        ; 
        REPEAT STRIP_TAC THEN 
        STRIP_ASSUME_TAC
        (MATCH_MP
         (ASSUME "!Wbsm E'.
                   WEAK_BISIM Wbsm /\ Wbsm E E' ==>
                   (?E2. EPS E' E2 /\ Wbsm E1 E2)")
         (CONJ (ASSUME "WEAK_BISIM Wbsm")
               (ASSUME "(Wbsm: CCS -> CCS -> bool) E E''"))) THEN
        STRIP_ASSUME_TAC
        (MATCH_MP
         (ASSUME "!Wbsm E''.
                   WEAK_BISIM Wbsm /\ Wbsm E1 E'' ==>
                   (?E2. EPS E'' E2 /\ Wbsm E' E2)") 
         (CONJ (ASSUME "WEAK_BISIM Wbsm")
               (ASSUME "(Wbsm: CCS -> CCS -> bool) E1 E2"))) THEN 
        EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[] THEN 
        EPS_TRANS_TAC THEN EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] ]);;  

% --------------------------------------------------------------------------- %
% Symmetric auxiliary result for EPS.                                   (182) %
% --------------------------------------------------------------------------- %
let INVERSE_REL =
     prove_thm
      (`INVERSE_REL`,
       "!(Rel: * -> ** -> bool) z w. Rel z w ==> (\x y. Rel y x) w z",
       REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[]);;

let EPS_TRANS_AUX_SYM =
     prove_thm
      (`EPS_TRANS_AUX_SYM`,
       "!E' E1.
         EPS E' E1 ==>
         (!Wbsm E. WEAK_BISIM Wbsm /\ Wbsm E E' ==>
          (?E2. EPS E E2 /\ Wbsm E2 E1))",
       REPEAT STRIP_TAC THEN IMP_RES_TAC INVERSE_REL THEN  
       IMP_RES_TAC CONVERSE_WEAK_BISIM THEN
       IMP_RES_TAC
       (SPEC "\x y. (Wbsm: CCS -> CCS -> bool) y x"
        (MATCH_MP EPS_TRANS_AUX (ASSUME "EPS E' E1"))) THEN 
       ASSUME_TAC
       (BETA_RULE (ASSUME "(\x y. (Wbsm: CCS -> CCS -> bool)y x)E1 E2'")) THEN
       EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------------- %
% Auxiliary result for WEAK_TRANS.                                      (197) % 
% --------------------------------------------------------------------------- %
let WEAK_TRANS_AUX =
     prove_thm
      (`WEAK_TRANS_AUX`, 
       "!E l E1. WEAK_TRANS E (label l) E1 ==>  
        (!Wbsm E'. WEAK_BISIM Wbsm /\ Wbsm E E' ==>  
         (?E2. WEAK_TRANS E' (label l) E2 /\ Wbsm E1 E2))",  
       REPEAT STRIP_TAC THEN 
       STRIP_ASSUME_TAC (REWRITE_RULE [WEAK_TRANS]
                         (ASSUME "WEAK_TRANS E(label l)E1")) THEN
       STRIP_ASSUME_TAC
       (MATCH_MP
        (MATCH_MP EPS_TRANS_AUX (ASSUME "EPS E E1'"))
        (CONJ (ASSUME "WEAK_BISIM Wbsm")
              (ASSUME "(Wbsm: CCS -> CCS -> bool) E E'"))) THEN
       IMP_RES_TAC
       (MATCH_MP
        (EQ_MP (SPEC_ALL WEAK_BISIM) (ASSUME "WEAK_BISIM Wbsm"))
        (ASSUME "(Wbsm: CCS -> CCS -> bool) E1' E2'")) THEN
       STRIP_ASSUME_TAC
       (MATCH_MP
        (MATCH_MP EPS_TRANS_AUX (ASSUME "EPS E2 E1"))
        (CONJ (ASSUME "WEAK_BISIM Wbsm")
              (ASSUME "(Wbsm: CCS -> CCS -> bool) E2 E2''"))) THEN
       ASSUME_TAC
       (MATCH_MP EPS_AND_WEAK
        (LIST_CONJ [ASSUME "EPS E' E2'";
                    ASSUME "WEAK_TRANS E2'(label l)E2''";
                    ASSUME "EPS E2'' E2'''"])) THEN
       EXISTS_TAC "E2''': CCS" THEN ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------------- %
% Symmetric auxiliary result for WEAK_TRANS.                            (173) %
% --------------------------------------------------------------------------- %
let WEAK_TRANS_AUX_SYM = 
     prove_thm
      (`WEAK_TRANS_AUX_SYM`, 
       "!E' l E1. 
         WEAK_TRANS E'(label l)E1 ==> 
         (!Wbsm E. WEAK_BISIM Wbsm /\ Wbsm E E' ==> 
          (?E2. WEAK_TRANS E(label l)E2 /\ Wbsm E2 E1))", 
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC (ISPEC "Wbsm: CCS -> CCS -> bool" INVERSE_REL) THEN 
       IMP_RES_TAC CONVERSE_WEAK_BISIM THEN 
       IMP_RES_TAC
       (SPEC "\x y. (Wbsm: CCS -> CCS -> bool) y x"  
        (MATCH_MP WEAK_TRANS_AUX (ASSUME "WEAK_TRANS E'(label l)E1"))) THEN
       ASSUME_TAC
       (BETA_RULE (ASSUME "(\x y. (Wbsm: CCS -> CCS -> bool)y x)E1 E2'")) THEN
       EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[]);;
 
% --------------------------------------------------------------------------- %
% The composition of two weak bisimulations is a weak bisimulation.     (579) %
% --------------------------------------------------------------------------- %
let COMP_WEAK_BISIM =
     prove_thm
      (`COMP_WEAK_BISIM`,
       "!Wbsm1 Wbsm2. 
         WEAK_BISIM Wbsm1 /\ WEAK_BISIM Wbsm2 ==>
         WEAK_BISIM (\x z. ?y. Wbsm1 x y /\ Wbsm2 y z)",
       REPEAT STRIP_TAC THEN 
       PURE_ONCE_REWRITE_TAC [WEAK_BISIM] THEN BETA_TAC THEN   
       REPEAT STRIP_TAC THENL 
       [IMP_RES_TAC TRANS_IMP_WEAK_TRANS THEN 
        STRIP_ASSUME_TAC    
        (MATCH_MP 
         (MATCH_MP WEAK_TRANS_AUX (ASSUME "WEAK_TRANS E(label l)E1"))   
         (CONJ (ASSUME "WEAK_BISIM Wbsm1") 
               (ASSUME "(Wbsm1: CCS -> CCS -> bool) E y"))) THEN           
        STRIP_ASSUME_TAC  
        (MATCH_MP
         (MATCH_MP WEAK_TRANS_AUX (ASSUME "WEAK_TRANS y(label l)E2"))
         (CONJ (ASSUME "WEAK_BISIM Wbsm2")
               (ASSUME "(Wbsm2: CCS -> CCS -> bool) y E'"))) THEN
        EXISTS_TAC "E2': CCS" THEN  
        ASM_REWRITE_TAC[] THEN EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]   
        ; 
        IMP_RES_TAC TRANS_IMP_WEAK_TRANS THEN 
        STRIP_ASSUME_TAC  
        (MATCH_MP
         (MATCH_MP WEAK_TRANS_AUX_SYM (ASSUME "WEAK_TRANS E'(label l)E2"))
         (CONJ (ASSUME "WEAK_BISIM Wbsm2")
               (ASSUME "(Wbsm2: CCS -> CCS -> bool) y E'"))) THEN
        STRIP_ASSUME_TAC  
        (MATCH_MP
         (MATCH_MP WEAK_TRANS_AUX_SYM (ASSUME "WEAK_TRANS y(label l)E2'"))
         (CONJ (ASSUME "WEAK_BISIM Wbsm1")
               (ASSUME "(Wbsm1: CCS -> CCS -> bool) E y"))) THEN
        EXISTS_TAC "E2'': CCS" THEN 
        ASM_REWRITE_TAC[] THEN EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[]  
        ; 
        IMP_RES_TAC ONE_TAU THEN 
        STRIP_ASSUME_TAC    
        (MATCH_MP    
         (MATCH_MP EPS_TRANS_AUX (ASSUME "EPS E E1")) 
         (CONJ (ASSUME "WEAK_BISIM Wbsm1")
               (ASSUME "(Wbsm1: CCS -> CCS -> bool) E y"))) THEN           
        STRIP_ASSUME_TAC  
        (MATCH_MP
         (MATCH_MP EPS_TRANS_AUX (ASSUME "EPS y E2")) 
         (CONJ (ASSUME "WEAK_BISIM Wbsm2")
               (ASSUME "(Wbsm2: CCS -> CCS -> bool) y E'"))) THEN
        EXISTS_TAC "E2': CCS" THEN 
        ASM_REWRITE_TAC[] THEN EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]  
        ; 
        IMP_RES_TAC ONE_TAU THEN 
        STRIP_ASSUME_TAC
        (MATCH_MP
         (MATCH_MP EPS_TRANS_AUX_SYM (ASSUME "EPS E' E2")) 
         (CONJ (ASSUME "WEAK_BISIM Wbsm2")
               (ASSUME "(Wbsm2: CCS -> CCS -> bool) y E'"))) THEN 
        STRIP_ASSUME_TAC
        (MATCH_MP
         (MATCH_MP EPS_TRANS_AUX_SYM (ASSUME "EPS y E2'"))
         (CONJ (ASSUME "WEAK_BISIM Wbsm1")
               (ASSUME "(Wbsm1: CCS -> CCS -> bool) E y"))) THEN
        EXISTS_TAC "E2'': CCS" THEN ASM_REWRITE_TAC[] THEN   
        EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[] ]);;   

% --------------------------------------------------------------------------- %
% The union of two weak bisimulations is a weak bisimulation.          (2060) %
% --------------------------------------------------------------------------- %
let UNION_WEAK_BISIM =
     prove_thm
      (`UNION_WEAK_BISIM`,
       "!Wbsm1 Wbsm2. 
         WEAK_BISIM Wbsm1 /\ WEAK_BISIM Wbsm2 ==>  
         WEAK_BISIM (\x y. Wbsm1 x y \/ Wbsm2 x y)",   
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [WEAK_BISIM] THEN BETA_TAC THEN 
       REPEAT STRIP_TAC THEN RES_TAC THENL 
       [EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS"; 
        EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS"; 
        EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS";
        EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS"] THEN ASM_REWRITE_TAC[]);; 

% --------------------------------------------------------------------------- %
% Define the observation equivalence over CCS agent expressions.              %
% --------------------------------------------------------------------------- %
let OBS_EQUIV =
     new_definition
      (`OBS_EQUIV`,
       "OBS_EQUIV E E' = (?Wbsm. Wbsm E E' /\ WEAK_BISIM Wbsm)");;

% --------------------------------------------------------------------------- %
% Observation equivalence is an equivalence relation.                         %
% --------------------------------------------------------------------------- %

% --------------------------------------------------------------------------- %
% Observation equivalence is a reflexive relation.                       (28) %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_REFL =
     prove_thm
      (`OBS_EQUIV_REFL`,
       "!E. OBS_EQUIV E E",
       GEN_TAC THEN PURE_ONCE_REWRITE_TAC [OBS_EQUIV] THEN
       EXISTS_TAC "\x y: CCS. x = y" THEN BETA_TAC THEN
       REWRITE_TAC [IDENTITY_WEAK_BISIM]);;

% --------------------------------------------------------------------------- %
% Observation equivalence is a symmetric relation.                       (57) %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_SYM =
     prove_thm
      (`OBS_EQUIV_SYM`,
       "!E E'. OBS_EQUIV E E' ==> OBS_EQUIV E' E",
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [OBS_EQUIV] THEN STRIP_TAC THEN     
       EXISTS_TAC "\x y. (Wbsm: CCS -> CCS -> bool) y x" THEN
       BETA_TAC THEN IMP_RES_TAC CONVERSE_WEAK_BISIM THEN
       ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------------- %
% Observation equivalence is a transitive relation.                     (147) %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_TRANS = 
     prove_thm
      (`OBS_EQUIV_TRANS`, 
       "!E E' E''. 
         OBS_EQUIV E E' /\ OBS_EQUIV E' E'' ==> OBS_EQUIV E E''", 
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [OBS_EQUIV] THEN STRIP_TAC THEN 
       EXISTS_TAC "\x z. ?y. (Wbsm: CCS -> CCS -> bool) x y /\
                             (Wbsm': CCS -> CCS -> bool) y z" THEN   
       CONJ_TAC THENL   
       [BETA_TAC THEN EXISTS_TAC "E': CCS" THEN ASM_REWRITE_TAC[] ;  
        IMP_RES_TAC COMP_WEAK_BISIM ]);;   

% --------------------------------------------------------------------------- %
% Prove that observation equivalence satisfies the property (*).              %
% --------------------------------------------------------------------------- %

% --------------------------------------------------------------------------- %
% Definition 7, page 110 in Milner's book.                                    %
% --------------------------------------------------------------------------- %
let OBS_EQUIV' = 
     new_definition
      (`OBS_EQUIV'`,  
       "OBS_EQUIV' E E' =     
        (!l.
          (!E1. TRANS E (label l) E1 ==>
                (?E2. WEAK_TRANS E' (label l) E2 /\ OBS_EQUIV E1 E2)) /\
          (!E2. TRANS E' (label l) E2 ==>
                (?E1. WEAK_TRANS E (label l) E1 /\ OBS_EQUIV E1 E2))) /\
          (!E1. TRANS E tau E1 ==>
                (?E2. EPS E' E2 /\ OBS_EQUIV E1 E2)) /\
          (!E2. TRANS E' tau E2 ==>
                (?E1. EPS E E1 /\ OBS_EQUIV E1 E2))");;

% --------------------------------------------------------------------------- %
% Observation equivalence implies the new relation.                     (507) %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_IMP_OBS_EQUIV' =    
     prove_thm
      (`OBS_EQUIV_IMP_OBS_EQUIV'`,
       "!E E'. OBS_EQUIV E E' ==> OBS_EQUIV' E E'",
       REPEAT GEN_TAC THEN 
       REWRITE_TAC [OBS_EQUIV'; OBS_EQUIV] THEN
       REPEAT STRIP_TAC THEN 
       IMP_RES_TAC 
       (MATCH_MP  
        (EQ_MP (SPEC "Wbsm: CCS -> CCS -> bool" WEAK_BISIM)   
               (ASSUME "WEAK_BISIM Wbsm"))    
        (ASSUME "(Wbsm: CCS -> CCS -> bool) E E'")) 
       THENL  
       [EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS"; 
        EXISTS_TAC "E2: CCS"; EXISTS_TAC "E1: CCS"] THEN 
       ASM_REWRITE_TAC[] THEN 
       EXISTS_TAC "Wbsm: CCS -> CCS -> bool" THEN ASM_REWRITE_TAC[]);;  

% --------------------------------------------------------------------------- %
% Lemma 3, page 110 in Milner's book:                                   (310) %
% the new relation OBS_EQUIV' is a weak bisimulation.                         %
% --------------------------------------------------------------------------- % 
let OBS_Lemma3 =                                 
     prove_thm
      (`OBS_Lemma3`,
       "WEAK_BISIM OBS_EQUIV'",
       PURE_ONCE_REWRITE_TAC [WEAK_BISIM] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC  
        (CONJUNCT1(EQ_MP (SPEC_ALL OBS_EQUIV') 
                         (ASSUME "OBS_EQUIV' E E'"))) THEN 
        EXISTS_TAC "E2: CCS" THEN
        IMP_RES_TAC OBS_EQUIV_IMP_OBS_EQUIV' THEN ASM_REWRITE_TAC[]    
        ;
        IMP_RES_TAC 
        (CONJUNCT1(EQ_MP (SPEC_ALL OBS_EQUIV')
                         (ASSUME "OBS_EQUIV' E E'"))) THEN 
        EXISTS_TAC "E1: CCS" THEN
        IMP_RES_TAC OBS_EQUIV_IMP_OBS_EQUIV' THEN ASM_REWRITE_TAC[] 
        ; 
        IMP_RES_TAC 
        (CONJUNCT2(EQ_MP (SPEC_ALL OBS_EQUIV')
                         (ASSUME "OBS_EQUIV' E E'"))) THEN 
        EXISTS_TAC "E2: CCS" THEN
        IMP_RES_TAC OBS_EQUIV_IMP_OBS_EQUIV' THEN ASM_REWRITE_TAC[]    
        ;
        IMP_RES_TAC 
        (CONJUNCT2(EQ_MP (SPEC_ALL OBS_EQUIV')
                         (ASSUME "OBS_EQUIV' E E'"))) THEN 
        EXISTS_TAC "E1: CCS" THEN
        IMP_RES_TAC OBS_EQUIV_IMP_OBS_EQUIV' THEN ASM_REWRITE_TAC[] ]);; 

% --------------------------------------------------------------------------- %
% The new relation implies observation equivalence.                      (25) %
% --------------------------------------------------------------------------- %
let OBS_EQUIV'_IMP_OBS_EQUIV =              
     prove_thm
      (`OBS_EQUIV'_IMP_OBS_EQUIV`,
       "!E E'. OBS_EQUIV' E E' ==> OBS_EQUIV E E'",
       REPEAT STRIP_TAC THEN
       PURE_ONCE_REWRITE_TAC [OBS_EQUIV] THEN
       EXISTS_TAC "OBS_EQUIV'" THEN ASM_REWRITE_TAC [OBS_Lemma3]);;

% --------------------------------------------------------------------------- %
% Observation equivalence satisfies the property (*).                    (50) %
% --------------------------------------------------------------------------- %
let OBS_PROP_STAR =           
     prove_thm
      (`OBS_PROP_STAR`,
       "!E E'. 
         OBS_EQUIV E E' =
         (!l.
           (!E1. TRANS E (label l) E1 ==>
                 (?E2. WEAK_TRANS E' (label l) E2 /\ OBS_EQUIV E1 E2)) /\
           (!E2. TRANS E' (label l) E2 ==>
                 (?E1. WEAK_TRANS E (label l) E1 /\ OBS_EQUIV E1 E2))) /\
           (!E1. TRANS E tau E1 ==>
                 (?E2. EPS E' E2 /\ OBS_EQUIV E1 E2)) /\
           (!E2. TRANS E' tau E2 ==>
                 (?E1. EPS E E1 /\ OBS_EQUIV E1 E2))",   
       REPEAT GEN_TAC THEN EQ_TAC THENL
       [PURE_ONCE_REWRITE_TAC
        [ONCE_REWRITE_RULE [OBS_EQUIV'] OBS_EQUIV_IMP_OBS_EQUIV'] ;
        PURE_ONCE_REWRITE_TAC
        [ONCE_REWRITE_RULE [OBS_EQUIV'] OBS_EQUIV'_IMP_OBS_EQUIV] ]);;

let OBS_PROP_STAR_LR = save_thm(`OBS_PROP_STAR_LR`, EQ_IMP_LR OBS_PROP_STAR);; 

% --------------------------------------------------------------------------- %
% Observation equivalence is substitutive under prefix operator.        (468) %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_SUBST_PREFIX = 
     prove_thm 
      (`OBS_EQUIV_SUBST_PREFIX`, 
       "!E E'. 
         OBS_EQUIV E E' ==> (!u. OBS_EQUIV(prefix u E)(prefix u E'))", 
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC 
           [SPECL ["prefix u E"; "prefix u E'"] OBS_PROP_STAR] THEN
       REPEAT STRIP_TAC THENL 
       [IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E': CCS" THEN
        ASM_REWRITE_TAC [WEAK_TRANS] THEN EXISTS_TAC "prefix u E'" THEN  
        EXISTS_TAC "E': CCS" THEN ASM_REWRITE_TAC [EPS_REFL; PREFIX] 
        ; 
        IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E: CCS" THEN 
        ASM_REWRITE_TAC [WEAK_TRANS] THEN EXISTS_TAC "prefix u E" THEN
        EXISTS_TAC "E: CCS" THEN ASM_REWRITE_TAC [EPS_REFL; PREFIX]
        ; 
        IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E': CCS" THEN 
        ASM_REWRITE_TAC[] THEN ONE_TAU_TAC THEN ASM_REWRITE_TAC [PREFIX]  
        ; 
        IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E: CCS" THEN 
        ASM_REWRITE_TAC[] THEN ONE_TAU_TAC THEN ASM_REWRITE_TAC [PREFIX] ]);; 

% --------------------------------------------------------------------------- %
% Definition of stable agent (tau-derivative do not exist).                   %
% --------------------------------------------------------------------------- %
let STABLE =
     new_definition
      (`STABLE`,
       "STABLE E = (!u E'. TRANS E u E' ==> ~(u = tau))");; 

% --------------------------------------------------------------------------- %
% Properties of stable agents with respect to the epsilon and weak transition %
% relations.                                                         (166+76) %
% --------------------------------------------------------------------------- %
let EPS_STABLE =
     prove_thm
      (`EPS_STABLE`,
       "!E E'. EPS E E' ==> (STABLE E ==> (E' = E))",
       EPS_INDUCT_TAC THENL 
       [REWRITE_TAC [STABLE] THEN DISCH_TAC THEN
        CHECK_ASSUME_TAC
        (REWRITE_RULE []
         (MATCH_MP (ASSUME "!u E'. TRANS E u E' ==> ~(u = tau)")
                   (ASSUME "TRANS E tau E'")))
        ;
        REWRITE_TAC[]
        ;
        DISCH_TAC THEN RES_TAC THEN
        REWRITE_TAC 
        [MATCH_MP (REWRITE_RULE [ASSUME "E1 = E: CCS"]
                          (ASSUME "STABLE E1 ==> (E' = E1)")) 
         (ASSUME "STABLE E")] ]);; 

let WEAK_TRANS_STABLE =
     prove_thm
      (`WEAK_TRANS_STABLE`,
       "!E l E'.
         WEAK_TRANS E (label l) E' /\ STABLE E ==>
         (?E''.  TRANS E (label l) E'' /\ EPS E'' E')",
       REPEAT GEN_TAC THEN
       REWRITE_TAC [WEAK_TRANS] THEN STRIP_TAC THEN
       ASSUME_TAC
       (MATCH_MP
        (MATCH_MP EPS_STABLE (ASSUME "EPS E E1"))
        (ASSUME "STABLE E")) THEN
       ASSUME_TAC (REWRITE_RULE [ASSUME "E1 = E: CCS"]
                          (ASSUME "TRANS E1(label l)E2")) THEN
       EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------------- %
% Observation equivalence of stable agents is preserved by             (1721) %
% binary summation.                                                           %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_PRESD_BY_SUM = 
     prove_thm
      (`OBS_EQUIV_PRESD_BY_SUM`,
       "!E1 E1' E2 E2'.
         OBS_EQUIV E1 E1' /\ STABLE E1 /\ STABLE E1' /\     
         OBS_EQUIV E2 E2' /\ STABLE E2 /\ STABLE E2' ==>    
         OBS_EQUIV(sum E1 E2)(sum E1' E2')",  
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [OBS_PROP_STAR] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC TRANS_SUM THENL
        [RES_TAC THEN EXISTS_TAC "E2'': CCS" THEN
         ASM_REWRITE_TAC [WEAK_TRANS] THEN
         EXISTS_TAC "sum E1' E2'" THEN REWRITE_TAC [EPS_REFL] THEN
         STRIP_ASSUME_TAC
         (MATCH_MP WEAK_TRANS_STABLE
          (CONJ (ASSUME "WEAK_TRANS E1'(label l)E2''")
                (ASSUME "STABLE E1'"))) THEN
         EXISTS_TAC "E'': CCS" THEN ASM_REWRITE_TAC[] THEN
         SUM1_TAC THEN ASM_REWRITE_TAC[]
         ;
         RES_TAC THEN EXISTS_TAC "E2'': CCS" THEN
         ASM_REWRITE_TAC [WEAK_TRANS] THEN
         EXISTS_TAC "sum E1' E2'" THEN REWRITE_TAC [EPS_REFL] THEN
         STRIP_ASSUME_TAC
         (MATCH_MP WEAK_TRANS_STABLE
          (CONJ (ASSUME "WEAK_TRANS E2'(label l)E2''")
                (ASSUME "STABLE E2'"))) THEN
         EXISTS_TAC "E'': CCS" THEN ASM_REWRITE_TAC[] THEN
         SUM2_TAC THEN ASM_REWRITE_TAC[] ]
        ;
        IMP_RES_TAC TRANS_SUM THENL
        [RES_TAC THEN EXISTS_TAC "E1'': CCS" THEN
         ASM_REWRITE_TAC [WEAK_TRANS] THEN
         EXISTS_TAC "sum E1 E2" THEN REWRITE_TAC [EPS_REFL] THEN
         STRIP_ASSUME_TAC
         (MATCH_MP WEAK_TRANS_STABLE
          (CONJ (ASSUME "WEAK_TRANS E1(label l)E1''")
                (ASSUME "STABLE E1"))) THEN
         EXISTS_TAC "E'': CCS" THEN ASM_REWRITE_TAC[] THEN
         SUM1_TAC THEN ASM_REWRITE_TAC[]
         ;
         RES_TAC THEN EXISTS_TAC "E1'': CCS" THEN
         ASM_REWRITE_TAC [WEAK_TRANS] THEN
         EXISTS_TAC "sum E1 E2" THEN REWRITE_TAC [EPS_REFL] THEN
         STRIP_ASSUME_TAC
         (MATCH_MP WEAK_TRANS_STABLE
          (CONJ (ASSUME "WEAK_TRANS E2(label l)E1''")
                (ASSUME "STABLE E2"))) THEN
         EXISTS_TAC "E'': CCS" THEN ASM_REWRITE_TAC[] THEN
         SUM2_TAC THEN ASM_REWRITE_TAC[] ]
        ;
        IMP_RES_TAC TRANS_SUM THENL
        [CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (SPEC "E1: CCS" STABLE) (ASSUME "STABLE E1"))
           (ASSUME "TRANS E1 tau E1''")))
         ;
         CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (SPEC "E2: CCS" STABLE) (ASSUME "STABLE E2"))
           (ASSUME "TRANS E2 tau E1''"))) ]
        ;
        IMP_RES_TAC TRANS_SUM THENL
        [CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (SPEC "E1': CCS" STABLE) (ASSUME "STABLE E1'")) 
           (ASSUME "TRANS E1' tau E2''")))
         ;
         CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (SPEC "E2': CCS" STABLE) (ASSUME "STABLE E2'")) 
           (ASSUME "TRANS E2' tau E2''"))) ]]);;

% --------------------------------------------------------------------------- %
% Observation equivalence of stable agents is substitutive under binary       %
% summation on the right.                                               (965) %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_SUBST_SUM_R = 
     prove_thm 
      (`OBS_EQUIV_SUBST_SUM_R`,  
       "!E E'.
         OBS_EQUIV E E' /\ STABLE E /\ STABLE E' ==>
         (!E''. OBS_EQUIV (sum E E'') (sum E' E''))", 
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [OBS_PROP_STAR] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC TRANS_SUM THENL
        [RES_TAC THEN EXISTS_TAC "E2: CCS" THEN
         ASM_REWRITE_TAC [WEAK_TRANS] THEN EXISTS_TAC "sum E' E''" THEN
         REWRITE_TAC [EPS_REFL] THEN
         STRIP_ASSUME_TAC
         (MATCH_MP WEAK_TRANS_STABLE
          (CONJ (ASSUME "WEAK_TRANS E'(label l)E2") (ASSUME "STABLE E'"))) THEN
         EXISTS_TAC "E''': CCS" THEN ASM_REWRITE_TAC[] THEN SUM1_TAC THEN
         ASM_REWRITE_TAC[]
         ;
         EXISTS_TAC "E1: CCS" THEN REWRITE_TAC [OBS_EQUIV_REFL; WEAK_TRANS] THEN
         EXISTS_TAC "sum E' E''" THEN EXISTS_TAC "E1: CCS" THEN
         REWRITE_TAC [EPS_REFL] THEN SUM2_TAC THEN ASM_REWRITE_TAC[] ]
        ;
        IMP_RES_TAC TRANS_SUM THENL
        [RES_TAC THEN EXISTS_TAC "E1: CCS" THEN
         ASM_REWRITE_TAC [WEAK_TRANS] THEN EXISTS_TAC "sum E E''" THEN
         REWRITE_TAC [EPS_REFL] THEN
         STRIP_ASSUME_TAC
         (MATCH_MP WEAK_TRANS_STABLE
          (CONJ (ASSUME "WEAK_TRANS E(label l)E1") (ASSUME "STABLE E"))) THEN
         EXISTS_TAC "E''': CCS" THEN ASM_REWRITE_TAC[] THEN SUM1_TAC THEN
         ASM_REWRITE_TAC[]
         ;
         EXISTS_TAC "E2: CCS" THEN REWRITE_TAC [OBS_EQUIV_REFL; WEAK_TRANS] THEN
         EXISTS_TAC "sum E E''" THEN EXISTS_TAC "E2: CCS" THEN
         REWRITE_TAC [EPS_REFL] THEN SUM2_TAC THEN ASM_REWRITE_TAC[] ] 
        ; 
        IMP_RES_TAC TRANS_SUM THENL
        [CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (SPEC "E: CCS" STABLE) (ASSUME "STABLE E"))
           (ASSUME "TRANS E tau E1")))
         ;
         EXISTS_TAC "E1: CCS" THEN REWRITE_TAC [OBS_EQUIV_REFL] THEN
         PURE_ONCE_REWRITE_TAC [EPS_cases] THEN DISJ1_TAC THEN SUM2_TAC THEN
         ASM_REWRITE_TAC[] ] 
        ;  
        IMP_RES_TAC TRANS_SUM THENL 
        [CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (SPEC "E': CCS" STABLE) (ASSUME "STABLE E'"))
           (ASSUME "TRANS E' tau E2")))
         ;
         EXISTS_TAC "E2: CCS" THEN REWRITE_TAC [OBS_EQUIV_REFL] THEN
         PURE_ONCE_REWRITE_TAC [EPS_cases] THEN DISJ1_TAC THEN SUM2_TAC THEN
         ASM_REWRITE_TAC[] ] ]);; 

% --------------------------------------------------------------------------- %
% The epsilon relation is preserved by the parallel operator.        (479+91) %
% --------------------------------------------------------------------------- %
let EPS_PAR =
     prove_thm
      (`EPS_PAR`,
       "!E E'.
         EPS E E' ==>
         !E''. EPS (par E E'') (par E' E'') /\ EPS (par E'' E) (par E'' E')",
       EPS_INDUCT_TAC THENL 
       [GEN_TAC THEN CONJ_TAC THENL
        [IMP_RES_TAC PAR1 THEN
         ASSUME_TAC (SPEC "E'': CCS"
                     (ASSUME "!E''. TRANS(par E E'')tau(par E' E'')")) THEN
         IMP_RES_TAC ONE_TAU
         ;
         IMP_RES_TAC PAR2 THEN
         ASSUME_TAC (SPEC "E'': CCS"
                     (ASSUME "!E''. TRANS(par E'' E)tau(par E'' E')")) THEN
         IMP_RES_TAC ONE_TAU ]
        ;
        REWRITE_TAC [EPS_REFL]
        ;
        GEN_TAC THEN
        CONJUNCTS_THEN ASSUME_TAC
        (SPEC "E'': CCS"
         (ASSUME "!E''. EPS(par E E'')(par E1 E'') /\
                        EPS(par E'' E)(par E'' E1)")) THEN
        CONJUNCTS_THEN ASSUME_TAC
        (SPEC "E'': CCS"
         (ASSUME "!E''. EPS(par E1 E'')(par E' E'') /\
                        EPS(par E'' E1)(par E'' E')")) THEN
        IMP_RES_TAC EPS_TRANS THEN ASM_REWRITE_TAC[] ]);;

let EPS_PAR_PAR =
     prove_thm
      (`EPS_PAR_PAR`,
       "!E1 E2 F1 F2.
         EPS E1 E2 /\ EPS F1 F2 ==> EPS (par E1 F1) (par E2 F2)",
       REPEAT STRIP_TAC THEN
       EPS_TRANS_TAC THEN EXISTS_TAC "par E2 F1" THEN
       IMP_RES_TAC EPS_PAR THEN ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------------- %
% The relation WEAK_TRANS is preserved by the parallel operator.        (272) %
% --------------------------------------------------------------------------- %
let WEAK_PAR =
     prove_thm
      (`WEAK_PAR`,
       "!E u E'.
         WEAK_TRANS E u E' ==>
         !E''. WEAK_TRANS (par E E'') u (par E' E'') /\
               WEAK_TRANS (par E'' E) u (par E'' E')",
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [WEAK_TRANS] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC EPS_PAR THEN EXISTS_TAC "par E1 E''" THEN
        EXISTS_TAC "par E2 E''" THEN ASM_REWRITE_TAC[] THEN PAR1_TAC THEN
        ASM_REWRITE_TAC[]
        ;
        IMP_RES_TAC EPS_PAR THEN EXISTS_TAC "par E'' E1" THEN
        EXISTS_TAC "par E'' E2" THEN ASM_REWRITE_TAC[] THEN PAR2_TAC THEN
        ASM_REWRITE_TAC[] ]);;

% --------------------------------------------------------------------------- %
% Observation equivalence is preserved by parallel operator.           (2839) % 
% --------------------------------------------------------------------------- %
let OBS_EQUIV_PRESD_BY_PAR =
     prove_thm
      (`OBS_EQUIV_PRESD_BY_PAR`,
       "!E1 E1' E2 E2'.
         OBS_EQUIV E1 E1' /\ OBS_EQUIV E2 E2' ==>
         OBS_EQUIV (par E1 E2) (par E1' E2')",
       REPEAT STRIP_TAC THEN
       PURE_ONCE_REWRITE_TAC [OBS_EQUIV] THEN
       EXISTS_TAC "\x y.
                   (?F1 F1' F2 F2'.
                    (x = par F1 F2) /\ (y = par F1' F2') /\
                    OBS_EQUIV F1 F1' /\ OBS_EQUIV F2 F2')" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "E1: CCS" THEN
        EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E2: CCS" THEN
        EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[]
        ;
        PURE_ONCE_REWRITE_TAC [WEAK_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E = par F1 F2"]
                            (ASSUME "TRANS E(label l)E1''")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [IMP_RES_TAC
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR 
                      (ASSUME "OBS_EQUIV F1 F1'"))) THEN
          EXISTS_TAC "par E2'' F2'" THEN
          CONJ_TAC THENL
          [ASM_REWRITE_TAC[] THEN IMP_RES_TAC WEAK_PAR THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2'': CCS" THEN 
           EXISTS_TAC "F2: CCS" THEN EXISTS_TAC "F2': CCS" THEN
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F2 F2'"))) THEN
          EXISTS_TAC "par F1' E2''" THEN
          CONJ_TAC THENL
          [ASM_REWRITE_TAC[] THEN IMP_RES_TAC WEAK_PAR THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "F1: CCS" THEN EXISTS_TAC "F1': CCS" THEN
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2'': CCS" THEN 
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC Action_Distinct_label ]
         ;
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = par F1' F2'"]
                            (ASSUME "TRANS E'(label l)E2''")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [IMP_RES_TAC
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F1 F1'"))) THEN
          EXISTS_TAC "par E1''' F2" THEN
          CONJ_TAC THENL
          [ASM_REWRITE_TAC[] THEN IMP_RES_TAC WEAK_PAR THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E1'': CCS" THEN 
           EXISTS_TAC "F2: CCS" THEN EXISTS_TAC "F2': CCS" THEN 
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F2 F2'"))) THEN
          EXISTS_TAC "par F1 E1''': CCS" THEN
          CONJ_TAC THENL
          [ASM_REWRITE_TAC[] THEN IMP_RES_TAC WEAK_PAR THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "F1: CCS" THEN EXISTS_TAC "F1': CCS" THEN
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E1'': CCS" THEN 
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC Action_Distinct_label ]
         ;
         ASSUME_TAC (REWRITE_RULE [ASSUME "E = par F1 F2"]
                            (ASSUME "TRANS E tau E1''")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [IMP_RES_TAC
          (CONJUNCT2 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F1 F1'"))) THEN
          EXISTS_TAC "par E2'' F2'" THEN
          CONJ_TAC THENL
          [ASM_REWRITE_TAC[] THEN IMP_RES_TAC EPS_PAR THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2'': CCS" THEN 
           EXISTS_TAC "F2: CCS" THEN EXISTS_TAC "F2': CCS" THEN 
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC
          (CONJUNCT2 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F2 F2'"))) THEN
          EXISTS_TAC "par F1' E2''" THEN
          CONJ_TAC THENL
          [ASM_REWRITE_TAC[] THEN IMP_RES_TAC EPS_PAR THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "F1: CCS" THEN EXISTS_TAC "F1': CCS" THEN
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2'': CCS" THEN 
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F1 F1'"))) THEN
          IMP_RES_TAC
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F2 F2'"))) THEN
          EXISTS_TAC "par E2''' E2''''" THEN
          CONJ_TAC THENL
          [ASM_REWRITE_TAC[] THEN EPS_TRANS_TAC THEN
           STRIP_ASSUME_TAC
           (REWRITE_RULE [WEAK_TRANS]
            (ASSUME "WEAK_TRANS F1'(label l)E2'''")) THEN
           STRIP_ASSUME_TAC
           (REWRITE_RULE [WEAK_TRANS]
            (ASSUME "WEAK_TRANS F2'(label(COMPL l))E2''''")) THEN
           EXISTS_TAC "par E1'''' E1'''''" THEN
           REWRITE_TAC
           [MATCH_MP EPS_PAR_PAR
            (CONJ (ASSUME "EPS F1' E1''''") (ASSUME "EPS F2' E1'''''"))] THEN 
           EPS_TRANS_TAC THEN EXISTS_TAC "par E2''''' E2''''''" THEN
           REWRITE_TAC
           [MATCH_MP EPS_PAR_PAR
            (CONJ (ASSUME "EPS E2''''' E2'''")
                  (ASSUME "EPS E2'''''' E2''''"))] THEN
           ONE_TAU_TAC THEN PAR3_TAC THEN EXISTS_TAC "l: Label" THEN
           ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2''': CCS" THEN
           EXISTS_TAC "E2'': CCS" THEN EXISTS_TAC "E2'''': CCS" THEN
           ASM_REWRITE_TAC[] ] ]
         ;
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = par F1' F2'"]
                            (ASSUME "TRANS E' tau E2''")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [IMP_RES_TAC
          (CONJUNCT2 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F1 F1'"))) THEN
          EXISTS_TAC "par E1''' F2" THEN
          CONJ_TAC THENL
          [IMP_RES_TAC EPS_PAR THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E1'': CCS" THEN
           EXISTS_TAC "F2: CCS" THEN EXISTS_TAC "F2': CCS" THEN
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC
          (CONJUNCT2 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F2 F2'"))) THEN
          EXISTS_TAC "par F1 E1'''" THEN
          CONJ_TAC THENL
          [IMP_RES_TAC EPS_PAR THEN ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "F1: CCS" THEN EXISTS_TAC "F1': CCS" THEN
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E1'': CCS" THEN
           ASM_REWRITE_TAC[] ]
          ;
          IMP_RES_TAC
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F1 F1'"))) THEN
          IMP_RES_TAC
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR
                      (ASSUME "OBS_EQUIV F2 F2'"))) THEN
          EXISTS_TAC "par E1''' E1''''" THEN
          CONJ_TAC THENL
          [ASM_REWRITE_TAC[] THEN EPS_TRANS_TAC THEN
           STRIP_ASSUME_TAC
           (REWRITE_RULE [WEAK_TRANS]
            (ASSUME "WEAK_TRANS F1(label l)E1'''")) THEN
           STRIP_ASSUME_TAC
           (REWRITE_RULE [WEAK_TRANS]
            (ASSUME "WEAK_TRANS F2(label(COMPL l))E1''''")) THEN
           EXISTS_TAC "par E1''''' E1''''''" THEN
           REWRITE_TAC
           [MATCH_MP EPS_PAR_PAR
            (CONJ (ASSUME "EPS F1 E1'''''")
                  (ASSUME "EPS F2 E1''''''"))] THEN
           EPS_TRANS_TAC THEN EXISTS_TAC "par E2'''' E2'''''" THEN
           REWRITE_TAC
           [MATCH_MP EPS_PAR_PAR
            (CONJ (ASSUME "EPS E2'''' E1'''")
                  (ASSUME "EPS E2''''' E1''''"))] THEN
           ONE_TAU_TAC THEN PAR3_TAC THEN EXISTS_TAC "l: Label" THEN
           ASM_REWRITE_TAC[]
           ;
           EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E1'': CCS" THEN
           EXISTS_TAC "E1'''': CCS" THEN EXISTS_TAC "E2''': CCS" THEN 
           ASM_REWRITE_TAC[] ]] ]]);;

% --------------------------------------------------------------------------- %
% Observation equivalence is substitutive under parallel operator on the      %
% right:                                                                      %
%  |- !E E'. OBS_EQUIV E E' ==> (!E''. OBS_EQUIV(par E E'')(par E' E''))      %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_SUBST_PAR_R =
     save_thm
      (`OBS_EQUIV_SUBST_PAR_R`,
       GEN_ALL
       (DISCH "OBS_EQUIV E E'"
        (GEN "E'': CCS"
         (MATCH_MP OBS_EQUIV_PRESD_BY_PAR
          (CONJ (ASSUME "OBS_EQUIV E E'")
                (SPEC "E'': CCS" OBS_EQUIV_REFL))))));;

% --------------------------------------------------------------------------- %
% Observation equivalence is substitutive under parallel operator on the left:%
%  |- !E E'. OBS_EQUIV E E' ==> (!E''. OBS_EQUIV(par E'' E)(par E'' E'))      %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_SUBST_PAR_L =
     save_thm
      (`OBS_EQUIV_SUBST_PAR_L`,
       GEN_ALL
       (DISCH "OBS_EQUIV E E'"
        (GEN "E'': CCS"
         (MATCH_MP OBS_EQUIV_PRESD_BY_PAR
          (CONJ (SPEC "E'': CCS" OBS_EQUIV_REFL)
                (ASSUME "OBS_EQUIV E E'"))))));;
 
% --------------------------------------------------------------------------- %
% The epsilon relation is preserved by the restriction operator.        (262) %
% --------------------------------------------------------------------------- % 
let EPS_RESTR =
     prove_thm
      (`EPS_RESTR`,
       "!E E'. EPS E E' ==> !L. EPS (restr E L) (restr E' L)",
       EPS_INDUCT_TAC THENL 
       [GEN_TAC THEN
        IMP_RES_TAC
        (REWRITE_RULE [] (SPECL ["E: CCS"; "tau"; "E': CCS"] RESTR)) THEN
        ASSUME_TAC
        (SPEC "L: (Label)set"
         (ASSUME "!L. TRANS(restr E L)tau(restr E' L)")) THEN
        IMP_RES_TAC ONE_TAU
        ;
        REWRITE_TAC [EPS_REFL]
        ;
        GEN_TAC THEN
        ASSUME_TAC (SPEC "L: (Label)set"
                    (ASSUME "!L. EPS(restr E L)(restr E1 L)")) THEN
        ASSUME_TAC (SPEC "L: (Label)set"
                    (ASSUME "!L. EPS(restr E1 L)(restr E' L)")) THEN
        IMP_RES_TAC EPS_TRANS ]);;

% --------------------------------------------------------------------------- %
% The relation WEAK_TRANS is preserved by the restriction operator.  (168+132)%
% --------------------------------------------------------------------------- %
let WEAK_RESTR_label = 
     prove_thm 
      (`WEAK_RESTR_label`, 
       "!l L E E'. 
         ~l IN L /\ ~(COMPL l) IN L /\ WEAK_TRANS E (label l) E' ==>
          WEAK_TRANS (restr E L) (label l) (restr E' L)", 
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [WEAK_TRANS] THEN STRIP_TAC THEN  
       EXISTS_TAC "restr E1 L" THEN EXISTS_TAC "restr E2 L" THEN
       IMP_RES_TAC EPS_RESTR THEN ASM_REWRITE_TAC[] THEN RESTR_TAC THEN
       EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[]);; 

let WEAK_RESTR_tau = 
     prove_thm
      (`WEAK_RESTR_tau`, 
       "!E E'. 
         WEAK_TRANS E tau E' ==> 
         !L. WEAK_TRANS (restr E L) tau (restr E' L)", 
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [WEAK_TRANS] THEN STRIP_TAC THEN GEN_TAC THEN 
       EXISTS_TAC "restr E1 L" THEN EXISTS_TAC "restr E2 L" THEN
       IMP_RES_TAC EPS_RESTR THEN ASM_REWRITE_TAC[] THEN RESTR_TAC THEN 
       ASM_REWRITE_TAC[]);; 

% --------------------------------------------------------------------------- %
% Observation equivalence is substitutive under restriction operator.   (1165)%
% --------------------------------------------------------------------------- % 
let OBS_EQUIV_SUBST_RESTR =
     prove_thm
      (`OBS_EQUIV_SUBST_RESTR`,
       "!E E'. 
         OBS_EQUIV E E' ==> !L. OBS_EQUIV (restr E L) (restr E' L)", 
       REPEAT STRIP_TAC THEN 
       PURE_ONCE_REWRITE_TAC [OBS_EQUIV] THEN
       EXISTS_TAC "\x y. ?E1 E2 L'. (x = restr E1 L') /\ (y = restr E2 L') /\
                                    OBS_EQUIV E1 E2" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E': CCS" THEN
        EXISTS_TAC "L: (Label)set" THEN ASM_REWRITE_TAC[] 
        ;
        PURE_ONCE_REWRITE_TAC [WEAK_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E'' = restr E1 L'"]
                            (ASSUME "TRANS E''(label l)E1'")) THEN
         IMP_RES_TAC TRANS_RESTR THENL
         [IMP_RES_TAC Action_Distinct_label 
          ; 
          IMP_RES_TAC  
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR 
                      (ASSUME "OBS_EQUIV E1 E2"))) THEN 
          EXISTS_TAC "restr E2' L'" THEN
          ASM_REWRITE_TAC   
          [MATCH_MP WEAK_RESTR_label
           (LIST_CONJ [ASSUME "~(l': Label) IN L'"; 
                       ASSUME "~(COMPL l') IN L'"; 
                       REWRITE_RULE [ASSUME "label l = label l'"] 
                              (ASSUME "WEAK_TRANS E2(label l)E2'")])] THEN  
           EXISTS_TAC "E'''': CCS" THEN EXISTS_TAC "E2': CCS" THEN 
           EXISTS_TAC "L': (Label)set" THEN ASM_REWRITE_TAC[] ]  
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E''' = restr E2 L'"]
                            (ASSUME "TRANS E'''(label l)E2'")) THEN
         IMP_RES_TAC TRANS_RESTR THENL
         [IMP_RES_TAC Action_Distinct_label
          ;
          IMP_RES_TAC
          (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR  
                      (ASSUME "OBS_EQUIV E1 E2"))) THEN
          EXISTS_TAC "restr E1' L'" THEN
          ASM_REWRITE_TAC 
          [MATCH_MP WEAK_RESTR_label
           (LIST_CONJ [ASSUME "~(l': Label) IN L'"; 
                       ASSUME "~(COMPL l') IN L'";  
                       REWRITE_RULE [ASSUME "label l = label l'"]
                              (ASSUME "WEAK_TRANS E1(label l)E1'")])] THEN
           EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E'''': CCS" THEN
           EXISTS_TAC "L': (Label)set" THEN ASM_REWRITE_TAC[] ]
         ;
         ASSUME_TAC (REWRITE_RULE [ASSUME "E'' = restr E1 L'"]
                            (ASSUME "TRANS E'' tau E1'")) THEN
         IMP_RES_TAC TRANS_RESTR THENL
         [IMP_RES_TAC
          (CONJUNCT2 (MATCH_MP OBS_PROP_STAR_LR   
                      (ASSUME "OBS_EQUIV E1 E2"))) THEN
          EXISTS_TAC "restr E2' L'" THEN
          IMP_RES_TAC EPS_RESTR THEN ASM_REWRITE_TAC[] THEN  
          EXISTS_TAC "E'''': CCS" THEN EXISTS_TAC "E2': CCS" THEN 
          EXISTS_TAC "L': (Label)set" THEN ASM_REWRITE_TAC[]  
          ; 
          IMP_RES_TAC Action_Distinct ]  
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E''' = restr E2 L'"]
                            (ASSUME "TRANS E''' tau E2'")) THEN 
         IMP_RES_TAC TRANS_RESTR THENL
         [IMP_RES_TAC
          (CONJUNCT2 (MATCH_MP OBS_PROP_STAR_LR  
                      (ASSUME "OBS_EQUIV E1 E2"))) THEN
          EXISTS_TAC "restr E1' L'" THEN
          IMP_RES_TAC EPS_RESTR THEN ASM_REWRITE_TAC[] THEN 
          EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E'''': CCS" THEN
          EXISTS_TAC "L': (Label)set" THEN ASM_REWRITE_TAC[] 
          ;
          IMP_RES_TAC Action_Distinct ]]]);; 

% --------------------------------------------------------------------------- %
% The epsilon relation is preserved by the relabelling operator.        (259) %
% --------------------------------------------------------------------------- %
let EPS_RELAB = 
     prove_thm
      (`EPS_RELAB`,  
       "!E E'. 
         EPS E E' ==> 
         !labl. EPS (relab E (RELAB labl)) (relab E' (RELAB labl))",
       EPS_INDUCT_TAC THENL 
       [GEN_TAC THEN
        IMP_RES_TAC
        (REWRITE_RULE [relabel] 
         (SPECL ["E: CCS"; "tau"; "E': CCS"] RELABELLING)) THEN
        ASSUME_TAC
        (SPEC "labl: (Label # Label)list"
         (ASSUME "!labl. 
                   TRANS(relab E(RELAB labl))tau(relab E'(RELAB labl))")) THEN
        IMP_RES_TAC ONE_TAU
        ;
        REWRITE_TAC [EPS_REFL]
        ;
        GEN_TAC THEN
        ASSUME_TAC (SPEC "labl: (Label # Label)list"
        (ASSUME "!labl. EPS(relab E(RELAB labl))(relab E1(RELAB labl))")) THEN
        ASSUME_TAC (SPEC "labl: (Label # Label)list"  
        (ASSUME "!labl. 
                  EPS(relab E1(RELAB labl))(relab E'(RELAB labl))")) THEN
        IMP_RES_TAC EPS_TRANS ]);;

% --------------------------------------------------------------------------- %
% The relation WEAK_TRANS is preserved by the relabelling operator.     (116) %
% --------------------------------------------------------------------------- %
let WEAK_RELAB = 
     prove_thm 
      (`WEAK_RELAB`, 
       "!E u E'.
         WEAK_TRANS E u E' ==>
         !labl. WEAK_TRANS (relab E (RELAB labl)) 
                    (relabel(Apply_Relab labl)u) (relab E' (RELAB labl))",  
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [WEAK_TRANS] THEN REPEAT STRIP_TAC THEN
       IMP_RES_TAC EPS_RELAB THEN EXISTS_TAC "relab E1(RELAB labl)" THEN 
       EXISTS_TAC "relab E2(RELAB labl)" THEN
       ASM_REWRITE_TAC[] THEN RELAB_TAC THEN ASM_REWRITE_TAC[]);;  

% --------------------------------------------------------------------------- %
% Observation equivalence is substitutive under relabelling operator.   (1291)%
% --------------------------------------------------------------------------- % 
let OBS_EQUIV_SUBST_RELAB =
     prove_thm
      (`OBS_EQUIV_SUBST_RELAB`,
       "!E E'. 
         OBS_EQUIV E E' ==> 
         (!rf. OBS_EQUIV (relab E rf) (relab E' rf))",   
       REPEAT STRIP_TAC THEN 
       PURE_ONCE_REWRITE_TAC [OBS_EQUIV] THEN
       EXISTS_TAC "\x y. ?E1 E2 rf'. (x = relab E1 rf') /\ (y = relab E2 rf') /\
                                     OBS_EQUIV E1 E2" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E': CCS" THEN
        EXISTS_TAC "rf: Relabelling" THEN ASM_REWRITE_TAC[] 
        ;
        PURE_ONCE_REWRITE_TAC [WEAK_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E'' = relab E1 rf'"]
                            (ASSUME "TRANS E''(label l)E1'")) THEN
         IMP_RES_TAC TRANS_RELAB THEN IMP_RES_TAC Relab_Label THEN 
         ASSUME_TAC (REWRITE_RULE [ASSUME "u' = label l'"] 
                            (ASSUME "TRANS E1 u' E''''")) THEN    
         IMP_RES_TAC
         (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR  
                     (ASSUME "OBS_EQUIV E1 E2"))) THEN
         EXISTS_TAC "relab E2' rf'" THEN
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN IMP_RES_TAC WEAK_RELAB THEN ASM_REWRITE_TAC[]
          ;
          EXISTS_TAC "E'''': CCS" THEN EXISTS_TAC "E2': CCS" THEN
          EXISTS_TAC "rf': Relabelling" THEN ASM_REWRITE_TAC[] ]
         ;    
         ASSUME_TAC (REWRITE_RULE [ASSUME "E''' = relab E2 rf'"]
                            (ASSUME "TRANS E'''(label l)E2'")) THEN
         IMP_RES_TAC TRANS_RELAB THEN IMP_RES_TAC Relab_Label THEN
         ASSUME_TAC (REWRITE_RULE [ASSUME "u' = label l'"]
                            (ASSUME "TRANS E2 u' E''''")) THEN
         IMP_RES_TAC
         (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR  
                     (ASSUME "OBS_EQUIV E1 E2"))) THEN
         EXISTS_TAC "relab E1' rf'" THEN 
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN IMP_RES_TAC WEAK_RELAB THEN ASM_REWRITE_TAC[]
          ;
          EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E'''': CCS" THEN
          EXISTS_TAC "rf': Relabelling" THEN ASM_REWRITE_TAC[] ]
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E'' = relab E1 rf'"]
                            (ASSUME "TRANS E'' tau E1'")) THEN
         IMP_RES_TAC TRANS_RELAB THEN IMP_RES_TAC Relab_Tau THEN  
         ASSUME_TAC (REWRITE_RULE [ASSUME "u' = tau"]
                            (ASSUME "TRANS E1 u' E''''")) THEN 
         IMP_RES_TAC
         (CONJUNCT2 (MATCH_MP OBS_PROP_STAR_LR
                     (ASSUME "OBS_EQUIV E1 E2"))) THEN
         EXISTS_TAC "relab E2' rf'" THEN
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN IMP_RES_TAC EPS_RELAB THEN ASM_REWRITE_TAC[]
          ;
          EXISTS_TAC "E'''': CCS" THEN EXISTS_TAC "E2': CCS" THEN
          EXISTS_TAC "rf': Relabelling" THEN ASM_REWRITE_TAC[] ]
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E''' = relab E2 rf'"]
                            (ASSUME "TRANS E''' tau E2'")) THEN
         IMP_RES_TAC TRANS_RELAB THEN IMP_RES_TAC Relab_Tau THEN
         ASSUME_TAC (REWRITE_RULE [ASSUME "u' = tau"]
                            (ASSUME "TRANS E2 u' E''''")) THEN
         IMP_RES_TAC
         (CONJUNCT2 (MATCH_MP OBS_PROP_STAR_LR
                     (ASSUME "OBS_EQUIV E1 E2"))) THEN
         EXISTS_TAC "relab E1' rf'" THEN
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN IMP_RES_TAC EPS_RELAB THEN ASM_REWRITE_TAC[]
          ;
          EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E'''': CCS" THEN
          EXISTS_TAC "rf': Relabelling" THEN ASM_REWRITE_TAC[] ]]]);; 

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

