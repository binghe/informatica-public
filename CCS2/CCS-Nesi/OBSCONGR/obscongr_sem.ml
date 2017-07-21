% =========================================================================== %
% FILE          : obscongr_sem.ml                                             %
% DESCRIPTION   : Operational definition of observation congruence for CCS    %
%                 and related properties                                      %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 14 November 1991                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `obscongr_sem`;;

% --------------------------------------------------------------------------- %
% Define the observation congruence over CCS agents expressions.              %
% --------------------------------------------------------------------------- %
let OBS_CONGR =
     new_definition
      (`OBS_CONGR`,
       "OBS_CONGR E E' =
        (!u.
          (!E1.
            TRANS E u E1 ==> 
            (?E2. WEAK_TRANS E' u E2 /\ OBS_EQUIV E1 E2)) /\
          (!E2.
            TRANS E' u E2 ==> 
            (?E1. WEAK_TRANS E u E1 /\ OBS_EQUIV E1 E2)))");;

% --------------------------------------------------------------------------- %
% Observation congruence is an equivalence relation.                          %
% --------------------------------------------------------------------------- %

% --------------------------------------------------------------------------- %
% Observation congruence is a reflexive relation.                        (88) %
% --------------------------------------------------------------------------- %
let OBS_CONGR_REFL =
     prove_thm
      (`OBS_CONGR_REFL`,
       "!E. OBS_CONGR E E",
       GEN_TAC THEN PURE_ONCE_REWRITE_TAC [OBS_CONGR] THEN
       REPEAT STRIP_TAC THEN 
       IMP_RES_TAC TRANS_IMP_WEAK_TRANS THENL  
       [EXISTS_TAC "E1: CCS"; EXISTS_TAC "E2: CCS"] THEN   
       ASM_REWRITE_TAC [OBS_EQUIV_REFL]);;

% --------------------------------------------------------------------------- %
% Observation congruence is a symmetric relation.                       (192) %
% --------------------------------------------------------------------------- %
let OBS_CONGR_SYM =
     prove_thm
      (`OBS_CONGR_SYM`,
       "!E E'. OBS_CONGR E E' ==> OBS_CONGR E' E",
       REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [OBS_CONGR] THEN
       REPEAT STRIP_TAC THEN 
       RES_TAC THEN IMP_RES_TAC OBS_EQUIV_SYM THENL  
       [EXISTS_TAC "E1': CCS"; EXISTS_TAC "E2': CCS"] THEN 
       ASM_REWRITE_TAC[]);; 

% --------------------------------------------------------------------------- %
% Observation congruence is a transitive relation.   (105) % 
% --------------------------------------------------------------------------- %
let PROP3 = 
mk_thm ([], 
        "!E E'. OBS_CONGR E E' = (!E''. OBS_EQUIV (sum E E'') (sum E' E''))");;
% hypothesis on sort? %

let OBS_CONGR_TRANS = 
     prove_thm
      (`OBS_CONGR_TRANS`,
       "!E E' E''. OBS_CONGR E E' /\ OBS_CONGR E' E'' ==> OBS_CONGR E E''", 
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [PROP3] THEN REPEAT STRIP_TAC THEN 
       MAP_EVERY (\tm. ASSUME_TAC (SPEC "E''': CCS" (ASSUME tm)))    
          ["!E''. OBS_EQUIV(sum E E'')(sum E' E'')";
           "!E'''. OBS_EQUIV(sum E' E''')(sum E'' E''')"] THEN 
       IMP_RES_TAC OBS_EQUIV_TRANS);;  

% --------------------------------------------------------------------------- %
% Syntactic equivalence implies observation congruence.                  (17) %
% --------------------------------------------------------------------------- %
let EQUAL_IMP_OBS_CONGR =
     prove_thm
      (`EQUAL_IMP_OBS_CONGR`,
       "!E E'. (E = E') ==> OBS_CONGR E E'",
       REPEAT STRIP_TAC THEN PURE_ASM_REWRITE_TAC [OBS_CONGR_REFL]);;

% --------------------------------------------------------------------------- %
% Prove that observation congruence implies observation equivalence.    (334) % 
% --------------------------------------------------------------------------- %
let OBS_CONGR_IMP_OBS_EQUIV = 
     prove_thm 
      (`OBS_CONGR_IMP_OBS_EQUIV`, 
       "!E E'. OBS_CONGR E E' ==> OBS_EQUIV E E'", 
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [OBS_CONGR; OBS_PROP_STAR] THEN 
       REPEAT STRIP_TAC THEN RES_TAC THENL 
       [EXISTS_TAC "E2: CCS"; 
        EXISTS_TAC "E1: CCS"; 
        IMP_RES_TAC WEAK_TRANS_TAU THEN EXISTS_TAC "E2: CCS"; 
        IMP_RES_TAC WEAK_TRANS_TAU THEN EXISTS_TAC "E1: CCS"] THEN 
       ASM_REWRITE_TAC[]);;  

% --------------------------------------------------------------------------- %
% Proposition 9, page 112.                                              (333) %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_STABLE_IMP_CONGR =
     prove_thm
      (`OBS_EQUIV_STABLE_IMP_CONGR`,
       "!E E'.
         OBS_EQUIV E E' /\ STABLE E /\ STABLE E' ==> OBS_CONGR E E'",
       REPEAT GEN_TAC THEN
       REWRITE_TAC [STABLE; OBS_CONGR] THEN
       REPEAT STRIP_TAC THENL
       [RES_TAC THEN IMP_RES_TAC Action_No_Tau_Is_Label THEN
        ASSUME_TAC (REWRITE_RULE [ASSUME "u = label L"]
                           (ASSUME "TRANS E u E1")) THEN
        IMP_RES_TAC
        (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR
                    (ASSUME "OBS_EQUIV E E'"))) THEN
        EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]
        ;
        RES_TAC THEN IMP_RES_TAC Action_No_Tau_Is_Label THEN
        ASSUME_TAC (REWRITE_RULE [ASSUME "u = label L"]
                           (ASSUME "TRANS E' u E2")) THEN
        IMP_RES_TAC
        (CONJUNCT1 (MATCH_MP OBS_PROP_STAR_LR
                    (ASSUME "OBS_EQUIV E E'"))) THEN
        EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] ]);;

% --------------------------------------------------------------------------- %
% Proposition 6 (Milner's book, page 154).                              (305) %
% |- !E E'. OBS_EQUIV E E' ==> (!u. OBS_CONGR (prefix u E) (prefix u E'))     %
% --------------------------------------------------------------------------- %
let PROP6 = 
     prove_thm 
      (`PROP6`, 
       "!E E'. 
         OBS_EQUIV E E' ==> (!u. OBS_CONGR (prefix u E) (prefix u E'))",
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [OBS_CONGR] THEN 
       REPEAT STRIP_TAC THENL 
       [IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E': CCS" THEN 
        ASM_REWRITE_TAC [WEAK_TRANS] THEN EXISTS_TAC "prefix u E'" THEN 
        EXISTS_TAC "E': CCS" THEN ASM_REWRITE_TAC [EPS_REFL; PREFIX] 
        ; 
        IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E: CCS" THEN 
        ASM_REWRITE_TAC [WEAK_TRANS] THEN EXISTS_TAC "prefix u E" THEN 
        EXISTS_TAC "E: CCS" THEN ASM_REWRITE_TAC [EPS_REFL; PREFIX] ]);; 

% --------------------------------------------------------------------------- %
% Observation congruence is substitutive under the prefix operator.      (49) %
% --------------------------------------------------------------------------- %
let SUBST_PREFIX = 
     prove_thm 
      (`SUBST_PREFIX`, 
       "!E E'. 
         OBS_CONGR E E' ==> (!u. OBS_CONGR (prefix u E) (prefix u E'))",
       REPEAT STRIP_TAC THEN 
       IMP_RES_TAC OBS_CONGR_IMP_OBS_EQUIV THEN 
       IMP_RES_TAC PROP6 THEN ASM_REWRITE_TAC[]);;
 
% --------------------------------------------------------------------------- %
% Observation congruence is preserved by binary summation.                    %
% --------------------------------------------------------------------------- %
%let OBS_CONGR_PRESD_BY_SUM = 
     prove_thm
      (`OBS_CONGR_PRESD_BY_SUM`,
       "!E1 E1' E2 E2'.
         OBS_CONGR E1 E1' /\ OBS_CONGR E2 E2' ==>
         OBS_CONGR(sum E1 E2)(sum E1' E2')",
       REPEAT STRIP_TAC THEN
       PURE_ONCE_REWRITE_TAC [PROP3] THEN GEN_TAC THEN
       OE_LHS_SUBST1_TAC
         (SPECL ["E1: CCS"; "E2: CCS"; "E'': CCS"] OBS_SUM_ASSOC_R) THEN
       OE_RHS_SUBST1_TAC
         (SPECL ["E1': CCS"; "E2': CCS"; "E'': CCS"] OBS_SUM_ASSOC_R) THEN 
       OE_LHS_SUBST1_TAC 
         (SPEC "sum E2 E''" 
          (MATCH_MP (EQ_IMP_LR PROP3) (ASSUME "OBS_CONGR E1 E1'"))) THEN 

SPEC "E'': CCS" (MATCH_MP (EQ_IMP_LR PROP3) (ASSUME "OBS_CONGR E2 E2'"))
%  

% --------------------------------------------------------------------------- %
% Observation congruence is substitutive under binary summation          (70) %
% on the right.                                                               %
% --------------------------------------------------------------------------- %
let SUBST_SUM_R =
     prove_thm
      (`SUBST_SUM_R`,
       "!E E'.
         OBS_CONGR E E' ==> (!E''. OBS_CONGR (sum E E'') (sum E' E''))", 
       REPEAT STRIP_TAC THEN 
       PURE_ONCE_REWRITE_TAC [PROP3] THEN GEN_TAC THEN   
       OE_LHS_SUBST1_TAC
         (SPECL ["E: CCS"; "E'': CCS"; "E''': CCS"] OBS_SUM_ASSOC_R) THEN
       OE_RHS_SUBST1_TAC
         (SPECL ["E': CCS"; "E'': CCS"; "E''': CCS"] OBS_SUM_ASSOC_R) THEN 
       REWRITE_TAC [MATCH_MP (EQ_IMP_LR PROP3) (ASSUME "OBS_CONGR E E'")]);;  

% --------------------------------------------------------------------------- %
% Observation congruence is preserved by parallel composition.         (1166) %
% --------------------------------------------------------------------------- %
let OBS_CONGR_PRESD_BY_PAR =
     prove_thm
      (`OBSCONG_PRESD_BY_PAR`,
       "!E1 E1' E2 E2'.
         OBS_CONGR E1 E1' /\ OBS_CONGR E2 E2' ==>
         OBS_CONGR (par E1 E2) (par E1' E2')",
       REPEAT STRIP_TAC THEN
       PURE_ONCE_REWRITE_TAC [OBS_CONGR] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC TRANS_PAR THENL
        [IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                             (ASSUME "OBS_CONGR E1 E1'")) THEN
         ASSUME_TAC
         (CONJUNCT1
          (SPEC "E2': CCS"
           (MATCH_MP WEAK_PAR (ASSUME "WEAK_TRANS E1' u E2''")))) THEN
         EXISTS_TAC "par E2'' E2'" THEN
         ASM_REWRITE_TAC
         [OE_TRANS
          (SPEC "E2: CCS"
           (MATCH_MP OBS_EQUIV_SUBST_PAR_R (ASSUME "OBS_EQUIV E1''' E2''")))
          (SPEC "E2'': CCS"
           (MATCH_MP OBS_EQUIV_SUBST_PAR_L
            (MATCH_MP OBS_CONGR_IMP_OBS_EQUIV (ASSUME "OBS_CONGR E2 E2'"))))]
         ;
         IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                             (ASSUME "OBS_CONGR E2 E2'")) THEN
         ASSUME_TAC
         (CONJUNCT2
          (SPEC "E1': CCS"
           (MATCH_MP WEAK_PAR (ASSUME "WEAK_TRANS E2' u E2''")))) THEN
         EXISTS_TAC "par E1' E2''" THEN
         ASM_REWRITE_TAC
         [OE_TRANS
          (SPEC "E1''': CCS"
           (MATCH_MP OBS_EQUIV_SUBST_PAR_R
            (MATCH_MP OBS_CONGR_IMP_OBS_EQUIV (ASSUME "OBS_CONGR E1 E1'"))))
          (SPEC "E1': CCS"
           (MATCH_MP OBS_EQUIV_SUBST_PAR_L (ASSUME "OBS_EQUIV E1''' E2''")))]
         ;
         IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                             (ASSUME "OBS_CONGR E1 E1'")) THEN
         IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                             (ASSUME "OBS_CONGR E2 E2'")) THEN
         EXISTS_TAC "par E2''' E2''''" THEN
         ASM_REWRITE_TAC
          [OE_TRANS
           (SPEC "E2'': CCS"
            (MATCH_MP OBS_EQUIV_SUBST_PAR_R (ASSUME "OBS_EQUIV E1''' E2'''")))
           (SPEC "E2''': CCS"
            (MATCH_MP OBS_EQUIV_SUBST_PAR_L (ASSUME "OBS_EQUIV E2'' E2''''")))]
         THEN PURE_ONCE_REWRITE_TAC [WEAK_TRANS] THEN
         STRIP_ASSUME_TAC
         (REWRITE_RULE [WEAK_TRANS]
                 (ASSUME "WEAK_TRANS E1'(label l)E2'''")) THEN
         STRIP_ASSUME_TAC
         (REWRITE_RULE [WEAK_TRANS]
                 (ASSUME "WEAK_TRANS E2'(label(COMPL l))E2''''")) THEN
         EXISTS_TAC "par E1'''' E1'''''" THEN
         EXISTS_TAC "par E2''''' E2''''''" THEN
         REWRITE_TAC
          [MATCH_MP EPS_PAR_PAR
           (CONJ (ASSUME "EPS E1' E1''''") (ASSUME "EPS E2' E1'''''"));
           MATCH_MP EPS_PAR_PAR
           (CONJ (ASSUME "EPS E2''''' E2'''") (ASSUME "EPS E2'''''' E2''''"))]
         THEN PAR3_TAC THEN EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[] ]
        ;
        IMP_RES_TAC TRANS_PAR THENL
        [IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                             (ASSUME "OBS_CONGR E1 E1'")) THEN
         ASSUME_TAC
         (CONJUNCT1
          (SPEC "E2: CCS"
           (MATCH_MP WEAK_PAR (ASSUME "WEAK_TRANS E1 u E1'''")))) THEN
         EXISTS_TAC "par E1''' E2" THEN
         ASM_REWRITE_TAC
         [OE_TRANS
          (SPEC "E2: CCS"
           (MATCH_MP OBS_EQUIV_SUBST_PAR_R (ASSUME "OBS_EQUIV E1''' E1''")))
          (SPEC "E1'': CCS"
           (MATCH_MP OBS_EQUIV_SUBST_PAR_L
            (MATCH_MP OBS_CONGR_IMP_OBS_EQUIV (ASSUME "OBS_CONGR E2 E2'"))))]
         ;
         IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                             (ASSUME "OBS_CONGR E2 E2'")) THEN
         ASSUME_TAC
         (CONJUNCT2
          (SPEC "E1: CCS"
           (MATCH_MP WEAK_PAR (ASSUME "WEAK_TRANS E2 u E1'''")))) THEN
         EXISTS_TAC "par E1 E1'''" THEN
         ASM_REWRITE_TAC
         [OE_TRANS
          (SPEC "E1''': CCS"
           (MATCH_MP OBS_EQUIV_SUBST_PAR_R
            (MATCH_MP OBS_CONGR_IMP_OBS_EQUIV (ASSUME "OBS_CONGR E1 E1'"))))
          (SPEC "E1': CCS"
           (MATCH_MP OBS_EQUIV_SUBST_PAR_L (ASSUME "OBS_EQUIV E1''' E1''")))]
         ;
         IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                             (ASSUME "OBS_CONGR E1 E1'")) THEN
         IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                             (ASSUME "OBS_CONGR E2 E2'")) THEN
         EXISTS_TAC "par E1''' E1''''" THEN
         ASM_REWRITE_TAC
          [OE_TRANS
           (SPEC "E1'''': CCS"
            (MATCH_MP OBS_EQUIV_SUBST_PAR_R (ASSUME "OBS_EQUIV E1''' E1''")))
           (SPEC "E1'': CCS"
            (MATCH_MP OBS_EQUIV_SUBST_PAR_L (ASSUME "OBS_EQUIV E1'''' E2'''")))]
         THEN PURE_ONCE_REWRITE_TAC [WEAK_TRANS] THEN
         STRIP_ASSUME_TAC
         (REWRITE_RULE [WEAK_TRANS]
                 (ASSUME "WEAK_TRANS E1(label l)E1'''")) THEN
         STRIP_ASSUME_TAC
         (REWRITE_RULE [WEAK_TRANS]
                 (ASSUME "WEAK_TRANS E2(label(COMPL l))E1''''")) THEN
         EXISTS_TAC "par E1''''' E1''''''" THEN
         EXISTS_TAC "par E2'''' E2'''''" THEN
         REWRITE_TAC
          [MATCH_MP EPS_PAR_PAR
           (CONJ (ASSUME "EPS E1 E1'''''") (ASSUME "EPS E2 E1''''''"));
           MATCH_MP EPS_PAR_PAR
           (CONJ (ASSUME "EPS E2'''' E1'''") (ASSUME "EPS E2''''' E1''''"))]
         THEN PAR3_TAC THEN EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[] ]]);;

% --------------------------------------------------------------------------- %
% Observation congruence is substitutive under parallel operator on the right:%
%  |- !E E'. OBS_CONGR E E' ==> (!E''. OBS_CONGR(par E E'')(par E' E''))      %
% --------------------------------------------------------------------------- %
let SUBST_PAR_R =
     save_thm
      (`SUBST_PAR_R`,
       GEN_ALL
       (DISCH "OBS_CONGR E E'"
        (GEN "E'': CCS"
         (MATCH_MP OBS_CONGR_PRESD_BY_PAR
          (CONJ (ASSUME "OBS_CONGR E E'")
                (SPEC "E'': CCS" OBS_CONGR_REFL))))));;

% --------------------------------------------------------------------------- %
% Observation congruence is substitutive under parallel operator on the left: %
%  |- !E E'. OBS_CONGR E E' ==> (!E''. OBS_CONGR(par E'' E)(par E'' E'))      %
% --------------------------------------------------------------------------- %
let SUBST_PAR_L =
     save_thm
      (`SUBST_PAR_L`,
       GEN_ALL
       (DISCH "OBS_CONGR E E'"
        (GEN "E'': CCS"
         (MATCH_MP OBS_CONGR_PRESD_BY_PAR
          (CONJ (SPEC "E'': CCS" OBS_CONGR_REFL)
                (ASSUME "OBS_CONGR E E'"))))));;

% --------------------------------------------------------------------------- %
% Observation congruence is substitutive under the restriction operator. (673)%
% --------------------------------------------------------------------------- %
let SUBST_RESTR =
     prove_thm
      (`SUBST_RESTR`,
       "!E E'. 
         OBS_CONGR E E' ==> !L. OBS_CONGR (restr E L) (restr E' L)", 
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [OBS_CONGR] THEN 
       REPEAT STRIP_TAC THENL 
       [IMP_RES_TAC TRANS_RESTR THENL 
        [RES_TAC THEN  
         ASSUME_TAC 
         (MATCH_MP WEAK_RESTR_tau 
          (REWRITE_RULE [ASSUME "u = tau"] (ASSUME "WEAK_TRANS E' u E2"))) THEN 
         EXISTS_TAC "restr E2 L" THEN 
         IMP_RES_TAC OBS_EQUIV_SUBST_RESTR THEN ASM_REWRITE_TAC[]   
         ; 
         RES_TAC THEN
         ASSUME_TAC
         (MATCH_MP WEAK_RESTR_label 
          (LIST_CONJ [ASSUME "~(l: Label) IN L"; ASSUME "~(COMPL l) IN L";  
                      REWRITE_RULE [ASSUME "u = label l"] 
                             (ASSUME "WEAK_TRANS E' u E2")])) THEN 
         EXISTS_TAC "restr E2 L" THEN
         IMP_RES_TAC OBS_EQUIV_SUBST_RESTR THEN ASM_REWRITE_TAC[] ] 
        ; 
        IMP_RES_TAC TRANS_RESTR THENL 
        [RES_TAC THEN
         ASSUME_TAC
         (MATCH_MP WEAK_RESTR_tau 
          (REWRITE_RULE [ASSUME "u = tau"] (ASSUME "WEAK_TRANS E u E1"))) THEN
         EXISTS_TAC "restr E1 L" THEN
         IMP_RES_TAC OBS_EQUIV_SUBST_RESTR THEN ASM_REWRITE_TAC[]
         ;
         RES_TAC THEN
         ASSUME_TAC
         (MATCH_MP WEAK_RESTR_label
          (LIST_CONJ [ASSUME "~(l: Label) IN L"; ASSUME "~(COMPL l) IN L"; 
                      REWRITE_RULE [ASSUME "u = label l"] 
                             (ASSUME "WEAK_TRANS E u E1")])) THEN
         EXISTS_TAC "restr E1 L" THEN
         IMP_RES_TAC OBS_EQUIV_SUBST_RESTR THEN ASM_REWRITE_TAC[] ] ]);; 

% --------------------------------------------------------------------------- %
% Observation congruence is substitutive under the relabelling operator. (368)%
% --------------------------------------------------------------------------- %
let SUBST_RELAB =
     prove_thm
      (`SUBST_RELAB`,
       "!E E'. 
         OBS_CONGR E E' ==> !rf. OBS_CONGR (relab E rf) (relab E' rf)",
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [OBS_CONGR] THEN
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC TRANS_RELAB THEN RES_TAC THENL  
       [ASSUME_TAC (MATCH_MP WEAK_RELAB (ASSUME "WEAK_TRANS E' u' E2")) THEN 
        EXISTS_TAC "relab E2(RELAB labl)" ; 
        ASSUME_TAC (MATCH_MP WEAK_RELAB (ASSUME "WEAK_TRANS E u' E1")) THEN
        EXISTS_TAC "relab E1(RELAB labl)"] THEN 
        IMP_RES_TAC OBS_EQUIV_SUBST_RELAB THEN ASM_REWRITE_TAC[] );;  

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

