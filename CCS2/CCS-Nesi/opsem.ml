% =========================================================================== %
% FILE          : opsem.ml                                                    %
% DESCRIPTION   : Definition of the transition relation for pure CCS          %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : August 1995                                                 %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Load the inductive definitions package.                                     %
% --------------------------------------------------------------------------- %
load_library `ind_defs`;;

% MP changed %

loadf `/homes/mn/CCS/ind-defs`;;

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `opsem`;;

% --------------------------------------------------------------------------- %
% Inductive definition of the transition relation TRANS for CCS.        (299) %
% --------------------------------------------------------------------------- %
let (trans_rules,trans_ind) =

    let TRANS = "TRANS: CCS -> Action -> CCS -> bool" in

    new_inductive_definition false `TRANS_DEF` ("^TRANS E u E'", [])

    [ [                           ],
      % ------------------------- %
        "^TRANS (prefix u E) u E" ;

      [     "^TRANS E u E1"      ],
      % ------------------------ %
        "^TRANS (sum E E') u E1" ;

      [     "^TRANS E u E1"      ],
      % ------------------------ %
        "^TRANS (sum E' E) u E1" ;

      [         "^TRANS E u E1"           ],
      % --------------------------------- %
        "^TRANS (par E E') u (par E1 E')" ;

      [         "^TRANS E u E1"           ],
      % --------------------------------- %
        "^TRANS (par E' E) u (par E' E1)" ;

      [ "^TRANS E (label l) E1"; "^TRANS E' (label(COMPL l)) E2" ],
      % -------------------------------------------------------- %
                "^TRANS (par E E') tau (par E1 E2)"              ;

      [                       "^TRANS E u E'" ;
       "(u = tau) \/ ((u = label l) /\ (~(l IN L)) /\ (~((COMPL l) IN L)))"],
      % ------------------------------------------------------------------ %
                     "^TRANS (restr E L) u (restr E' L)"                   ;

      [                  "^TRANS E u E'"                     ],
      % ---------------------------------------------------- %
        "^TRANS (relab E rf) (relabel rf u) (relab E' rf)"   ;

      [ "^TRANS (CCS_Subst E (rec X E) X) u E1" ], 
      % --------------------------------------- %
               "^TRANS (rec X E) u E1"          ];;

% --------------------------------------------------------------------------- %
% Backward case analysis theorem (equational version).                 (1979) %
% --------------------------------------------------------------------------- %
let TRANS_cases = derive_cases_thm (trans_rules,trans_ind);;

% --------------------------------------------------------------------------- %
% Rule induction tactic for TRANS.                                            %
% --------------------------------------------------------------------------- %
let TRANS_INDUCT_TAC = RULE_INDUCT_THEN trans_ind ASSUME_TAC ASSUME_TAC;;

let s_trans_ind = derive_strong_induction(trans_rules,trans_ind);;

let S_TRANS_INDUCT_TAC = RULE_INDUCT_THEN s_trans_ind ASSUME_TAC ASSUME_TAC;;

% --------------------------------------------------------------------------- %
% The rules for the transition relation TRANS as individual theorems.         %
% --------------------------------------------------------------------------- %
let [PREFIX; SUM1; SUM2; PAR1; PAR2; PAR3; 
     RESTR; RELABELLING; REC] = trans_rules;;

% --------------------------------------------------------------------------- %
% Tactics for proofs about the transition relation TRANS.                     %
% --------------------------------------------------------------------------- %
let [PREFIX_TAC; SUM1_TAC; SUM2_TAC; 
     PAR1_TAC; PAR2_TAC; PAR3_TAC; 
     RESTR_TAC; RELAB_TAC; REC_TAC] = map RULE_TAC trans_rules;;

% --------------------------------------------------------------------------- %
% The process nil has no transitions.                                  (1137) %
%   |- !u E'. ~TRANS nil u E'                                                 %
% --------------------------------------------------------------------------- %
let NIL_NO_TRANS = 
     save_thm 
      (`NIL_NO_TRANS`, REWRITE_RULE [CCS_Distinct] (SPEC "nil" TRANS_cases));;  

% --------------------------------------------------------------------------- %
% Prove that if a process can do an action, then the process is not nil.      %
%   |- !E u E'. TRANS E u E' ==> ~(E = nil)                            (1366) %
% --------------------------------------------------------------------------- %
let TRANS_IMP_NO_NIL =
     prove_thm
      (`TRANS_IMP_NO_NIL`,
       "!E u E'. TRANS E u E' ==> ~(E = nil)",
       TRANS_INDUCT_TAC THEN REWRITE_TAC [CCS_Distinct]);;

% --------------------------------------------------------------------------- %
% An agent variable has no transitions.                                (1228) %
%   |- !X u E'. ~TRANS (var X) u E'                                           %
% --------------------------------------------------------------------------- %
let VAR_NO_TRANS =
     save_thm
      (`VAR_NO_TRANS`,
       GEN_ALL
       (REWRITE_RULE [CCS_Distinct; CCS_One_One]
        (SPEC "var X" TRANS_cases)));;

% --------------------------------------------------------------------------- %
%  |- !u E u'' E'. TRANS(prefix u E)u'' E' = (u'' = u) /\ (E' = E)     (1245) %
% --------------------------------------------------------------------------- %
let TRANS_PREFIX_EQ =
     save_thm
      (`TRANS_PREFIX_EQ`,
       GEN_ALL
       (ONCE_REW_RHS_RULE [EQ_SYM_EQ]
        (SPEC_ALL (REWRITE_RULE [CCS_Distinct; CCS_One_One]
                   (SPEC "prefix u E" TRANS_cases)))));;

let TRANS_PREFIX = save_thm(`TRANS_PREFIX`, EQ_IMP_LR TRANS_PREFIX_EQ);;

% --------------------------------------------------------------------------- %
% The transitions of a binary summation.                           (1201+137) %
% TRANS_SUM_EQ:                                                               %
%  |- !E E' u E''. TRANS(sum E E')u E'' = TRANS E u E'' \/ TRANS E' u E''     %
% --------------------------------------------------------------------------- %
let SUM_cases_EQ = 
     save_thm 
      (`SUM_cases_EQ`, 
       GEN_ALL
       (REWRITE_RULE [CCS_Distinct; CCS_One_One]
        (SPEC "sum E E'" TRANS_cases)));;

let SUM_cases = save_thm(`SUM_cases`, EQ_IMP_LR SUM_cases_EQ);; 

let TRANS_SUM_EQ =
     prove_thm 
      (`TRANS_SUM_EQ`, 
       "!E E' u E''. 
         TRANS(sum E E')u E'' = TRANS E u E'' \/ TRANS E' u E''", 
       REPEAT GEN_TAC THEN 
       EQ_TAC THENL 
       [DISCH_TAC THEN IMP_RES_TAC SUM_cases THEN ASM_REWRITE_TAC[] ; 
        STRIP_TAC THENL [SUM1_TAC; SUM2_TAC] THEN ASM_REWRITE_TAC[] ]);; 
 
let TRANS_SUM = save_thm(`TRANS_SUM`, EQ_IMP_LR TRANS_SUM_EQ);; 

% --------------------------------------------------------------------------- %
%   |- !E E' u E''. TRANS(sum E E')u E'' = TRANS(sum E' E)u E''         (110) %
% --------------------------------------------------------------------------- %
let TRANS_COMM_EQ =
     prove_thm
      (`TRANS_COMM_EQ`,
       "!E E' u E''. TRANS (sum E E') u E'' = TRANS (sum E' E) u E''",
       REPEAT GEN_TAC THEN EQ_TAC THENL 
       [DISCH_TAC THEN IMP_RES_TAC TRANS_SUM THENL
        [SUM2_TAC; SUM1_TAC] THEN ASM_REWRITE_TAC[] 
        ;
        DISCH_TAC THEN IMP_RES_TAC TRANS_SUM THENL
        [SUM2_TAC; SUM1_TAC] THEN ASM_REWRITE_TAC[] ]);; 

% --------------------------------------------------------------------------- %
%   |- !E E' E'' E1 u.                                                  (318) %
%       TRANS(sum(sum E E')E'')u E1 = TRANS(sum E(sum E' E''))u E1            %
% --------------------------------------------------------------------------- %
let TRANS_ASSOC_EQ =
     prove_thm
      (`TRANS_ASSOC_EQ`,
       "!E E' E'' E1 u.
         TRANS (sum (sum E E') E'') u E1 = TRANS (sum E (sum E' E'')) u E1",
       REPEAT GEN_TAC THEN EQ_TAC THENL
       [DISCH_TAC THEN IMP_RES_TAC TRANS_SUM THENL
        [IMP_RES_TAC TRANS_SUM THENL
         [SUM1_TAC; SUM1_TAC; SUM2_TAC THEN SUM1_TAC; SUM2_TAC THEN SUM1_TAC] 
         THEN ASM_REWRITE_TAC[] ;
         SUM2_TAC THEN SUM2_TAC THEN ASM_REWRITE_TAC[] ]
        ;
        DISCH_TAC THEN IMP_RES_TAC TRANS_SUM THENL
        [SUM1_TAC THEN SUM1_TAC THEN ASM_REWRITE_TAC[] ;
         IMP_RES_TAC TRANS_SUM THENL
         [SUM1_TAC THEN SUM1_TAC; SUM1_TAC THEN SUM2_TAC; SUM2_TAC; SUM2_TAC]
         THEN ASM_REWRITE_TAC[] ]]);; 

let TRANS_ASSOC_RL = save_thm(`TRANS_ASSOC_RL`, EQ_IMP_RL TRANS_ASSOC_EQ);;

% --------------------------------------------------------------------------- %
%   |- !E u E'. TRANS(sum E nil)u E' = TRANS E u E'                      (62) %
% --------------------------------------------------------------------------- %
let TRANS_SUM_NIL_EQ =
     prove_thm
      (`TRANS_SUM_NIL_EQ`,
       "!E u E'. TRANS (sum E nil) u E' = TRANS E u E'", 
       REPEAT GEN_TAC THEN EQ_TAC THENL 
       [DISCH_TAC THEN IMP_RES_TAC TRANS_SUM THEN 
        IMP_RES_TAC NIL_NO_TRANS ;
        DISCH_TAC THEN SUM1_TAC THEN ASM_REWRITE_TAC[] ]);;   

let TRANS_SUM_NIL = save_thm(`TRANS_SUM_NIL`, EQ_IMP_LR TRANS_SUM_NIL_EQ);; 

% --------------------------------------------------------------------------- %
%   |- !E u E'. TRANS(sum E E)u E' = TRANS E u E'                        (48) %
% --------------------------------------------------------------------------- %
let TRANS_P_SUM_P_EQ =
     prove_thm
      (`TRANS_P_SUM_P_EQ`,
       "!E u E'. TRANS (sum E E) u E' = TRANS E u E'",
       REPEAT GEN_TAC THEN EQ_TAC THENL 
       [DISCH_TAC THEN IMP_RES_TAC TRANS_SUM ; 
        DISCH_TAC THEN SUM1_TAC THEN ASM_REWRITE_TAC[] ]);; 

let TRANS_P_SUM_P = save_thm(`TRANS_P_SUM_P`, EQ_IMP_LR TRANS_P_SUM_P_EQ);;  

% --------------------------------------------------------------------------- %
% |- !E E' u E''.                                                  (1162+381) %
%     TRANS(par E E')u E'' =                                                  %
%     (?E1. (E'' = par E1 E') /\ TRANS E u E1) \/                             %
%     (?E1. (E'' = par E E1) /\ TRANS E' u E1) \/                             %
%     (?E1 E2 l. (u = tau) /\ (E'' = par E1 E2) /\                            %
%                TRANS E(label l)E1 /\ TRANS E'(label(COMPL l))E2)            %
% --------------------------------------------------------------------------- %
let PAR_cases_EQ = 
     save_thm 
      (`PAR_cases_EQ`, 
       GEN_ALL 
       (REWRITE_RULE [CCS_Distinct; CCS_One_One] 
        (SPEC "par E E'" TRANS_cases)));;

let PAR_cases = save_thm(`PAR_cases`, EQ_IMP_LR PAR_cases_EQ);;

let TRANS_PAR_EQ =
     prove_thm
      (`TRANS_PAR_EQ`,
       "!E E' u E''.
          TRANS (par E E') u E'' =
          (?E1. (E'' = par E1 E') /\ TRANS E u E1) \/
          (?E1. (E'' = par E E1) /\ TRANS E' u E1) \/
          (?E1 E2 l. (u = tau) /\ (E'' = par E1 E2) /\
                     TRANS E (label l) E1 /\ TRANS E' (label(COMPL l)) E2)",
       REPEAT GEN_TAC THEN
       EQ_TAC THENL
       [STRIP_TAC THEN IMP_RES_TAC PAR_cases THENL
        [DISJ1_TAC THEN EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[]
         ;
         DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC "E1: CCS" THEN
         ASM_REWRITE_TAC[]
         ;
         DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC "E1: CCS" THEN
         EXISTS_TAC "E2: CCS" THEN EXISTS_TAC "l: Label" THEN
         ASM_REWRITE_TAC[] ]
        ;
        STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
        [PAR1_TAC; PAR2_TAC; PAR3_TAC THEN EXISTS_TAC "l: Label"] THEN
        ASM_REWRITE_TAC[] ]);;

let TRANS_PAR = save_thm(`TRANS_PAR`, EQ_IMP_LR TRANS_PAR_EQ);;

% --------------------------------------------------------------------------- %
% |- !E u E'.                                                           (141) %
%     TRANS(par E nil)u E' ==> (?E''. TRANS E u E'' /\ (E' = par E'' nil))    %
% --------------------------------------------------------------------------- %
let TRANS_PAR_P_NIL =
     prove_thm
      (`TRANS_PAR_P_NIL`,
       "!E u E'.
         TRANS (par E nil) u E' ==>
         (?E''. TRANS E u E'' /\ (E' = par E'' nil))",
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC TRANS_PAR THENL
       [EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] ;
        IMP_RES_TAC NIL_NO_TRANS ;
        IMP_RES_TAC NIL_NO_TRANS ]);;

% --------------------------------------------------------------------------- %
%  |- !l l'.                                                            (310) %
%      ~(l = COMPL l') ==>                                                    %
%      (!E E' E''. ~TRANS(par(prefix(label l)E)(prefix(label l')E'))tau E'')  %
% --------------------------------------------------------------------------- %
let TRANS_PAR_NO_SYNCR =
     prove_thm
      (`TRANS_PAR_NO_SYNCR`,
       "!l l'.
         ~(l = COMPL l') ==>
         (!E E' E''.
          ~(TRANS (par (prefix(label l) E) (prefix(label l') E')) tau E''))",
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC TRANS_PAR THENL
       [IMP_RES_TAC TRANS_PREFIX THEN IMP_RES_TAC Action_Distinct
        ;
        IMP_RES_TAC TRANS_PREFIX THEN IMP_RES_TAC Action_Distinct
        ;
        IMP_RES_TAC TRANS_PREFIX THEN IMP_RES_TAC Action_One_One THEN
        CHECK_ASSUME_TAC
        (REWRITE_RULE [SYM(ASSUME "l'': Label = l");
                       SYM(ASSUME "COMPL l'' = l'"); COMPL_COMPL]
                (ASSUME "~(l = COMPL l')")) ]);;

% --------------------------------------------------------------------------- %
%  |- !E L u E'.                                                   (1205+360) %
%      TRANS(restr E L)u E' =                                                 %
%      (?E'' l.                                                               %
%        (E' = restr E'' L) /\ TRANS E u E'' /\                               %
%        ((u = tau) \/ (u = label l) /\ ~l IN L /\ ~(COMPL l) IN L))          %
% --------------------------------------------------------------------------- %
let RESTR_cases_EQ = 
     save_thm 
      (`RESTR_cases_EQ`, 
       GEN_ALL 
       (REWRITE_RULE [CCS_Distinct; CCS_One_One]
        (SPEC "restr E L" TRANS_cases)));;

let RESTR_cases = save_thm(`RESTR_cases`, EQ_IMP_LR RESTR_cases_EQ);;   

let TRANS_RESTR_EQ =
     prove_thm
      (`TRANS_RESTR_EQ`,
       "!E L u E'.
         TRANS (restr E L) u E' = 
         (?E'' l. 
           (E' = restr E'' L) /\ TRANS E u E'' /\
           ((u = tau) \/ (u = label l) /\ ~l IN L /\ ~(COMPL l) IN L))",
       REPEAT GEN_TAC THEN
       EQ_TAC THENL
       [STRIP_TAC THEN IMP_RES_TAC RESTR_cases THEN
        EXISTS_TAC "E''': CCS" THEN EXISTS_TAC "l: Label" THENL
        [ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "u = tau"]
                          (ASSUME "TRANS E'' u E'''")] ;
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "u = label l"]
                          (ASSUME "TRANS E'' u E'''")] ]
        ;
        STRIP_TAC THENL
        [ASM_REWRITE_TAC[] THEN RESTR_TAC THEN
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "u = tau"]
                          (ASSUME "TRANS E u E''")] ;
         ASM_REWRITE_TAC[] THEN RESTR_TAC THEN EXISTS_TAC "l: Label" THEN
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "u = label l"]
                          (ASSUME "TRANS E u E''")] ] ]);;

let TRANS_RESTR = save_thm(`TRANS_RESTR`, EQ_IMP_LR TRANS_RESTR_EQ);;

% --------------------------------------------------------------------------- %
%   |- !E u E' L. TRANS(restr E L)u(restr E' L) ==> TRANS E u E'        (191) %
% --------------------------------------------------------------------------- %
let TRANS_P_RESTR =
     prove_thm
      (`TRANS_P_RESTR`,
       "!E u E' L. TRANS (restr E L) u (restr E' L) ==> TRANS E u E'",
       let thm = REWRITE_RULE [CCS_One_One]
                 (ASSUME "restr E' L = restr E'' L") in 
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC TRANS_RESTR THENL
       [FILTER_ASM_REWRITE_TAC (\t. not(t = "u = tau")) [thm]
        ;
        FILTER_ASM_REWRITE_TAC (\t. not(t = "u = label l")) [thm] ]);;

% --------------------------------------------------------------------------- %
%   |- !L u E. ~TRANS(restr nil L)u E                                    (98) %
% --------------------------------------------------------------------------- %
let RESTR_NIL_NO_TRANS =
     prove_thm
      (`RESTR_NIL_NO_TRANS`,
       "!L u E. ~(TRANS (restr nil L) u E)",
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC TRANS_RESTR THEN IMP_RES_TAC NIL_NO_TRANS);;

% --------------------------------------------------------------------------- %
%   |- !E u E'. TRANS E u E' ==> (!L. ~(E = restr nil L))                (40) %
% --------------------------------------------------------------------------- %
let TRANS_IMP_NO_RESTR_NIL =
     prove_thm
      (`TRANS_IMP_NO_RESTR_NIL`,
       "!E u E'. TRANS E u E' ==> !L. ~(E = restr nil L)",
       REPEAT STRIP_TAC THEN
       ASSUME_TAC (REWRITE_RULE [ASSUME "E = restr nil L"]
                          (ASSUME "TRANS E u E'")) THEN
       IMP_RES_TAC RESTR_NIL_NO_TRANS);;

% --------------------------------------------------------------------------- %
%   |- !E L u E'. TRANS(restr E L)u(restr E' L) ==> ~(E = nil)          (118) %
% --------------------------------------------------------------------------- %
let TRANS_RESTR_NO_NIL =
     prove_thm
      (`TRANS_RESTR_NO_NIL`,
       "!E L u E'. TRANS (restr E L) u (restr E' L) ==> ~(E = nil)",
       REPEAT STRIP_TAC THEN 
       IMP_RES_TAC TRANS_RESTR THEN
       ASSUME_TAC (REWRITE_RULE [ASSUME "E = nil"]
                          (ASSUME "TRANS E u E''")) THEN
       IMP_RES_TAC NIL_NO_TRANS);;

% --------------------------------------------------------------------------- %
%   |- !l L.                                                            (374) %
%       l IN L \/ (COMPL l) IN L ==>                                          %
%       (!E u E'. ~TRANS(restr(prefix(label l)E)L)u E')                       %
% --------------------------------------------------------------------------- %
let RESTR_LABEL_NO_TRANS =
     prove_thm
      (`RESTR_LABEL_NO_TRANS`,
       "!l L. 
         (l IN L) \/ ((COMPL l) IN L) ==>
         (!E u E'. ~(TRANS (restr (prefix (label l) E) L) u E'))",
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC TRANS_RESTR THENL
        [IMP_RES_TAC TRANS_PREFIX THEN 
         CHECK_ASSUME_TAC
         (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct]
                 (ASSUME "u = label l")) 
         ;
         IMP_RES_TAC TRANS_PREFIX THEN
         CHECK_ASSUME_TAC
         (MP (REWRITE_RULE
              [REWRITE_RULE [ASSUME "u = label l'"; Action_One_One]
                      (ASSUME "u = label l")]
              (ASSUME "~(l': Label) IN L"))
             (ASSUME "(l: Label) IN L")) ]
        ;
        IMP_RES_TAC TRANS_RESTR THENL
        [IMP_RES_TAC TRANS_PREFIX THEN
         CHECK_ASSUME_TAC
         (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct]
                 (ASSUME "u = label l"))
         ;
         IMP_RES_TAC TRANS_PREFIX THEN
         CHECK_ASSUME_TAC
         (MP (REWRITE_RULE
              [REWRITE_RULE [ASSUME "u = label l'"; Action_One_One]
                      (ASSUME "u = label l")]
                     (ASSUME "~(COMPL l') IN L"))
             (ASSUME "(COMPL l) IN L")) ] ]);;

% --------------------------------------------------------------------------- %
%  !E rf u E'.                                                     (1205+157) %
%   TRANS(relab E f)u E' =                                                    %
%   (?u' E''. (u = relabel rf u') /\ (E' = relab E'' rf) /\ TRANS E u' E'')   %
% --------------------------------------------------------------------------- %
let RELAB_cases_EQ = 
     save_thm 
      (`RELAB_cases_EQ`, 
       GEN_ALL 
       (REWRITE_RULE [CCS_Distinct; CCS_One_One]
        (SPEC "relab E rf" TRANS_cases)));; 

let RELAB_cases = save_thm(`RELAB_cases`, EQ_IMP_LR RELAB_cases_EQ);;   

let TRANS_RELAB_EQ =
     prove_thm
      (`TRANS_RELAB_EQ`,
       "!E rf u E'.
         TRANS (relab E rf) u E' =
         (?u' E''.
           (u = relabel rf u') /\ 
           (E' = relab E'' rf) /\ TRANS E u' E'')",
       REPEAT GEN_TAC THEN EQ_TAC THENL
       [DISCH_TAC THEN IMP_RES_TAC RELAB_cases THEN
        EXISTS_TAC "u': Action" THEN EXISTS_TAC "E''': CCS" THEN
        ASM_REWRITE_TAC[]
        ;
        STRIP_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] THEN RELAB_TAC THEN
        PURE_ONCE_ASM_REWRITE_TAC[] ]);;

let TRANS_RELAB = save_thm(`TRANS_RELAB`, EQ_IMP_LR TRANS_RELAB_EQ);;

let TRANS_RELAB_labl =
     save_thm 
      (`TRANS_RELAB_labl`, 
       GEN_ALL 
       (SPECL ["E: CCS"; "RELAB (labl: (Label # Label)list)"] TRANS_RELAB));;

% --------------------------------------------------------------------------- %
%   |- !rf u E. ~TRANS(relab nil f)u E                                   (60) %
% --------------------------------------------------------------------------- %
let RELAB_NIL_NO_TRANS =
     prove_thm
      (`RELAB_NIL_NO_TRANS`,
       "!rf u E. ~(TRANS (relab nil rf) u E)",
       REPEAT STRIP_TAC THEN 
       IMP_RES_TAC TRANS_RELAB THEN IMP_RES_TAC NIL_NO_TRANS);;

% --------------------------------------------------------------------------- %
% APPLY_RELAB_THM =                                                           %
%   |- !labl labl'.                                                           %
%       (RELAB labl = RELAB labl') = (Apply_Relab labl = Apply_Relab labl')   %
% --------------------------------------------------------------------------- %
let APPLY_RELAB_THM =
     save_thm
      (`APPLY_RELAB_THM`,
       GEN_ALL
       (REWRITE_RULE [GSYM RELAB]
        (MATCH_MP
         (MATCH_MP ABS_Relabelling_one_one
          (SPEC "labl: (Label#Label)list" IS_RELABELLING))
         (SPEC "labl': (Label#Label)list" IS_RELABELLING))));;

% --------------------------------------------------------------------------- %
%  |- !X E u E'.                                                    (1215+72) %
%      TRANS(rec X E)u E' = TRANS(CCS_Subst E(rec X E)X)u E'                  %
% --------------------------------------------------------------------------- %
let REC_cases_EQ = 
     save_thm 
      (`REC_cases_EQ`, 
       GEN_ALL 
       (REWRITE_RULE [CCS_Distinct; CCS_One_One]
        (SPEC "rec X E" TRANS_cases)));;

let REC_cases = save_thm(`REC_cases`, EQ_IMP_LR REC_cases_EQ);;

let TRANS_REC_EQ =
     prove_thm
      (`TRANS_REC_EQ`,
       "!X E u E'.
         TRANS (rec X E) u E' = TRANS (CCS_Subst E (rec X E) X) u E'",
       REPEAT GEN_TAC THEN EQ_TAC THENL  
       [PURE_ONCE_REWRITE_TAC [REC_cases_EQ] THEN
        REPEAT STRIP_TAC THEN PURE_ASM_REWRITE_TAC[] ;   
        PURE_ONCE_REWRITE_TAC [REC] ]);;

let TRANS_REC = save_thm(`TRANS_REC`, EQ_IMP_LR TRANS_REC_EQ);; 

% --------------------------------------------------------------------------- %
% Close the theory.                                                           % 
% --------------------------------------------------------------------------- %
close_theory();; 

