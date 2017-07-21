% =========================================================================== %
% FILE          : sum_strong_laws.ml                                          %
% DESCRIPTION   : Basic laws of strong equivalence for the summation operator % 
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 21 October 1991                                             %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      % 
% --------------------------------------------------------------------------- %
new_theory `sum_strong_laws`;;

% --------------------------------------------------------------------------- %
% Prove STRONG_SUM_IDENT_R: |- !E. STRONG_EQUIV(sum E nil)E             (278) %
% --------------------------------------------------------------------------- %
let STRONG_SUM_IDENT_R =
     prove_thm
      (`STRONG_SUM_IDENT_R`,
       "!E. STRONG_EQUIV (sum E nil) E",
       GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y. (x = y) \/ (?E'. (x = sum E' nil) /\ (y = E'))" THEN
       CONJ_TAC THENL 
       [BETA_TAC THEN DISJ2_TAC THEN 
        EXISTS_TAC "E: CCS" THEN REWRITE_TAC[]  
        ;
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN      
        REPEAT STRIP_TAC THENL
        [EXISTS_TAC "E1: CCS" THEN
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "E: CCS = E'"] 
                                 (ASSUME "TRANS E u E1")] 
         ; 
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
         ;  
         ASSUME_TAC (REWRITE_RULE [ASSUME "E = sum E'' nil"]
                            (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_SUM_NIL THEN 
         EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] 
         ;  
         ASSUME_TAC (REWRITE_RULE [ASSUME "E': CCS = E''"]
                            (ASSUME "TRANS E' u E2")) THEN
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] THEN SUM1_TAC THEN 
         PURE_ONCE_ASM_REWRITE_TAC[] ]]);;

% --------------------------------------------------------------------------- %
% Prove STRONG_SUM_IDEMP: |- !E. STRONG_EQUIV(sum E E)E                 (269) %
% --------------------------------------------------------------------------- %
let STRONG_SUM_IDEMP =
     prove_thm
      (`STRONG_SUM_IDEMP`,
       "!E. STRONG_EQUIV (sum E E) E",
       GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y. (x = y) \/ (?E'. (x = sum E' E') /\ (y = E'))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN 
        EXISTS_TAC "E: CCS" THEN REWRITE_TAC[] 
        ;  
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN      
        REPEAT STRIP_TAC THENL
        [EXISTS_TAC "E1: CCS" THEN
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "E: CCS = E'"] 
                                 (ASSUME "TRANS E u E1")] 
         ;  
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
         ;  
         ASSUME_TAC (REWRITE_RULE [ASSUME "E = sum E'' E''"]
                            (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_P_SUM_P THEN EXISTS_TAC "E1: CCS" THEN 
         ASM_REWRITE_TAC[] 
         ;  
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] THEN SUM1_TAC THEN    
         PURE_ONCE_REWRITE_TAC [REWRITE_RULE [ASSUME "E': CCS = E''"]
                                       (ASSUME "TRANS E' u E2")] ]]);; 

% --------------------------------------------------------------------------- %
% Prove STRONG_SUM_COMM: |- !E E'. STRONG_EQUIV(sum E E')(sum E' E)     (265) %
% --------------------------------------------------------------------------- %
let STRONG_SUM_COMM =
     prove_thm
      (`STRONG_SUM_COMM`,
       "!E E'. STRONG_EQUIV (sum E E') (sum E' E)",
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y. (x = y) \/ (?E1 E2. (x = sum E1 E2) /\ (y = sum E2 E1))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "E: CCS" THEN 
        EXISTS_TAC "E': CCS" THEN REWRITE_TAC[] 
        ;   
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN     
        REPEAT STRIP_TAC THENL
        [EXISTS_TAC "E1: CCS" THEN
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "E: CCS = E'"] 
                                 (ASSUME "TRANS E u E1")] 
         ;   
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
         ;  
         EXISTS_TAC "E1': CCS" THEN 
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "E = sum E1 E2"] 
                                 (ASSUME "TRANS E u E1'"); 
                          TRANS_COMM_EQ] 
         ; 
         EXISTS_TAC "E2': CCS" THEN 
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "E' = sum E2 E1"] 
                                 (ASSUME "TRANS E' u E2'"); 
                          TRANS_COMM_EQ] ]]);; 

% --------------------------------------------------------------------------- %
% Prove STRONG_SUM_IDENT_L: |- !E. STRONG_EQUIV(sum nil E)E                   %
% --------------------------------------------------------------------------- %
let STRONG_SUM_IDENT_L =
     save_thm
      (`STRONG_SUM_IDENT_L`,
       GEN_ALL
       (S_TRANS (SPECL ["nil"; "E: CCS"] STRONG_SUM_COMM)
                (SPEC "E: CCS" STRONG_SUM_IDENT_R)));;

% --------------------------------------------------------------------------- %
% Prove STRONG_SUM_ASSOC_R:                                             (285) % 
%   |- !E E' E''. STRONG_EQUIV(sum(sum E E')E'')(sum E(sum E' E'')).          %
% --------------------------------------------------------------------------- %
let STRONG_SUM_ASSOC_R =
     prove_thm
      (`STRONG_SUM_ASSOC_R`,
       "!E E' E''. 
         STRONG_EQUIV (sum (sum E E') E'') (sum E (sum E' E''))",
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y. (x = y) \/ (?E1 E2 E3. (x = sum (sum E1 E2) E3) /\
                                     (y = sum E1 (sum E2 E3)))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "E: CCS" THEN
        EXISTS_TAC "E': CCS" THEN EXISTS_TAC "E'': CCS" THEN REWRITE_TAC[]
        ;
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN     
        REPEAT STRIP_TAC THENL
        [EXISTS_TAC "E1: CCS" THEN
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "E: CCS = E'"] 
                                 (ASSUME "TRANS E u E1")] 
         ; 
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
         ;   
         EXISTS_TAC "E1': CCS" THEN ASM_REWRITE_TAC[] THEN   
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "E = sum(sum E1 E2)E3"]
                                 (ASSUME "TRANS E u E1'"); 
                          SYM (SPEC_ALL TRANS_ASSOC_EQ)] 
         ; 
         EXISTS_TAC "E2': CCS" THEN    
         ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "E' = sum E1(sum E2 E3)"]
                                 (ASSUME "TRANS E' u E2'"); 
                          TRANS_ASSOC_EQ] ]]);;  

% --------------------------------------------------------------------------- %
% Prove STRONG_SUM_ASSOC_L:                                                   %
%  |- !E E' E''. STRONG_EQUIV(sum E(sum E' E''))(sum(sum E E')E'')            %
% --------------------------------------------------------------------------- %
let STRONG_SUM_ASSOC_L =
     save_thm
      (`STRONG_SUM_ASSOC_L`,
       GEN_ALL
       (S_SYM
        (SPECL ["E: CCS"; "E': CCS"; "E'': CCS"] STRONG_SUM_ASSOC_R)));;

% --------------------------------------------------------------------------- %
% Prove STRONG_SUM_MID_IDEMP:                                                 %
%  |- !E E'. STRONG_EQUIV(sum(sum E E')E)(sum E' E)                           %
% --------------------------------------------------------------------------- %
let STRONG_SUM_MID_IDEMP =
     save_thm
      (`STRONG_SUM_MID_IDEMP`,
       GEN_ALL
       (S_TRANS
        (SPEC "E: CCS"
         (MATCH_MP STRONG_EQUIV_SUBST_SUM_R
          (SPECL ["E: CCS"; "E': CCS"] STRONG_SUM_COMM)))
        (S_TRANS
         (SPECL ["E': CCS"; "E: CCS"; "E: CCS"] STRONG_SUM_ASSOC_R)
         (SPEC "E': CCS" 
          (MATCH_MP STRONG_EQUIV_SUBST_SUM_L 
           (SPEC "E: CCS" STRONG_SUM_IDEMP))))));;

% --------------------------------------------------------------------------- %
% Prove STRONG_LEFT_SUM_MID_IDEMP:                                            %
%  |- !E E' E''. STRONG_EQUIV(sum(sum(sum E E')E'')E')(sum(sum E E'')E')      %
% --------------------------------------------------------------------------- %
let STRONG_LEFT_SUM_MID_IDEMP =
     save_thm
      (`STRONG_LEFT_SUM_MID_IDEMP`,
       GEN_ALL
       (S_TRANS
        (S_TRANS
         (SPEC "E': CCS"
          (MATCH_MP STRONG_EQUIV_SUBST_SUM_R
           (SPEC "E'': CCS"
            (MATCH_MP STRONG_EQUIV_SUBST_SUM_R
             (SPECL ["E: CCS"; "E': CCS"] STRONG_SUM_COMM)))))
         (SPEC "E': CCS"
          (MATCH_MP STRONG_EQUIV_SUBST_SUM_R
           (SPECL ["E': CCS"; "E: CCS"; "E'': CCS"] STRONG_SUM_ASSOC_R))))
        (SPECL ["E': CCS"; "sum E E''"] STRONG_SUM_MID_IDEMP)));;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();; 
 
