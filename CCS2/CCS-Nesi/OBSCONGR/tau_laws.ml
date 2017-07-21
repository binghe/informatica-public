% =========================================================================== %
% FILE          : tau_laws.ml                                                 %
% DESCRIPTION   : tau-laws for observation congruence (and the same tau-laws  %
%                 for observation equivalence derived through the congruence) %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 21 October 1991                                             %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `tau_laws`;;

% --------------------------------------------------------------------------- %
% Prove TAU1:                                                           (271) %
%     |- !u E. OBS_CONGR(prefix u(prefix tau E))(prefix u E)                  %
% --------------------------------------------------------------------------- %
let TAU1 =
     prove_thm
      (`TAU1`,
       "!u E. OBS_CONGR (prefix u (prefix tau E)) (prefix u E)",
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [OBS_CONGR] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E: CCS" THEN  
        ASM_REWRITE_TAC [WEAK_TRANS; TAU_WEAK] THEN EXISTS_TAC "prefix u E" THEN
        EXISTS_TAC "E: CCS" THEN ASM_REWRITE_TAC [EPS_REFL] THEN PREFIX_TAC 
        ; 
        IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "prefix tau E2" THEN 
        ASM_REWRITE_TAC [WEAK_TRANS; TAU_WEAK] THEN 
        EXISTS_TAC "prefix u(prefix tau E2)" THEN 
        EXISTS_TAC "prefix tau E2" THEN ASM_REWRITE_TAC [EPS_REFL] THEN 
        PREFIX_TAC ]);;   

% --------------------------------------------------------------------------- %
% Prove TAU1_EQUIV:                                                           %
%       |- !u E. OBS_EQUIV(prefix u(prefix tau E))(prefix u E)                %
% --------------------------------------------------------------------------- %
let TAU1_EQUIV = 
     save_thm 
      (`TAU1_EQUIV`, 
       GEN_ALL (MATCH_MP OBS_CONGR_IMP_OBS_EQUIV (SPEC_ALL TAU1)));; 
 
% --------------------------------------------------------------------------- %
% Prove TAU2:                                                           (253) % 
%     |- !E. OBS_CONGR(sum E(prefix tau E))(prefix tau E)                     %
% --------------------------------------------------------------------------- %
let TAU2 =
     prove_thm
      (`TAU2`,
       "!E. OBS_CONGR (sum E (prefix tau E)) (prefix tau E)",
       GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [OBS_CONGR] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC TRANS_SUM THENL
        [EXISTS_TAC "E1: CCS" THEN REWRITE_TAC [WEAK_TRANS; OBS_EQUIV_REFL] THEN
         EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E1: CCS" THEN 
         ASM_REWRITE_TAC [EPS_REFL] THEN ONE_TAU_TAC THEN PREFIX_TAC 
         ;  
         IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E1: CCS" THEN
         REWRITE_TAC [OBS_EQUIV_REFL] THEN IMP_RES_TAC TRANS_IMP_WEAK_TRANS ] 
        ;  
        IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E2: CCS" THEN
        REWRITE_TAC [WEAK_TRANS; OBS_EQUIV_REFL] THEN
        EXISTS_TAC "sum E(prefix tau E)" THEN EXISTS_TAC "E2: CCS" THEN   
        REWRITE_TAC [EPS_REFL] THEN SUM2_TAC THEN 
        PURE_ONCE_ASM_REWRITE_TAC[] ]);;        

% --------------------------------------------------------------------------- %
% Prove TAU2_EQUIV:                                                           %
%       |- !E. OBS_EQUIV(sum E(prefix tau E))(prefix tau E)                   %
% --------------------------------------------------------------------------- %
let TAU2_EQUIV =
     save_thm 
      (`TAU2_EQUIV`, 
       GEN_ALL (MATCH_MP OBS_CONGR_IMP_OBS_EQUIV (SPEC_ALL TAU2)));;  

% --------------------------------------------------------------------------- %
% Prove TAU3:                                                           (320) %
%  |- !u E E'.                                                                %
%      OBS_CONGR (sum(prefix u(sum E(prefix tau E')))(prefix u E'))           %
%                (prefix u(sum E(prefix tau E')))                             %
% --------------------------------------------------------------------------- %
let TAU3 =
     prove_thm
      (`TAU3`,
       "!u E E'.
        OBS_CONGR (sum (prefix u (sum E (prefix tau E'))) (prefix u E'))
                  (prefix u (sum E (prefix tau E')))",
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [OBS_CONGR] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC TRANS_SUM THENL
        [IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E1: CCS" THEN
         REWRITE_TAC [OBS_EQUIV_REFL] THEN IMP_RES_TAC TRANS_IMP_WEAK_TRANS 
         ; 
         IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E1: CCS" THEN
         ASM_REWRITE_TAC [WEAK_TRANS; OBS_EQUIV_REFL] THEN 
         EXISTS_TAC "prefix u(sum E(prefix tau E'))" THEN
         EXISTS_TAC "sum E(prefix tau E')" THEN
         REWRITE_TAC [EPS_REFL; PREFIX] THEN ONE_TAU_TAC THEN   
         SUM2_TAC THEN PREFIX_TAC ]  
        ;
        IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E2: CCS" THEN
        REWRITE_TAC [WEAK_TRANS; OBS_EQUIV_REFL] THEN 
        EXISTS_TAC "sum(prefix u(sum E(prefix tau E')))(prefix u E')" THEN 
        EXISTS_TAC "E2: CCS" THEN REWRITE_TAC [EPS_REFL] THEN   
        SUM1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ]);;       

% --------------------------------------------------------------------------- %
% Prove TAU3_EQUIV:                                                           %
%  |- !u E E'.                                                                %
%      OBS_EQUIV (sum(prefix u(sum E(prefix tau E')))(prefix u E'))           %
%                (prefix u(sum E(prefix tau E')))                             %
% --------------------------------------------------------------------------- %
let TAU3_EQUIV =
     save_thm 
      (`TAU3_EQUIV`, 
       GEN_ALL (MATCH_MP OBS_CONGR_IMP_OBS_EQUIV (SPEC_ALL TAU3)));; 

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

