% =========================================================================== %
% FILE          : tau_weak.ml                                                 %
% DESCRIPTION   : the tau-law "tau.E = E" for observation equivalence         %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : August 1994                                                 %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `tau_weak`;;

% --------------------------------------------------------------------------- %
% Prove TAU_WEAK:  |- !E. OBS_EQUIV(prefix tau E)E                      (235) %
% --------------------------------------------------------------------------- %
let TAU_WEAK =
     prove_thm
      (`TAU_WEAK`,
       "!E. OBS_EQUIV (prefix tau E) E",
       GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [OBS_PROP_STAR] THEN
       REPEAT STRIP_TAC THENL
       [IMP_RES_TAC TRANS_PREFIX THEN IMP_RES_TAC Action_Distinct_label
        ;
        EXISTS_TAC "E2: CCS" THEN REWRITE_TAC [WEAK_TRANS; OBS_EQUIV_REFL] THEN
        EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E2: CCS" THEN   
        ASM_REWRITE_TAC [EPS_REFL] THEN ONE_TAU_TAC THEN PREFIX_TAC
        ;
        IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E1: CCS" THEN
        ASM_REWRITE_TAC [EPS_REFL; OBS_EQUIV_REFL]
        ;
        EXISTS_TAC "E2: CCS" THEN REWRITE_TAC [OBS_EQUIV_REFL] THEN
        EPS_TRANS_TAC THEN EXISTS_TAC "E: CCS" THEN
        IMP_RES_TAC ONE_TAU THEN ASM_REWRITE_TAC[] THEN ONE_TAU_TAC THEN
        PREFIX_TAC]);;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

