% =========================================================================== %
% FILE          : weak_vs_strong.ml                                           %
% DESCRIPTION   : Relationship between strong bisimulation (strong equiv.)    %
%                 and weak bisimulation (observation equivalence)             %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 29 February 1992                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `weak_vs_strong`;;

% --------------------------------------------------------------------------- %
% Prove that a strong bisimulation is a particular weak bisimulation.   (370) %
% --------------------------------------------------------------------------- %
let STRONG_IMP_WEAK_BISIM =
     prove_thm
      (`STRONG_IMP_WEAK_BISIM`,
       "!Bsm. STRONG_BISIM Bsm ==> WEAK_BISIM Bsm",
       GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [WEAK_BISIM] THEN
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC 
       (MATCH_MP (REWRITE_RULE [STRONG_BISIM] (ASSUME "STRONG_BISIM Bsm"))  
        (ASSUME "(Bsm: CCS -> CCS -> bool) E E'")) THENL  
       [IMP_RES_TAC TRANS_IMP_WEAK_TRANS THEN 
        EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]  
        ;
        IMP_RES_TAC TRANS_IMP_WEAK_TRANS THEN 
        EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] 
        ;
        IMP_RES_TAC ONE_TAU THEN 
        EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
        ;
        IMP_RES_TAC ONE_TAU THEN 
        EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] ]);;

% --------------------------------------------------------------------------- %
% Prove that strong equivalence implies observation equivalence.         (55) %
% --------------------------------------------------------------------------- %
let STRONG_IMP_OBS_EQUIV =
     prove_thm
      (`STRONG_IMP_OBS_EQUIV`,
       "!E E'. STRONG_EQUIV E E' ==> OBS_EQUIV E E'",
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV; OBS_EQUIV] THEN
       STRIP_TAC THEN IMP_RES_TAC STRONG_IMP_WEAK_BISIM THEN    
       EXISTS_TAC "Bsm: CCS -> CCS -> bool" THEN ASM_REWRITE_TAC[]);;     

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;


