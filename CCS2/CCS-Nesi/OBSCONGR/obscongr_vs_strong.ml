% =========================================================================== %
% FILE          : obscongr_vs_strong.ml                                       %
% DESCRIPTION   : Relationship between strong equivalence and observation     %
%                 congruence                                                  %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 29 February 1992                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `obscongr_vs_strong`;;

% --------------------------------------------------------------------------- %
% Prove that strong equivalence implies observation congruence.         (256) %
% --------------------------------------------------------------------------- %
let STRONG_IMP_OBS_CONGR =         
     prove_thm
      (`STRONG_IMP_OBS_CONGR`,
       "!E E'. STRONG_EQUIV E E' ==> OBS_CONGR E E'",
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [PROPERTY_STAR; OBS_CONGR] THEN
       REPEAT STRIP_TAC THENL
       [RES_TAC THEN IMP_RES_TAC TRANS_IMP_WEAK_TRANS THEN
        IMP_RES_TAC STRONG_IMP_OBS_EQUIV THEN EXISTS_TAC "E2: CCS" THEN
        ASM_REWRITE_TAC[] 
        ;
        RES_TAC THEN IMP_RES_TAC TRANS_IMP_WEAK_TRANS THEN
        IMP_RES_TAC STRONG_IMP_OBS_EQUIV THEN EXISTS_TAC "E1: CCS" THEN
        ASM_REWRITE_TAC[] ]);;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;


