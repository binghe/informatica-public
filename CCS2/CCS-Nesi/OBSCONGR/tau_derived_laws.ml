% =========================================================================== %
% FILE          : tau_derived_laws.ml                                         %
% DESCRIPTION   : A derived tau-law for observation congruence                %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `tau_derived_laws`;; 

% --------------------------------------------------------------------------- %
% Theorem TAU_STRAT:                                                    (200) %
%  |- !E E'. OBS_CONGR(sum E(prefix tau(sum E' E)))(prefix tau(sum E' E))     %
% --------------------------------------------------------------------------- %
let TAU_STRAT =
     prove_thm
      (`TAU_STRAT`,
       "!E E'.
         OBS_CONGR (sum E (prefix tau (sum E' E))) (prefix tau (sum E' E))",
       REPEAT GEN_TAC THEN
       OC_LHS_SUBST1_TAC 
       (SPEC "sum E' E" (GEN_ALL (OC_SYM (SPEC_ALL TAU2)))) THEN
       SUM_IDEMP_TAC THEN
       OC_LHS_SUBST1_TAC (SPEC "sum E' E" TAU2));;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;


