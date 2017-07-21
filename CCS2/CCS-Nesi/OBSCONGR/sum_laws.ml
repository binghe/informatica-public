% =========================================================================== %
% FILE          : sum_laws.ml                                                 %
% DESCRIPTION   : Basic laws of observation congruence for binary summation   %
%                 through strong equivalence                                  %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 26 June 1992                                                %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `sum_laws`;;

% --------------------------------------------------------------------------- %
% Prove SUM_IDENT_R: |- !E. OBS_CONGR(sum E nil)E                             %
% --------------------------------------------------------------------------- %
let SUM_IDENT_R =
     save_thm 
      (`SUM_IDENT_R`, 
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_CONGR (SPEC "E: CCS" STRONG_SUM_IDENT_R)));;  
 
% --------------------------------------------------------------------------- %
% Prove SUM_IDENT_L: |- !E. OBS_CONGR(sum nil E)E                             %
% --------------------------------------------------------------------------- %
let SUM_IDENT_L =
     save_thm
      (`SUM_IDENT_L`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR (SPEC "E: CCS" STRONG_SUM_IDENT_L)));;  

% --------------------------------------------------------------------------- %
% Prove SUM_IDEMP: |- !E. OBS_CONGR(sum E E)E                                 %
% --------------------------------------------------------------------------- %
let SUM_IDEMP =
     save_thm
      (`SUM_IDEMP`, 
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR (SPEC "E: CCS" STRONG_SUM_IDEMP)));;

% --------------------------------------------------------------------------- %
% Prove SUM_COMM: |- !E E'. OBS_CONGR(sum E E')(sum E' E)                     %
% --------------------------------------------------------------------------- %
let SUM_COMM =
     save_thm
      (`SUM_COMM`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR
        (SPECL ["E: CCS"; "E': CCS"] STRONG_SUM_COMM)));; 

% --------------------------------------------------------------------------- %
% Observation congruence is substitutive under the binary summation operator  %
% on the left:                                                                %
%  |- !E E'. OBS_CONGR E E' ==> (!E''. OBS_CONGR(sum E'' E)(sum E'' E'))      %
% --------------------------------------------------------------------------- %
let SUBST_SUM_L =
     save_thm
      (`SUBST_SUM_L`,
       GEN_ALL
       (DISCH "OBS_CONGR E E'"
        (GEN "E'': CCS"
         (OC_TRANS
          (SPECL ["E'': CCS"; "E: CCS"] SUM_COMM)
           (OC_TRANS
            (SPEC_ALL (UNDISCH (SPEC_ALL SUBST_SUM_R)))
            (SPECL ["E': CCS"; "E'': CCS"] SUM_COMM))))));;

% --------------------------------------------------------------------------- %
% Observation congruence is preserved by the binary summation operator.       %
%  |- !E1 E1' E2 E2'.                                                         %
%      OBS_CONGR E1 E1' /\ OBS_CONGR E2 E2' ==>                               %
%      OBS_CONGR(sum E1 E2)(sum E1' E2')                                      %
% --------------------------------------------------------------------------- %
let OBS_CONGR_PRESD_BY_SUM =
     save_thm
      (`OBS_CONGR_PRESD_BY_SUM`,
       GEN_ALL
       (REWRITE_RULE [AND_IMP_INTRO]
        (DISCH "OBS_CONGR E1 E1'"
         (DISCH "OBS_CONGR E2 E2'"
          (OC_TRANS
           (SPEC "E2: CCS"
            (MATCH_MP SUBST_SUM_R (ASSUME "OBS_CONGR E1 E1'"))) 
           (SPEC "E1': CCS"
            (MATCH_MP SUBST_SUM_L (ASSUME "OBS_CONGR E2 E2'"))))))));; 

% --------------------------------------------------------------------------- %
% Prove SUM_ASSOC_R:                                                          %
%  |- !E E' E''. OBS_CONGR(sum(sum E E')E'')(sum E(sum E' E''))               %
% --------------------------------------------------------------------------- %
let SUM_ASSOC_R =
     save_thm
      (`SUM_ASSOC_R`, 
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR 
        (SPECL ["E: CCS"; "E': CCS"; "E'': CCS"] STRONG_SUM_ASSOC_R)));; 

% --------------------------------------------------------------------------- %
% Prove SUM_ASSOC_L:                                                          %
%  |- !E E' E''. OBS_CONGR(sum E(sum E' E''))(sum(sum E E')E'')               %
% --------------------------------------------------------------------------- %
let SUM_ASSOC_L = 
     save_thm
      (`SUM_ASSOC_L`, 
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR
        (SPECL ["E: CCS"; "E': CCS"; "E'': CCS"] STRONG_SUM_ASSOC_L)));; 

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;


