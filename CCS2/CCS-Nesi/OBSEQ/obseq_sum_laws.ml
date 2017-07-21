% =========================================================================== %
% FILE          : obseq_sum_laws.ml                                           %
% DESCRIPTION   : Basic laws of observation equivalence for the binary        %
%                 summation operator derived through strong equivalence       % 
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 29 February 1992                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `obseq_sum_laws`;;

% --------------------------------------------------------------------------- %
% Prove OBS_SUM_IDENT_R: |- !E. OBS_EQUIV(sum E nil)E                         %
% --------------------------------------------------------------------------- %
let OBS_SUM_IDENT_R =
     save_thm
      (`OBS_SUM_IDENT_R`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPEC "E: CCS" STRONG_SUM_IDENT_R)));;

% --------------------------------------------------------------------------- %
% Prove OBS_SUM_IDENT_L: |- !E. OBS_EQUIV(sum nil E)E                         %
% --------------------------------------------------------------------------- %
let OBS_SUM_IDENT_L =
     save_thm
      (`OBS_SUM_IDENT_L`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPEC "E: CCS" STRONG_SUM_IDENT_L)));;

% --------------------------------------------------------------------------- %
% Prove OBS_SUM_IDEMP: |- !E. OBS_EQUIV(sum E E)E                             %
% --------------------------------------------------------------------------- %
let OBS_SUM_IDEMP =
     save_thm
      (`OBS_SUM_IDEMP`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_EQUIV 
        (SPEC "E: CCS" STRONG_SUM_IDEMP)));;

% --------------------------------------------------------------------------- %
% Prove OBS_SUM_COMM: |- !E E'. OBS_EQUIV(sum E E')(sum E' E)                 %
% --------------------------------------------------------------------------- %
let OBS_SUM_COMM =
     save_thm
      (`OBS_SUM_COMM`,
       GEN_ALL   
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["E: CCS"; "E': CCS"] STRONG_SUM_COMM)));;

% --------------------------------------------------------------------------- %
% Observation equivalence of stable agents is substitutive under the binary   %
% summation operator on the left:                                             %
%  |- !E E'. OBS_EQUIV E E' /\ STABLE E /\ STABLE E' ==>                      %
%            (!E''. OBS_EQUIV(sum E'' E)(sum E'' E'))                         %
% --------------------------------------------------------------------------- %
let OBS_EQUIV_SUBST_SUM_L =
     save_thm
      (`OBS_EQUIV_SUBST_SUM_L`,
       GEN_ALL
       (DISCH_ALL
        (GEN "E'': CCS"
         (OE_TRANS
          (SPECL ["E'': CCS"; "E: CCS"] OBS_SUM_COMM)
           (OE_TRANS
            (SPEC_ALL (UNDISCH (SPEC_ALL OBS_EQUIV_SUBST_SUM_R)))
            (SPECL ["E': CCS"; "E'': CCS"] OBS_SUM_COMM))))));;

% --------------------------------------------------------------------------- %
% Prove OBS_SUM_ASSOC_R:                                                      %
%  |- !E E' E''. OBS_EQUIV(sum(sum E E')E'')(sum E(sum E' E''))               %
% --------------------------------------------------------------------------- %
let OBS_SUM_ASSOC_R =
     save_thm
      (`OBS_SUM_ASSOC_R`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["E: CCS"; "E': CCS"; "E'': CCS"] STRONG_SUM_ASSOC_R)));;

% --------------------------------------------------------------------------- %
% Prove OBS_SUM_ASSOC_L:                                                      %
%  |- !E E' E''. OBS_EQUIV(sum E(sum E' E''))(sum(sum E E')E'')               %
% --------------------------------------------------------------------------- %
let OBS_SUM_ASSOC_L =
     save_thm
      (`OBS_SUM_ASSOC_L`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["E: CCS"; "E': CCS"; "E'': CCS"] STRONG_SUM_ASSOC_L)));;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;


