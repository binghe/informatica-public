% =========================================================================== %
% FILE          : par_laws.ml                                                 %
% DESCRIPTION   : Basic laws of observation congruence for the parallel       %
%                 operator through strong equivalence                         %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 26 June 1992                                                %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `par_laws`;;

% --------------------------------------------------------------------------- %
% Prove PAR_IDENT_R: |- !E. OBS_CONGR(par E nil)E                             %
% --------------------------------------------------------------------------- %
let PAR_IDENT_R = 
     save_thm
      (`PAR_IDENT_R`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_CONGR (SPEC "E: CCS" STRONG_PAR_IDENT_R)));;

% --------------------------------------------------------------------------- %
% Prove PAR_IDENT_L: |- !E. OBS_CONGR(par nil E)E                             %
% --------------------------------------------------------------------------- %
let PAR_IDENT_L =
     save_thm
      (`PAR_IDENT_L`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_CONGR (SPEC "E: CCS" STRONG_PAR_IDENT_L)));;

% --------------------------------------------------------------------------- %
% Prove PAR_COMM: |- !E E'. OBS_CONGR(par E E')(par E' E)                     %
% --------------------------------------------------------------------------- %
let PAR_COMM =
     save_thm
      (`PAR_COMM`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_CONGR 
        (SPECL ["E: CCS"; "E': CCS"] STRONG_PAR_COMM)));;

% --------------------------------------------------------------------------- %
% Prove PAR_ASSOC:                                                            %
%  |- !E E' E''. OBS_CONGR(par(par E E')E'')(par E(par E' E''))               %
% --------------------------------------------------------------------------- %
let PAR_ASSOC =
     save_thm
      (`PAR_ASSOC`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR 
        (SPECL ["E: CCS"; "E': CCS"; "E'': CCS"] STRONG_PAR_ASSOC)));;
 
% --------------------------------------------------------------------------- %
% Prove PAR_PREF_TAU:                                                         %
%  |- !u E E'.                                                                %
%      OBS_CONGR (par(prefix u E)(prefix tau E'))                             %
%                (sum(prefix u(par E(prefix tau E')))                         %
%                    (prefix tau(par(prefix u E)E')))                         %
% --------------------------------------------------------------------------- %
let PAR_PREF_TAU =
     save_thm
      (`PAR_PREF_TAU`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR  
        (SPECL ["u: Action"; "E: CCS"; "E': CCS"] STRONG_PAR_PREF_TAU)));;

% --------------------------------------------------------------------------- %
% Prove PAR_TAU_PREF:                                                         %
%  |- !E u E'.                                                                %
%      OBS_CONGR (par(prefix tau E)(prefix u E'))                             %
%                (sum(prefix tau(par E(prefix u E')))                         %
%                    (prefix u(par(prefix tau E)E')))                         %
% --------------------------------------------------------------------------- %
let PAR_TAU_PREF =
     save_thm
      (`PAR_TAU_PREF`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR  
        (SPECL ["E: CCS"; "u: Action"; "E': CCS"] STRONG_PAR_TAU_PREF)));;

% --------------------------------------------------------------------------- %
% Prove PAR_TAU_TAU:                                                          %
%  |- !E E'.                                                                  %
%      OBS_CONGR (par(prefix tau E)(prefix tau E'))                           %
%                (sum(prefix tau(par E(prefix tau E')))                       %
%                    (prefix tau(par(prefix tau E)E')))                       %
% --------------------------------------------------------------------------- %
let PAR_TAU_TAU = save_thm(`PAR_TAU_TAU`, SPEC "tau" PAR_PREF_TAU);;    

% --------------------------------------------------------------------------- %
% Prove PAR_PREF_NO_SYNCR:                                                    %
%  |- !l l'.                                                                  %
%      ~(l = COMPL l') ==>                                                    %
%      (!E E'.                                                                %
%        OBS_CONGR (par(prefix(label l)E)(prefix(label l')E'))                %
%                  (sum(prefix(label l)(par E(prefix(label l')E')))           %
%                      (prefix(label l')(par(prefix(label l)E)E'))))          %
% --------------------------------------------------------------------------- %
let PAR_PREF_NO_SYNCR =
     save_thm
      (`PAR_PREF_NO_SYNCR`,
       GEN_ALL
       (DISCH "~(l = COMPL l')"
        (GEN_ALL
         (MATCH_MP STRONG_IMP_OBS_CONGR  
          (SPECL ["E: CCS"; "E': CCS"]
           (UNDISCH (SPECL ["l: Label"; "l': Label"]
                           STRONG_PAR_PREF_NO_SYNCR)))))));;
 
% --------------------------------------------------------------------------- %
% Prove PAR_PREF_SYNCR:                                                       %
%  |- !l l'.                                                                  %
%      (l = COMPL l') ==>                                                     %
%      (!E E'.                                                                %
%        OBS_CONGR (par(prefix(label l)E)(prefix(label l')E'))                %
%                  (sum                                                       %
%                   (sum(prefix(label l)(par E(prefix(label l')E')))          %
%                       (prefix(label l')(par(prefix(label l)E)E')))          %
%                   (prefix tau(par E E'))))                                  %
% --------------------------------------------------------------------------- %
let PAR_PREF_SYNCR =
     save_thm
      (`PAR_PREF_SYNCR`,
       GEN_ALL
       (DISCH "(l = COMPL l')"
        (GEN_ALL
         (MATCH_MP STRONG_IMP_OBS_CONGR  
          (SPECL ["E: CCS"; "E': CCS"]
           (UNDISCH (SPECL ["l: Label"; "l': Label"]
                           STRONG_PAR_PREF_SYNCR)))))));;

% --------------------------------------------------------------------------- %
% The expansion law PAR_LAW for observation congruence:                       %
% |- !f n f' m.                                                               %
%     (!i. i <= n ==> Is_Prefix(f i)) /\ (!j. j <= m ==> Is_Prefix(f' j)) ==> %
%    OBS_CONGR                                                                %
%    (par(SIGMA f n)(SIGMA f' m))                                             %
%     (sum                                                                    %
%      (sum                                                                   %
%       (SIGMA(\i. prefix(PREF_ACT(f i))(par(PREF_PROC(f i))(SIGMA f' m)))n)  %
%       (SIGMA(\j. prefix(PREF_ACT(f' j))(par(SIGMA f n)(PREF_PROC(f' j))))m))%
%      (ALL_SYNC f n f' m))                                                   %
% --------------------------------------------------------------------------- %
let PAR_LAW =
     save_thm
      (`PAR_LAW`,
       GENL ["f: num -> CCS"; "n: num"; "f': num -> CCS"; "m: num"] 
       (DISCH_ALL
        (MATCH_MP STRONG_IMP_OBS_CONGR 
         (UNDISCH
          (SPECL ["f: num -> CCS"; "n: num"; "f': num -> CCS"; "m: num"]
           STRONG_PAR_LAW)))));;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

