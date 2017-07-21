% =========================================================================== %
% FILE          : obseq_par_laws.ml                                           %
% DESCRIPTION   : Basic laws of observation equivalence for the parallel      %
%                 operator derived through strong equivalence                 %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 29 February 1992                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `obseq_par_laws`;;

% --------------------------------------------------------------------------- %
% Prove OBS_PAR_IDENT_R: |- !E. OBS_EQUIV(par E nil)E                         %
% --------------------------------------------------------------------------- %
let OBS_PAR_IDENT_R =
     save_thm
      (`OBS_PAR_IDENT_R`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPEC "E: CCS" STRONG_PAR_IDENT_R)));;

% --------------------------------------------------------------------------- %
% Prove OBS_PAR_IDENT_L: |- !E. OBS_EQUIV(par nil E)E                         %
% --------------------------------------------------------------------------- %
let OBS_PAR_IDENT_L =
     save_thm
      (`OBS_PAR_IDENT_L`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPEC "E: CCS" STRONG_PAR_IDENT_L)));;

% --------------------------------------------------------------------------- %
% Prove OBS_PAR_COMM: |- !E E'. OBS_EQUIV(par E E')(par E' E)                 %
% --------------------------------------------------------------------------- %
let OBS_PAR_COMM =
     save_thm
      (`OBS_PAR_COMM`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["E: CCS"; "E': CCS"] STRONG_PAR_COMM)));;

% --------------------------------------------------------------------------- %
% Prove OBS_PAR_ASSOC:                                                        %
%  |- !E E' E''. OBS_EQUIV(par(par E E')E'')(par E(par E' E''))               %
% --------------------------------------------------------------------------- %
let OBS_PAR_ASSOC =
     save_thm
      (`OBS_PAR_ASSOC`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["E: CCS"; "E': CCS"; "E'': CCS"] STRONG_PAR_ASSOC)));;

% --------------------------------------------------------------------------- %
% Prove OBS_PAR_PREF_TAU:                                                     %
%  |- !u E E'.                                                                %
%      OBS_EQUIV (par(prefix u E)(prefix tau E'))                             %
%                (sum(prefix u(par E(prefix tau E')))                         %
%                    (prefix tau(par(prefix u E)E')))                         %
% --------------------------------------------------------------------------- %
let OBS_PAR_PREF_TAU =
     save_thm
      (`OBS_PAR_PREF_TAU`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["u: Action"; "E: CCS"; "E': CCS"] STRONG_PAR_PREF_TAU)));;

% --------------------------------------------------------------------------- %
% Prove OBS_PAR_TAU_PREF:                                                     %
%  |- !E u E'.                                                                %
%      OBS_EQUIV (par(prefix tau E)(prefix u E'))                             %
%                (sum(prefix tau(par E(prefix u E')))                         %
%                    (prefix u(par(prefix tau E)E')))                         %
% --------------------------------------------------------------------------- %
let OBS_PAR_TAU_PREF =
     save_thm
      (`OBS_PAR_TAU_PREF`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["E: CCS"; "u: Action"; "E': CCS"] STRONG_PAR_TAU_PREF)));;

% --------------------------------------------------------------------------- %
% Prove OBS_PAR_TAU_TAU:                                                      %
%  |- !E E'.                                                                  %
%      OBS_EQUIV (par(prefix tau E)(prefix tau E'))                           %
%                (sum(prefix tau(par E(prefix tau E')))                       %
%                    (prefix tau(par(prefix tau E)E')))                       %
% --------------------------------------------------------------------------- %
let OBS_PAR_TAU_TAU = 
     save_thm(`OBS_PAR_TAU_TAU`, SPEC "tau" OBS_PAR_PREF_TAU);;

% --------------------------------------------------------------------------- %
% Prove OBS_PAR_PREF_NO_SYNCR:                                                %
%  |- !l l'.                                                                  %
%      ~(l = COMPL l') ==>                                                    %
%      (!E E'.                                                                %
%        OBS_EQUIV (par(prefix(label l)E)(prefix(label l')E'))                %
%                  (sum(prefix(label l)(par E(prefix(label l')E')))           %
%                      (prefix(label l')(par(prefix(label l)E)E'))))          %
% --------------------------------------------------------------------------- %
let OBS_PAR_PREF_NO_SYNCR =
     save_thm
      (`OBS_PAR_PREF_NO_SYNCR`,
       GEN_ALL
       (DISCH "~(l = COMPL l')"
        (GEN_ALL
         (MATCH_MP STRONG_IMP_OBS_EQUIV
          (SPECL ["E: CCS"; "E': CCS"]
           (UNDISCH (SPECL ["l: Label"; "l': Label"]
                           STRONG_PAR_PREF_NO_SYNCR)))))));;

% --------------------------------------------------------------------------- %
% Prove OBS_PAR_PREF_SYNCR:                                                   %
%  |- !l l'.                                                                  %
%      (l = COMPL l') ==>                                                     %
%      (!E E'.                                                                %
%        OBS_EQUIV (par(prefix(label l)E)(prefix(label l')E'))                %
%                  (sum                                                       %
%                   (sum(prefix(label l)(par E(prefix(label l')E')))          %
%                       (prefix(label l')(par(prefix(label l)E)E')))          %
%                   (prefix tau(par E E'))))                                  %
% --------------------------------------------------------------------------- %
let OBS_PAR_PREF_SYNCR =
     save_thm
      (`OBS_PAR_PREF_SYNCR`,
       GEN_ALL
       (DISCH "(l = COMPL l')"
        (GEN_ALL
         (MATCH_MP STRONG_IMP_OBS_EQUIV
          (SPECL ["E: CCS"; "E': CCS"]
           (UNDISCH (SPECL ["l: Label"; "l': Label"]
                           STRONG_PAR_PREF_SYNCR)))))));;

% --------------------------------------------------------------------------- %
% The expansion law OBS_PAR_LAW for observation equivalence:                  %
% |- !f n f' m.                                                               %
%     (!i. i <= n ==> Is_Prefix(f i)) /\ (!j. j <= m ==> Is_Prefix(f' j)) ==> %
%     OBS_EQUIV                                                               %
%     (par(SIGMA f n)(SIGMA f' m))                                            %
%     (sum                                                                    %
%      (sum                                                                   %
%       (SIGMA(\i. prefix(PREF_ACT(f i))(par(PREF_PROC(f i))(SIGMA f' m)))n)  %
%       (SIGMA(\j. prefix(PREF_ACT(f' j))(par(SIGMA f n)(PREF_PROC(f' j))))m))%
%      (ALL_SYNC f n f' m))                                                   %
% --------------------------------------------------------------------------- %
let OBS_PAR_LAW =
     save_thm
      (`OBS_PAR_LAW`,
       GENL ["f: num -> CCS"; "n: num"; "f': num -> CCS"; "m: num"]  
       (DISCH_ALL 
        (MATCH_MP STRONG_IMP_OBS_EQUIV  
         (UNDISCH 
          (SPECL ["f: num -> CCS"; "n: num"; "f': num -> CCS"; "m: num"]
           STRONG_PAR_LAW)))));;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

