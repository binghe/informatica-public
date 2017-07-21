% =========================================================================== %
% FILE          : obseq_restr_laws.ml                                         %
% DESCRIPTION   : Basic laws of observation equivalence for the restriction   %
%                 operator derived through strong equivalence                 % 
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 29 February 1992                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `obseq_restr_laws`;;

% --------------------------------------------------------------------------- %
% Prove OBS_RESTR_NIL: |- !L. OBS_EQUIV(restr nil L)nil                       %
% --------------------------------------------------------------------------- %
let OBS_RESTR_NIL =
     save_thm
      (`OBS_RESTR_NIL`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["L: (Label)set"] STRONG_RESTR_NIL)));;

% --------------------------------------------------------------------------- %
% Prove OBS_RESTR_SUM:                                                        %
%   |- !E E' L. OBS_EQUIV(restr(sum E E')L)(sum(restr E L)(restr E' L))       %
% --------------------------------------------------------------------------- %
let OBS_RESTR_SUM =
     save_thm
      (`OBS_RESTR_SUM`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["E: CCS"; "E': CCS"; "L: (Label)set"] STRONG_RESTR_SUM)));; 

% --------------------------------------------------------------------------- %
% Prove OBS_RESTR_PREFIX_TAU:                                                 %
%  |- !E L. OBS_EQUIV(restr(prefix tau E)L)(prefix tau(restr E L))            %
% --------------------------------------------------------------------------- %
let OBS_RESTR_PREFIX_TAU =
     save_thm
      (`OBS_RESTR_PREFIX_TAU`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["E: CCS"; "L: (Label)set"] STRONG_RESTR_PREFIX_TAU)));;

% --------------------------------------------------------------------------- %
% Prove OBS_RESTR_PR_LAB_NIL:                                                 %
%  |- !l L. l IN L \/ (COMPL l) IN L ==>                                      %
%           (!E. OBS_EQUIV(restr(prefix(label l)E)L)nil)                      %
% --------------------------------------------------------------------------- %
let OBS_RESTR_PR_LAB_NIL =
     save_thm
      (`OBS_RESTR_PR_LAB_NIL`,
       GEN_ALL
       (DISCH "l IN L \/ (COMPL l) IN L"
        (GEN "E: CCS"
         (UNDISCH
          (IMP_TRANS
           (DISCH "l IN L \/ (COMPL l) IN L"
            (SPEC "E: CCS"
             (UNDISCH
              (SPECL ["l: Label"; "L: (Label)set"] STRONG_RESTR_PR_LAB_NIL)))) 
           (SPECL ["restr(prefix(label l)E) L"; "nil"]
                  STRONG_IMP_OBS_EQUIV))))));;

% --------------------------------------------------------------------------- %
% Prove OBS_RESTR_PREFIX_LABEL:                                               %
%  |- !l L.                                                                   %
%      ~l IN L /\ ~(COMPL l) IN L ==>                                         %
%      (!E. OBS_EQUIV(restr(prefix(label l)E)L)(prefix(label l)(restr E L)))  %
% --------------------------------------------------------------------------- %
let OBS_RESTR_PREFIX_LABEL =
     save_thm
      (`OBS_RESTR_PREFIX_LABEL`,
       GEN_ALL
       (DISCH "~l IN L /\ ~(COMPL l) IN L"
        (GEN "E: CCS"
         (UNDISCH
          (IMP_TRANS
           (DISCH "~l IN L /\ ~(COMPL l) IN L"
            (SPEC "E: CCS"
             (UNDISCH
              (SPECL ["l: Label"; "L: (Label)set"] STRONG_RESTR_PREFIX_LABEL))))
           (SPECL ["restr(prefix(label l)E) L";
                   "prefix(label l)(restr E L)"] STRONG_IMP_OBS_EQUIV))))));; 

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

