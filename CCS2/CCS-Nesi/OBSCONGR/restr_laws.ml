% =========================================================================== %
% FILE          : restr_laws.ml                                               %
% DESCRIPTION   : Basic laws of observation congruence for the restriction    %
%                 operator through strong equivalence                         % 
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 26 June 1992                                                %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `restr_laws`;;        

% --------------------------------------------------------------------------- %
% Prove RESTR_NIL: |- !L. OBS_CONGR(restr nil L)nil                           %
% --------------------------------------------------------------------------- %
let RESTR_NIL =
     save_thm
      (`RESTR_NIL`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_CONGR 
        (SPEC "L: (Label)set" STRONG_RESTR_NIL)));; 

% --------------------------------------------------------------------------- %
% Prove RESTR_SUM:                                                            %
%  |- !E E' L. OBS_CONGR(restr(sum E E')L)(sum(restr E L)(restr E' L))        %
% --------------------------------------------------------------------------- %
let RESTR_SUM =
     save_thm
      (`RESTR_SUM`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR
        (SPECL ["E: CCS"; "E': CCS"; "L: (Label)set"] STRONG_RESTR_SUM)));;

% --------------------------------------------------------------------------- %
% Prove RESTR_PREFIX_TAU:                                                     %
%  |- !E L. OBS_CONGR(restr(prefix tau E)L)(prefix tau(restr E L))            %
% --------------------------------------------------------------------------- %
let RESTR_PREFIX_TAU =
     save_thm
      (`RESTR_PREFIX_TAU`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR
        (SPECL ["E: CCS"; "L: (Label)set"] STRONG_RESTR_PREFIX_TAU)));; 
  
% --------------------------------------------------------------------------- %
% Prove RESTR_PR_LAB_NIL:                                                     %
%  |- !l L.                                                                   %
%      l IN L \/ (COMPL l) IN L ==>                                           %
%      (!E. OBS_CONGR(restr(prefix(label l)E)L)nil)                           %
% --------------------------------------------------------------------------- %
let RESTR_PR_LAB_NIL =
     save_thm
      (`RESTR_PR_LAB_NIL`,
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
                  STRONG_IMP_OBS_CONGR))))));;
 
% --------------------------------------------------------------------------- %
% Prove RESTR_PREFIX_LABEL:                                                   %
%  |- !l L.                                                                   %
%      ~l IN L /\ ~(COMPL l) IN L ==>                                         %
%      (!E. OBS_CONGR(restr(prefix(label l)E)L)(prefix(label l)(restr E L)))  %
% --------------------------------------------------------------------------- %
let RESTR_PREFIX_LABEL =
     save_thm
      (`RESTR_PREFIX_LABEL`,
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
                   "prefix(label l)(restr E L)"] STRONG_IMP_OBS_CONGR))))));;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;    
 
