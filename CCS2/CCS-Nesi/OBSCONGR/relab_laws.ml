% =========================================================================== %
% FILE          : relab_laws.ml                                               %
% DESCRIPTION   : Basic laws of observation congruence for the relabelling    %
%                 operator through strong equivalence                         %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 26 June 1992                                                %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `relab_laws`;;

% --------------------------------------------------------------------------- %
% Prove RELAB_NIL: |- !rf. OBS_CONGR(relab nil rf)nil                         %
% --------------------------------------------------------------------------- %
let RELAB_NIL =
     save_thm
      (`RELAB_NIL`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_CONGR 
        (SPEC "rf: Relabelling" STRONG_RELAB_NIL)));; 

% --------------------------------------------------------------------------- %
% Prove RELAB_SUM:                                                            %
%  |- !E E' rf. OBS_CONGR(relab(sum E E')rf)(sum(relab E rf)(relab E' rf))    %
% --------------------------------------------------------------------------- %
let RELAB_SUM =
     save_thm
      (`RELAB_SUM`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR
        (SPECL ["E: CCS"; "E': CCS"; "rf: Relabelling"] STRONG_RELAB_SUM)));; 

% --------------------------------------------------------------------------- %
% Prove RELAB_PREFIX:                                                         %
%  |- !u E labl.                                                              %
%      OBS_CONGR(relab(prefix u E)(RELAB labl))                               %
%               (prefix(relabel(Apply_Relab labl)u)(relab E(RELAB labl)))     %
% --------------------------------------------------------------------------- %
let RELAB_PREFIX =
     save_thm
      (`RELAB_PREFIX`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR
        (SPECL ["u: Action"; "E: CCS"; "labl: (Label#Label)list"] 
               STRONG_RELAB_PREFIX)));;
  
% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

