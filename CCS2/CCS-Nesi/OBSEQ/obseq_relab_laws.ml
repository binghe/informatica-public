% =========================================================================== %
% FILE          : obseq_relab_laws.ml                                         %
% DESCRIPTION   : Basic laws of observation equivalence for the relabelling   %
%                 operator derived through strong equivalence                 %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 29 February 1992                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `obseq_relab_laws`;;

% --------------------------------------------------------------------------- %
% Prove OBS_RELAB_NIL: |- !rf. OBS_EQUIV(relab nil rf)nil                     %
% --------------------------------------------------------------------------- %
let OBS_RELAB_NIL =
     save_thm
      (`OBS_RELAB_NIL`,
       GEN_ALL 
       (MATCH_MP STRONG_IMP_OBS_EQUIV 
        (SPEC "rf: Relabelling" STRONG_RELAB_NIL)));;

% --------------------------------------------------------------------------- %
% Prove OBS_RELAB_SUM:                                                        %
%   |- !E E' rf. OBS_EQUIV(relab(sum E E')rf)(sum(relab E rf)(relab E' rf))   %
% --------------------------------------------------------------------------- %
let OBS_RELAB_SUM =
     save_thm
      (`OBS_RELAB_SUM`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV 
        (SPECL ["E: CCS"; "E': CCS"; "rf: Relabelling"] STRONG_RELAB_SUM)));;

% --------------------------------------------------------------------------- %
% Prove OBS_RELAB_PREFIX:                                                     %
%   |- !u E labl.                                                             %
%       OBS_EQUIV (relab(prefix u E)(RELAB labl))                             %
%                 (prefix(relabel(Apply_Relab labl)u)(relab E(RELAB labl)))   %
% --------------------------------------------------------------------------- %
let OBS_RELAB_PREFIX =
     save_thm
      (`OBS_RELAB_PREFIX`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["u: Action"; "E: CCS"; "labl: (Label#Label)list"]
               STRONG_RELAB_PREFIX)));;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

