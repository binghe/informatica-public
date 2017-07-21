% =========================================================================== %
% FILE          : rec_laws.ml                                                 %
% DESCRIPTION   : Basic laws of observation congruence for the recursion      %
%                 operator through strong equivalence                         %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `rec_laws`;;

% --------------------------------------------------------------------------- %
% The unfolding law:                                                          %
%   UNFOLDING: |- !X E. OBS_CONGR(rec X E)(CCS_Subst E(rec X E)X)             %
% --------------------------------------------------------------------------- %
let UNFOLDING =
     save_thm
      (`UNFOLDING`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR
        (SPECL ["X: string"; "E: CCS"] STRONG_UNFOLDING)));;

% --------------------------------------------------------------------------- %
% Prove the theorem PREF_REC_EQUIV:                                           %
%  |- !u s v.                                                                 % 
%      OBS_CONGR                                                              % 
%      (prefix u(rec s(prefix v(prefix u(var s)))))                           % 
%      (rec s(prefix u(prefix v(var s))))                                     % 
% --------------------------------------------------------------------------- %
let PREF_REC_EQUIV = 
     save_thm 
      (`PREF_REC_EQUIV`, 
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_CONGR
        (SPECL ["u: Action"; "s: string"; "v: Action"] 
               STRONG_PREF_REC_EQUIV)));;
 
% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

