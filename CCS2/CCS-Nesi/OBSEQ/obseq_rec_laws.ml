% =========================================================================== %
% FILE          : obseq_rec_laws.ml                                           %
% DESCRIPTION   : Basic laws of observation equivalence for the recursion     %
%                 operator through strong equivalence                         %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `obseq_rec_laws`;;

% --------------------------------------------------------------------------- %
% The unfolding law:                                                          %
%   OBS_UNFOLDING: |- !X E. OBS_EQUIV(rec X E)(CCS_Subst E(rec X E)X)         %
% --------------------------------------------------------------------------- %
let OBS_UNFOLDING =
     save_thm
      (`OBS_UNFOLDING`,
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["X: string"; "E: CCS"] STRONG_UNFOLDING)));;

% --------------------------------------------------------------------------- %
% Prove the theorem OBS_PREF_REC_EQUIV:                                       %
%  |- !u s v.                                                                 % 
%      OBS_EQUIV                                                              % 
%      (prefix u(rec s(prefix v(prefix u(var s)))))                           % 
%      (rec s(prefix u(prefix v(var s))))                                     % 
% --------------------------------------------------------------------------- %
let OBS_PREF_REC_EQUIV = 
     save_thm 
      (`OBS_PREF_REC_EQUIV`, 
       GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
        (SPECL ["u: Action"; "s: string"; "v: Action"] 
               STRONG_PREF_REC_EQUIV)));;
 
% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

