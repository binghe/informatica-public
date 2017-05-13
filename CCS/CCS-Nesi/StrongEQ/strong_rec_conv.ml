% =========================================================================== %
% FILE          : strong_rec_conv.ml                                          %
% DESCRIPTION   : Conversions for the recursion operator and strong equivalence%
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : June 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Conversion for applying the unfolding law for the recursion operator.       %
% --------------------------------------------------------------------------- %
let STRONG_REC_UNF_CONV rtm =
   is_rec rtm =>
    let (X,E) = args_rec rtm in 
     REWRITE_RULE [CCS_Subst] (SPECL [X; E] STRONG_UNFOLDING) |
    failwith `STRONG_REC_UNF_CONV: no recursive terms`;;

% --------------------------------------------------------------------------- %
% Conversion for folding a recursive term.                                    %
% --------------------------------------------------------------------------- %
%let STRONG_REC_FOLD_CONV rtm =
   is_rec rtm =>
    let (X,E) = args_rec rtm in 
     S_SYM (REWRITE_RULE [CCS_Subst] (SPECL [X; E] STRONG_UNFOLDING)) |
    failwith `STRONG_REC_FOLD_CONV: no recursive terms`;;
%

