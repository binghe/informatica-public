% =========================================================================== %
% FILE          : basic_fun.ml                                                %
% DESCRIPTION   : Basic functions and conversions for rewriting with          %
%                 the CCS laws for strong equivalence                         %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 2 December 1991                                             %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Define S_SYM such that, when given a theorem A |- STRONG_EQUIV t1 t2,       % 
% returns the theorem A |- STRONG_EQUIV t2 t1.                                %
% --------------------------------------------------------------------------- %
let S_SYM thm = MATCH_MP STRONG_EQUIV_SYM thm;;  

% --------------------------------------------------------------------------- %
% Define S_TRANS such that, when given the theorems thm1 and thm2, applies    %
% STRONG_EQUIV_TRANS on them, if possible.                                    %
% --------------------------------------------------------------------------- %
let S_TRANS thm1 thm2 = 
   (rhs_tm thm1 = lhs_tm thm2) => 
    MATCH_MP STRONG_EQUIV_TRANS (CONJ thm1 thm2) | 
   failwith `transitivity of strong equivalence not applicable`;; 

% --------------------------------------------------------------------------- %
% When applied to a term "t: CCS", the conversion S_ALL_CONV returns the      % 
% theorem: |- STRONG_EQUIV t t                                                %
% --------------------------------------------------------------------------- % 
let S_ALL_CONV t = SPEC t STRONG_EQUIV_REFL;;

% --------------------------------------------------------------------------- %
% Define the function S_THENC.                                                %
% --------------------------------------------------------------------------- %
ml_curried_infix `S_THENC`;;

let (c1 S_THENC c2): conv =
   \t.
    let thm1 = c1 t in 
    let thm2 = c2 (rhs_tm thm1) in S_TRANS thm1 thm2;;

% --------------------------------------------------------------------------- %
% Define the function S_ORELSEC.                                              %
% --------------------------------------------------------------------------- %
ml_curried_infix `S_ORELSEC`;;

let (c1 S_ORELSEC c2): conv = \t. c1 t ? c2 t;;

% --------------------------------------------------------------------------- %
% Define the function S_REPEATC.                                              %
% --------------------------------------------------------------------------- %
letrec S_REPEATC (c: conv) t =
   ((c S_THENC (S_REPEATC c)) S_ORELSEC S_ALL_CONV) t;;

% --------------------------------------------------------------------------- %
% Convert a conversion for the application of the laws for STRONG_EQUIV to a  %
% tactic.                                                                     %
% --------------------------------------------------------------------------- %
let S_LHS_CONV_TAC c :tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in 
   (op = "STRONG_EQUIV") =>
    let thm = c t1 in 
    let (t1',t') = args_thm thm in                     % t1' = t1 %
    (t' = t2) =>
     ([], \[]. S_TRANS thm (SPEC t' STRONG_EQUIV_REFL)) |
     ([asl,"STRONG_EQUIV ^t' ^t2"], \[thm']. S_TRANS thm thm') |
   failwith `the goal is not a STRONG_EQUIV relation`;;

let S_RHS_CONV_TAC c :tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in
   (op = "STRONG_EQUIV") =>
    let thm = c t2 in 
    let (t2',t'') = args_thm thm in        % t2' = t2 %
    (t'' = t1) =>
     ([], \[]. S_SYM thm) |
     ([asl,"STRONG_EQUIV ^t1 ^t''"], \[thm']. S_TRANS thm' (S_SYM thm)) |
   failwith `the goal is not a STRONG_EQUIV relation`;;

 
