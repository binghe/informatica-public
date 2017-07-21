% =========================================================================== %
% FILE          : basic_fun.ml                                                %
% DESCRIPTION   : Basic functions and conversions for rewriting               %
%                 with the laws for observational equivalence                 %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 2 December 1991                                             %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Define OE_SYM such that, when given a theorem A |- OBS_EQUIV t1 t2,         %
% returns the theorem A |- OBS_EQUIV t2 t1.                                   %
% --------------------------------------------------------------------------- %
let OE_SYM thm = MATCH_MP OBS_EQUIV_SYM thm;; 

% --------------------------------------------------------------------------- %
% Define OE_TRANS such that, when given the theorems thm1 and thm2, applies   %
% OBS_EQUIV_TRANS on them, if possible.                                       %
% --------------------------------------------------------------------------- %
let OE_TRANS thm1 thm2 =
   (rhs_tm thm1 = lhs_tm thm2) =>
    MATCH_MP OBS_EQUIV_TRANS (CONJ thm1 thm2) |
   failwith `transitivity of observation equivalence not applicable`;;

% --------------------------------------------------------------------------- %
% When applied to a term "t: CCS", the conversion OE_ALL_CONV returns the     %
% theorem: |- OBS_EQUIV t t                                                   %
% --------------------------------------------------------------------------- %
let OE_ALL_CONV t = SPEC t OBS_EQUIV_REFL;;

% --------------------------------------------------------------------------- %
% Define the function OE_THENC.                                               %
% --------------------------------------------------------------------------- %
ml_curried_infix `OE_THENC`;;

let (c1 OE_THENC c2): conv =
   \t.
    let thm1 = c1 t in 
    let thm2 = c2 (rhs_tm thm1) in OE_TRANS thm1 thm2;;  

% --------------------------------------------------------------------------- %
% Define the function OE_ORELSEC.                                             %
% --------------------------------------------------------------------------- %
ml_curried_infix `OE_ORELSEC`;;

let (c1 OE_ORELSEC c2): conv = \t. c1 t ? c2 t;;

% --------------------------------------------------------------------------- %
% Define the function OE_REPEATC.                                             %
% --------------------------------------------------------------------------- %
letrec OE_REPEATC (c: conv) t =
   ((c OE_THENC (OE_REPEATC c)) OE_ORELSEC OE_ALL_CONV) t;;

% --------------------------------------------------------------------------- %
% Convert a conversion for the application of the laws for STRONG_EQUIV to a  %
% tactic applying the laws for OBS_EQUIV (i.e. c is a conversion for strong   %
% equivalence).                                                               %
% --------------------------------------------------------------------------- %
let OE_LHS_CONV_TAC c :tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in 
   (op = "OBS_EQUIV") =>
    let thm = MATCH_MP STRONG_IMP_OBS_EQUIV ((S_DEPTH_CONV c) t1) in 
    let (t1',t') = args_thm thm in                               % t1' = t1 %
    (t' = t2) =>
     ([], \[]. OE_TRANS thm (SPEC t' OBS_EQUIV_REFL)) |
     ([asl,"OBS_EQUIV ^t' ^t2"], \[thm']. OE_TRANS thm thm') |
   failwith `the goal is not an OBS_EQUIV relation`;;

let OE_RHS_CONV_TAC c :tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in 
   (op = "OBS_EQUIV") =>
    let thm = MATCH_MP STRONG_IMP_OBS_EQUIV ((S_DEPTH_CONV c) t2) in 
    let (t2',t') = args_thm thm in                               % t2' = t2 %
    (t' = t1) =>
     ([], \[]. OE_SYM thm) |
     ([asl,"OBS_EQUIV ^t1 ^t'"], \[thm']. OE_TRANS thm' (OE_SYM thm)) |
   failwith `the goal is not an OBS_EQUIV relation`;;


