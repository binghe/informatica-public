% =========================================================================== %
% FILE          : basic_fun.ml                                                %
% DESCRIPTION   : Basic functions and conversions for rewriting with          % 
%                 the CCS laws for observation congruence                     %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Define OC_SYM such that, when given a theorem A |- OBS_CONGR t1 t2,         %
% returns the theorem A |- OBS_CONGR t2 t1.                                   %
% --------------------------------------------------------------------------- %
let OC_SYM thm = MATCH_MP OBS_CONGR_SYM thm;; 

% --------------------------------------------------------------------------- %
% Define OC_TRANS such that, when given the theorems thm1 and thm2, applies   %
% OBS_CONGR_TRANS on them, if possible.                                       % 
% --------------------------------------------------------------------------- %
let OC_TRANS thm1 thm2 =
   (rhs_tm thm1 = lhs_tm thm2) =>
    MATCH_MP OBS_CONGR_TRANS (CONJ thm1 thm2) |
   failwith `transitivity of observation congruence not applicable`;;

% --------------------------------------------------------------------------- %
% When applied to a term "t: CCS", the conversion OC_ALL_CONV returns the     %
% theorem: |- OBS_CONGR t t                                                   %
% --------------------------------------------------------------------------- %
let OC_ALL_CONV t = SPEC t OBS_CONGR_REFL;;

% --------------------------------------------------------------------------- %
% Define the function OC_THENC.                                               %
% --------------------------------------------------------------------------- %
ml_curried_infix `OC_THENC`;;

let (c1 OC_THENC c2): conv =
   \t.
    let thm1 = c1 t in
    let thm2 = c2 (rhs_tm thm1) in OC_TRANS thm1 thm2;;

% --------------------------------------------------------------------------- %
% Define the function OC_ORELSEC.                                             %
% --------------------------------------------------------------------------- %
ml_curried_infix `OC_ORELSEC`;;

let (c1 OC_ORELSEC c2): conv = \t. c1 t ? c2 t;;

% --------------------------------------------------------------------------- %
% Define the function OC_REPEATC.                                             %
% --------------------------------------------------------------------------- %
letrec OC_REPEATC (c: conv) t =
   ((c OC_THENC (OC_REPEATC c)) OC_ORELSEC OC_ALL_CONV) t;;

% --------------------------------------------------------------------------- %
% Convert a conversion for the application of the laws for OBS_CONGR to a     %
% tactic.                                                                     %
% --------------------------------------------------------------------------- %
let OC_LHS_CONV_TAC c :tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in 
   (op = "OBS_CONGR") =>
    let thm = c t1 in 
    let (t1',t') = args_thm thm in                            % t1' = t1 %
    (t' = t2) =>
     ([], \[]. OC_TRANS thm (SPEC t' OBS_CONGR_REFL)) |
     ([asl,"OBS_CONGR ^t' ^t2"], \[thm']. OC_TRANS thm thm') |
   failwith `the goal is not an OBS_CONGR relation`;;


let OC_RHS_CONV_TAC c :tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in 
   (op = "OBS_CONGR") =>
    let thm = c t2 in  
    let (t2',t'') = args_thm thm in                           % t2' = t2 %
    (t'' = t1) =>
     ([], \[]. OC_SYM thm) |
     ([asl,"OBS_CONGR ^t1 ^t''"], \[thm']. OC_TRANS thm' (OC_SYM thm)) |
   failwith `the goal is not an OBS_CONGR relation`;;


