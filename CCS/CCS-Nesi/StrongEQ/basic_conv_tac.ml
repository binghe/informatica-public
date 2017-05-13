% =========================================================================== %
% FILE          : basic_conv_tac.ml                                           %
% DESCRIPTION   : Basic conversions and tactics for applying the laws for     %
%                 strong equivalence                                          %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Define the function S_SUB_CONV.                                             %
% --------------------------------------------------------------------------- %
let S_SUB_CONV (c: conv) tm =
   is_prefix tm =>
    let u,P = args_prefix tm in
    let thm = c P in
     SPEC u (MATCH_MP STRONG_EQUIV_SUBST_PREFIX thm) |
   is_sum tm =>
    let t1,t2 = args_sum tm in
    let thm1 = c t1
    and thm2 = c t2 in
     MATCH_MP STRONG_EQUIV_PRESD_BY_SUM (CONJ thm1 thm2) | 
   is_par tm =>
    let t1,t2 = args_par tm in
    let thm1 = c t1
    and thm2 = c t2 in
     MATCH_MP STRONG_EQUIV_PRESD_BY_PAR (CONJ thm1 thm2) |
   is_restr tm =>
    let P,L = args_restr tm in
    let thm = c P in
     SPEC L (MATCH_MP STRONG_EQUIV_SUBST_RESTR thm) |
   is_relab tm =>
    let P,rf = args_relab tm in
    let thm = c P in
     SPEC rf (MATCH_MP STRONG_EQUIV_SUBST_RELAB thm) |
   S_ALL_CONV tm;; 

% --------------------------------------------------------------------------- %
% Define the function S_DEPTH_CONV.                                           %
% --------------------------------------------------------------------------- %
letrec S_DEPTH_CONV (c: conv) t =
   (S_SUB_CONV (S_DEPTH_CONV c) S_THENC (S_REPEATC c)) t;;     

% --------------------------------------------------------------------------- %
% Define the function S_TOP_DEPTH_CONV.                                       %
% --------------------------------------------------------------------------- %
letrec S_TOP_DEPTH_CONV (c: conv) t =
   ((S_REPEATC c) S_THENC
    (S_SUB_CONV (S_TOP_DEPTH_CONV c)) S_THENC
    ((c S_THENC (S_TOP_DEPTH_CONV c)) S_ORELSEC S_ALL_CONV))
   t;;

% --------------------------------------------------------------------------- %
% Define the function S_SUBST for substitution in STRONG_EQUIV terms.         %
% --------------------------------------------------------------------------- %
letrec S_SUBST thm tm = 
   let (ti,ti') = args_thm thm in
   (tm = ti) => thm |
   is_prefix tm =>
    let u,t = args_prefix tm in
    let thm1 = S_SUBST thm t in
     SPEC u (MATCH_MP STRONG_EQUIV_SUBST_PREFIX thm1) |
   is_sum tm =>
    let t1,t2 = args_sum tm in
    let thm1 = S_SUBST thm t1
    and thm2 = S_SUBST thm t2 in
     MATCH_MP STRONG_EQUIV_PRESD_BY_SUM (CONJ thm1 thm2) | 
   is_par tm =>
    let t1,t2 = args_par tm in
    let thm1 = S_SUBST thm t1
    and thm2 = S_SUBST thm t2 in
     MATCH_MP STRONG_EQUIV_PRESD_BY_PAR (CONJ thm1 thm2) | 
   is_restr tm =>
    let t,L = args_restr tm in
    let thm1 = S_SUBST thm t in
     SPEC L (MATCH_MP STRONG_EQUIV_SUBST_RESTR thm1) |
   is_relab tm =>
    let t,rf = args_relab tm in
    let thm1 = S_SUBST thm t in
     SPEC rf (MATCH_MP STRONG_EQUIV_SUBST_RELAB thm1) |
   S_ALL_CONV tm;;

% --------------------------------------------------------------------------- %
% Define the tactic S_LHS_SUBST1_TAC: thm_tactic which substitutes a theorem  %
% in the left-hand side of a strong equivalence.                              %
% --------------------------------------------------------------------------- %
let S_LHS_SUBST1_TAC thm : tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in
   (op = "STRONG_EQUIV") =>  
    let thm' = S_SUBST thm t1 in  
    let (t1',t') = args_thm thm' in                      % t1' = t1 %
    (t' = t2) =>
     ([], \[]. S_TRANS thm' (SPEC t' STRONG_EQUIV_REFL)) |
     ([asl,"STRONG_EQUIV ^t' ^t2"], \[thm'']. S_TRANS thm' thm'') |
   failwith `the goal is not a STRONG_EQUIV relation`;;

% --------------------------------------------------------------------------- %
% The tactic S_LHS_SUBST_TAC substitutes a list of theorems in the left-hand  %
% side of a strong equivalence.                                               %
% --------------------------------------------------------------------------- %
let S_LHS_SUBST_TAC thmlist = EVERY (map S_LHS_SUBST1_TAC thmlist);;

% --------------------------------------------------------------------------- %
% The tactic S_RHS_SUBST1_TAC substitutes a theorem in the right-hand side of %
% a strong equivalence.                                                       %
% --------------------------------------------------------------------------- %
let S_RHS_SUBST1_TAC thm =
    REPEAT GEN_TAC THEN RULE_TAC STRONG_EQUIV_SYM THEN
    S_LHS_SUBST1_TAC thm THEN RULE_TAC STRONG_EQUIV_SYM;;

% --------------------------------------------------------------------------- %
% The tactic S_RHS_SUBST_TAC substitutes a list of theorems in the right-hand %
% side of a strong equivalence.                                               %
% --------------------------------------------------------------------------- %
let S_RHS_SUBST_TAC thmlist = 
    REPEAT GEN_TAC THEN RULE_TAC STRONG_EQUIV_SYM THEN
    S_LHS_SUBST_TAC thmlist THEN RULE_TAC STRONG_EQUIV_SYM;;

% --------------------------------------------------------------------------- %
% The tactic S_SUBST1_TAC (S_SUBST_TAC) substitutes a (list of) theorem(s) in %
% both sides of a strong equivalence.                                         %
% --------------------------------------------------------------------------- %
let S_SUBST1_TAC = \thm. S_LHS_SUBST1_TAC thm THEN S_RHS_SUBST1_TAC thm;;

let S_SUBST_TAC = 
    \thmlist. S_LHS_SUBST_TAC thmlist THEN S_RHS_SUBST_TAC thmlist;; 

