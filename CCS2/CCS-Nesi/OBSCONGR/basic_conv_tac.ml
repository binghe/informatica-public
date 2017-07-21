% =========================================================================== %
% FILE          : basic_conv_tac.ml                                           %
% DESCRIPTION   : Basic conversions and tactics for applying the laws for     % 
%                 observation congruence                                      %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Define the function OC_SUB_CONV.                                            %
% --------------------------------------------------------------------------- %
let OC_SUB_CONV (c: conv) tm =
   is_prefix tm =>
    let u,P = args_prefix tm in
    let thm = c P in
     SPEC u (MATCH_MP SUBST_PREFIX thm) |
   is_sum tm =>
    let t1,t2 = args_sum tm in
    let thm1 = c t1
    and thm2 = c t2 in
     MATCH_MP OBS_CONGR_PRESD_BY_SUM (CONJ thm1 thm2) |
   is_par tm =>
    let t1,t2 = args_par tm in
    let thm1 = c t1
    and thm2 = c t2 in
     MATCH_MP OBS_CONGR_PRESD_BY_PAR (CONJ thm1 thm2) |
   is_restr tm =>
    let P,L = args_restr tm in
    let thm = c P in
     SPEC L (MATCH_MP SUBST_RESTR thm) |
   is_relab tm =>
    let P,rf = args_relab tm in
    let thm = c P in
     SPEC rf (MATCH_MP SUBST_RELAB thm) |
   OC_ALL_CONV tm;;

% --------------------------------------------------------------------------- %
% Define the function OC_DEPTH_CONV.                                          %
% --------------------------------------------------------------------------- %
letrec OC_DEPTH_CONV (c: conv) t =
   (OC_SUB_CONV (OC_DEPTH_CONV c) OC_THENC (OC_REPEATC c)) t;;

% --------------------------------------------------------------------------- %
% Define the function OC_TOP_DEPTH_CONV.                                      %
% --------------------------------------------------------------------------- %
letrec OC_TOP_DEPTH_CONV (c: conv) t =
   ((OC_REPEATC c) OC_THENC
    (OC_SUB_CONV (OC_TOP_DEPTH_CONV c)) OC_THENC
    ((c OC_THENC (OC_TOP_DEPTH_CONV c)) OC_ORELSEC OC_ALL_CONV))
   t;;

% --------------------------------------------------------------------------- %
% Define the function OC_SUBST for substitution in OBS_CONGR terms.           %
% --------------------------------------------------------------------------- %
letrec OC_SUBST thm tm =
   let (ti,ti') = args_thm thm in 
   (tm = ti) => thm |
   is_prefix tm =>
    let u,t = args_prefix tm in
    let thm1 = OC_SUBST thm t in
     SPEC u (MATCH_MP SUBST_PREFIX thm1) |
   is_sum tm =>
    let t1,t2 = args_sum tm in
    let thm1 = OC_SUBST thm t1
    and thm2 = OC_SUBST thm t2 in 
     MATCH_MP OBS_CONGR_PRESD_BY_SUM (CONJ thm1 thm2) | 
   is_par tm =>
    let t1,t2 = args_par tm in
    let thm1 = OC_SUBST thm t1
    and thm2 = OC_SUBST thm t2 in
     MATCH_MP OBS_CONGR_PRESD_BY_PAR (CONJ thm1 thm2) |
   is_restr tm =>
    let t,L = args_restr tm in
    let thm1 = OC_SUBST thm t in
     SPEC L (MATCH_MP SUBST_RESTR thm1) |
   is_relab tm =>
    let t,rf = args_relab tm in
    let thm1 = OC_SUBST thm t in
     SPEC rf (MATCH_MP SUBST_RELAB thm1) |
   OC_ALL_CONV tm;;

% --------------------------------------------------------------------------- %
% Define the tactic OC_LHS_SUBST1_TAC: thm_tactic which substitutes a theorem %
% in the left-hand side of an observation congruence.                         %
% --------------------------------------------------------------------------- %
let OC_LHS_SUBST1_TAC thm : tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in 
   (op = "OBS_CONGR") =>
    let thm' = OC_SUBST thm t1 in 
    let (t1',t') = args_thm thm' in                              % t1' = t1 %
    (t' = t2) =>
     ([], \[]. OC_TRANS thm' (SPEC t' OBS_CONGR_REFL)) |
     ([asl,"OBS_CONGR ^t' ^t2"], \[thm'']. OC_TRANS thm' thm'') |
   failwith `the goal is not an OBS_CONGR relation`;;

% --------------------------------------------------------------------------- %
% The tactic OC_LHS_SUBST_TAC substitutes a list of theorems in the left-hand %
% side of an observation congruence.                                          %
% --------------------------------------------------------------------------- %
let OC_LHS_SUBST_TAC thmlist = EVERY (map OC_LHS_SUBST1_TAC thmlist);;

% --------------------------------------------------------------------------- %
% The tactic OC_RHS_SUBST1_TAC substitutes a theorem in the right-hand side   %
% of an observation congruence.                                               %
% --------------------------------------------------------------------------- %
let OC_RHS_SUBST1_TAC thm =
    REPEAT GEN_TAC THEN RULE_TAC OBS_CONGR_SYM THEN
    OC_LHS_SUBST1_TAC thm THEN RULE_TAC OBS_CONGR_SYM;;

% --------------------------------------------------------------------------- %
% The tactic OC_RHS_SUBST_TAC substitutes a list of theorems in the right-hand%
% side of an observation congruence.                                          %
% --------------------------------------------------------------------------- %
let OC_RHS_SUBST_TAC thmlist =
    REPEAT GEN_TAC THEN RULE_TAC OBS_CONGR_SYM THEN
    OC_LHS_SUBST_TAC thmlist THEN RULE_TAC OBS_CONGR_SYM;;

% --------------------------------------------------------------------------- %
% The tactic OC_SUBST1_TAC (OC_SUBST_TAC) substitutes a (list of) theorem(s)  %
% in both sides of an observation congruence.                                 %
% --------------------------------------------------------------------------- %
let OC_SUBST1_TAC = \thm. OC_LHS_SUBST1_TAC thm THEN OC_RHS_SUBST1_TAC thm;;

let OC_SUBST_TAC =
    \thmlist. OC_LHS_SUBST_TAC thmlist THEN OC_RHS_SUBST_TAC thmlist;;

