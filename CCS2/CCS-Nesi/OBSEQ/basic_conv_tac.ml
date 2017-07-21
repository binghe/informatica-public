% =========================================================================== %
% FILE          : basic_conv_tac.ml                                           %
% DESCRIPTION   : Basic conversions and tactics for applying the laws for     %
%                 observation equivalence                                     %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

loadf `/homes/mn/CCS/run`;;

loadf `/homes/mn/CCS/runM`;;

% --------------------------------------------------------------------------- %
% Conversion that proves whether or not a CCS term is stable.                 %
% --------------------------------------------------------------------------- %
letrec STABLE_CONV tm = 
   let list2_pair [x;y] = (x,y)
   and f = (\c. map (snd o dest_eq) (conjuncts c)) in
   let thm = runM tm in 
   let lp = map (list2_pair o f) (disjuncts(rconcl thm)) in 
   let taul = filter (\(act,_). act = "tau") lp in 
   (null taul) => 
    prove 
    ("STABLE ^tm", 
     REWRITE_TAC [STABLE; thm] THEN REPEAT STRIP_TAC THENL 
     list_apply_tac 
     (\act. 
       CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct]
                                (ASSUME "u = ^act"))) (fst(split lp)) ) | 
    prove 
    ("~STABLE ^tm", 
     REWRITE_TAC [STABLE; thm] THEN 
     CONV_TAC (TOP_DEPTH_CONV NOT_FORALL_CONV) THEN
     EXISTS_TAC (fst(hd taul)) THEN EXISTS_TAC (snd(hd taul)) THEN 
     REWRITE_TAC[]) ;; 
    
% --------------------------------------------------------------------------- %
% Define the function OE_SUB_CONV.                                            %
% --------------------------------------------------------------------------- %
let OE_SUB_CONV (c: conv) tm =
   is_prefix tm =>
    let u,P = args_prefix tm in
    let thm = c P in
     SPEC u (MATCH_MP OBS_EQUIV_SUBST_PREFIX thm) |
   is_sum tm =>
    let t1,t2 = args_sum tm in
    let thm1 = c t1
    and thm2 = c t2 in
    let t1',t1'' = args_thm thm1                   % t1' = t1, t2' = t2 %
    and t2',t2'' = args_thm thm2 in
    (t1' = t1'') & (t2' = t2'') =>
     SPEC (mk_sum(t1',t2')) OBS_EQUIV_REFL |
    (t1' = t1'') =>
     SPEC t1'
     (MATCH_MP OBS_EQUIV_SUBST_SUM_L
      (LIST_CONJ [thm2; STABLE_CONV t2'; STABLE_CONV t2''])) | 
    (t2' = t2'') =>
     SPEC t2'
     (MATCH_MP OBS_EQUIV_SUBST_SUM_R
      (LIST_CONJ [thm1; STABLE_CONV t1'; STABLE_CONV t1''])) |
     MATCH_MP OBS_EQUIV_PRESD_BY_SUM  
     (LIST_CONJ [thm1; STABLE_CONV t1'; STABLE_CONV t1'';
                thm2; STABLE_CONV t2'; STABLE_CONV t2'']) ?
    failwith `stable conditions not satisfied` | 
   is_par tm =>
    let t1,t2 = args_par tm in
    let thm1 = c t1
    and thm2 = c t2 in
     MATCH_MP OBS_EQUIV_PRESD_BY_PAR (CONJ thm1 thm2) |
   is_restr tm =>
    let P,L = args_restr tm in
    let thm = c P in
     SPEC L (MATCH_MP OBS_EQUIV_SUBST_RESTR thm) |
   is_relab tm =>
    let P,rf = args_relab tm in
    let thm = c P in
     SPEC rf (MATCH_MP OBS_EQUIV_SUBST_RELAB thm) |
   OE_ALL_CONV tm;;

% --------------------------------------------------------------------------- %
% Define the function OE_DEPTH_CONV.                                          %
% --------------------------------------------------------------------------- %
letrec OE_DEPTH_CONV (c: conv) t =
   (OE_SUB_CONV (OE_DEPTH_CONV c) OE_THENC (OE_REPEATC c)) t;;

% --------------------------------------------------------------------------- %
% Define the function OE_TOP_DEPTH_CONV.                                      %
% --------------------------------------------------------------------------- %
letrec OE_TOP_DEPTH_CONV (c: conv) t =
   ((OE_REPEATC c) OE_THENC
    (OE_SUB_CONV (OE_TOP_DEPTH_CONV c)) OE_THENC
    ((c OE_THENC (OE_TOP_DEPTH_CONV c)) OE_ORELSEC OE_ALL_CONV))
   t;;

% --------------------------------------------------------------------------- %
% Define the function OE_SUBST for substitution in OBS_EQUIV terms.           %
% --------------------------------------------------------------------------- %
letrec OE_SUBST thm tm =
   let (ti,ti') = args_thm thm in 
   (tm = ti) => thm |
   is_prefix tm =>
    let u,t = args_prefix tm in
    let thm1 = OE_SUBST thm t in
     SPEC u (MATCH_MP OBS_EQUIV_SUBST_PREFIX thm1) |
   is_sum tm => 
   let t1,t2 = args_sum tm in 
   let thm1 = OE_SUBST thm t1
   and thm2 = OE_SUBST thm t2 in 
   let t1',t1'' = args_thm thm1                     % t1' = t1, t2' = t2 %
   and t2',t2'' = args_thm thm2 in 
   (t1' = t1'') & (t2' = t2'') => 
    SPEC (mk_sum(t1',t2')) OBS_EQUIV_REFL | 
   (t1' = t1'') =>
    SPEC t1'
    (MATCH_MP OBS_EQUIV_SUBST_SUM_L
     (LIST_CONJ [thm2; STABLE_CONV t2'; STABLE_CONV t2''])) |
   (t2' = t2'') =>
    SPEC t2'
    (MATCH_MP OBS_EQUIV_SUBST_SUM_R
     (LIST_CONJ [thm1; STABLE_CONV t1'; STABLE_CONV t1''])) |
    MATCH_MP OBS_EQUIV_PRESD_BY_SUM
    (LIST_CONJ [thm1; STABLE_CONV t1'; STABLE_CONV t1''; 
                thm2; STABLE_CONV t2'; STABLE_CONV t2'']) ?
    failwith `stable conditions not satisfied` | 
   is_par tm =>
    let t1,t2 = args_par tm in
    let thm1 = OE_SUBST thm t1
    and thm2 = OE_SUBST thm t2 in
     MATCH_MP OBS_EQUIV_PRESD_BY_PAR (CONJ thm1 thm2) |
   is_restr tm =>
    let t,L = args_restr tm in
    let thm1 = OE_SUBST thm t in
     SPEC L (MATCH_MP OBS_EQUIV_SUBST_RESTR thm1) |
   is_relab tm =>
    let t,rf = args_relab tm in
    let thm1 = OE_SUBST thm t in
     SPEC rf (MATCH_MP OBS_EQUIV_SUBST_RELAB thm1) |
   OE_ALL_CONV tm;;

% --------------------------------------------------------------------------- %
% Define the tactic OE_LHS_SUBST1_TAC: thm_tactic which substitutes a theorem %
% in the left-hand side of an observation equivalence.                        %
% --------------------------------------------------------------------------- %
let OE_LHS_SUBST1_TAC thm : tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in 
   (op = "OBS_EQUIV") =>
    let thm' = OE_SUBST thm t1 in 
    let (t1',t') = args_thm thm' in                              % t1' = t1 %
    (t' = t2) =>
     ([], \[]. OE_TRANS thm' (SPEC t' OBS_EQUIV_REFL)) |
     ([asl,"OBS_EQUIV ^t' ^t2"], \[thm'']. OE_TRANS thm' thm'') |
   failwith `the goal is not an OBS_EQUIV relation`;;

% --------------------------------------------------------------------------- %
% The tactic OE_LHS_SUBST_TAC substitutes a list of theorems in the left-hand %
% side of an observation equivalence.                                         %
% --------------------------------------------------------------------------- %
let OE_LHS_SUBST_TAC thmlist = EVERY (map OE_LHS_SUBST1_TAC thmlist);;

% --------------------------------------------------------------------------- %
% The tactic OE_RHS_SUBST1_TAC substitutes a theorem in the right-hand side   %
% of an observation equivalence.                                              %
% --------------------------------------------------------------------------- %
let OE_RHS_SUBST1_TAC thm =
    REPEAT GEN_TAC THEN RULE_TAC OBS_EQUIV_SYM THEN
    OE_LHS_SUBST1_TAC thm THEN RULE_TAC OBS_EQUIV_SYM;;

% --------------------------------------------------------------------------- %
% The tactic OE_RHS_SUBST_TAC substitutes a list of theorems in the right-hand%
% side of an observation equivalence.                                         %
% --------------------------------------------------------------------------- %
let OE_RHS_SUBST_TAC thmlist =
    REPEAT GEN_TAC THEN RULE_TAC OBS_EQUIV_SYM THEN
    OE_LHS_SUBST_TAC thmlist THEN RULE_TAC OBS_EQUIV_SYM;;

% --------------------------------------------------------------------------- %
% The tactic OE_SUBST1_TAC (OE_SUBST_TAC) substitutes a (list of) theorem(s)  %
% in both sides of an observation equivalence.                                %
% --------------------------------------------------------------------------- %
let OE_SUBST1_TAC = \thm. OE_LHS_SUBST1_TAC thm THEN OE_RHS_SUBST1_TAC thm;;

let OE_SUBST_TAC =
    \thmlist. OE_LHS_SUBST_TAC thmlist THEN OE_RHS_SUBST_TAC thmlist;;


