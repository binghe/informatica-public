(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure WeakEQLib :> WeakEQLib =
struct

open HolKernel Parse boolLib bossLib;
open stringLib PFset_conv IndDefRules;
open CCSLib CCSTheory CCSSyntax StrongEQLib;
open WeakEQTheory;

(******************************************************************************)
(*                                                                            *)
(*              Basic functions and conversions for rewriting		      *)
(*               with the laws for observational equivalence		      *)
(*                                                                            *)
(******************************************************************************)

(* Define OE_SYM such that, when given a theorem A |- OBS_EQUIV t1 t2,
   returns the theorem A |- OBS_EQUIV t2 t1. *)
fun OE_SYM thm = MATCH_MP OBS_EQUIV_SYM thm;

(* Define OE_TRANS such that, when given the theorems thm1 and thm2, applies
   OBS_EQUIV_TRANS on them, if possible.
 *)
fun OE_TRANS thm1 thm2 =
    if (rhs_tm thm1 = lhs_tm thm2) then
	MATCH_MP OBS_EQUIV_TRANS (CONJ thm1 thm2)
    else
	failwith "transitivity of observation equivalence not applicable";

(* When applied to a term "t: CCS", the conversion OE_ALL_CONV returns the
   theorem: |- OBS_EQUIV t t
 *)
fun OE_ALL_CONV t = SPEC t OBS_EQUIV_REFL;

infix 0 OE_THENC OE_ORELSEC;

(* Define the function OE_THENC. *)
fun op OE_THENC ((c1, c2) :conv * conv) :conv =
  fn t => let
      val thm1 = c1 t;
      val thm2 = c2 (rhs_tm thm1)
  in
      OE_TRANS thm1 thm2
  end;

(* Define the function OE_ORELSEC. *)
fun op OE_ORELSEC ((c1, c2) :conv * conv) :conv =
  fn t => c1 t handle HOL_ERR _ => c2 t;

(* Define the function OE_REPEATC *)
fun OE_REPEATC (c :conv) (t :term) :thm =
  ((c OE_THENC (OE_REPEATC c)) OE_ORELSEC OE_ALL_CONV) t;

(* Convert a conversion for the application of the laws for STRONG_EQUIV to a
   tactic applying the laws for OBS_EQUIV (i.e. c is a conversion for strong
   equivalence).
 *)
fun OE_LHS_CONV_TAC (c :conv) :tactic =
  fn (asl, w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if (opt = ``OBS_EQUIV``) then
	  let val thm = MATCH_MP STRONG_IMP_OBS_EQUIV ((S_DEPTH_CONV c) t1);
	      val (t1', t') = args_thm thm (* t1' = t1 *)
	  in
	      if (t' = t2) then
		  ([], fn [] => OE_TRANS thm (SPEC t' OBS_EQUIV_REFL))
	      else
		  ([(asl, ``OBS_EQUIV ^t' ^t2``)],
		   fn [thm'] => OE_TRANS thm thm')
	  end
      else
	  failwith "the goal is not an OBS_EQUIV relation"
  end;

fun OE_RHS_CONV_TAC (c :conv) :tactic =
  fn (asl,w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if (opt = ``OBS_EQUIV``) then
	  let val thm = MATCH_MP STRONG_IMP_OBS_EQUIV ((S_DEPTH_CONV c) t2);
	      val (t2',t') = args_thm thm (* t2' = t2 *)
	  in
	      if (t' = t1) then
		  ([], fn [] => OE_SYM thm)
	      else
		  ([(asl, ``OBS_EQUIV ^t1 ^t'``)],
		   fn [thm'] => OE_TRANS thm' (OE_SYM thm))
	  end
      else
	  failwith "the goal is not an OBS_EQUIV relation"
  end;

(******************************************************************************)
(*                                                                            *)
(*           Basic conversions and tactics for applying the laws for	      *)
(*                        observation equivalence			      *)
(*                                                                            *)
(******************************************************************************)

(*
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

 *)

end (* struct *)

(* last updated: Jun 18, 2017 *)
