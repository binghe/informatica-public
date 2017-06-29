(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure CCSSimps :> CCSSimps =
struct

open HolKernel Parse boolLib bossLib;
open IndDefRules;
open CCSLib CCSTheory CCSSyntax;

(******************************************************************************)
(*									      *)
(*	Conversion for computing the transitions of a pure CCS agent	      *)
(*									      *)
(******************************************************************************)

(* Source Level Debugging in Poly/ML

 trace true;
 PolyML.Compiler.debug := true;
 open PolyML.Debug;
 breakIn "CCS_TRANS_CONV";

 clearIn "CCS_TRANS_CONV";

Tracing program execution

    val trace = fn : bool -> unit

Breakpoints

    val breakAt = fn : string * int -> unit
    val breakIn = fn : string -> unit
    val breakEx = fn : exn -> unit
    val clearAt = fn : string * int -> unit
    val clearIn = fn : string -> unit
    val clearEx = fn : exn -> unit

Single Stepping and Continuing

    val continue = fn : unit -> unit
    val step = fn : unit -> unit
    val stepOver = fn : unit -> unit
    val stepOut = fn : unit -> unit

Examining and Traversing the Stack

    val up = fn : unit -> unit
    val down = fn : unit -> unit
    val dump = fn : unit -> unit
    val variables = fn : unit -> unit
 *)

fun eqf_elim thm = let
    val concl = (rconcl thm) handle HOL_ERR _ => ``F``
in
    if concl = ``F`` then
	STRIP_FORALL_RULE EQF_ELIM thm
    else
	thm
end;

(* Conversion for executing the operational semantics. *)
local
    val list2_pair = fn [x, y] => (x, y);
    val f = (fn c => map (snd o dest_eq) (strip_conj c));
in

fun strip_trans (thm) = let
    val concl = (rconcl thm) handle HOL_ERR _ => ``F``
in
    if concl = ``F`` then []
    else
	map (list2_pair o f) (strip_disj concl)
end;

fun CCS_TRANS_CONV tm =

(* case 1: nil *)
  if is_nil tm then
      NIL_NO_TRANS_EQF

(* case 2: prefix *)
  else if is_prefix tm then
      let val (u, P) = args_prefix tm
      in
	  SPECL [u, P] TRANS_PREFIX_EQ
      end

(* case 3: sum *)
  else if is_sum tm then
      let val (P1, P2) = args_sum tm;
	  val thm1 = CCS_TRANS_CONV P1
	  and thm2 = CCS_TRANS_CONV P2
      in
	  REWRITE_RULE [thm1, thm2] (SPECL [P1, P2] TRANS_SUM_EQ')
      end

(* case 4: restr *)
  else if is_restr tm then
      let fun extr_acts [] _ = []
	    | extr_acts actl L = let
		val act = hd actl
	    in
		if is_tau act then
		    act :: (extr_acts (tl actl) L)
		else
		    let val l = arg_action act;
			val thml = Label_IN_CONV l L
		    in
			if (rconcl thml = ``T``) then
			    extr_acts (tl actl) L
			else
			    let	val thmlc = Label_IN_CONV 
					      (rconcl
						(REWRITE_CONV [COMPL_LAB_def] ``COMPL ^l``))
					      L
			    in
				if (rconcl thmlc = ``T``) then
				    extr_acts (tl actl) L
				else
				    act :: (extr_acts (tl actl) L)
			    end (* val thmlc *)
		    end (* val l *)
	    end; (* val act *)
	  val (P, L) = args_restr tm;
	  val thm = CCS_TRANS_CONV P
      in
	  if (rconcl thm = ``F``) then
	      prove (``!u E. TRANS ^tm u E = F``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_RESTR \\
      IMP_RES_TAC thm,
      (* goal 2 *)
      REWRITE_TAC [] ])
(****************************************************************** Q. E. D. **)
	  else
	      let val dl = strip_disj (rconcl thm);
		  val actl = map (snd o dest_eq o hd o strip_conj o hd o strip_disj) dl;
		  val actl_not = extr_acts actl L
	      in
		  if (null actl_not) then
		      prove (``!u E. TRANS ^tm u E = F``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC >> EQ_TAC
 >| [ (* goal 1 *)
      STRIP_TAC \\
      IMP_RES_TAC TRANS_RESTR >|
      [ (* goal 1.1 *)
	IMP_RES_TAC thm >|
	(list_apply_tac
	  (fn a => CHECK_ASSUME_TAC
		     (REWRITE_RULE [ASSUME ``u = tau``, Action_distinct]
				   (ASSUME ``u = ^a``))) actl),
	(* goal 1.2 *)
	IMP_RES_TAC thm >|
	(list_apply_tac
	  (fn a => ASSUME_TAC (REWRITE_RULE [ASSUME ``u = label l``, Action_11]
					    (ASSUME ``u = ^a``)) \\
		   CHECK_ASSUME_TAC
		     (REWRITE_RULE [ASSUME ``l = ^(arg_action a)``,
				    Label_IN_CONV (arg_action a) L]
				   (ASSUME ``~(l IN ^L)``)) \\
		   CHECK_ASSUME_TAC
		     (REWRITE_RULE [ASSUME ``l = ^(arg_action a)``, COMPL_LAB_def,
				    Label_IN_CONV
					(rconcl (REWRITE_CONV [COMPL_LAB_def]
							      ``COMPL ^(arg_action a)``)) L]
				   (ASSUME ``~((COMPL_LAB l) IN ^L)``))) actl) ],
      (* goal 2 *)
      REWRITE_TAC [] ])
(****************************************************************** Q. E. D. **)
		  else (* actl_not is not empty => the list of pairs lp is not empty as well *)
		      let fun build_disj lp L =
			    let val (u, p) = hd lp in
				if (null (tl lp)) then
				    mk_conj (``u = ^u``, ``E = ^(mk_restr (p, L))``)
				else
				    mk_disj (mk_conj (``u = ^u``,
						      ``E = ^(mk_restr (p, L))``),
					     build_disj (tl lp) L)
			    end;
			  val lp = map (list2_pair o f)
				       (filter (fn c =>
						   mem ((snd o dest_eq o hd o strip_conj
								       o hd o strip_disj) c)
						       actl_not) dl);
			  val dsjt = build_disj lp L
		      in
			  prove (``!u E. TRANS ^tm u E = ^dsjt``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC >> EQ_TAC
 >| [ (* goal 1 *)
      DISCH_TAC >> IMP_RES_TAC TRANS_RESTR >|
      [ (* goal 1.1 *)
	IMP_RES_TAC thm >|
	(list_apply_tac
	  (fn a => CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME ``u = tau``, Action_distinct]
						  (ASSUME ``u = ^a``)) \\
		   ASM_REWRITE_TAC []) actl),
	(* goal 1.2 *)	
	IMP_RES_TAC thm >|
	(list_apply_tac
	  (fn a => if is_tau a then
	  	       ASSUME_TAC (REWRITE_RULE [ASSUME ``u = label l``, Action_11]
						(ASSUME ``u = ^a``)) \\
		       ASM_REWRITE_TAC []
		   else
		       ASSUME_TAC (REWRITE_RULE [ASSUME ``u = label l``, Action_11]
						(ASSUME ``u = ^a``)) \\
		       CHECK_ASSUME_TAC
			 (REWRITE_RULE [ASSUME ``l = ^(arg_action a)``,
					Label_IN_CONV (arg_action a) L]
				       (ASSUME ``~(l IN ^L)``)) \\
		       CHECK_ASSUME_TAC
			 (REWRITE_RULE
			      [ASSUME ``l = ^(arg_action a)``, COMPL_LAB_def,
			       Label_IN_CONV
				 (rconcl (REWRITE_CONV [COMPL_LAB_def] ``COMPL ^(arg_action a)``)) L]
			      (ASSUME ``~((COMPL_LAB l) IN ^L)``)) \\
		       ASM_REWRITE_TAC []) actl) ],
      (* goal 2 *)
      STRIP_TAC >|
      (list_apply_tac
	(fn (a, P) =>
	    REWRITE_TAC [ASSUME ``u = ^a``,
			 ASSUME ``E = restr ^L ^P``] \\
	    MATCH_MP_TAC RESTR \\
	    (if is_tau a then
		 ASM_REWRITE_TAC [thm]
	     else
		 EXISTS_TAC (arg_action a) \\
		 ASM_REWRITE_TAC
		     [thm, COMPL_LAB_def,
		      Label_IN_CONV (arg_action a) L,
		      Label_IN_CONV (rconcl (REWRITE_CONV [COMPL_LAB_def]
							  ``COMPL ^(arg_action a)``)) L]))
	lp) ]) (* prove *)
(****************************************************************** Q. E. D. **)
		      end (* let: build_disj *)
	      end (* let: dl *)
      end (* let: extr_acts *)

(* case 5: relab *)
  else if is_relab tm then
      let val (P, rf) = args_relab tm;
	  val thm = CCS_TRANS_CONV P
      in
	  if (rconcl thm = ``F``) then
	      prove (``!u E. TRANS ^tm u E = F``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_RELAB \\
      IMP_RES_TAC thm,
      (* goal 2 (of 2) *)
      REWRITE_TAC [] ])
(****************************************************************** Q. E. D. **)
	  else (* ~(rconcl thm = "F") implies  dl is not empty *)
	      let fun relab_act [] _ = []
		    | relab_act actl labl = let
			val act = hd actl;
			val thm_act =
			    REWRITE_RHS_RULE [relabel_def, Apply_Relab_def,
					      Label_distinct, Label_distinct', Label_11,
					      COMPL_LAB_def, COMPL_COMPL_LAB]
					     (REFL ``relabel (Apply_Relab ^labl) ^act``);
			val thm_act' = RELAB_EVAL_CONV (rconcl thm_act)
		    in
			(TRANS thm_act thm_act') :: (relab_act (tl actl) labl)
		    end;
		  fun build_disj_relab rlp rf =
		    let val (u, p) = hd rlp
		    in
			if (null (tl rlp)) then
			    mk_conj (``u = ^u``,
				     ``E = ^(mk_relab (p, rf))``)
			else
			    mk_disj (mk_conj (``u = ^u``,
					      ``E = ^(mk_relab (p, rf))``),
				     build_disj_relab (tl rlp) rf)
		    end;
		  val dl = strip_disj (rconcl thm);
		  val actl = map (snd o dest_eq o hd o strip_conj) dl
		  and labl = arg_relabelling rf;
		  val thml = relab_act actl labl;
		  val rlp = combine (map rconcl thml, map (snd o list2_pair o f) dl);
		  val disjt = build_disj_relab rlp rf
	      in
		  prove (``!u E. TRANS ^tm u E = ^disjt``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_RELAB \\
      IMP_RES_TAC thm >|
      (list_apply_tac
	(fn (a, thm_act) =>
	    REWRITE_TAC [REWRITE_RULE [ASSUME ``u' = ^a``, thm_act]
			    (REWRITE_RULE [SYM (ASSUME ``RELAB ^labl = RELAB labl``)]
				(ASSUME ``u = relabel (Apply_Relab labl) u'``))] \\
	    ASM_REWRITE_TAC [])
	(combine (actl, thml))),
      (* goal 2 (of 2) *)
      STRIP_TAC >|
      (list_apply_tac 
	(fn ((a, P), thm_act) =>
	    REWRITE_TAC [ONCE_REWRITE_RULE [SYM thm_act]
					   (ASSUME ``u = ^a``),
			 ASSUME ``E = relab ^P ^rf``] \\
	    MATCH_MP_TAC RELABELING \\
	    REWRITE_TAC [thm])
	(combine (rlp, thml))) ])
(****************************************************************** Q. E. D. **)
	      end (* fun relab_act *)
      end (* val (P, rf) *)

(* case 6: par *)
  else if is_par tm then
      let fun build_disj1 dl P =
	    let val (u, p) = hd dl
	    in
		if (null (tl dl)) then
		    mk_conj (``u = ^u``, ``E = ^(mk_par (p, P))``)
		else
		    mk_disj (mk_conj (``u = ^u``, ``E = ^(mk_par (p, P))``),
			     build_disj1 (tl dl) P)
	    end;
	  fun build_disj2 dl P =
	    let val (u, p) = hd dl
	    in
		if (null (tl dl)) then
		    mk_conj (``u = ^u``, ``E = ^(mk_par (P, p))``)
		else
		    mk_disj (mk_conj (``u = ^u``, ``E = ^(mk_par (P, p))``),
			     build_disj2 (tl dl) P)
	    end;
	  fun build_disj_tau _ [] = ``F``
	    | build_disj_tau  p syncl = let
		val (_, p') = hd syncl
	    in
		mk_disj (mk_conj (``u = tau``, ``E = ^(mk_par (p, p'))``),
			 build_disj_tau p (tl syncl))
	    end;
	  fun act_sync [] _ = []
	    | act_sync dl1 dl2 = let
		val (act, p) = hd dl1;
		val syncl = filter (fn (a, p) =>
				       a = (if is_tau act then
						act
					    else
						rconcl (REWRITE_CONV [COMPL_ACT_def, COMPL_LAB_def]
								    ``COMPL_ACT ^act``)))
				   dl2
	    in
		if (null syncl) then
		    act_sync (tl dl1) dl2
		else
		    act :: (act_sync (tl dl1) dl2)
	    end;
	  fun build_sync dl1 dl2 =
	    let val (act, p) = hd dl1;
		val syncl = filter (fn (a, p) =>
				       a = (if is_tau act then
						act
					    else
						rconcl (REWRITE_CONV [COMPL_ACT_def, COMPL_LAB_def]
								    ``COMPL_ACT ^act``)))
				   dl2
	    in
		if (null (tl dl1)) then
		    build_disj_tau p syncl
		else
		    mk_disj (build_disj_tau p syncl, build_sync (tl dl1) dl2)
	    end;
	  val (P1, P2) = args_par tm;
	  val thm1 = CCS_TRANS_CONV P1
	  and thm2 = CCS_TRANS_CONV P2
      in
	  if (rconcl thm1 = ``F``) andalso (rconcl thm2 = ``F``) then
	      prove (``!u E. TRANS ^tm u E = F``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ IMP_RES_TAC thm1, IMP_RES_TAC thm2, IMP_RES_TAC thm1 ],
      (* goal 2 *)
      REWRITE_TAC [] ])
(****************************************************************** Q. E. D. **)
	  else if (rconcl thm1 = ``F``) then
	      let val dl2 = map (list2_pair o f) (strip_disj (rconcl thm2));
		  val actl2 = map fst dl2
		  and disj_nosync = build_disj2 dl2 P1
	      in
		  prove (``!u E. TRANS ^tm u E = ^disj_nosync``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ IMP_RES_TAC thm1,
	IMP_RES_TAC thm2 >> ASM_REWRITE_TAC [],
	IMP_RES_TAC thm1 ],
      (* goal 2 (of 2) *)
      STRIP_TAC >|
      (list_apply_tac
	(fn a => ASM_REWRITE_TAC [] >> MATCH_MP_TAC PAR2 \\
		 REWRITE_TAC [GEN_ALL thm2]) actl2) ])
(****************************************************************** Q. E. D. **)
	      end
	  else if (rconcl thm2 = ``F``) then
	      let val dl1 = map (list2_pair o f) (strip_disj (rconcl thm1));
		  val actl1 = map fst dl1
		  and disj_nosync = build_disj1 dl1 P2
	      in
		  prove (``!u E. TRANS ^tm u E = ^disj_nosync``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_PAR >|
      [ IMP_RES_TAC thm1 >> ASM_REWRITE_TAC [],
	IMP_RES_TAC thm2,
	IMP_RES_TAC thm2 ],
      (* goal 2 (of 2) *)
      STRIP_TAC >|
      (list_apply_tac
	(fn a => ASM_REWRITE_TAC [] >> MATCH_MP_TAC PAR1 \\
		 REWRITE_TAC [GEN_ALL thm1]) actl1) ])
(****************************************************************** Q. E. D. **)
	      end
	  else (* ~(rconcl thm1 = "F") and ~(rconcl thm2 = "F") => dl1 and dl2 are not empty *)
	      let val [dl1, dl2] = map ((map (list2_pair o f)) o strip_disj o rconcl)
				       [thm1, thm2];
		  val [actl1, actl2] = map (map fst) [dl1, dl2]
		  and disj_nosync = mk_disj (build_disj1 dl1 P2, build_disj2 dl2 P1)
		  and disj_sync = rconcl (QCONV (REWRITE_CONV []) (build_sync dl1 dl2))
	      in
		  if (disj_sync = ``F``) then
		      prove (``!u E. TRANS ^tm u E = ^disj_nosync``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ IMP_RES_TAC thm1 >> ASM_REWRITE_TAC [],
	IMP_RES_TAC thm2 >> ASM_REWRITE_TAC [],
	IMP_RES_TAC thm1 \\
	IMP_RES_TAC thm2 >|
	(list_apply_tac
	  (fn a =>
	      if is_tau (hd actl1) then
	      	  IMP_RES_TAC Action_distinct_label
	      else
		  let val eq = REWRITE_RULE [REWRITE_RULE [Action_11]
							  (ASSUME ``label l = ^(hd actl1)``),
					     COMPL_LAB_def]
					    (ASSUME ``label (COMPL_LAB l) = ^a``)
		  in
		      CHECK_ASSUME_TAC
			  (REWRITE_RULE [eq] (Action_EQ_CONV (concl eq)))
		  end) actl2) ],
      (* goal 2 (of 2) *)
      STRIP_TAC >| (* as many as the number of the summands *)
      (list_apply_tac
	(fn a => ASM_REWRITE_TAC [] >> MATCH_MP_TAC PAR1 \\
		 REWRITE_TAC [GEN_ALL thm1]) actl1) @ 
      (list_apply_tac
	(fn a => ASM_REWRITE_TAC [] >> MATCH_MP_TAC PAR2 \\
		 REWRITE_TAC [GEN_ALL thm2]) actl2) @
      (list_apply_tac
	(fn a => ASM_REWRITE_TAC [] \\
		 MATCH_MP_TAC PAR3 \\
		 EXISTS_TAC (arg_action a) \\
		 REWRITE_TAC [COMPL_LAB_def, GEN_ALL thm1, GEN_ALL thm2])
	(act_sync dl1 dl2)) ])
(****************************************************************** Q. E. D. **)
		  else
		      prove (``!u E. TRANS ^tm u E = ^(mk_disj (disj_nosync, disj_sync))``,
(** PROOF BEGIN ***************************************************************)
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ IMP_RES_TAC thm1 >> ASM_REWRITE_TAC [],
	IMP_RES_TAC thm2 >> ASM_REWRITE_TAC [],
	IMP_RES_TAC thm1 >> IMP_RES_TAC thm2 >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      STRIP_TAC >| (* as many as the number of the summands *)
      (list_apply_tac (* goal 2.1 *)
	(fn a => ASM_REWRITE_TAC [] >> MATCH_MP_TAC PAR1 \\
		 REWRITE_TAC [GEN_ALL thm1]) actl1) @
      (list_apply_tac (* goal 2.2 *)
	(fn a => ASM_REWRITE_TAC [] >> MATCH_MP_TAC PAR2 \\
		 REWRITE_TAC [GEN_ALL thm2]) actl2) @
      (list_apply_tac (* goal 2.3 *)
	(fn a => ASM_REWRITE_TAC [] \\
		 MATCH_MP_TAC PAR3 \\
		 EXISTS_TAC (arg_action a) \\
		 REWRITE_TAC [COMPL_LAB_def, GEN_ALL thm1, GEN_ALL thm2])
	(act_sync dl1 dl2)) ])
(****************************************************************** Q. E. D. **)
	      end (* val [dl1, dl2] *)
      end (* fun build_disj1 *)

(* case 7: rec *)
  else if is_rec tm then
      let val (X, P) = args_rec tm;
	  val thmS = SIMP_CONV (srw_ss ()) [CCS_Subst_def] ``CCS_Subst ^P ^tm ^X``;
	  val thm = CCS_TRANS_CONV (rconcl thmS)
      in
	  GEN_ALL (REWRITE_CONV [TRANS_REC_EQ, thmS, thm] ``TRANS ^tm u E``)
      end (* val (X, P) *)
  else (* no need to distinguish on (rconcl thm) *)
      failwith "CCS_TRANS_CONV";

(** CCS_TRANS returns both a theorem and a list of CCS transitions **)
fun CCS_TRANS tm =
  let val thm = CCS_TRANS_CONV tm;
      val trans = strip_trans thm
  in
      (eqf_elim thm, trans)
  end;

end; (* local *)

(******************************************************************************)
(*									      *)
(*		       Test cases for CCS_TRANS_CONV			      *)
(*									      *)
(******************************************************************************)
(*

 1. (ν a) (a.0 | `a.0)
   CCS_TRANS_CONV ``(restr {name "a"}) (label (name "a")..nil || label (coname "a")..nil)``

   |- ∀u E.
     ν {name "a"} (label (name "a")..nil || label (coname "a")..nil) --u->
     E ⇔ (u = τ) ∧ (E = ν {name "a"} (nil || nil))

 2. a.0 | `a.0
   CCS_TRANS_CONV
	 ``par (prefix (label (name "a")) nil)
	       (prefix (label (coname "a")) nil)``

   |- ∀u E.
     label (name "a")..nil || label (coname "a")..nil --u-> E ⇔
     ((u = label (name "a")) ∧ (E = nil || label (coname "a")..nil) ∨
      (u = label (coname "a")) ∧ (E = label (name "a")..nil || nil)) ∨
     (u = τ) ∧ (E = nil || nil)

 3. nil | nil
   CCS_TRANS_CONV ``par nil nil``

   |- ∀u E. nil || nil --u-> E ⇔ F

 4. (ν a) (nil | nil)
   CCS_TRANS_CONV ``restr { name "a" } (par nil nil)``

   |- ∀u E. ν {name "a"} (nil || nil) --u-> E ⇔ F:

 5. a.b.0 + b.a.0
   CCS_TRANS_CONV ``label (name "a")..label (name "b")..nil +
		    label (name "b")..label (name "a")..nil``

   |- ∀u E''.
     label (name "a")..label (name "b")..nil +
     label (name "b")..label (name "a")..nil
     --u->
     E'' ⇔
     (u = label (name "a")) ∧ (E'' = label (name "b")..nil) ∨
     (u = label (name "b")) ∧ (E'' = label (name "a")..nil)

 6. (nu a)(a.0|`a.0) | a.0
   CCS_TRANS_CONV ``(restr {name "a"} (label (name "a")..nil || label (coname "a")..nil)) ||
		    (label (name "a")..nil)``

   |- ∀u E.
     ν {name "a"} (label (name "a")..nil || label (coname "a")..nil) ||
     label (name "a")..nil
     --u->
     E ⇔
     (u = τ) ∧
     (E = ν {name "a"} (nil || nil) || label (name "a")..nil) ∨
     (u = label (name "a")) ∧
     (E =
      ν {name "a"} (label (name "a")..nil || label (coname "a")..nil) ||
      nil)

 7. CCS_TRANS_CONV
	``rec "VM" (In "coin"..(In "ask-esp"..rec "VM1" (Out "esp-coffee"..var "VM") +
				In "ask-am"..rec "VM2" (Out "am-coffee"..var "VM")))``

   |- ∀u E.
     rec "VM1"
       (Out "esp-coffee"
	..
	rec "VM"
	  (In "coin"
	   ..
	   (In "ask-esp"..rec "VM1" (Out "esp-coffee"..var "VM") +
	    In "ask-am"..rec "VM2" (Out "am-coffee"..var "VM"))))
     --u->
     E ⇔
     (u = Out "esp-coffee") ∧
     (E =
      rec "VM"
	(In "coin"
	 ..
	 (In "ask-esp"..rec "VM1" (Out "esp-coffee"..var "VM") +
	  In "ask-am"..rec "VM2" (Out "am-coffee"..var "VM"))))
 *)

end (* struct *)

(* last updated: May 15, 2017 *)
