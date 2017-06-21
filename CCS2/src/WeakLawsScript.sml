(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory prim_recTheory arithmeticTheory relationTheory;
open CCSLib CCSTheory StrongEQTheory StrongLawsTheory;
open WeakEQTheory WeakEQLib;

val _ = new_theory "WeakLaws";

(******************************************************************************)
(*									      *)
(*	   the tau-law "tau.E = E" for observation equivalence		      *)
(*									      *)
(******************************************************************************)

(* Prove TAU_WEAK:  |- !E. OBS_EQUIV (prefix tau E) E *)
val TAU_WEAK = store_thm ("TAU_WEAK",
  ``!E. OBS_EQUIV (prefix tau E) E``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      IMP_RES_TAC Action_distinct_label,
      (* goal 2 (of 4) *)
      Q.EXISTS_TAC `E2` \\
      REWRITE_TAC [WEAK_TRANS, OBS_EQUIV_REFL] \\
      take [`E`, `E2`] \\
      ASM_REWRITE_TAC [EPS_REFL] \\
      MATCH_MP_TAC ONE_TAU \\
      REWRITE_TAC [PREFIX],
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E1` \\
      ASM_REWRITE_TAC [EPS_REFL, OBS_EQUIV_REFL],
      (* goal 4 (of 4) *)
      Q.EXISTS_TAC `E2` \\
      REWRITE_TAC [OBS_EQUIV_REFL] \\
      MATCH_MP_TAC EPS_TRANS \\
      Q.EXISTS_TAC `E` \\
      IMP_RES_TAC ONE_TAU >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC ONE_TAU \\
      REWRITE_TAC [PREFIX] ]);

(******************************************************************************)
(*									      *)
(*  Basic laws of observation equivalence for the binary summation operator   *)
(*		derived through strong equivalence			      *)
(*									      *)
(******************************************************************************)

(* Prove OBS_SUM_IDENT_R: |- !E. OBS_EQUIV (sum E nil) E *)
val OBS_SUM_IDENT_R = save_thm (
   "OBS_SUM_IDENT_R",
    GEN_ALL
      (MATCH_MP STRONG_IMP_OBS_EQUIV
		(Q.SPEC `E` STRONG_SUM_IDENT_R)));

(* Prove OBS_SUM_IDENT_L: |- !E. OBS_EQUIV (sum nil E) E *)
val OBS_SUM_IDENT_L = save_thm (
   "OBS_SUM_IDENT_L",
    GEN_ALL
      (MATCH_MP STRONG_IMP_OBS_EQUIV
		(Q.SPEC `E` STRONG_SUM_IDENT_L)));

(* Prove OBS_SUM_IDEMP: |- !E. OBS_EQUIV (sum E E) E *)
val OBS_SUM_IDEMP = save_thm (
   "OBS_SUM_IDEMP",
    GEN_ALL
      (MATCH_MP STRONG_IMP_OBS_EQUIV
		(Q.SPEC `E` STRONG_SUM_IDEMP)));

(* Prove OBS_SUM_COMM: |- !E E'. OBS_EQUIV (sum E E') (sum E' E) *)
val OBS_SUM_COMM = save_thm (
   "OBS_SUM_COMM",
    Q.GENL [`E'`, `E`]
      (MATCH_MP STRONG_IMP_OBS_EQUIV
		(Q.SPECL [`E`, `E'`] STRONG_SUM_COMM)));

(* Observation equivalence of stable agents is substitutive under the binary
   summation operator on the left:
   |- !E E'. OBS_EQUIV E E' /\ STABLE E /\ STABLE E' ==>
	     (!E''. OBS_EQUIV (sum E'' E) (sum E'' E'))
 *)
val OBS_EQUIV_SUBST_SUM_L = save_thm (
   "OBS_EQUIV_SUBST_SUM_L",
    Q.GENL [`E'`, `E`]
     (DISCH_ALL
      (Q.GEN `E''`
       (OE_TRANS
	 (Q.SPECL [`E''`, `E`] OBS_SUM_COMM)
	 (OE_TRANS
	   (SPEC_ALL (UNDISCH (SPEC_ALL OBS_EQUIV_SUBST_SUM_R)))
	   (Q.SPECL [`E'`, `E''`] OBS_SUM_COMM))))));

(* Prove OBS_SUM_ASSOC_R:
   |- !E E' E''. OBS_EQUIV (sum (sum E E') E'') (sum E (sum E' E''))
 *)
val OBS_SUM_ASSOC_R = save_thm (
   "OBS_SUM_ASSOC_R",
    Q.GENL [`E''`, `E'`, `E`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`E`, `E'`, `E''`] STRONG_SUM_ASSOC_R)));

(* Prove OBS_SUM_ASSOC_L:
   |- !E E' E''. OBS_EQUIV (sum E (sum E' E'')) (sum (sum E E') E'')
 *)
val OBS_SUM_ASSOC_L = save_thm (
   "OBS_SUM_ASSOC_L",
    Q.GENL [`E''`, `E'`, `E`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`E`, `E'`, `E''`] STRONG_SUM_ASSOC_L)));

(******************************************************************************)
(*									      *)
(*	     Basic laws of observation equivalence for the parallel	      *)
(*	       operator derived through strong equivalence		      *)
(*									      *)
(******************************************************************************)

(* Prove OBS_PAR_IDENT_R: |- !E. OBS_EQUIV (par E nil) E
 *)
val OBS_PAR_IDENT_R = save_thm (
   "OBS_PAR_IDENT_R",
    GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPEC `E` STRONG_PAR_IDENT_R)));

(* Prove OBS_PAR_IDENT_L: |- !E. OBS_EQUIV (par nil E) E
 *)
val OBS_PAR_IDENT_L = save_thm (
   "OBS_PAR_IDENT_L",
    GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPEC `E` STRONG_PAR_IDENT_L)));

(* Prove OBS_PAR_COMM: |- !E E'. OBS_EQUIV (par E E') (par E' E)
 *)
val OBS_PAR_COMM = save_thm (
   "OBS_PAR_COMM",
    Q.GENL [`E'`, `E`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`E`, `E'`] STRONG_PAR_COMM)));

(* Prove OBS_PAR_ASSOC:
   |- !E E' E''. OBS_EQUIV (par (par E E') E'') (par E (par E' E''))
 *)
val OBS_PAR_ASSOC = save_thm (
   "OBS_PAR_ASSOC",
    Q.GENL [`E''`, `E'`, `E`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`E`, `E'`, `E''`] STRONG_PAR_ASSOC)));

(* Prove OBS_PAR_PREF_TAU:
   |- !u E E'.
       OBS_EQUIV (par (prefix u E) (prefix tau E'))
		 (sum (prefix u (par E (prefix tau E')))
		      (prefix tau (par (prefix u E) E')))
 *)
val OBS_PAR_PREF_TAU = save_thm (
   "OBS_PAR_PREF_TAU",
    Q.GENL [`E'`, `E`, `u`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`u`, `E`, `E'`] STRONG_PAR_PREF_TAU)));

(* Prove OBS_PAR_TAU_PREF:
   |- !E u E'.
       OBS_EQUIV (par (prefix tau E) (prefix u E'))
		 (sum (prefix tau (par E (prefix u E')))
		      (prefix u (par (prefix tau E) E')))
 *)
val OBS_PAR_TAU_PREF = save_thm (
   "OBS_PAR_TAU_PREF",
    Q.GENL [`E'`, `u`, `E`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`E`, `u`, `E'`] STRONG_PAR_TAU_PREF)));

(* Prove OBS_PAR_TAU_TAU:
   |- !E E'.
       OBS_EQUIV (par (prefix tau E) (prefix tau E'))
		 (sum (prefix tau (par E (prefix tau E')))
		      (prefix tau (par (prefix tau E) E')))
 *)
val OBS_PAR_TAU_TAU = save_thm (
   "OBS_PAR_TAU_TAU", Q.SPEC `tau` OBS_PAR_PREF_TAU);

(* Prove OBS_PAR_PREF_NO_SYNCR:
   |- !l l'.
       ~(l = COMPL l') ==>
       (!E E'.
	 OBS_EQUIV (par (prefix (label l) E) (prefix (label l') E'))
		   (sum (prefix (label l) (par E (prefix (label l') E')))
			(prefix (label l') (par (prefix (label l) E) E'))))
 *)
val OBS_PAR_PREF_NO_SYNCR = save_thm (
   "OBS_PAR_PREF_NO_SYNCR",
    Q.GENL [`l'`, `l`]
       (DISCH ``~((l :'b Label) = COMPL l')``
	(Q.GENL [`E'`, `E`]
	 (MATCH_MP STRONG_IMP_OBS_EQUIV
	  (Q.SPECL [`E`, `E'`]
	   (UNDISCH (Q.SPECL [`l`, `l'`]
			     STRONG_PAR_PREF_NO_SYNCR)))))));

(* Prove OBS_PAR_PREF_SYNCR:
   |- !l l'.
       (l = COMPL l') ==>
       (!E E'.
	 OBS_EQUIV (par (prefix (label l) E) (prefix (label l') E'))
		   (sum
		    (sum (prefix (label l) (par E (prefix (label l') E')))
			 (prefix (label l') (par (prefix (label l) E) E')))
		    (prefix tau (par E E'))))
 *)
val OBS_PAR_PREF_SYNCR = save_thm (
   "OBS_PAR_PREF_SYNCR",
    Q.GENL [`l'`, `l`]
       (DISCH ``((l :'b Label) = COMPL l')``
	(Q.GENL [`E'`, `E`]
	 (MATCH_MP STRONG_IMP_OBS_EQUIV
	  (Q.SPECL [`E`, `E'`]
	   (UNDISCH (Q.SPECL [`l`, `l'`]
			     STRONG_PAR_PREF_SYNCR)))))));

(* The expansion law WEAK_PAR_LAW for observation equivalence:
  |- !f n f' m.
      (!i. i <= n ==> Is_Prefix(f i)) /\ (!j. j <= m ==> Is_Prefix(f' j)) ==>
      OBS_EQUIV
      (par (SIGMA f n) (SIGMA f' m))
      (sum
       (sum
	(SIGMA (\i. prefix (PREF_ACT (f i)) (par (PREF_PROC (f i)) (SIGMA f' m))) n)
	(SIGMA (\j. prefix (PREF_ACT (f' j)) (par (SIGMA f n) (PREF_PROC (f' j)))) m))
       (ALL_SYNC f n f' m))
 *)
val WEAK_PAR_LAW = save_thm (
   "WEAK_PAR_LAW",
    Q.GENL [`m`, `f'`, `n`, `f`]
       (DISCH_ALL
	(MATCH_MP STRONG_IMP_OBS_EQUIV
	 (UNDISCH
	  (Q.SPECL [`f`, `n`, `f'`, `m`] STRONG_PAR_LAW)))));

(******************************************************************************)
(*									      *)
(*	Basic laws of observation equivalence for the restriction	      *)
(*	      operator derived through strong equivalence		      *)
(*									      *)
(******************************************************************************)

(* Prove OBS_RESTR_NIL: |- !L. OBS_EQUIV (restr nil L) nil *)
val OBS_RESTR_NIL = save_thm (
   "OBS_RESTR_NIL",
    GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`L`] STRONG_RESTR_NIL)));

(* Prove OBS_RESTR_SUM:
   |- !E E' L. OBS_EQUIV (restr (sum E E') L) (sum (restr E L) (restr E' L))
 *)
val OBS_RESTR_SUM = save_thm (
   "OBS_RESTR_SUM",
    Q.GENL [`L`, `E'`, `E`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`E`, `E'`, `L`] STRONG_RESTR_SUM)));

(* Prove OBS_RESTR_PREFIX_TAU:
   |- !E L. OBS_EQUIV (restr (prefix tau E) L) (prefix tau (restr E L))
 *)
val OBS_RESTR_PREFIX_TAU = save_thm (
   "OBS_RESTR_PREFIX_TAU",
    Q.GENL [`L`, `E`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
	(Q.SPECL [`E`, `L`] STRONG_RESTR_PREFIX_TAU)));

(* Prove OBS_RESTR_PR_LAB_NIL:
   |- !l L. l IN L \/ (COMPL l) IN L ==>
	    (!E. OBS_EQUIV (restr (prefix (label l) E) L) nil)
 *)
val OBS_RESTR_PR_LAB_NIL = save_thm (
   "OBS_RESTR_PR_LAB_NIL",
    GEN_ALL
       (DISCH ``(l :'b Label) IN L \/ (COMPL l) IN L``
	(Q.GEN `E`
	 (UNDISCH
	  (IMP_TRANS
	   (DISCH ``(l :'b Label) IN L \/ (COMPL l) IN L``
	    (Q.SPEC `E`
	     (UNDISCH
	      (Q.SPECL [`l`, `L`] STRONG_RESTR_PR_LAB_NIL))))
	   (SPECL [``restr (L :'b Label set) (prefix (label l) E)``, ``nil``]
		    STRONG_IMP_OBS_EQUIV))))));

(* Prove OBS_RESTR_PREFIX_LABEL:
   |- !l L.
       ~l IN L /\ ~(COMPL l) IN L ==>
       (!E. OBS_EQUIV (restr (prefix (label l) E) L) (prefix (label l) (restr E L)))
 *)
val OBS_RESTR_PREFIX_LABEL = save_thm (
   "OBS_RESTR_PREFIX_LABEL",
    GEN_ALL
       (DISCH ``~((l :'b Label) IN L) /\ ~((COMPL l) IN L)``
	(Q.GEN `E`
	 (UNDISCH
	  (IMP_TRANS
	   (DISCH ``~((l :'b Label) IN L) /\ ~((COMPL l) IN L)``
	    (Q.SPEC `E`
	     (UNDISCH
	      (Q.SPECL [`l`, `L`] STRONG_RESTR_PREFIX_LABEL))))
	   (SPECL [``restr (L :'b Label set) (prefix (label l) E)``,
		   ``prefix (label (l :'b Label)) (restr L E)``]
		  STRONG_IMP_OBS_EQUIV))))));

(******************************************************************************)
(*									      *)
(*	  Basic laws of observation equivalence for the relabelling	      *)
(*		operator derived through strong equivalence		      *)
(*									      *)
(******************************************************************************)

(* Prove OBS_RELAB_NIL: |- !rf. OBS_EQUIV (relab nil rf) nil *)
val OBS_RELAB_NIL = save_thm (
   "OBS_RELAB_NIL",
    GEN_ALL
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPEC `rf` STRONG_RELAB_NIL)));

(* Prove OBS_RELAB_SUM:
   |- !E E' rf. OBS_EQUIV (relab (sum E E') rf) (sum (relab E rf) (relab E' rf))
 *)
val OBS_RELAB_SUM = save_thm (
   "OBS_RELAB_SUM",
    Q.GENL [`rf`, `E'`, `E`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`E`, `E'`, `rf`] STRONG_RELAB_SUM)));

(* Prove OBS_RELAB_PREFIX:
   |- !u E labl.
       OBS_EQUIV (relab (prefix u E) (RELAB labl))
		 (prefix (relabel (Apply_Relab labl) u) (relab E (RELAB labl)))
 *)
val OBS_RELAB_PREFIX = save_thm (
   "OBS_RELAB_PREFIX",
    Q.GENL [`labl`, `E`, `u`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`u`, `E`, `labl`] STRONG_RELAB_PREFIX)));

(******************************************************************************)
(*									      *)
(*	 Basic laws of observation equivalence for the recursion	      *)
(*		 operator through strong equivalence			      *)
(*									      *)
(******************************************************************************)

(* The unfolding law:
   OBS_UNFOLDING: |- !X E. OBS_EQUIV (rec X E) (CCS_Subst E (rec X E) X)
 *)
val OBS_UNFOLDING = save_thm ("OBS_UNFOLDING",
    Q.GENL [`E`, `X`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`X`, `E`] STRONG_UNFOLDING)));

(* Prove the theorem OBS_PREF_REC_EQUIV:
   |- !u s v.
       OBS_EQUIV
       (prefix u (rec s (prefix v (prefix u (var s)))))
       (rec s (prefix u (prefix v (var s))))
 *)
val OBS_PREF_REC_EQUIV = save_thm (
   "OBS_PREF_REC_EQUIV",
    Q.GENL [`v`, `s`, `u`]
       (MATCH_MP STRONG_IMP_OBS_EQUIV
		 (Q.SPECL [`u`, `s` ,`v`] STRONG_PREF_REC_EQUIV)));

val _ = export_theory ();
val _ = DB.html_theory "WeakLaws";

(* last updated: Jun 20, 2017 *)
