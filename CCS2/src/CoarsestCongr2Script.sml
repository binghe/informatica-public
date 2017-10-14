(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory cardinalTheory ordinalTheory;

open CCSLib CCSTheory StrongEQTheory WeakEQTheory ObsCongrTheory;
open CoarsestCongrTheory;

val _ = new_theory "CoarsestCongr2";

(******************************************************************************)
(*                                                                            *)
(*       Coarsest congruence contained in WEAK_EQUIV (full version)           *)
(*                                                                            *)
(******************************************************************************)

val _ = new_constant ("summ", ``:('a, 'b) CCS set -> ('a, 'b) CCS``);

val summ_Axiom = new_axiom (
   "summ_Axiom", ``?f. !rs u E. TRANS (f rs) u E = ?r. r IN rs /\ TRANS r u E``);

val summ_axiom = new_specification ("summ_axiom", ["summ"], summ_Axiom);

(* The full version of Klop function defined on orginals:
 |- ∀a.
     Klop a 0o = nil ∧
    (∀α. Klop a α⁺ = Klop a α + label a..Klop a α) ∧
     ∀α. 0o < α ∧ islimit α ⇒ Klop a α = summ (IMAGE (Klop a) (preds α))
 *)
val Klop_def = new_specification ("Klop_def", ["Klop"],
    ord_RECURSION |> INST_TYPE [``:'a`` |-> ``:'c``]
		  |> ISPEC ``nil :('a, 'b) CCS``		(* z *)
		  |> Q.SPEC `\x r. sum r (prefix (label a) r)`	(* sf *)
		  |> Q.SPEC `\x rs. summ rs`			(* lf *)
		  |> SIMP_RULE (srw_ss()) []
		  |> Q.GEN `a`
		  |> CONV_RULE SKOLEM_CONV );

(* Transition cases theorems for Klop processes *)
val Klop_case0 = store_thm (
   "Klop_case0", ``!(a :'b Label). Klop a (0 :'c ordinal) = nil``,
    GEN_TAC >> REWRITE_TAC [Klop_def]);

val Klop_case1 = store_thm (
   "Klop_case1",
  ``!(a :'b Label) (n :'c ordinal) (u :'b Action) (E :('a, 'b) CCS).
     TRANS (Klop a (ordSUC n)) u E = (((u = label a) /\ (E = Klop a n)) \/
				      TRANS (Klop a n) u E)``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [Klop_def]
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        DISJ2_TAC >> ASM_REWRITE_TAC [],
        (* goal 1.2 (of 2) *)
        DISJ1_TAC \\
        IMP_RES_TAC TRANS_PREFIX >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX],
        (* goal 2.2 (of 2) *)
        MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [] ] ]);

val Klop_case2 = store_thm (
   "Klop_case2",
  ``!(a :'b Label) (n :'c ordinal) (u :'b Action) (E :('a, 'b) CCS).
     0 < n /\ islimit n ==> (TRANS (Klop a n) u E = (?m. m < n /\ TRANS (Klop a m) u E))``,
    REPEAT STRIP_TAC
 >> RW_TAC std_ss [Klop_def, summ_axiom]
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REPEAT STRIP_TAC \\
      NTAC 2 (POP_ASSUM MP_TAC) \\
      REWRITE_TAC [IN_IMAGE, IN_preds] \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `x` \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      REWRITE_TAC [IN_IMAGE, IN_preds] \\
      REPEAT STRIP_TAC \\
      Q.EXISTS_TAC `Klop a m` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `m` >> ASM_REWRITE_TAC [] ]);

val Klop_cases = save_thm ((* NEW *)
   "Klop_cases", LIST_CONJ [Klop_case0, Klop_case1, Klop_case2]);

(* Transition rules for Klop processes *)
val Klop_rule1 = store_thm ((* NEW *)
   "Klop_rule1",
  ``!(a :'b Label) (n :'c ordinal). TRANS (Klop a (ordSUC n)) (label a) (Klop a n)``,
    REPEAT GEN_TAC
 >> Q.ABBREV_TAC `E = Klop a n`
 >> REWRITE_TAC [Klop_case1]
 >> DISJ1_TAC
 >> Q.UNABBREV_TAC `E`
 >> RW_TAC std_ss []);

val Klop_rule2 = store_thm ((* NEW *)
   "Klop_rule2",
  ``!(a :'b Label) (n :'c ordinal) m u (E :('a, 'b) CCS).
	0 < n /\ islimit n /\ m < n /\ TRANS (Klop a m) u E ==> TRANS (Klop a n) u E``,
    REPEAT STRIP_TAC
 >> RW_TAC std_ss [Klop_case2]
 >> Q.EXISTS_TAC `m`
 >> ASM_REWRITE_TAC []);

val Klop_rules = save_thm ((* NEW *)
   "Klop_rules", LIST_CONJ [Klop_rule1, Klop_rule2]);

val K0_NO_TRANS' = store_thm ((* NEW *)
   "K0_NO_TRANS'", ``!(a :'b Label) u E. ~(TRANS (Klop a 0) u E)``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [Klop_case0]
 >> REWRITE_TAC [NIL_NO_TRANS]);

val Klop_PROP0 = store_thm ((* NEW *)
   "Klop_PROP0", ``!(a :'b Label) (n :'c ordinal). STABLE (Klop a n)``,
    GEN_TAC
 >> HO_MATCH_MP_TAC simple_ord_induction
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [STABLE] \\
      RW_TAC std_ss [K0_NO_TRANS'],
      (* goal 2 (of 3) *)
      REWRITE_TAC [STABLE] \\
      REPEAT STRIP_TAC \\
      PAT_X_ASSUM ``TRANS (Klop a (ordSUC n)) u E'``
	(STRIP_ASSUME_TAC o (REWRITE_RULE [Klop_case1])) >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        PROVE_TAC [Action_distinct],
        (* goal 2.2 (of 2) *)
        PROVE_TAC [STABLE] ],
      (* goal 3 (of 3) *)
      REWRITE_TAC [STABLE] >> REPEAT STRIP_TAC \\
      IMP_RES_TAC Klop_case2 \\
      PROVE_TAC [STABLE] ]);

(* Any transition of Klop processes is still a Klop process. Together with Prop 0,
   this also implies that Klop processes are tau-free. *)
val Klop_PROP1_LR = store_thm ((* NEW *)
   "Klop_PROP1_LR",
  ``!(a :'b Label) (n :'c ordinal) (E :('a, 'b) CCS).
     TRANS (Klop a n) (label a) E ==> ?m. m < n /\ (E = Klop a m)``,
    GEN_TAC
 >> HO_MATCH_MP_TAC simple_ord_induction
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      PROVE_TAC [K0_NO_TRANS'],
      (* goal 2 (of 3) *)
      PAT_X_ASSUM ``TRANS (Klop a (ordSUC n)) (label a) E``
	(STRIP_ASSUME_TAC o (REWRITE_RULE [Klop_case1])) >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        Q.EXISTS_TAC `n` >> ASM_REWRITE_TAC [ordlt_SUC],
        (* goal 2.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `m` >> ASM_REWRITE_TAC [] \\
        `n < ordSUC n` by PROVE_TAC [ordlt_SUC] \\
        IMP_RES_TAC ordlt_TRANS ],
      (* goal 3 (of 3) *)
      MP_TAC (Q.SPECL [`a`, `n`, `label a`, `E`] Klop_case2) \\
      RW_TAC std_ss [] \\
      NTAC 2 RES_TAC \\
      Q.EXISTS_TAC `m''` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ordlt_TRANS ]);

val Klop_PROP1_RL = store_thm ((* NEW *)
   "Klop_PROP1_RL",
  ``!(a :'b Label) (n :'c ordinal) (E :('a, 'b) CCS).
     (?m. m < n /\ (E = Klop a m)) ==> TRANS (Klop a n) (label a) E``,
    GEN_TAC
 >> HO_MATCH_MP_TAC simple_ord_induction
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      PROVE_TAC [ordlt_ZERO],
      (* goal 2 (of 3) *)
      REWRITE_TAC [Klop_case1] \\
      PAT_X_ASSUM ``m < ordSUC n``
	(STRIP_ASSUME_TAC o (REWRITE_RULE [ordlt_SUC_DISCRETE])) >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        DISJ2_TAC >> RES_TAC,
        (* goal 2.2 (of 2) *)
        DISJ1_TAC >> ASM_REWRITE_TAC [] ],
      (* goal 3 (of 3) *)
      `ordSUC m < n` by PROVE_TAC [islimit_SUC_lt] \\
      ASSUME_TAC (SPECL [``a :'b Label``, ``m :'c ordinal``] Klop_rule1) \\
      PROVE_TAC [Klop_rule2] ]);

(* Klop processes are closed under transition *)
val Klop_PROP1 = store_thm ((* NEW *)
   "Klop_PROP1",
  ``!(a :'b Label) (n :'c ordinal) (E :('a, 'b) CCS).
     TRANS (Klop a n) (label a) E = (?m. m < n /\ (E = Klop a m))``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [Klop_PROP1_LR],
      (* goal 2 (of 2) *)
      REWRITE_TAC [Klop_PROP1_RL] ]);

(* Klop processes are closed under weak transition *)
val Klop_PROP1' = store_thm ((* NEW *)
   "Klop_PROP1'",
  ``!(a :'b Label) (n :'c ordinal) (E :('a, 'b) CCS).
	WEAK_TRANS (Klop a n) (label a) E = (?m. m < n /\ (E = Klop a m))``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        ASSUME_TAC (Q.SPECL [`a`, `n`] Klop_PROP0) \\
        IMP_RES_TAC STABLE_NO_TRANS_TAU,
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC Klop_PROP1_LR \\
        IMP_RES_TAC EPS_cases1 >| (* 2 sub-goals here *)
        [ (* goal 1.2.1 (of 2) *)
          Q.EXISTS_TAC `m` >> PROVE_TAC [],
          (* goal 1.2.2 (of 2) *)
          ASSUME_TAC (Q.SPECL [`a`, `m`] Klop_PROP0) \\
          PROVE_TAC [STABLE_NO_TRANS_TAU] ] ],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      MATCH_MP_TAC TRANS_IMP_WEAK_TRANS \\
      RW_TAC std_ss [Q.SPECL [`a`, `n`, `E`] Klop_PROP1_RL] ]);

(* Klop processes are strongly distinct with each other *)
val Klop_PROP2 = store_thm ((* NEW *)
   "Klop_PROP2",
  ``!(a :'b Label) (n :'c ordinal) m. m < n ==> ~(STRONG_EQUIV (Klop a m) (Klop a n))``,
    GEN_TAC
 >> HO_MATCH_MP_TAC ord_induction
 >> REPEAT STRIP_TAC
 >> `TRANS (Klop a n) (label a) (Klop a m)` by PROVE_TAC [Klop_PROP1]
 >> PAT_X_ASSUM ``STRONG_EQUIV (Klop a m) (Klop a n)``
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR]))
 >> RES_TAC
 >> PAT_X_ASSUM ``TRANS (Klop a m) (label a) E1``
	(STRIP_ASSUME_TAC o (REWRITE_RULE [Klop_PROP1]))
 >> PROVE_TAC []);

(* Klop processes are weakly distinct with each other *)
val Klop_PROP2' = store_thm ((* NEW *)
   "Klop_PROP2'",
  ``!(a :'b Label) (n :'c ordinal) m. m < n ==> ~(WEAK_EQUIV (Klop a m) (Klop a n))``,
    GEN_TAC
 >> HO_MATCH_MP_TAC ord_induction
 >> REPEAT STRIP_TAC
 >> `TRANS (Klop a n) (label a) (Klop a m)` by PROVE_TAC [Klop_PROP1]
 >> PAT_X_ASSUM ``WEAK_EQUIV (Klop a m) (Klop a n)``
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR]))
 >> RES_TAC
 >> PAT_X_ASSUM ``WEAK_TRANS (Klop a m) (label a) E1``
	(STRIP_ASSUME_TAC o (REWRITE_RULE [Klop_PROP1']))
 >> PROVE_TAC []);

val Klop_ONE_ONE = store_thm ((* NEW *)
   "Klop_ONE_ONE", ``!(a :'b Label). ONE_ONE ((Klop a) :'c ordinal -> ('a, 'b) CCS)``,
    REWRITE_TAC [ONE_ONE_DEF]
 >> BETA_TAC
 >> REPEAT STRIP_TAC
 >> IMP_RES_TAC EQUAL_IMP_STRONG_EQUIV
 >> CCONTR_TAC
 >> `x1 < x2 \/ x2 < x1` by PROVE_TAC [ordlt_trichotomy] (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC Klop_PROP2,
      (* goal 2 (of 2) *)
      IMP_RES_TAC Klop_PROP2 \\
      PROVE_TAC [STRONG_EQUIV_SYM] ]);

(* Not used in the project, but this is a pure math result *)
val ONE_ONE_IMP_NOTIN = store_thm ((* NEW *)
   "ONE_ONE_IMP_NOTIN",
  ``!(A :'a set) (f :'a ordinal -> 'a). ONE_ONE f ==> ?n. f n NOTIN A``,
    REPEAT GEN_TAC
 >> MP_TAC univ_ord_greater_cardinal
 >> RW_TAC std_ss [ONE_ONE_DEF, cardleq_def, INJ_DEF, IN_UNIV]
 >> CCONTR_TAC
 >> FIRST_X_ASSUM
	(Q.SPEC_THEN `\n. if n < omega then INL (@m. &m = n) else INR (f n)` MP_TAC)
 >> BETA_TAC
 >> REPEAT STRIP_TAC
 >> Cases_on `x < omega` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      FULL_SIMP_TAC std_ss [] \\
      Q.PAT_X_ASSUM `(@m. &m = x) = P` MP_TAC \\
      REWRITE_TAC [] \\
      NTAC 2 SELECT_ELIM_TAC \\
      REPEAT STRIP_TAC >| (* 3 sub-goals here *)
      [ (* goal 1.1 (of 3) *)
        Q.PAT_X_ASSUM `y < omega` (ASSUME_TAC o (REWRITE_RULE [lt_omega])) \\
        PROVE_TAC [],
        (* goal 1.2 (of 3) *)
        Q.PAT_X_ASSUM `x < omega` (ASSUME_TAC o (REWRITE_RULE [lt_omega])) \\
        PROVE_TAC [],
        (* goal 1.3 (of 3) *)
        FULL_SIMP_TAC std_ss [] ],
      (* goal 2 (of 2) *)
      FULL_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] \\
      PROVE_TAC [] ]);

val INFINITE_KLOP_EXISTS_LEMMA = store_thm ((* NEW *)
   "INFINITE_KLOP_EXISTS_LEMMA",
  ``!(a :'b Label) (A :('a, 'b) CCS set).
     ?(n :('a, 'b) CCS set ordinal). (!x. x IN A ==> ~(WEAK_EQUIV x (Klop a n)))``,
    REPEAT STRIP_TAC
 >> MP_TAC (INST_TYPE [``:'a`` |-> ``:('a, 'b) CCS set``] univ_ord_greater_cardinal)
 >> RW_TAC std_ss [cardleq_def, INJ_DEF, IN_UNIV]
 >> CCONTR_TAC
 >> FIRST_X_ASSUM
	(Q.SPEC_THEN `\n. if n < omega then INL (@m. &m = n)
			  else INR { x | x IN A /\ WEAK_EQUIV x (Klop a n) }` MP_TAC)
 >> BETA_TAC
 >> REPEAT STRIP_TAC
 >> Cases_on `x < omega` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      FULL_SIMP_TAC std_ss [] \\
      PAT_X_ASSUM ``(@m. &m = x) = @m. &m = y`` MP_TAC \\
      REWRITE_TAC [] \\
      NTAC 2 SELECT_ELIM_TAC \\
      REPEAT STRIP_TAC >| (* 3 sub-goals here *)
      [ (* goal 1.1 (of 3) *)
        Q.PAT_X_ASSUM `y < omega` (ASSUME_TAC o (REWRITE_RULE [lt_omega])) \\
        PROVE_TAC [],
        (* goal 1.2 (of 3) *)
        Q.PAT_X_ASSUM `x < omega` (ASSUME_TAC o (REWRITE_RULE [lt_omega])) \\
        PROVE_TAC [],
        (* goal 1.3 (of 3) *)
        FULL_SIMP_TAC std_ss [] ],
      (* goal 2 (of 2) *)
      FULL_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] \\
      `?z. z IN A /\ WEAK_EQUIV z (Klop a x)` by PROVE_TAC [] \\
      RES_TAC \\
      `WEAK_EQUIV (Klop a x) z` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      IMP_RES_TAC WEAK_EQUIV_TRANS \\
      NTAC 3 (POP_ASSUM K_TAC) \\
      `x < y \/ y < x` by PROVE_TAC [ordlt_trichotomy] >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        IMP_RES_TAC Klop_PROP2',
        (* goal 2.2 (of 2) *)
        IMP_RES_TAC WEAK_EQUIV_SYM \\
        IMP_RES_TAC Klop_PROP2' ] ]);

(* The full version of Klop's Lemma *)
val KLOP_LEMMA = store_thm ((* NEW *)
   "KLOP_LEMMA",
  ``!p q. ?k. STABLE k /\ (!p' u. WEAK_TRANS p u p' ==> ~(WEAK_EQUIV p' k)) /\
			  (!q' u. WEAK_TRANS q u q' ==> ~(WEAK_EQUIV q' k))``,
    REPEAT STRIP_TAC
 >> Q.ABBREV_TAC `nodes = (NODES p) UNION (NODES q)`
 >> Cases_on `FINITE nodes` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC KLOP_LEMMA_FINITE \\
      `FINITE (NODES p) /\ FINITE (NODES q)` by PROVE_TAC [FINITE_UNION] \\
      PROVE_TAC [FINITE_STATE_def],
      (* goal 2 (of 2) *)
      Q.ABBREV_TAC `a = (ARB :'b Label)` \\
      ASSUME_TAC (Q.SPECL [`a`, `nodes`] INFINITE_KLOP_EXISTS_LEMMA) \\
      POP_ASSUM MP_TAC >> STRIP_TAC \\
      Q.EXISTS_TAC `Klop a n` \\
      REWRITE_TAC [Klop_PROP0] \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        `!x. x IN (NODES p) ==> ~(WEAK_EQUIV x (Klop a n))` by PROVE_TAC [IN_UNION] \\
        REPEAT STRIP_TAC \\
        IMP_RES_TAC WEAK_TRANS_IN_NODES \\
        PROVE_TAC [],
        (* goal 2.2 (of 2) *)
        `!x. x IN (NODES q) ==> ~(WEAK_EQUIV x (Klop a n))` by PROVE_TAC [IN_UNION] \\
        REPEAT STRIP_TAC \\
        IMP_RES_TAC WEAK_TRANS_IN_NODES \\
        PROVE_TAC [] ] ]);

(* A stronger version of COARSEST_CONGR_THM from [vGl05], without any assumption.
   Noticed that, HOL type system automatically guarantees that any type must have
   at least one instance, so there's always at least one action a IN Act - {tau},
   no matter what Act type 'b is there.
 *)
val COARSEST_CONGR_RL_FULL = store_thm ((* NEW *)
   "COARSEST_CONGR_RL_FULL",
  ``!p q. (!r. WEAK_EQUIV (sum p r) (sum q r)) ==> OBS_CONGR p q``,
    REPEAT STRIP_TAC
 >> MP_TAC (Q.SPECL [`p`, `q`] KLOP_LEMMA)
 >> RW_TAC std_ss [PROP3_COMMON]);

val COARSEST_CONGR_FULL = store_thm ((* NEW *)
   "COARSEST_CONGR_FULL",
  ``!p q. OBS_CONGR p q = !r. WEAK_EQUIV (sum p r) (sum q r)``,
    REPEAT STRIP_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >- REWRITE_TAC [COARSEST_CONGR_LR]
 >> REWRITE_TAC [COARSEST_CONGR_RL_FULL]);

(* OBS_CONGR coincides with SUM_EQUIV *)
val OBS_CONGR_IS_SUM_EQUIV = store_thm ((* NEW *)
   "OBS_CONGR_IS_SUM_EQUIV", ``OBS_CONGR = SUM_EQUIV``,
    REWRITE_TAC [FUN_EQ_THM]
 >> REPEAT GEN_TAC
 >> REWRITE_TAC [SUM_EQUIV]
 >> BETA_TAC
 >> REWRITE_TAC [COARSEST_CONGR_FULL]);

(* OBS_CONGR coincides with WEAK_CONGR, thus is indeed the coarsest congruence
   contained in WEAK_EQUIV, there's no other in the middle!
 *)
val OBS_CONGR_IS_WEAK_CONGR = store_thm ((* NEW *)
   "OBS_CONGR_IS_WEAK_CONGR", ``OBS_CONGR = WEAK_CONGR``,
    REWRITE_TAC [FUN_EQ_THM]
 >> REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >- REWRITE_TAC [OBS_CONGR_IMP_WEAK_CONGR]
 >> REWRITE_TAC [OBS_CONGR_IS_SUM_EQUIV]
 >> REWRITE_TAC [WEAK_CONGR_IMP_SUM_EQUIV]);

(** Bibliography:

[Den07] Y. Deng, “A simple completeness proof for the axiomatisations of weak behavioural
    equivalences”, Bulletin of the EATCS, 93:207-219, 2007.

[Mil89] R. Milner, Communication and Concurrency, Prentice-Hall, 1989.

[vGl05] R.J. van Glabbeek, “A characterisation of weak bisimulation congruence”, in Processes,
    Terms and Cycles: Steps on the Road to Infinity, Essays dedicated to Jan Willem Klop, on the
    occasion of his 60th birthday, LNCS 3838, 26-39. Springer-Verlag, 2005.
 *)

val _ = export_theory ();
val _ = html_theory "CoarsestCongr2";

(* last updated: Jun 24, 2017 *)
