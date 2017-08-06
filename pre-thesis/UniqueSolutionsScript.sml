(*
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pairTheory sumTheory listTheory;
open prim_recTheory arithmeticTheory combinTheory;

open CCSLib CCSTheory CCSSyntax CCSConv;
open StrongEQTheory StrongEQLib StrongLawsTheory StrongLawsConv;
open WeakEQTheory WeakEQLib WeakLawsTheory WeakLawsConv;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory ObsCongrConv;
open BisimulationUptoTheory;
open CoarsestCongrTheory;

(* this file contains the theorems of "unique solutions of equations" in CCS *)
val _ = new_theory "UniqueSolutions";

(******************************************************************************)
(*                                                                            *)
(*              CCS expressions and weakly guarded expressions                *)
(*                                                                            *)
(******************************************************************************)

(* Weakly guarded (WG) expressions *)
val (WG_rules, WG_ind, WG_cases) = Hol_reln `
    (!a.                            WG (\t. prefix a t)) /\          (* WG1 *)
    (!p.                            WG (\t. p)) /\                   (* WG2 *)
    (!a e.   WG e               ==> WG (\t. prefix a (e t))) /\      (* WG3 *)
    (!e1 e2. WG e1 /\ WG e2     ==> WG (\t. sum (e1 t) (e2 t))) /\   (* WG4 *)
    (!e1 e2. WG e1 /\ WG e2     ==> WG (\t. par (e1 t) (e2 t))) /\   (* WG5 *)
    (!L e.   WG e               ==> WG (\t. restr L (e t))) /\       (* WG6 *)
    (!rf e.  WG e               ==> WG (\t. relab (e t) rf)) `;      (* WG7 *)
(*
    (!X e.   WG e            ==> WG (\t. rec X (e t))) `;            (* WG8 *)
 *)

val [WG1, WG2, WG3, WG4, WG5, WG6, WG7 (*, WG8 *)] =
    map save_thm
        (combine (["WG1", "WG2", "WG3", "WG4",
		   "WG5", "WG6", "WG7" (*, "WG8" *)], CONJUNCTS WG_rules));

(* Expressions = multi-hole (or non-hole) contexts. *)
val (EXPR_rules, EXPR_ind, EXPR_cases) = Hol_reln `
    (                               EXPR (\t. t)) /\                 (* EXPR1 *)
    (!p.                            EXPR (\t. p)) /\                 (* EXPR2 *)
    (!a e.   EXPR e             ==> EXPR (\t. prefix a (e t))) /\    (* EXPR3 *)
    (!e1 e2. EXPR e1 /\ EXPR e2 ==> EXPR (\t. sum (e1 t) (e2 t))) /\ (* EXPR4 *)
    (!e1 e2. EXPR e1 /\ EXPR e2 ==> EXPR (\t. par (e1 t) (e2 t))) /\ (* EXPR5 *)
    (!L e.   EXPR e             ==> EXPR (\t. restr L (e t))) /\     (* EXPR6 *)
    (!rf e.  EXPR e             ==> EXPR (\t. relab (e t) rf)) `;    (* EXPR7 *)
(*
    (!X e.   EXPR e             ==> EXPR (\t. rec X (e t))) `;       (* EXPR8 *)
 *)

val [EXPR1, EXPR2, EXPR3, EXPR4, EXPR5, EXPR6, EXPR7 (*, EXPR8*)] =
    map save_thm
        (combine (["EXPR1", "EXPR2", "EXPR3", "EXPR4", "EXPR5", "EXPR6", "EXPR7"(*, "EXPR8"*)],
                  CONJUNCTS EXPR_rules));

val EXPR3a = store_thm ("EXPR3a",
  ``!a :'b Action. EXPR (\t. prefix a t)``,
    ASSUME_TAC EXPR1
 >> IMP_RES_TAC EXPR3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

(* One-hole contexts are also expressions *)
val CONTEXT_IS_EXPR = store_thm (
   "CONTEXT_IS_EXPR", ``!c. CONTEXT c ==> EXPR c``,
    Induct_on `CONTEXT`
 >> rpt STRIP_TAC (* 8 sub-goals here *)
 >| [ (* goal 1 (of 8) *)
      REWRITE_TAC [EXPR1],
      (* goal 2 (of 8) *)
      MATCH_MP_TAC EXPR3 >> ASM_REWRITE_TAC [],
      (* goal 3 (of 8) *)
      `EXPR (\y. x)` by REWRITE_TAC [EXPR2] \\
      Know `EXPR (\t. c t + (\y. x) t)`
      >- ( MATCH_MP_TAC EXPR4 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 4 (of 8) *)
      `EXPR (\y. x)` by REWRITE_TAC [EXPR2] \\
      Know `EXPR (\t. (\y. x) t + c t)`
      >- ( MATCH_MP_TAC EXPR4 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 5 (of 8) *)
      `EXPR (\y. x)` by REWRITE_TAC [EXPR2] \\
      Know `EXPR (\t. c t || (\y. x) t)`
      >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 6 (of 8) *)
      `EXPR (\y. x)` by REWRITE_TAC [EXPR2] \\
      Know `EXPR (\t. (\y. x) t || c t)`
      >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 7 (of 8) *)
      MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [],
      (* goal 8 (of 8) *)
      MATCH_MP_TAC EXPR7 >> ASM_REWRITE_TAC [] ]);

(* Weakly guarded expressions are also expressions *)
val WG_IS_EXPR = store_thm (
   "WG_IS_EXPR", ``!e. WG e ==> EXPR e``,
    Induct_on `WG`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- REWRITE_TAC [EXPR3a]
 >- REWRITE_TAC [EXPR2]
 >| [ MATCH_MP_TAC EXPR3,
      MATCH_MP_TAC EXPR4,
      MATCH_MP_TAC EXPR5,
      MATCH_MP_TAC EXPR6,
      MATCH_MP_TAC EXPR7 (*, MATCH_MP_TAC EXPR8 *) ]
 >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*                 Unique solutions theorem for STRONG_EQUIV                  *)
(*                                                                            *)
(******************************************************************************)

(* Lemma 4.13 (single variable version):
   If the variable X is weakly guarded in E, and E{P/X} --a-> P', then P' takes the form
   E'{P/X} (for some expression E'), and moreover, for any Q, E{Q/X} --a-> E'{Q/X}.
 *)
val STRONG_UNIQUE_SOLUTIONS_LEMMA = store_thm (
   "STRONG_UNIQUE_SOLUTIONS_LEMMA",
  ``!E. WG E ==>
	!P a P'. TRANS (E P) a P' ==>
		 ?E'. EXPR E' /\ (P' = E' P) /\ !Q. TRANS (E Q) a (E' Q)``,
    Induct_on `WG` >> BETA_TAC
 >> COUNT_TAC (rpt STRIP_TAC) (* 8 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      IMP_RES_TAC TRANS_PREFIX \\
      ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `\x. x` \\
      ASM_REWRITE_TAC [EXPR1] \\
      BETA_TAC >> ASM_REWRITE_TAC [PREFIX],
      (* goal 2 (of 7) *)
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
      Q.EXISTS_TAC `\t. P'` >> BETA_TAC \\
      ASM_REWRITE_TAC [EXPR2] >| (* 10 sub-goals here *)
      [ REWRITE_TAC [PREFIX],
        MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l` >> FULL_SIMP_TAC std_ss [],
        MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l` >> FULL_SIMP_TAC std_ss [],
        MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC REC >> ASM_REWRITE_TAC [] ],
      (* goal 3 (of 7) *)
      IMP_RES_TAC TRANS_PREFIX \\
      ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E` >> REWRITE_TAC [] \\
      CONJ_TAC >- IMP_RES_TAC WG_IS_EXPR \\
      REWRITE_TAC [PREFIX],
      (* goal 4 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        (* goal 4.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ],
      (* goal 5 (of 7) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 5.1 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E'' t) (E' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 5.1.1 (of 2) *)
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WG_IS_EXPR,
          (* goal 5.1.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [] ],
        (* goal 5.2 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E t) (E'' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 5.2.1 (of 2) *)
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WG_IS_EXPR,
          (* goal 5.2.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [] ],
        (* goal 5.3 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E''' t) (E'' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 5.3.1 (of 2) *)
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [],
          (* goal 5.3.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR3 \\
          Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ] ],
      (* goal 6 (of 7) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 6.1 (of 2) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. restr L (E' t)` >> BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >- ( MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [] ) \\
        GEN_TAC >> MATCH_MP_TAC RESTR \\
        FULL_SIMP_TAC std_ss [] \\
        PROVE_TAC [],
        (* goal 6.2 (of 2) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. restr L (E' t)` >> BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >- ( MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [] ) \\
        GEN_TAC >> MATCH_MP_TAC RESTR \\
        Q.EXISTS_TAC `l` >> FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        PROVE_TAC [] ],
      (* goal 7 (of 7) *)
      IMP_RES_TAC TRANS_RELAB \\
      RES_TAC >> FULL_SIMP_TAC std_ss [] \\
      Q.EXISTS_TAC `\t. relab (E' t) rf` >> BETA_TAC >> REWRITE_TAC [] \\
      CONJ_TAC >- ( MATCH_MP_TAC EXPR7 >> ASM_REWRITE_TAC [] ) \\
      GEN_TAC >> MATCH_MP_TAC RELABELING \\
      ASM_REWRITE_TAC [] ]);

(* Proposition 3.14 (2):
   Let the expression E contains at most the variable X, and let X be weakly guarded in
   each E. Then
       If P ~ E{P/X} and Q ~ E{Q/X} then P ~ Q.
 *)
val STRONG_UNIQUE_SOLUTIONS = store_thm (
   "STRONG_UNIQUE_SOLUTIONS",
  ``!E. WG E ==>
	!P Q. STRONG_EQUIV P (E P) /\ STRONG_EQUIV Q (E Q) ==> STRONG_EQUIV P Q``,
    rpt STRIP_TAC
 >> irule (REWRITE_RULE [RSUBSET] STRONG_BISIM_UPTO_THM)
 >> Q.EXISTS_TAC `\x y. (x = y) \/ (?G. EXPR G /\ (x = G P) /\ (y = G Q))`
 >> BETA_TAC >> REVERSE CONJ_TAC
 >- ( DISJ2_TAC >> Q.EXISTS_TAC `\x. x` >> BETA_TAC \\
      KILL_TAC >> RW_TAC std_ss [EXPR1] )
 >> REWRITE_TAC [STRONG_BISIM_UPTO]
 >> Q.X_GEN_TAC `P'`
 >> Q.X_GEN_TAC `Q'`
 >> BETA_TAC >> STRIP_TAC (* 2 sub-goals here *)
 >- ( ASM_REWRITE_TAC [] >> rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 1 (of 2) *)
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
        REWRITE_TAC [O_DEF] \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
        BETA_TAC >> DISJ1_TAC >> RW_TAC std_ss [],
        (* goal 2 (of 2) *)
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
        REWRITE_TAC [O_DEF] \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
        BETA_TAC >> DISJ1_TAC >> RW_TAC std_ss [] ] )
 >> ASM_REWRITE_TAC []
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`G`, `G`)
 >> COUNT_TAC (Induct_on `EXPR` >> BETA_TAC >> rpt STRIP_TAC) (* 14 sub-goals here *)
 >| [ (* goal 1 (of 14) *)
      Q.PAT_X_ASSUM `STRONG_EQUIV P (E P)`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      RES_TAC \\
      IMP_RES_TAC STRONG_UNIQUE_SOLUTIONS_LEMMA \\ (* lemma used here *)
      FULL_SIMP_TAC std_ss [] \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      Q.PAT_X_ASSUM `STRONG_EQUIV Q (E Q)`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      RES_TAC \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] \\
      `STRONG_EQUIV (E' Q) E1'` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      Q.EXISTS_TAC `E' Q` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E' P` >> ASM_REWRITE_TAC [] \\
      BETA_TAC >> DISJ2_TAC \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 14) *)
      Q.PAT_X_ASSUM `STRONG_EQUIV Q (E Q)`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      RES_TAC \\
      IMP_RES_TAC STRONG_UNIQUE_SOLUTIONS_LEMMA \\ (* lemma used here *)
      FULL_SIMP_TAC std_ss [] \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      Q.PAT_X_ASSUM `STRONG_EQUIV P (E P)`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      RES_TAC \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] \\
      `STRONG_EQUIV (E' P) E1` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      `STRONG_EQUIV (E' Q) E2` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      Q.EXISTS_TAC `E' Q` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E' P` >> ASM_REWRITE_TAC [] \\
      BETA_TAC >> DISJ2_TAC \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [],

      (* goal 3 (of 14) *)
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
      BETA_TAC >> DISJ1_TAC >> RW_TAC std_ss [],
      (* goal 4 (of 14) *)
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
      BETA_TAC >> DISJ1_TAC >> RW_TAC std_ss [],

      (* goal 5 (of 14) *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G Q` >> REWRITE_TAC [PREFIX] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `G Q` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `G P` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      DISJ2_TAC >> Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [],
      (* goal 6 (of 14) *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G P` >> REWRITE_TAC [PREFIX] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `G Q` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `G P` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      DISJ2_TAC >> Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [],

      (* goal 7 (of 14) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 7.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [] ) \\
        ASM_REWRITE_TAC [],
        (* goal 7.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ) \\
        ASM_REWRITE_TAC [] ],
      (* goal 8 (of 14) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 8.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E1` \\
        CONJ_TAC >- ( MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [] ) \\
        ASM_REWRITE_TAC [],
        (* goal 8.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E1` \\
        CONJ_TAC >- ( MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ) \\
        ASM_REWRITE_TAC [] ],

      (* goal 9 (of 14) *)
      IMP_RES_TAC TRANS_PAR >> FULL_SIMP_TAC std_ss [] >| (* 3 sub-goals here *)
      [ (* goal 9.1 (of 3) *)
        Q.PAT_X_ASSUM `E1 = X` K_TAC \\
        RES_TAC \\
        Q.EXISTS_TAC `E2 || G' Q` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 9.1.1 (of 2) *)
          Q.EXISTS_TAC `y || G' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `y || G' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. y || G' t` >> BETA_TAC >> REWRITE_TAC [] \\
          `EXPR (\z. y)` by REWRITE_TAC [EXPR2] \\
          Know `EXPR (\t. (\z. y) t || G' t)`
          >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 9.1.2 (of 2) *)
          Q.EXISTS_TAC `G'' Q || G' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G'' P || G' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || G' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ],
        (* goal 9.2 (of 3) *)
        Q.PAT_X_ASSUM `E1 = X` K_TAC \\
        RES_TAC \\
        Q.EXISTS_TAC `G Q || E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 9.2.1 (of 2) *)
          Q.EXISTS_TAC `G Q || y` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G P || y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G t || y` >> BETA_TAC >> REWRITE_TAC [] \\
          `EXPR (\z. y)` by REWRITE_TAC [EXPR2] \\
          Know `EXPR (\t. G t || (\z. y) t)`
          >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 9.2.2 (of 2) *)
          Q.EXISTS_TAC `G Q || G'' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G P || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G t || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ],
        (* goal 9.3 (of 3) *)
        Q.PAT_X_ASSUM `E1 = X` K_TAC \\
        Q.PAT_X_ASSUM `u = tau` K_TAC \\
        RES_TAC \\
        Q.EXISTS_TAC `E2'' || E2'` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ) \\
        Q.PAT_X_ASSUM `X E2 E2'` MP_TAC \\
        Q.PAT_X_ASSUM `X E1' E2''` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 4 sub-goals here *)
        [ (* goal 9.3.1 (of 4) *)
          Q.EXISTS_TAC `y || y''` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `y || y''` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 9.3.2 (of 4) *)
          Q.EXISTS_TAC `y || G'' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `y || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. y || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          `EXPR (\z. y)` by REWRITE_TAC [EXPR2] \\
          Know `EXPR (\t. (\z. y) t || G'' t)`
          >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 9.3.3 (of 4) *)
          Q.EXISTS_TAC `G'' Q || y''` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `G'' P || y''` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || y''` >> BETA_TAC >> REWRITE_TAC [] \\
          `EXPR (\z. y'')` by REWRITE_TAC [EXPR2] \\
          Know `EXPR (\t. G'' t || (\z. y'') t)`
          >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 9.3.4 (of 4) *)
          Q.EXISTS_TAC `G'' Q || G''' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `G'' P || G''' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || G''' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ] ],
      (* goal 10 (of 14) *)
      IMP_RES_TAC TRANS_PAR >> FULL_SIMP_TAC std_ss [] >| (* 3 sub-goals here *)
      [ (* goal 10.1 (of 3) *)
        Q.PAT_X_ASSUM `E2 = X` K_TAC \\
        RES_TAC \\
        Q.EXISTS_TAC `E1' || G' P` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 10.1.1 (of 2) *)
          Q.EXISTS_TAC `y || G' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `y || G' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. y || G' t` >> BETA_TAC >> REWRITE_TAC [] \\
          `EXPR (\z. y)` by REWRITE_TAC [EXPR2] \\
          Know `EXPR (\t. (\z. y) t || G' t)`
          >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 10.1.2 (of 2) *)
          Q.EXISTS_TAC `G'' Q || G' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G'' P || G' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || G' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ],
        (* goal 10.2 (of 3) *)
        Q.PAT_X_ASSUM `E2 = X` K_TAC \\
        RES_TAC \\
        Q.EXISTS_TAC `G P || E1'` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 10.2.1 (of 2) *)
          Q.EXISTS_TAC `G Q || y` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G P || y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G t || y` >> BETA_TAC >> REWRITE_TAC [] \\
          `EXPR (\z. y)` by REWRITE_TAC [EXPR2] \\
          Know `EXPR (\t. G t || (\z. y) t)`
          >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 10.2.2 (of 2) *)
          Q.EXISTS_TAC `G Q || G'' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G P || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G t || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ],
        (* goal 10.3 (of 3) *)
        Q.PAT_X_ASSUM `E2 = X` K_TAC \\
        Q.PAT_X_ASSUM `u = tau` K_TAC \\
        RES_TAC \\
        Q.EXISTS_TAC `E1'' || E1'` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ) \\
        Q.PAT_X_ASSUM `X E1'' E1` MP_TAC \\
        Q.PAT_X_ASSUM `X E1' E2'` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 4 sub-goals here *)
        [ (* goal 10.3.1 (of 4) *)
          Q.EXISTS_TAC `y'' || y` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `y'' || y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 10.3.2 (of 4) *)
          Q.EXISTS_TAC `G'' Q || y` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `G'' P || y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || y` >> BETA_TAC >> REWRITE_TAC [] \\
          `EXPR (\z. y)` by REWRITE_TAC [EXPR2] \\
          Know `EXPR (\t. G'' t || (\z. y) t)`
          >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 10.3.3 (of 4) *)
          Q.EXISTS_TAC `y'' || G'' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `y'' || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. y'' || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          `EXPR (\z. y'')` by REWRITE_TAC [EXPR2] \\
          Know `EXPR (\t. (\z. y'') t || G'' t)`
          >- ( MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 10.3.4 (of 4) *)
          Q.EXISTS_TAC `G''' Q || G'' Q` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `G''' P || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G''' t || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] ] ],

      (* goal 11 (of 14) *)
      IMP_RES_TAC TRANS_RESTR >> FULL_SIMP_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 11.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> FULL_SIMP_TAC std_ss [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 11.1.1 (of 2) *)
          Q.EXISTS_TAC `restr L y` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 11.1.2 (of 2) *)
          Q.EXISTS_TAC `restr L (G' Q)` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L (G' P)` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. restr L (G' t)` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [] ],
        (* goal 11.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 11.2.1 (of 2) *)
          Q.EXISTS_TAC `restr L y` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 11.2.2 (of 2) *)
          Q.EXISTS_TAC `restr L (G' Q)` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L (G' P)` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. restr L (G' t)` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [] ] ],
      (* goal 12 (of 14) *)
      IMP_RES_TAC TRANS_RESTR >> FULL_SIMP_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 12.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E1` \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> FULL_SIMP_TAC std_ss [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 12.1.1 (of 2) *)
          Q.EXISTS_TAC `restr L y` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 12.1.2 (of 2) *)
          Q.EXISTS_TAC `restr L (G' Q)` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L (G' P)` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. restr L (G' t)` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [] ],
        (* goal 12.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E1` \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 12.2.1 (of 2) *)
          Q.EXISTS_TAC `restr L y` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 12.2.2 (of 2) *)
          Q.EXISTS_TAC `restr L (G' Q)` \\
          REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L (G' P)` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. restr L (G' t)` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [] ] ],

      (* goal 13 (of 14) *)
      IMP_RES_TAC TRANS_RELAB \\
      FULL_SIMP_TAC std_ss [] \\
      RES_TAC \\
      Q.EXISTS_TAC `relab E2 rf` \\
      CONJ_TAC >- ( MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [] ) \\
      POP_ASSUM MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 13.1 (of 2) *)
        Q.EXISTS_TAC `relab y rf` \\
        REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
			      ASM_REWRITE_TAC [] ) \\
        Q.EXISTS_TAC `relab y rf` \\
        CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
        DISJ1_TAC >> REWRITE_TAC [],
        (* goal 13.2 (of 2) *)
        Q.EXISTS_TAC `relab (G' Q) rf` \\
        REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
			      ASM_REWRITE_TAC [] ) \\
        Q.EXISTS_TAC `relab (G' P) rf` \\
        CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
        DISJ2_TAC \\
        Q.EXISTS_TAC `\t. relab (G' t) rf` >> BETA_TAC >> REWRITE_TAC [] \\
        MATCH_MP_TAC EXPR7 >> ASM_REWRITE_TAC [] ],
      (* goal 14 (of 14) *)
      IMP_RES_TAC TRANS_RELAB \\
      FULL_SIMP_TAC std_ss [] \\
      RES_TAC \\
      Q.EXISTS_TAC `relab E1 rf` \\
      CONJ_TAC >- ( MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [] ) \\
      POP_ASSUM MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 14.1 (of 2) *)
        Q.EXISTS_TAC `relab y rf` \\
        REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
			      ASM_REWRITE_TAC [] ) \\
        Q.EXISTS_TAC `relab y rf` \\
        CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
        DISJ1_TAC >> REWRITE_TAC [],
        (* goal 14.2 (of 2) *)
        Q.EXISTS_TAC `relab (G' Q) rf` \\
        REVERSE CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
			      ASM_REWRITE_TAC [] ) \\
        Q.EXISTS_TAC `relab (G' P) rf` \\
        CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
        DISJ2_TAC \\
        Q.EXISTS_TAC `\t. relab (G' t) rf` >> BETA_TAC >> REWRITE_TAC [] \\
        MATCH_MP_TAC EXPR7 >> ASM_REWRITE_TAC [] ] ]);

(* Bibliography:
 *
 * [1] Milner, R.: Communication and concurrency. (1989).
.* [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer, Cham (2015).
 * [3] Sangiorgi, D.: Introduction to Bisimulation and Coinduction. Cambridge University Press (2011).
 * [4] Sangiorgi, D., Rutten, J.: Advanced Topics in Bisimulation and Coinduction.
				  Cambridge University Press (2011).
 * [5] Sangiorgi, D.: Equations, contractions, and unique solutions. ACM SIGPLAN Notices. (2015).
 *)

val _ = export_theory ();
val _ = print_theory_to_file "-" "UniqueSolutions.lst";
val _ = DB.html_theory "UniqueSolutions";

(* last updated: Aug 3, 2017 *)
