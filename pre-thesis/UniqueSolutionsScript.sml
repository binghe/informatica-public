(*
 * A formalization of unique solutions of equations in process algebra
 *
 * Copyright 2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pairTheory sumTheory listTheory;
open prim_recTheory arithmeticTheory combinTheory;

open CCSLib CCSTheory;
open StrongEQTheory StrongEQLib StrongLawsTheory;
open WeakEQTheory WeakEQLib WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory;
open BisimulationUptoTheory;
open CoarsestCongrTheory;

val _ = new_theory "UniqueSolutions";

(******************************************************************************)
(*                                                                            *)
(*              CCS expressions and weakly guarded expressions                *)
(*                                                                            *)
(******************************************************************************)

(* Expressions = multi-hole (or non-hole) contexts. *)
val (EXPR_rules, EXPR_ind, EXPR_cases) = Hol_reln `
    (                               EXPR (\t. t)) /\                 (* EXPR1 *)
    (!p.                            EXPR (\t. p)) /\                 (* EXPR2 *)
    (!a e.   EXPR e             ==> EXPR (\t. prefix a (e t))) /\    (* EXPR3 *)
    (!e1 e2. EXPR e1 /\ EXPR e2 ==> EXPR (\t. sum (e1 t) (e2 t))) /\ (* EXPR4 *)
    (!e1 e2. EXPR e1 /\ EXPR e2 ==> EXPR (\t. par (e1 t) (e2 t))) /\ (* EXPR5 *)
    (!L e.   EXPR e             ==> EXPR (\t. restr L (e t))) /\     (* EXPR6 *)
    (!rf e.  EXPR e             ==> EXPR (\t. relab (e t) rf)) `;    (* EXPR7 *)

val [EXPR1, EXPR2, EXPR3, EXPR4, EXPR5, EXPR6, EXPR7] =
    map save_thm
        (combine (["EXPR1", "EXPR2", "EXPR3", "EXPR4", "EXPR5", "EXPR6", "EXPR7"],
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

val STRONG_EQUIV_SUBST_EXPR = store_thm (
   "STRONG_EQUIV_SUBST_EXPR",
  ``!P Q. STRONG_EQUIV P Q ==> !E. EXPR E ==> STRONG_EQUIV (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `EXPR` >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [STRONG_EQUIV_REFL]
 >| [ (* goal 1 (of 5) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 2 (of 5) *)
      IMP_RES_TAC STRONG_EQUIV_PRESD_BY_SUM,
      (* goal 3 (of 5) *)
      IMP_RES_TAC STRONG_EQUIV_PRESD_BY_PAR,
      (* goal 4 (of 5) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [],
      (* goal 5 (of 5) *)
      MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ]);

val OBS_CONGR_SUBST_EXPR = store_thm (
   "OBS_CONGR_SUBST_EXPR",
  ``!P Q. OBS_CONGR P Q ==> !E. EXPR E ==> OBS_CONGR (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `EXPR` >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [OBS_CONGR_REFL]
 >| [ (* goal 1 (of 5) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 2 (of 5) *)
      IMP_RES_TAC OBS_CONGR_PRESD_BY_SUM,
      (* goal 3 (of 5) *)
      IMP_RES_TAC OBS_CONGR_PRESD_BY_PAR,
      (* goal 4 (of 5) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_RESTR >> ASM_REWRITE_TAC [],
      (* goal 5 (of 5) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_RELAB >> ASM_REWRITE_TAC [] ]);

(* Weakly guarded (WG) expressions *)
val (WG_rules, WG_ind, WG_cases) = Hol_reln `
    (!p.                            WG (\t. p)) /\                   (* WG2 *)
    (!a e.   EXPR e             ==> WG (\t. prefix a (e t))) /\      (* WG3 *)
    (!e1 e2. WG e1 /\ WG e2     ==> WG (\t. sum (e1 t) (e2 t))) /\   (* WG4 *)
    (!e1 e2. WG e1 /\ WG e2     ==> WG (\t. par (e1 t) (e2 t))) /\   (* WG5 *)
    (!L e.   WG e               ==> WG (\t. restr L (e t))) /\       (* WG6 *)
    (!rf e.  WG e               ==> WG (\t. relab (e t) rf)) `;      (* WG7 *)

val [WG2, WG3, WG4, WG5, WG6, WG7] =
    map save_thm
        (combine (["WG2", "WG3", "WG4", "WG5", "WG6", "WG7"], CONJUNCTS WG_rules));

(** WG1 is derivable from WG3 *)
val WG1 = store_thm ("WG1",
  ``!a :'b Action. WG (\t. prefix a t)``,
    ASSUME_TAC EXPR1
 >> IMP_RES_TAC WG3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC
 >> REWRITE_TAC []);

(* Weakly guarded expressions are also expressions *)
val WG_IS_EXPR = store_thm (
   "WG_IS_EXPR", ``!e. WG e ==> EXPR e``,
    Induct_on `WG`
 >> rpt STRIP_TAC (* 6 sub-goals here *)
 >| [ REWRITE_TAC [EXPR2],
      MATCH_MP_TAC EXPR3 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR4 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR7 >> ASM_REWRITE_TAC [] ]);

(******************************************************************************)
(*                                                                            *)
(*             Milner's unique solutions theorem for STRONG_EQUIV             *)
(*                                                                            *)
(******************************************************************************)

(* Lemma 4.13 in Milner's book [1]:
   If the variable X is weakly guarded in E, and E{P/X} --a-> P', then P' takes the form
   E'{P/X} (for some expression E'), and moreover, for any Q, E{Q/X} --a-> E'{Q/X}.
 *)
val STRONG_UNIQUE_SOLUTIONS_LEMMA = store_thm (
   "STRONG_UNIQUE_SOLUTIONS_LEMMA",
  ``!E. WG E ==>
	!P a P'. TRANS (E P) a P' ==>
		 ?E'. EXPR E' /\ (P' = E' P) /\ !Q. TRANS (E Q) a (E' Q)``,
    Induct_on `WG` >> BETA_TAC
 >> COUNT_TAC (rpt STRIP_TAC) (* 6 sub-goals here *)
 >| [ (* goal 1 (of 6) *)
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
      (* goal 2 (of 6) *)
      IMP_RES_TAC TRANS_PREFIX \\
      ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `e` \\
      ASM_REWRITE_TAC [PREFIX],
      (* goal 3 (of 6) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ],
      (* goal 4 (of 6) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 4.1 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E'' t) (E' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.1.1 (of 2) *)
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WG_IS_EXPR,
          (* goal 4.1.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [] ],
        (* goal 4.2 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E t) (E'' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.2.1 (of 2) *)
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WG_IS_EXPR,
          (* goal 4.2.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [] ],
        (* goal 4.3 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E''' t) (E'' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.3.1 (of 2) *)
          MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [],
          (* goal 4.3.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR3 \\
          Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ] ],
      (* goal 5 (of 6) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. restr L (E' t)` >> BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >- ( MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [] ) \\
        GEN_TAC >> MATCH_MP_TAC RESTR \\
        FULL_SIMP_TAC std_ss [] \\
        PROVE_TAC [],
        (* goal 5.2 (of 2) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. restr L (E' t)` >> BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >- ( MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [] ) \\
        GEN_TAC >> MATCH_MP_TAC RESTR \\
        Q.EXISTS_TAC `l` >> FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        PROVE_TAC [] ],
      (* goal 6 (of 6) *)
      IMP_RES_TAC TRANS_RELAB \\
      RES_TAC >> FULL_SIMP_TAC std_ss [] \\
      Q.EXISTS_TAC `\t. relab (E' t) rf` >> BETA_TAC >> REWRITE_TAC [] \\
      CONJ_TAC >- ( MATCH_MP_TAC EXPR7 >> ASM_REWRITE_TAC [] ) \\
      GEN_TAC >> MATCH_MP_TAC RELABELING \\
      ASM_REWRITE_TAC [] ]);

(* Proposition 3.14 in Milner's book [1]:
   Let the expression E contains at most the variable X, and let X be weakly guarded in E,
   then:
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

(******************************************************************************)
(*                                                                            *)
(*             Milner's unique solutions theorem for OBS_CONGR                *)
(*                                                                            *)
(******************************************************************************)

(* (Strongly) guarded (SG) expressions:
   X is guarded in E if each occurrence of X is within some subexpression of E of
   the form l.F *)
val (SG_rules, SG_ind, SG_cases) = Hol_reln `
    (!p.                        SG (\t. p)) /\                      (* SG1 *)
    (!l e.   EXPR e         ==> SG (\t. prefix (label l) (e t))) /\ (* SG2 *)
    (!a e.   SG e           ==> SG (\t. prefix a (e t))) /\	    (* SG3 *)
    (!e1 e2. SG e1 /\ SG e2 ==> SG (\t. sum (e1 t) (e2 t))) /\      (* SG4 *)
    (!e1 e2. SG e1 /\ SG e2 ==> SG (\t. par (e1 t) (e2 t))) /\      (* SG5 *)
    (!L e.   SG e           ==> SG (\t. restr L (e t))) /\          (* SG6 *)
    (!rf e.  SG e           ==> SG (\t. relab (e t) rf)) `;         (* SG7 *)

val [SG1, SG2, SG3, SG4, SG5, SG6, SG7] =
    map save_thm
        (combine (["SG1", "SG2", "SG3", "SG4", "SG5", "SG6", "SG7"],
		  CONJUNCTS SG_rules));

(* Strongly guarded expressions are expressions *)
val SG_IS_EXPR = store_thm (
   "SG_IS_EXPR", ``!e. SG e ==> EXPR e``,
    Induct_on `SG`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ REWRITE_TAC [EXPR2],
      MATCH_MP_TAC EXPR3 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR3 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR4 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR5 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR6 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR7 >> ASM_REWRITE_TAC [] ]);

(* Strong guardness implies weak guardness *)
val SG_IMP_WG = store_thm (
   "SG_IMP_WG", ``!e. SG e ==> WG e``,
    Induct_on `SG`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ REWRITE_TAC [WG2],
      MATCH_MP_TAC WG3 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC WG3 >> IMP_RES_TAC WG_IS_EXPR,
      MATCH_MP_TAC WG4 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC WG5 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC WG6 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC WG7 >> ASM_REWRITE_TAC [] ]);

val lemma = Q.prove (`!p :('a, 'b) CCS. ?q. q <> p`,
    Cases_on `p`
 >- ( Q.EXISTS_TAC `nil + nil` >> PROVE_TAC [CCS_distinct'] )
 >> ( Q.EXISTS_TAC `nil` >> PROVE_TAC [CCS_distinct'] ));

(* an important backward property of SG *)
val SG8 = store_thm ("SG8",
  ``!e. SG (\t. prefix tau (e t)) ==> SG e``,
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
      Cases_on `p` >| (* 8 sub-goals here *)
      [ (* goal 1.1 (of 8) *)
        PROVE_TAC [CCS_distinct'],
        (* goal 1.2 (of 8) *)
        PROVE_TAC [CCS_distinct'],
        (* goal 1.3 (of 8) *)
        FULL_SIMP_TAC std_ss [CCS_11] \\
        `e = \t. C'` by PROVE_TAC [] \\
        ASM_REWRITE_TAC [] \\
        REWRITE_TAC [SG1],
        (* goal 1.4 (of 8) *)
        PROVE_TAC [CCS_distinct'],
        (* goal 1.5 (of 8) *)
        PROVE_TAC [CCS_distinct'],
        (* goal 1.6 (of 8) *)
        PROVE_TAC [CCS_distinct'],
        (* goal 1.7 (of 8) *)
        PROVE_TAC [CCS_distinct'],
        (* goal 1.8 (of 8) *)
        PROVE_TAC [CCS_distinct'] ],
      (* goal 2 (of 7) *)
      Q.PAT_X_ASSUM `(\t. prefix tau (e t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_11, Action_distinct],
      (* goal 3 (of 7) *)
      Q.PAT_X_ASSUM `(\t. prefix tau (e t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      FULL_SIMP_TAC std_ss [CCS_11] \\
      METIS_TAC [],
      (* goal 4 (of 7) *)
      Q.PAT_X_ASSUM `(\t. prefix tau (e t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 5 (of 7) *)
      Q.PAT_X_ASSUM `(\t. prefix tau (e t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 6 (of 7) *)
      Q.PAT_X_ASSUM `(\t. prefix tau (e t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 7 (of 7) *)
      Q.PAT_X_ASSUM `(\t. prefix tau (e t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'] ]);

(* another important backward property of SG *)
val SG9 = store_thm ("SG9",
  ``!e e'. SG (\t. sum (e t) (e' t)) ==> SG e /\ SG e'``,
    rpt STRIP_TAC >> (* 2 sub-goals here, same tacticals *)
  ( POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
      Cases_on `p` >| (* 8 sub-goals here *)
      [ (* goal 1.1 (of 8) *)
        PROVE_TAC [CCS_distinct],
        (* goal 1.2 (of 8) *)
        PROVE_TAC [CCS_distinct],
        (* goal 1.3 (of 8) *)
        PROVE_TAC [CCS_distinct],
        (* goal 1.4 (of 8) *)
        FULL_SIMP_TAC std_ss [CCS_11] \\
        `(e = \t. C') /\ (e' = \t. C0)` by PROVE_TAC [] \\
        ASM_REWRITE_TAC [] \\
        REWRITE_TAC [SG1],
        (* goal 1.5 (of 8) *)
        PROVE_TAC [CCS_distinct],
        (* goal 1.6 (of 8) *)
        PROVE_TAC [CCS_distinct],
        (* goal 1.7 (of 8) *)
        PROVE_TAC [CCS_distinct],
        (* goal 1.8 (of 8) *)
        PROVE_TAC [CCS_distinct] ],
      (* goal 2 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (e t) (e' t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 3 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (e t) (e' t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 4 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (e t) (e' t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      FULL_SIMP_TAC std_ss [CCS_11] \\
      METIS_TAC [],
      (* goal 5 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (e t) (e' t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 6 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (e t) (e' t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 7 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (e t) (e' t)) = X`
	(ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'] ] ));

val SG10 = store_thm ("SG10",
  ``!e e'. SG (\t. sum (prefix tau (e t)) (prefix tau (e' t))) ==> SG e /\ SG e'``,
    rpt STRIP_TAC (* 2 sub-goals here, same tacticals *)
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) >| (* 7 sub-goals here *)
      [ (* goal 1.1 (of 7) *)
        POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
        Cases_on `p` >| (* 8 sub-goals here *)
        [ (* goal 1.1.1 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.2 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.3 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.4 (of 8) *)
          FULL_SIMP_TAC std_ss [CCS_11] \\
          Cases_on `C'` >| (* 8 sub-goals here *)
          [ PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct],
            FULL_SIMP_TAC std_ss [CCS_11] \\
            `(e = \t. C'')` by PROVE_TAC [] \\
            ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1],
            PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct] ],
          (* goal 1.1.5 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.6 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.7 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.8 (of 8) *)
          PROVE_TAC [CCS_distinct] ],
        (* goal 1.2 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.3 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.4 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        FULL_SIMP_TAC std_ss [CCS_11] \\
        `e1 = \t. prefix tau (e t)` by PROVE_TAC [] \\
        FULL_SIMP_TAC std_ss [] \\
        IMP_RES_TAC SG8, (* SG8 used here! *)
        (* goal 1.5 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.6 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.7 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'] ],
      (* goal 2 (of 2) *)
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) >| (* 7 sub-goals here *)
      [ (* goal 1.1 (of 7) *)
        POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
        Cases_on `p` >| (* 8 sub-goals here *)
        [ (* goal 1.1.1 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.2 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.3 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.4 (of 8) *)
          FULL_SIMP_TAC std_ss [CCS_11] \\
          Cases_on `C0` >| (* 8 sub-goals here *)
          [ PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct],
            FULL_SIMP_TAC std_ss [CCS_11] \\
            `(e' = \t. C'')` by PROVE_TAC [] \\
            ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1],
            PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct],
            PROVE_TAC [CCS_distinct] ],
          (* goal 1.1.5 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.6 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.7 (of 8) *)
          PROVE_TAC [CCS_distinct],
          (* goal 1.1.8 (of 8) *)
          PROVE_TAC [CCS_distinct] ],
        (* goal 1.2 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.3 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.4 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        FULL_SIMP_TAC std_ss [CCS_11] \\
        `e2 = \t. prefix tau (e' t)` by PROVE_TAC [] \\
        FULL_SIMP_TAC std_ss [] \\
        IMP_RES_TAC SG8, (* SG8 used here! *)
        (* goal 1.5 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.6 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'],
        (* goal 1.7 (of 7) *)
        Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
        PROVE_TAC [CCS_distinct'] ]]);

val SG11 = store_thm ("SG11",
  ``!e e' L. SG (\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) ==> SG e``,
    rpt STRIP_TAC 
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
      Cases_on `p` >| (* 8 sub-goals here *)
      [ PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct],
        FULL_SIMP_TAC std_ss [CCS_11] \\
        Cases_on `C'` >| (* 8 sub-goals here *)
        [ PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct],
          FULL_SIMP_TAC std_ss [CCS_11] \\
          `(e = \t. C'')` by PROVE_TAC [] \\
          ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1],
          PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct] ],
        PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct] ],
      (* goal 2 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 3 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 4 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      FULL_SIMP_TAC std_ss [CCS_11] \\
      `e1 = \t. prefix tau (e t)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\
      IMP_RES_TAC SG8, (* SG8 used here! *)
      (* goal 5 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 6 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 7 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix tau (e t)) (prefix (label L) (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'] ]);

val SG11' = store_thm ("SG11'",
  ``!e e' L. SG (\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) ==> SG e'``,
    rpt STRIP_TAC 
 >> POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
      Cases_on `p` >| (* 8 sub-goals here *)
      [ PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct],
        FULL_SIMP_TAC std_ss [CCS_11] \\
        Cases_on `C0` >| (* 8 sub-goals here *)
        [ PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct],
          FULL_SIMP_TAC std_ss [CCS_11] \\
          `(e' = \t. C'')` by PROVE_TAC [] \\
          ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1],
          PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct],
          PROVE_TAC [CCS_distinct] ],
        PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct],
        PROVE_TAC [CCS_distinct] ],
      (* goal 2 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 3 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 4 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      FULL_SIMP_TAC std_ss [CCS_11] \\
      `e2 = \t. prefix tau (e' t)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\
      IMP_RES_TAC SG8, (* SG8 used here! *)
      (* goal 5 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 6 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 7 (of 7) *)
      Q.PAT_X_ASSUM `(\t. sum (prefix (label L) (e t)) (prefix tau (e' t))) = X`
	  (ASSUME_TAC o BETA_RULE o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'] ]);

val OBS_CONGR_SUBST_SG = store_thm (
   "OBS_CONGR_SUBST_SG",
  ``!P Q. OBS_CONGR P Q ==> !E. SG E ==> OBS_CONGR (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `SG` >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- REWRITE_TAC [OBS_CONGR_REFL]
 >| [ (* goal 1 (of 6) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_PREFIX \\
      irule OBS_CONGR_SUBST_EXPR >> ASM_REWRITE_TAC [],
      (* goal 2 (of 6) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 3 (of 6) *)
      IMP_RES_TAC OBS_CONGR_PRESD_BY_SUM,
      (* goal 4 (of 6) *)
      IMP_RES_TAC OBS_CONGR_PRESD_BY_PAR,
      (* goal 5 (of 6) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_RESTR >> ASM_REWRITE_TAC [],
      (* goal 6 (of 6) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_RELAB >> ASM_REWRITE_TAC [] ]);

(* Sequential (SEQ) expressions:
   X is sequential in E if every subexpression of E which contains X, apart from
   X itself, is of the form a.F or Sigma F_i *)
val (SEQ_rules, SEQ_ind, SEQ_cases) = Hol_reln `
    (                             SEQ (\t. t)) /\                  (* SEQ1 *)
    (!p.                          SEQ (\t. p)) /\                  (* SEQ2 *)
    (!a e.   SEQ e            ==> SEQ (\t. prefix a (e t))) /\	   (* SEQ3 *)
    (!e1 e2. SEQ e1 /\ SEQ e2 ==> SEQ (\t. sum (e1 t) (e2 t))) `;  (* SEQ4 *)

val [SEQ1, SEQ2, SEQ3, SEQ4] =
    map save_thm (combine (["SEQ1", "SEQ2", "SEQ3", "SEQ4"],
			   CONJUNCTS SEQ_rules));

val SEQ3a = store_thm ("SEQ3a",
  ``!a :'b Action. SEQ (\t. prefix a t)``,
    ASSUME_TAC SEQ1
 >> IMP_RES_TAC SEQ3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

val SEQ_IS_EXPR = store_thm (
   "SEQ_IS_EXPR", ``!e. SEQ e ==> EXPR e``,
    Induct_on `SEQ`
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ REWRITE_TAC [EXPR1],
      REWRITE_TAC [EXPR2],
      MATCH_MP_TAC EXPR3 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC EXPR4 >> ASM_REWRITE_TAC [] ]);

val SEQ_compose = store_thm (
   "SEQ_compose", ``!E. SEQ E ==> !E'. SEQ E' ==> SEQ (E o E')``,
    Induct_on `SEQ`
 >> REWRITE_TAC [o_DEF] >> BETA_TAC
 >> REWRITE_TAC [ETA_THM]
 >> rpt STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [SEQ2],
      (* goal 2 (of 3) *)
      RES_TAC >> IMP_RES_TAC SEQ3 \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      POP_ASSUM (MP_TAC o (Q.SPEC `a`)) \\
      KILL_TAC \\
      BETA_TAC >> DISCH_TAC >> METIS_TAC [],
      (* goal 3 (of 3) *)
      NTAC 2 (Q.PAT_X_ASSUM `!E. X` (ASSUME_TAC o (Q.SPEC `E''`))) \\
      RES_TAC \\
      IMP_RES_TAC (Q.SPECL [`\x. E (E'' x)`, `\x. E' (E'' x)`] SEQ4) \\
      POP_ASSUM K_TAC \\
      POP_ASSUM MP_TAC \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      KILL_TAC \\
      BETA_TAC >> DISCH_TAC >> METIS_TAC [] ]);

val OBS_CONGR_SUBST_SEQ = store_thm (
   "OBS_CONGR_SUBST_SEQ",
  ``!P Q. OBS_CONGR P Q ==> !E. SEQ E ==> OBS_CONGR (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `SEQ` >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [OBS_CONGR_REFL]
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC OBS_CONGR_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC OBS_CONGR_PRESD_BY_SUM ]);

(* Sequential expression with only guarded sums *)
val (GSEQ_rules, GSEQ_ind, GSEQ_cases) = Hol_reln `
    (                             GSEQ (\t. t)) /\                 (* GSEQ1 *)
    (!p.                          GSEQ (\t. p)) /\                 (* GSEQ2 *)
    (!a e.            GSEQ e  ==> GSEQ (\t. prefix a (e t))) /\	   (* GSEQ3 *)
    (!a1 a2 e1 e2.
           GSEQ e1 /\ GSEQ e2 ==> GSEQ (\t. sum (prefix a1 (e1 t)) (* GSEQ4 *)
						(prefix a2 (e2 t))))`;

val [GSEQ1, GSEQ2, GSEQ3, GSEQ4] =
    map save_thm (combine (["GSEQ1", "GSEQ2", "GSEQ3", "GSEQ4"],
			   CONJUNCTS GSEQ_rules));

val GSEQ3a = store_thm ("GSEQ3a",
  ``!a :'b Action. GSEQ (\t. prefix a t)``,
    ASSUME_TAC GSEQ1
 >> IMP_RES_TAC GSEQ3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

val GSEQ_IS_EXPR = store_thm (
   "GSEQ_IS_EXPR", ``!e. GSEQ e ==> EXPR e``,
    Induct_on `GSEQ`
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ REWRITE_TAC [EXPR1],
      REWRITE_TAC [EXPR2],
      MATCH_MP_TAC EXPR3 >> ASM_REWRITE_TAC [],
      Q.PAT_X_ASSUM `EXPR e1` (ASSUME_TAC o (Q.SPEC `a1`) o (MATCH_MP EXPR3)) \\
      Q.PAT_X_ASSUM `EXPR e2` (ASSUME_TAC o (Q.SPEC `a2`) o (MATCH_MP EXPR3)) \\
      MP_TAC (Q.SPECL [`\t. (prefix a1 (e1 t))`, `\t. (prefix a2 (e2 t))`] EXPR4) \\
      BETA_TAC >> RW_TAC std_ss [] ]);

val GSEQ_compose = store_thm (
   "GSEQ_compose", ``!E. GSEQ E ==> !E'. GSEQ E' ==> GSEQ (E o E')``,
    Induct_on `GSEQ`
 >> REWRITE_TAC [o_DEF] >> BETA_TAC
 >> REWRITE_TAC [ETA_THM]
 >> rpt STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [GSEQ2],
      (* goal 2 (of 3) *)
      RES_TAC >> IMP_RES_TAC GSEQ3 \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      POP_ASSUM (MP_TAC o (Q.SPEC `a`)) \\
      KILL_TAC \\
      BETA_TAC >> DISCH_TAC >> METIS_TAC [],
      (* goal 3 (of 3) *)
      NTAC 2 (Q.PAT_X_ASSUM `!E. X` (ASSUME_TAC o (Q.SPEC `E''`))) \\
      RES_TAC \\
      IMP_RES_TAC (Q.SPECL [`a1`, `a2`, `\x. E (E'' x)`, `\x. E' (E'' x)`] GSEQ4) \\
      POP_ASSUM K_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`a2`, `a1`])) \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      KILL_TAC \\
      BETA_TAC >> DISCH_TAC >> METIS_TAC [] ]);

val WEAK_EQUIV_SUBST_GSEQ = store_thm (
   "WEAK_EQUIV_SUBST_GSEQ",
  ``!P Q. WEAK_EQUIV P Q ==> !E. GSEQ E ==> WEAK_EQUIV (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [WEAK_EQUIV_REFL]
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC WEAK_EQUIV_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC WEAK_EQUIV_PRESD_BY_GUARDED_SUM \\
      ASM_REWRITE_TAC [] ]);

(* A combined (strong) induction theorem for SG + SEQ expression, it's easier to prove
   this induction theorem than defining another combined inductive relation SG_SEQ and
   prove SG /\ SEQ = SQ_SEQ, which is a combinatorial explosion of cases.
 *)
val SG_SEQ_strong_induction = store_thm (
   "SG_SEQ_strong_induction",
  ``!R. (!p. R (\t. p)) /\
	(!(l :'b Label) e. SEQ e ==> R (\t. prefix (label l) (e t))) /\
	(!(a :'b Action) e. SG e /\ SEQ e /\ R e ==> R (\t. prefix a (e t))) /\
	(!e1 e2. SG e1 /\ SEQ e1 /\ R e1 /\
		 SG e2 /\ SEQ e2 /\ R e2 ==> R (\t. sum (e1 t) (e2 t)))
	==> (!e. SG e /\ SEQ e ==> R e)``,
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `SG e` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`e`, `e`)
 >> Induct_on `SEQ`
 >> rpt STRIP_TAC >> FULL_SIMP_TAC std_ss [] >> ASM_REWRITE_TAC [] (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      Suff `~SG (\t. t)` >- PROVE_TAC [] \\
      KILL_TAC \\
      CCONTR_TAC >> FULL_SIMP_TAC std_ss [] \\
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
      >- ( POP_ASSUM (MP_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
           STRIP_ASSUME_TAC (Q.SPEC `p` lemma) >> PROVE_TAC [] ) \\
      Q.PAT_X_ASSUM `(\t. t) = X`
	(ASSUME_TAC o BETA_RULE o (Q.SPEC `nil`) o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 2 (of 3) *)
      REVERSE (Cases_on `a`) >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        Q.PAT_X_ASSUM `!l e. SEQ e ==> P` MATCH_MP_TAC \\
        ASM_REWRITE_TAC [],
        (* goal 2.2 (of 2) *)
        Suff `SG e` >- ( DISCH_TAC \\
			 Q.PAT_X_ASSUM `!a e. SG e /\ SEQ e /\ R e ==> P` MATCH_MP_TAC \\
			 ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG8 >> ASM_REWRITE_TAC [] ],
      (* goal 3 (of 3) *)
      Q.PAT_X_ASSUM `!e1 e2. X` MATCH_MP_TAC \\
      ASM_REWRITE_TAC [] \\
      Suff `SG e /\ SG e'` >- ( STRIP_TAC >> ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
      POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
      MATCH_MP_TAC SG9 >> ASM_REWRITE_TAC [] ]);

val SG_GSEQ_strong_induction = store_thm (
   "SG_GSEQ_strong_induction",
  ``!R. (!p. R (\t. p)) /\
	(!(l :'b Label) e. GSEQ e ==> R (\t. prefix (label l) (e t))) /\
	(!(a :'b Action) e. SG e /\ GSEQ e /\ R e ==> R (\t. prefix a (e t))) /\
	(!e1 e2.       SG e1 /\ GSEQ e1 /\ R e1 /\ SG e2 /\ GSEQ e2 /\ R e2
		   ==> R (\t. sum (prefix tau (e1 t)) (prefix tau (e2 t)))) /\
	(!l2 e1 e2.    SG e1 /\ GSEQ e1 /\ R e1 /\ GSEQ e2
		   ==> R (\t. sum (prefix tau (e1 t)) (prefix (label l2) (e2 t)))) /\
	(!l1 e1 e2.    GSEQ e1 /\ SG e2 /\ GSEQ e2 /\ R e2
		   ==> R (\t. sum (prefix (label l1) (e1 t)) (prefix tau (e2 t)))) /\
	(!l1 l2 e1 e2. GSEQ e1 /\ GSEQ e2
		   ==> R (\t. sum (prefix (label l1) (e1 t)) (prefix (label l2) (e2 t))))
	==> (!e. SG e /\ GSEQ e ==> R e)``,
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `SG e` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`e`, `e`)
 >> Induct_on `GSEQ`
 >> rpt STRIP_TAC >> FULL_SIMP_TAC std_ss [] >> ASM_REWRITE_TAC [] (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      Suff `~SG (\t. t)` >- PROVE_TAC [] \\
      KILL_TAC \\
      CCONTR_TAC >> FULL_SIMP_TAC std_ss [] \\
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
      >- ( POP_ASSUM (MP_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
           STRIP_ASSUME_TAC (Q.SPEC `p` lemma) >> PROVE_TAC [] ) \\
      Q.PAT_X_ASSUM `(\t. t) = X`
	(ASSUME_TAC o BETA_RULE o (Q.SPEC `nil`) o (REWRITE_RULE [FUN_EQ_THM])) \\
      PROVE_TAC [CCS_distinct'],
      (* goal 2 (of 3) *)
      REVERSE (Cases_on `a`) >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        Q.PAT_X_ASSUM `!l e. GSEQ e ==> P` MATCH_MP_TAC \\
        ASM_REWRITE_TAC [],
        (* goal 2.2 (of 2) *)
        Suff `SG e` >- ( DISCH_TAC \\
			 Q.PAT_X_ASSUM `!a e. SG e /\ GSEQ e /\ R e ==> P` MATCH_MP_TAC \\
			 ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG8 >> ASM_REWRITE_TAC [] ],
      (* goal 3 (of 3) *)
      Cases_on `a1` >> Cases_on `a2` >| (* 4 sub-goals here *)
      [ (* goal 3.1 (of 4) *)
        Q.PAT_X_ASSUM `!e1 e2. X ==> R (\t. prefix tau (e1 t) + prefix tau (e2 t))` MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] \\
        Suff `SG e /\ SG e'` >- ( STRIP_TAC >> ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG10 >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 4) *)
        Q.PAT_X_ASSUM `!l2 e1 e2. X ==> R (\t. prefix tau (e1 t) + prefix (label l2) (e2 t))`
	  MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] \\
        Suff `SG e` >- ( STRIP_TAC >> ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG11 >> take [`e'`, `L`] >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 4) *)
        Q.PAT_X_ASSUM `!l1 e1 e2. X ==> R (\t. prefix (label l1) (e1 t) + prefix tau (e2 t))`
	  MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] \\
        Suff `SG e'` >- ( STRIP_TAC >> ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG11' >> take [`e`, `L`] >> ASM_REWRITE_TAC [],
        (* goal 3.4 (of 4) *)
        Q.PAT_X_ASSUM `!l1 l2 e1 e2. X ==> R (\t. prefix (label l1) (e1 t) + prefix (label l2) (e2 t))`
	  MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] ] ]);

val SG_SEQ_compose = store_thm (
   "SG_SEQ_compose", ``!E. SG E /\ SEQ E ==> !H. SEQ H ==> (SG (H o E) /\ SEQ (H o E))``,
    HO_MATCH_MP_TAC SG_SEQ_strong_induction
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC >> rpt STRIP_TAC (* 8 sub-goals here *)
 >| [ (* goal 1 (of 8) *)
      REWRITE_TAC [SG1],
      (* goal 2 (of 8) *)
      REWRITE_TAC [SEQ2],
      (* goal 3 (of 8) *)
      POP_ASSUM MP_TAC >> Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `SEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 3.1 (of 4) *)
        IMP_RES_TAC SEQ_IS_EXPR \\
        MATCH_MP_TAC SG2 >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 3.3 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM MP_TAC >> BETA_TAC \\
        STRIP_TAC >> METIS_TAC [],
        (* goal 3.4 (of 4) *)
        IMP_RES_TAC (Q.SPECL [`\x. H (prefix (label l) (E x))`,
			      `\x. H' (prefix (label l) (E x))`] SG4) \\
        POP_ASSUM K_TAC \\
        POP_ASSUM MP_TAC \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [] ],
      (* goal 4 (of 8) *)
      ASSUME_TAC (Q.SPECL [`label l`, `E`] SEQ3) \\
      RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` SEQ_compose) \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> KILL_TAC \\
      REWRITE_TAC [o_DEF] >> BETA_TAC \\
      REWRITE_TAC [],
      (* goal 5 (of 8) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `SEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 5.1 (of 4) *)
        MATCH_MP_TAC SG3 >> ASM_REWRITE_TAC [],
        (* goal 5.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 5.3 (of 4) *)
        ASSUME_TAC (Q.SPECL [`a' :'b Action`,
			     `\x. (H :('a, 'b) CCS -> ('a, 'b) CCS) (prefix a (E x))`] SG3) \\
        POP_ASSUM MP_TAC \\
        BETA_TAC >> rpt STRIP_TAC >> RES_TAC,
        (* goal 5.4 (of 4) *)
        IMP_RES_TAC (Q.SPECL [`\x. H (prefix a (E x))`, `\x. H' (prefix a (E x))`] SG4) \\
        POP_ASSUM K_TAC \\
        POP_ASSUM MP_TAC \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 6 (of 8) *)
      ASSUME_TAC (Q.SPECL [`a :'b Action`, `E`] SEQ3) \\
      RES_TAC >> NTAC 4 (POP_ASSUM K_TAC) \\
      ASSUME_TAC (Q.SPEC `H` SEQ_compose) \\
      POP_ASSUM (ASSUME_TAC o (fn th => MP th (ASSUME ``SEQ H``))) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `\t. prefix a (E t)`)) \\
      POP_ASSUM MP_TAC \\
      REWRITE_TAC [o_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      PROVE_TAC [],
      (* goal 7 (of 8) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `SEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 7.1 (of 4) *)
        MATCH_MP_TAC SG4 >> ASM_REWRITE_TAC [],
        (* goal 7.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 7.3 (of 4) *)
        ASSUME_TAC (Q.SPECL [`a :'b Action`,
			     `\x. (H :('a, 'b) CCS -> ('a, 'b) CCS) (E x + E' x)`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC \\
        PROVE_TAC [],
        (* goal 7.4 (of 4) *)
        IMP_RES_TAC (Q.SPECL [`\x. H (E x + E' x)`,
			      `\x. H' (E x + E' x)`] SG4) \\
        POP_ASSUM K_TAC \\
        POP_ASSUM MP_TAC \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 8 (of 8) *)
      ASSUME_TAC (Q.SPECL [`E`, `E'`] SEQ4) \\
      NTAC 2 (Q.PAT_X_ASSUM `!H. X` K_TAC) >> RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` SEQ_compose) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [] ]);

val SG_GSEQ_compose = store_thm (
   "SG_GSEQ_compose", ``!E. SG E /\ GSEQ E ==> !H. GSEQ H ==> (SG (H o E) /\ GSEQ (H o E))``,
    HO_MATCH_MP_TAC SG_GSEQ_strong_induction
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC >> rpt STRIP_TAC (* 14 sub-goals here *)
 >| [ (* goal 1 (of 14) *)
      REWRITE_TAC [SG1],
      (* goal 2 (of 14) *)
      REWRITE_TAC [GSEQ2],
      (* goal 3 (of 14) *)
      POP_ASSUM MP_TAC >> Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 3.1 (of 4) *)
        IMP_RES_TAC GSEQ_IS_EXPR \\
        MATCH_MP_TAC SG2 >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 3.3 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM MP_TAC >> BETA_TAC \\
        STRIP_TAC >> METIS_TAC [],
        (* goal 3.4 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix a1 (H (prefix (label l) (E t))))`,
			      `\t. (prefix a2 (H' (prefix (label l) (E t))))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [] ],
      (* goal 4 (of 14) *)
      ASSUME_TAC (Q.SPECL [`label l`, `E`] GSEQ3) \\
      RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_compose) \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> KILL_TAC \\
      REWRITE_TAC [o_DEF] >> BETA_TAC \\
      REWRITE_TAC [],
      (* goal 5 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 5.1 (of 4) *)
        MATCH_MP_TAC SG3 >> ASM_REWRITE_TAC [],
        (* goal 5.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 5.3 (of 4) *)
        ASSUME_TAC (Q.SPECL [`a' :'b Action`,
			     `\x. (H :('a, 'b) CCS -> ('a, 'b) CCS) (prefix a (E x))`] SG3) \\
        POP_ASSUM MP_TAC \\
        BETA_TAC >> rpt STRIP_TAC >> RES_TAC,
        (* goal 5.4 (of 4) *)
        IMP_RES_TAC SG3 >> POP_ASSUM K_TAC \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix a1 (H (prefix a (E t))))`,
			      `\t. (prefix a2 (H' (prefix a (E t))))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [] ],
      (* goal 6 (of 14) *)
      ASSUME_TAC (Q.SPECL [`a :'b Action`, `E`] GSEQ3) \\
      RES_TAC >> NTAC 4 (POP_ASSUM K_TAC) \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_compose) \\
      POP_ASSUM (ASSUME_TAC o (fn th => MP th (ASSUME ``GSEQ H``))) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `\t. prefix a (E t)`)) \\
      POP_ASSUM MP_TAC \\
      REWRITE_TAC [o_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      PROVE_TAC [],

      (* goal 7 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 7.1 (of 4) *)
        IMP_RES_TAC SG3 \\
        NTAC 2 (POP_ASSUM (MP_TAC o (Q.SPEC `tau`))) >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix tau (E t))`, `\t. (prefix tau (E' t))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [],
        (* goal 7.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 7.3 (of 4) *)
        ASSUME_TAC
	  (Q.SPECL [`a :'b Action`,
		    `\x. (H :('a, 'b) CCS -> ('a, 'b) CCS) (tau..(E x) + tau..(E' x))`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC \\
        PROVE_TAC [],
        (* goal 7.4 (of 4) *)
        IMP_RES_TAC SG3 >> NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. a1..(H (tau..(E t) + tau..(E' t)))`,
			      `\t. a2..(H' (tau..(E t) + tau..(E' t)))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 8 (of 14) *)
      ASSUME_TAC (Q.SPECL [`tau`, `tau`, `E`, `E'`] GSEQ4) \\
      NTAC 2 (Q.PAT_X_ASSUM `!H. X` K_TAC) >> RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_compose) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [],
      (* goal 9 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 9.1 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `tau`)) \\
        IMP_RES_TAC GSEQ_IS_EXPR \\
        POP_ASSUM K_TAC \\
        IMP_RES_TAC SG2 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `l2`)) \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix tau (E t))`, `\t. (prefix (label l2) (e2 t))`] SG4) \\
        POP_ASSUM MP_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [],
        (* goal 9.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 9.3 (of 4) *)
        ASSUME_TAC
	  (Q.SPECL [`a :'b Action`,
		    `\x. (H :('a, 'b) CCS -> ('a, 'b) CCS) (tau..(E x) + (label l2)..(e2 x))`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC \\
        PROVE_TAC [],
        (* goal 9.4 (of 4) *)
        IMP_RES_TAC SG3 >> POP_ASSUM K_TAC \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. a1..(H (tau..(E t) + (label l2)..(e2 t)))`,
			      `\t. a2..(H' (tau..(E t) + (label l2)..(e2 t)))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 10 (of 14) *)
      ASSUME_TAC (Q.SPECL [`tau`, `label l2`, `E`, `e2`] GSEQ4) \\
      Q.PAT_X_ASSUM `!H. X` K_TAC >> RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_compose) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [],
      (* goal 11 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 11.1 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `tau`)) \\
        IMP_RES_TAC GSEQ_IS_EXPR \\
        Q.PAT_X_ASSUM `EXPR E` K_TAC \\
        IMP_RES_TAC SG2 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `l1`)) \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix (label l1) (e1 t))`, `\t. (prefix tau (E t))`] SG4) \\
        POP_ASSUM MP_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [],
        (* goal 11.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 11.3 (of 4) *)
        ASSUME_TAC
	  (Q.SPECL [`a :'b Action`,
		    `\x. (H :('a, 'b) CCS -> ('a, 'b) CCS) ((label l1)..(e1 x) + tau..(E x))`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC \\
        PROVE_TAC [],
        (* goal 11.4 (of 4) *)
        IMP_RES_TAC SG3 >> POP_ASSUM K_TAC \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. a1..(H ((label l2)..(e2 t) + tau..(E t)))`,
			      `\t. a2..(H' ((label l2)..(e2 t) + tau..(E t)))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC \\
        POP_ASSUM K_TAC \\
        BETA_TAC >> DISCH_TAC \\
        METIS_TAC [] ],
      (* goal 12 (of 14) *)
      ASSUME_TAC (Q.SPECL [`label l1`, `tau`, `e1`, `E`] GSEQ4) \\
      Q.PAT_X_ASSUM `!H. X` K_TAC >> RES_TAC \\
      ASSUME_TAC (Q.SPEC `H` GSEQ_compose) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [],
      (* goal 13 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 13.1 (of 4) *)
        IMP_RES_TAC GSEQ_IS_EXPR \\
        IMP_RES_TAC SG2 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `l2`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `l1`)) \\
        rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. (prefix (label l1) (e1 t))`,
			      `\t. (prefix (label l2) (e2 t))`] SG4) \\
        POP_ASSUM K_TAC \\
        POP_ASSUM MP_TAC >> KILL_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [],
        (* goal 13.2 (of 4) *)
        REWRITE_TAC [SG1],
        (* goal 13.3 (of 4) *)
        ASSUME_TAC
	  (Q.SPECL [`a :'b Action`,
		    `\x. (H :('a, 'b) CCS -> ('a, 'b) CCS)
			 ((label l1)..(e1 x) + (label l2)..(e2 x))`] SG3) \\
        POP_ASSUM MP_TAC >> BETA_TAC >> rpt STRIP_TAC >> PROVE_TAC [],
        (* goal 13.4 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a1`)) \\
        POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
        BETA_TAC >> rpt DISCH_TAC \\
        IMP_RES_TAC (Q.SPECL [`\t. a1..(H ((label l1)..(e1 t) + (label l2)..(e2 t)))`,
			      `\t. a2..(H' ((label l1)..(e1 t) + (label l2)..(e2 t)))`] SG4) \\
        NTAC 2 (POP_ASSUM K_TAC) \\
        POP_ASSUM MP_TAC >> KILL_TAC \\
        BETA_TAC >> DISCH_TAC >> METIS_TAC [] ],
      (* goal 14 (of 14) *)
      MP_TAC (Q.SPECL [`label l1`, `label l2`, `e1`, `e2`] GSEQ4) \\
      MP_TAC (Q.SPEC `H` GSEQ_compose) \\
      RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!E'. GSEQ E' ==> X`
	(MP_TAC o (Q.SPEC `\t. (label l1)..(e1 t) + (label l2)..(e2 t)`)) \\
      REWRITE_TAC [o_DEF] >> BETA_TAC >> METIS_TAC [] ]);

(* Lemma 7.12 in Milner's book [1]:
   If the variable X is guarded and sequential in G, and G{P/X} --a-> P', then there is
   an expression H such that G --a--> H, P' = H{P/X} and, for any Q, G{Q/X} --a-> H{Q/X}.
   Moreover H is sequential, and if a = tau then H is also guarded.
 *)
val WEAK_UNIQUE_SOLUTIONS_LEMMA = store_thm (
   "WEAK_UNIQUE_SOLUTIONS_LEMMA",
  ``!G. SG G /\ GSEQ G ==>
	!P a P'. TRANS (G P) a P' ==>
		 ?H. GSEQ H /\ ((a = tau) ==> SG H) /\
		     (P' = H P) /\ !Q. TRANS (G Q) a (H Q)``,
    HO_MATCH_MP_TAC SG_GSEQ_strong_induction
 >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      Q.EXISTS_TAC `\t. P'` >> BETA_TAC \\
      ASM_SIMP_TAC std_ss [GSEQ2] \\
      DISCH_TAC \\
      REWRITE_TAC [SG1],
      (* goal 2 (of 7), `a = tau` used here! *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
      SIMP_TAC std_ss [Action_distinct_label] \\
      REWRITE_TAC [PREFIX],
      (* goal 3 (of 7) *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 3 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G` \\
      ASM_SIMP_TAC std_ss [PREFIX],
      (* goal 4 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G'` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 5 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e2` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 6 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e1` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 7 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e1` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e2` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ] ]);

(* The EPS version of WEAK_UNIQUE_SOLUTIONS_LEMMA.
   NOTE: the WEAK_TRANS version cannot be derived, because of the missing of SG in the middle.
 *)
val WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS = store_thm (
   "WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS",
  ``!G. SG G /\ GSEQ G ==>
	!P P'. EPS (G P) P' ==>
	       ?H. SG H /\ GSEQ H /\ (P' = H P) /\ !Q. EPS (G Q) (H Q)``,
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `GP = G P`
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`P`, `P`)
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`P'`, `P'`)
 >> Q.SPEC_TAC (`GP`, `GP`)
 >> HO_MATCH_MP_TAC EPS_strongind_right
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >- ( Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
      Q.UNABBREV_TAC `GP` >> ASM_REWRITE_TAC [EPS_REFL] )
 >> RES_TAC
 >> Q.UNABBREV_TAC `GP`
 >> Q.PAT_X_ASSUM `!P''. Abbrev (G P = G P'') ==> X` K_TAC
 >> FULL_SIMP_TAC std_ss []
 >> IMP_RES_TAC (Q.SPEC `H` WEAK_UNIQUE_SOLUTIONS_LEMMA) (* lemma used here *)
 >> FULL_SIMP_TAC std_ss []
 >> Q.EXISTS_TAC `H''`
 >> ASM_REWRITE_TAC [EQ_SYM]
 >> GEN_TAC
 >> `EPS (G Q) (H Q) /\ EPS (H Q) (H'' Q)` by PROVE_TAC [ONE_TAU]
 >> IMP_RES_TAC EPS_TRANS);

val OBS_UNIQUE_SOLUTIONS_LEMMA = store_thm (
   "OBS_UNIQUE_SOLUTIONS_LEMMA",
  ``!G. SG G /\ SEQ G ==>
	!P a P'. TRANS (G P) a P' ==>
		 ?H. SEQ H /\ ((a = tau) ==> SG H) /\
		     (P' = H P) /\ !Q. TRANS (G Q) a (H Q)``,
    HO_MATCH_MP_TAC SG_SEQ_strong_induction
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      Q.EXISTS_TAC `\t. P'` >> BETA_TAC \\
      ASM_SIMP_TAC std_ss [SEQ2] \\
      DISCH_TAC \\
      REWRITE_TAC [SG1],
      (* goal 2 (of 4), `a = tau` used here! *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
      SIMP_TAC std_ss [Action_distinct_label] \\
      REWRITE_TAC [PREFIX],
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 3 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G` \\
      ASM_SIMP_TAC std_ss [PREFIX],
      (* goal 4 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `H` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        (* goal 4.2 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `H` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ] ]);

(* The EPS version of OBS_UNIQUE_SOLUTIONS_LEMMA.
   NOTE: the WEAK_TRANS version cannot be derived, because of the missing of SG in the middle.
 *)
val OBS_UNIQUE_SOLUTIONS_LEMMA_EPS = store_thm (
   "OBS_UNIQUE_SOLUTIONS_LEMMA_EPS",
  ``!G. SG G /\ SEQ G ==>
	!P P'. EPS (G P) P' ==>
	       ?H. SG H /\ SEQ H /\ (P' = H P) /\ !Q. EPS (G Q) (H Q)``,
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `GP = G P`
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`P`, `P`)
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`P'`, `P'`)
 >> Q.SPEC_TAC (`GP`, `GP`)
 >> HO_MATCH_MP_TAC EPS_strongind_right
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >- ( Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
      Q.UNABBREV_TAC `GP` >> ASM_REWRITE_TAC [EPS_REFL] )
 >> RES_TAC
 >> Q.UNABBREV_TAC `GP`
 >> Q.PAT_X_ASSUM `!P''. Abbrev (G P = G P'') ==> X` K_TAC
 >> FULL_SIMP_TAC std_ss []
 >> IMP_RES_TAC (Q.SPEC `H` OBS_UNIQUE_SOLUTIONS_LEMMA) (* lemma used here *)
 >> FULL_SIMP_TAC std_ss []
 >> Q.EXISTS_TAC `H''`
 >> ASM_REWRITE_TAC [EQ_SYM]
 >> GEN_TAC
 >> `EPS (G Q) (H Q) /\ EPS (H Q) (H'' Q)` by PROVE_TAC [ONE_TAU]
 >> IMP_RES_TAC EPS_TRANS);

(* Proposition 7.13 in Milner's book [1]:
   Let the expression E contains at most the variable X, and let X be guarded and sequential
   in E, then:
	If P = E{P/X} and Q = E{Q/X} then P = Q. (here "=" means OBS_CONGR or WEAK_EQUIV)
 *)
val GSEQ_EPS_lemma = Q.prove (
   `!E P Q R H. SG E /\ GSEQ E /\ WEAK_EQUIV P (E P) /\ WEAK_EQUIV Q (E Q) /\ GSEQ H /\
		(R = \x y. ?H. GSEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q))
    ==> (!P'. EPS (H P) P' ==> ?Q'. EPS (H Q) Q' /\ (WEAK_EQUIV O R O STRONG_EQUIV) P' Q') /\
	(!Q'. EPS (H Q) Q' ==> ?P'. EPS (H P) P' /\ (STRONG_EQUIV O R O WEAK_EQUIV) P' Q')`,
    REPEAT GEN_TAC >> STRIP_TAC
 >> `WEAK_EQUIV (H P) ((H o E) P) /\ WEAK_EQUIV (H Q) ((H o E) Q)`
				 by PROVE_TAC [WEAK_EQUIV_SUBST_GSEQ, o_DEF]
 >> `SG (H o E) /\ GSEQ (H o E)` by PROVE_TAC [SG_GSEQ_compose]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] WEAK_EQUIV_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `Q`)) \\
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] WEAK_EQUIV_EPS') \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV (H' Q) E1` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H' Q` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `P'` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL] \\
      PROVE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] WEAK_EQUIV_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `P`)) \\
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] WEAK_EQUIV_EPS') \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV E2 Q'` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `Q'` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `H' P` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL] \\
      PROVE_TAC [WEAK_EQUIV_SYM] ]);

val WEAK_UNIQUE_SOLUTIONS = store_thm (
   "WEAK_UNIQUE_SOLUTIONS",
  ``!E. SG E /\ GSEQ E ==>
	!P Q. WEAK_EQUIV P (E P) /\ WEAK_EQUIV Q (E Q) ==> WEAK_EQUIV P Q``,
    REPEAT STRIP_TAC
 >> irule (REWRITE_RULE [RSUBSET] WEAK_BISIM_UPTO_THM)
 >> Q.EXISTS_TAC `\x y. ?H. GSEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)`
 >> BETA_TAC >> REVERSE CONJ_TAC
 >- ( Q.EXISTS_TAC `\x. x` >> BETA_TAC \\
      KILL_TAC >> REWRITE_TAC [GSEQ1, WEAK_EQUIV_REFL] )
 >> REWRITE_TAC [WEAK_BISIM_UPTO]
 >> Q.X_GEN_TAC `P'`
 >> Q.X_GEN_TAC `Q'`
 >> BETA_TAC >> STRIP_TAC
 >> ASM_REWRITE_TAC []
 >> Q.ABBREV_TAC `R = \x y. ?H. GSEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)`
 >> `WEAK_EQUIV (H P) ((H o E) P) /\ WEAK_EQUIV (H Q) ((H o E) Q)`
					by PROVE_TAC [WEAK_EQUIV_SUBST_GSEQ, o_DEF]
 >> `SG (H o E) /\ GSEQ (H o E)` by PROVE_TAC [SG_GSEQ_compose]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      `?E2. WEAK_TRANS (H P) (label l) E2 /\ WEAK_EQUIV E1 E2`
				by PROVE_TAC [WEAK_EQUIV_TRANS_label] \\
      `?E3. WEAK_TRANS ((H o E) P) (label l) E3 /\ WEAK_EQUIV E2 E3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label] \\
      Q.PAT_X_ASSUM `WEAK_TRANS ((H o E) P) (label l) E3`
	(STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `TRANS (H' P) (label l) E2'` by PROVE_TAC [] \\
      IMP_RES_TAC (Q.SPEC `H'` WEAK_UNIQUE_SOLUTIONS_LEMMA) \\
      NTAC 7 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `EPS (H'' P) E3` by PROVE_TAC [] \\
      MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H''`] GSEQ_EPS_lemma) \\
      RW_TAC std_ss [] >> POP_ASSUM K_TAC \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      `WEAK_TRANS ((H o E) Q) (label l) Q''` by PROVE_TAC [WEAK_TRANS] \\
      `?Q3. WEAK_TRANS (H Q) (label l) Q3 /\ WEAK_EQUIV Q3 Q''`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      `?Q4. WEAK_TRANS Q' (label l) Q4 /\ WEAK_EQUIV Q4 Q3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      Q.EXISTS_TAC `Q4` >> ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `X E3 Q''` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      Q.PAT_X_ASSUM `R y' y` MP_TAC \\
      Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
      `WEAK_EQUIV E3 y'` by PROVE_TAC [STRONG_IMP_WEAK_EQUIV] \\
      `WEAK_EQUIV y Q4` by PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E1` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `H'''` >> ASM_REWRITE_TAC [] \\
      PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
(*
 (case 4)                              (case 1)
   P'  ======== tau =====> P4            P'  ----------------- l --------------> E1
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H P ======== eps =====> P3            H P ================= l ==============> E2
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H(E(P)) ==== eps =====> H' P         H(E(P)) ==eps=> E1'  --l-> E2'   ==eps=> E3   ~ y' ~~ H''' P
                           |                            (H' P)     (H'' P)              |
                           R                                                            R
                           |                                                            |
   H(E(Q)) ==== eps =====> E3 = H' Q    H(E(Q)) ==eps=> H' Q --l-> H'' Q ==eps=> Q'' ~~ y  ~~ H''' Q
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H Q ======== eps =====> E1           H Q ================== l ==============> Q3
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   Q'  -------- eps -----> E2            Q' ================== l ==============> Q4
 *)
      (* goal 2 (of 4) *)
      `?E1. WEAK_TRANS (H Q) (label l) E1 /\ WEAK_EQUIV E2 E1`
				by PROVE_TAC [WEAK_EQUIV_TRANS_label] \\
      `?E3. WEAK_TRANS ((H o E) Q) (label l) E3 /\ WEAK_EQUIV E1 E3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label] \\
      Q.PAT_X_ASSUM `WEAK_TRANS ((H o E) Q) (label l) E3`
	(STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      `TRANS (H' Q) (label l) E2'` by PROVE_TAC [] \\
      IMP_RES_TAC (Q.SPEC `H'` WEAK_UNIQUE_SOLUTIONS_LEMMA) \\
      NTAC 7 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      `EPS (H'' Q) E3` by PROVE_TAC [] \\
      MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H''`] GSEQ_EPS_lemma) \\
      RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!P'. EPS (H'' P) P' ==> X` K_TAC \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      `WEAK_TRANS ((H o E) P) (label l) P''` by PROVE_TAC [WEAK_TRANS] \\
      `?P3. WEAK_TRANS (H P) (label l) P3 /\ WEAK_EQUIV P3 P''`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      `?P4. WEAK_TRANS P' (label l) P4 /\ WEAK_EQUIV P4 P3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      Q.EXISTS_TAC `P4` >> ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `X P'' E3` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      Q.PAT_X_ASSUM `R y' y` MP_TAC \\
      Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
      `WEAK_EQUIV y E3` by PROVE_TAC [STRONG_IMP_WEAK_EQUIV] \\
      Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      `WEAK_EQUIV P4 y'` by PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `y'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H'''` >> ASM_REWRITE_TAC [] \\
      PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
(*
 (case 3)                              (case 2)
   P'  -------- tau -----> E1            P'  ================== l ==============> P4
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   H P ======== eps =====> E2            H P ================== l ==============> P3
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   H(E(P)) ==== eps =====> E3 = H' P    H(E(P)) ==eps=> H' P --l-> H'' P ==eps=> P'' ~~ y' ~~ H''' P
                           |                                                            |
                           R                                                            R
                           |                           (H' Q)     (H'' Q)               |
   H(E(Q)) ==== eps =====> H' Q         H(E(Q)) ==eps=> E1'  --l-> E2'   ==eps=> E3   ~ y  ~~ H''' Q
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   H Q ======== eps =====> Q3            H Q ================== l ==============> E1
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   Q'  ======== eps =====> Q4            Q'  ------------------ l --------------> E2
 *)
      (* goal 3 (of 4) *)
      `?E2. EPS (H P) E2 /\ WEAK_EQUIV E1 E2` by PROVE_TAC [WEAK_EQUIV_TRANS_tau] \\
      `?E3. EPS ((H o E) P) E3 /\ WEAK_EQUIV E2 E3` by PROVE_TAC [WEAK_EQUIV_EPS] \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `?Q3. EPS (H Q) Q3 /\ WEAK_EQUIV Q3 (H' Q)` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      `?Q4. EPS Q' Q4 /\ WEAK_EQUIV Q4 Q3` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      Q.EXISTS_TAC `Q4` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.UNABBREV_TAC `R` >> BETA_TAC \\
      Q.EXISTS_TAC `Q4` >> REWRITE_TAC [WEAK_EQUIV_REFL] \\
      Q.EXISTS_TAC `E1` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [] \\
      PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
      (* goal 4 (of 4) *)
      `?E1. EPS (H Q) E1 /\ WEAK_EQUIV E2 E1` by PROVE_TAC [WEAK_EQUIV_TRANS_tau] \\
      `?E3. EPS ((H o E) Q) E3 /\ WEAK_EQUIV E1 E3` by PROVE_TAC [WEAK_EQUIV_EPS] \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      `?P3. EPS (H P) P3 /\ WEAK_EQUIV P3 (H' P)` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      `?P4. EPS P' P4 /\ WEAK_EQUIV P4 P3` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      Q.EXISTS_TAC `P4` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.UNABBREV_TAC `R` >> BETA_TAC \\
      Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `P4` >> REWRITE_TAC [WEAK_EQUIV_REFL] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [] \\
      PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] ]);

(* These lemmas may apply at the final stage, it doesn't require (SG H), just (SEQ H) *)
val SEQ_EPS_lemma1 = Q.prove (
   `!E P Q R H. SG E /\ SEQ E /\ OBS_CONGR P (E P) /\ OBS_CONGR Q (E Q) /\ SEQ H /\
		(R = \x y. ?H. SEQ H /\ (x = H P) /\ (y = H Q)) ==>
	(!P'. EPS (H P) P' ==> ?Q'. EPS (H Q) Q' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q') /\
	(!Q'. EPS (H Q) Q' ==> ?P'. EPS (H P) P' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q')`,
    REPEAT GEN_TAC >> STRIP_TAC
 >> `OBS_CONGR (H P) ((H o E) P) /\ OBS_CONGR (H Q) ((H o E) Q)`
				by PROVE_TAC [OBS_CONGR_SUBST_SEQ, o_DEF]
 >> `SG (H o E) /\ SEQ (H o E)` by PROVE_TAC [SG_SEQ_compose]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] OBS_CONGR_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `Q`)) \\
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] OBS_CONGR_EPS') \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV (H' Q) E1` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H' Q` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] OBS_CONGR_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `P`)) \\
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] OBS_CONGR_EPS') \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV E2 Q'` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H' P` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [] ]);

val SEQ_EPS_lemma2 = Q.prove (
   `!E P Q R H. SG E /\ SEQ E /\ OBS_CONGR P (E P) /\ OBS_CONGR Q (E Q) /\ SEQ H /\
		(R = \x y. ?H. SEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q))
    ==> (!P'. EPS (H P) P' ==> ?Q'. EPS (H Q) Q' /\ (WEAK_EQUIV O R O STRONG_EQUIV) P' Q') /\
	(!Q'. EPS (H Q) Q' ==> ?P'. EPS (H P) P' /\ (STRONG_EQUIV O R O WEAK_EQUIV) P' Q')`,
    REPEAT GEN_TAC >> STRIP_TAC
 >> `OBS_CONGR (H P) ((H o E) P) /\ OBS_CONGR (H Q) ((H o E) Q)`
				by PROVE_TAC [OBS_CONGR_SUBST_SEQ, o_DEF]
 >> `SG (H o E) /\ SEQ (H o E)` by PROVE_TAC [SG_SEQ_compose]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] OBS_CONGR_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `Q`)) \\
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] OBS_CONGR_EPS') \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV (H' Q) E1` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H' Q` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `P'` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL] \\
      PROVE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] OBS_CONGR_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `P`)) \\
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] OBS_CONGR_EPS') \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV E2 Q'` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `Q'` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `H' P` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL] \\
      PROVE_TAC [WEAK_EQUIV_SYM] ]);

(*
val OBS_UNIQUE_SOLUTIONS = store_thm (
   "OBS_UNIQUE_SOLUTIONS",
  ``!E. SG E /\ SEQ E ==>
	!P Q. OBS_CONGR P (E P) /\ OBS_CONGR Q (E Q) ==> OBS_CONGR P Q``,
    REPEAT STRIP_TAC
 >> irule (REWRITE_RULE [RSUBSET] OBS_BISIM_UPTO_THM)
 >> Q.EXISTS_TAC `\x y. ?H. SEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)`
 >> BETA_TAC >> REVERSE CONJ_TAC
 >- ( Q.EXISTS_TAC `\x. x` >> BETA_TAC \\
      KILL_TAC >> REWRITE_TAC [SEQ1, WEAK_EQUIV_REFL] )
 >> REWRITE_TAC [OBS_BISIM_UPTO]
 >> Q.X_GEN_TAC `P'`
 >> Q.X_GEN_TAC `Q'`
 >> BETA_TAC >> STRIP_TAC
 >> ASM_REWRITE_TAC []
 >> Q.ABBREV_TAC `R = \x y. ?H. SEQ H /\ OBS_CONGR x (H P) /\ OBS_CONGR y (H Q)`
 >> `OBS_CONGR (H P) ((H o E) P) /\ OBS_CONGR (H Q) ((H o E) Q)`
					by PROVE_TAC [OBS_CONGR_SUBST_SEQ, o_DEF]
 >> `SG (H o E) /\ SEQ (H o E)` by PROVE_TAC [SG_SEQ_compose]
 >> GEN_TAC >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      `?E2. WEAK_TRANS (H P) u E2 /\ WEAK_EQUIV E1 E2` by PROVE_TAC [OBS_CONGR_HALF_LEFT] \\
      `?E3. WEAK_TRANS ((H o E) P) u E3 /\ WEAK_EQUIV E2 E3`
				by PROVE_TAC [OBS_CONGR_WEAK_TRANS] \\
      Q.PAT_X_ASSUM `WEAK_TRANS ((H o E) P) u E3`
	(STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
      IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `TRANS (H' P) u E2'` by PROVE_TAC [] \\
      IMP_RES_TAC (Q.SPEC `H'` OBS_UNIQUE_SOLUTIONS_LEMMA) \\
      NTAC 7 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `EPS (H'' P) E3` by PROVE_TAC [] \\
      MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H''`] SEQ_EPS_lemma2) \\
      RW_TAC std_ss []
      Q.UNABBREV_TAC `R`
 *)
(*
 (case 1)                              (case 2)
   P'  -------- tau -----> E1            P'  ------------------ l --------------> E1
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   H P ======== eps =====> E2            H P ================== l ==============> E2
   |                       |             |                                        |
   ~~c                     ~~            ~~c                                      ~~
   |                       |             |                                        |
   H(E(P)) ==== eps =====> E1' ----+     H(E(P)) ==eps=> E1'  ==l=> E2'   ==eps=> E3 ~~ ?
                          (H' P)   |                    (H' P)     (H'' P)              |
                                   R                                                    R
                                   |                                                    |
   H(E(Q)) ==== eps =====> H' Q ---+     H(E(Q)) ==eps=> H' Q ==l=> H'' Q ==eps=> Q' ~~ ?
   |                       |             |                                        |
   ~~c                     ~~            ~~c                                      ~~
   |                       |             |                                        |
   H Q ======== eps =====> ?             H Q ================== l ==============> ?
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   Q'  ======== eps =====> ?             Q'  ================== l ==============> ?
 *)

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
