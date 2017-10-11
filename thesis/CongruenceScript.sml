(* ========================================================================== *)
(* FILE          : CongruenceScript.sml                                       *)
(* DESCRIPTION   : The theory of congruence and guarded contexts              *)
(*                                                                            *)
(* THESIS        : A Formalization of Unique Solutions of Equations in        *)
(*                 Process Algebra                                            *)
(* AUTHOR        : (c) Chun Tian, University of Bologna                       *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory combinTheory arithmeticTheory;
open CCSLib CCSTheory;
open StrongEQTheory StrongLawsTheory WeakEQTheory WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory ObsCongrConv;

val _ = new_theory "Congruence";
val _ = temp_loose_equality ();

(******************************************************************************)
(*                                                                            *)
(*                one-hole contexts and multi-hole contexts                   *)
(*                                                                            *)
(******************************************************************************)

val _ = type_abbrev ("context", ``:('a, 'b) CCS -> ('a, 'b) CCS``);

(* ONE HOLE CONTEXT for CCS *)
val (OH_CONTEXT_rules, OH_CONTEXT_ind, OH_CONTEXT_cases) = Hol_reln `
    (                        OH_CONTEXT (\t. t)) /\		 (* OH_CONTEXT1 *)
    (!a c.  OH_CONTEXT c ==> OH_CONTEXT (\t. prefix a (c t))) /\ (* OH_CONTEXT2 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. sum (c t) x)) /\	 (* OH_CONTEXT3 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. sum x (c t))) /\	 (* OH_CONTEXT4 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. par (c t) x)) /\	 (* OH_CONTEXT5 *)
    (!x c.  OH_CONTEXT c ==> OH_CONTEXT (\t. par x (c t))) /\	 (* OH_CONTEXT6 *)
    (!L c.  OH_CONTEXT c ==> OH_CONTEXT (\t. restr L (c t))) /\	 (* OH_CONTEXT7 *)
    (!rf c. OH_CONTEXT c ==> OH_CONTEXT (\t. relab (c t) rf)) `; (* OH_CONTEXT8 *)

val [OH_CONTEXT1, OH_CONTEXT2, OH_CONTEXT3, OH_CONTEXT4, OH_CONTEXT5, OH_CONTEXT6,
     OH_CONTEXT7, OH_CONTEXT8] =
    map save_thm
        (combine (["OH_CONTEXT1", "OH_CONTEXT2", "OH_CONTEXT3", "OH_CONTEXT4",
		   "OH_CONTEXT5", "OH_CONTEXT6", "OH_CONTEXT7", "OH_CONTEXT8"],
                  CONJUNCTS OH_CONTEXT_rules));

val OH_CONTEXT_combin = store_thm (
   "OH_CONTEXT_combin", ``!c1 c2. OH_CONTEXT c1 /\ OH_CONTEXT c2 ==> OH_CONTEXT (c1 o c2)``,
    REPEAT STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c1`, `c`)
 >> HO_MATCH_MP_TAC OH_CONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> REPEAT STRIP_TAC (* 7 sub-goals here *)
 >| [ FULL_SIMP_TAC std_ss [OH_CONTEXT2],
      FULL_SIMP_TAC std_ss [OH_CONTEXT3],
      FULL_SIMP_TAC std_ss [OH_CONTEXT4],
      FULL_SIMP_TAC std_ss [OH_CONTEXT5],
      FULL_SIMP_TAC std_ss [OH_CONTEXT6],
      FULL_SIMP_TAC std_ss [OH_CONTEXT7],
      FULL_SIMP_TAC std_ss [OH_CONTEXT8] ]);

(* multi-hole (or non-hole) contexts. *)
val (CONTEXT_rules, CONTEXT_ind, CONTEXT_cases) = Hol_reln `
    (        CONTEXT (\t. t)) /\                               (* CONTEXT1 *)
    (!p.     CONTEXT (\t. p)) /\                               (* CONTEXT2 *)
    (!a e.   CONTEXT e ==> CONTEXT (\t. prefix a (e t))) /\    (* CONTEXT3 *)
    (!e1 e2. CONTEXT e1 /\ CONTEXT e2
		       ==> CONTEXT (\t. sum (e1 t) (e2 t))) /\ (* CONTEXT4 *)
    (!e1 e2. CONTEXT e1 /\ CONTEXT e2
		       ==> CONTEXT (\t. par (e1 t) (e2 t))) /\ (* CONTEXT5 *)
    (!L e.   CONTEXT e ==> CONTEXT (\t. restr L (e t))) /\     (* CONTEXT6 *)
    (!rf e.  CONTEXT e ==> CONTEXT (\t. relab (e t) rf)) `;    (* CONTEXT7 *)

val [CONTEXT1, CONTEXT2, CONTEXT3, CONTEXT4, CONTEXT5, CONTEXT6, CONTEXT7] =
    map save_thm
        (combine (["CONTEXT1", "CONTEXT2", "CONTEXT3", "CONTEXT4", "CONTEXT5",
		   "CONTEXT6", "CONTEXT7"],
                  CONJUNCTS CONTEXT_rules));

val CONTEXT3a = store_thm (
   "CONTEXT3a",
  ``!a :'b Action. CONTEXT (\t. prefix a t)``,
    ASSUME_TAC CONTEXT1
 >> IMP_RES_TAC CONTEXT3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

val CONTEXT_combin = store_thm (
   "CONTEXT_combin", ``!c1 c2. CONTEXT c1 /\ CONTEXT c2 ==> CONTEXT (c1 o c2)``,
    REPEAT STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c1`, `c`)
 >> HO_MATCH_MP_TAC CONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> REPEAT STRIP_TAC (* 6 sub-goals here *)
 >| [ REWRITE_TAC [CONTEXT2],
      FULL_SIMP_TAC std_ss [CONTEXT3],
      FULL_SIMP_TAC std_ss [CONTEXT4],
      FULL_SIMP_TAC std_ss [CONTEXT5],
      FULL_SIMP_TAC std_ss [CONTEXT6],
      FULL_SIMP_TAC std_ss [CONTEXT7] ]);

(* One-hole contexts are also multi-hole contexts *)
val OH_CONTEXT_IS_CONTEXT = store_thm (
   "OH_CONTEXT_IS_CONTEXT", ``!c. OH_CONTEXT c ==> CONTEXT c``,
    Induct_on `OH_CONTEXT`
 >> rpt STRIP_TAC (* 8 sub-goals here *)
 >| [ (* goal 1 (of 8) *)
      REWRITE_TAC [CONTEXT1],
      (* goal 2 (of 8) *)
      MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [],
      (* goal 3 (of 8) *)
      `CONTEXT (\y. x)` by REWRITE_TAC [CONTEXT2] \\
      Know `CONTEXT (\t. c t + (\y. x) t)`
      >- ( MATCH_MP_TAC CONTEXT4 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 4 (of 8) *)
      `CONTEXT (\y. x)` by REWRITE_TAC [CONTEXT2] \\
      Know `CONTEXT (\t. (\y. x) t + c t)`
      >- ( MATCH_MP_TAC CONTEXT4 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 5 (of 8) *)
      `CONTEXT (\y. x)` by REWRITE_TAC [CONTEXT2] \\
      Know `CONTEXT (\t. c t || (\y. x) t)`
      >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 6 (of 8) *)
      `CONTEXT (\y. x)` by REWRITE_TAC [CONTEXT2] \\
      Know `CONTEXT (\t. (\y. x) t || c t)`
      >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 7 (of 8) *)
      MATCH_MP_TAC CONTEXT6 >> ASM_REWRITE_TAC [],
      (* goal 8 (of 8) *)
      MATCH_MP_TAC CONTEXT7 >> ASM_REWRITE_TAC [] ]);

val STRONG_EQUIV_SUBST_CONTEXT = store_thm (
   "STRONG_EQUIV_SUBST_CONTEXT",
  ``!P Q. STRONG_EQUIV P Q ==> !E. CONTEXT E ==> STRONG_EQUIV (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `CONTEXT` >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
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

val OBS_CONGR_SUBST_CONTEXT = store_thm (
   "OBS_CONGR_SUBST_CONTEXT",
  ``!P Q. OBS_CONGR P Q ==> !E. CONTEXT E ==> OBS_CONGR (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `CONTEXT` >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
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

(******************************************************************************)
(*                                                                            *)
(*             Multi-hole context with guarded sums (GCONTEXT)                *)
(*                                                                            *)
(******************************************************************************)

val (GCONTEXT_rules, GCONTEXT_ind, GCONTEXT_cases) = Hol_reln `
    (        GCONTEXT (\t. t)) /\                                (* GCONTEXT1 *)
    (!p.     GCONTEXT (\t. p)) /\                                (* GCONTEXT2 *)
    (!a e.   GCONTEXT e ==> GCONTEXT (\t. prefix a (e t))) /\    (* GCONTEXT3 *)
    (!a1 a2 e1 e2.
	     GCONTEXT e1 /\ GCONTEXT e2
			==> GCONTEXT (\t. sum (prefix a1 (e1 t)) (* GCONTEXT4 *)
					      (prefix a2 (e2 t)))) /\
    (!e1 e2. GCONTEXT e1 /\ GCONTEXT e2
			==> GCONTEXT (\t. par (e1 t) (e2 t))) /\ (* GCONTEXT5 *)
    (!L e.   GCONTEXT e ==> GCONTEXT (\t. restr L (e t))) /\     (* GCONTEXT6 *)
    (!rf e.  GCONTEXT e ==> GCONTEXT (\t. relab (e t) rf)) `;    (* GCONTEXT7 *)

val [GCONTEXT1, GCONTEXT2, GCONTEXT3, GCONTEXT4, GCONTEXT5,
     GCONTEXT6, GCONTEXT7] =
    map save_thm
        (combine (["GCONTEXT1", "GCONTEXT2", "GCONTEXT3", "GCONTEXT4",
		   "GCONTEXT5", "GCONTEXT6", "GCONTEXT7"],
                  CONJUNCTS GCONTEXT_rules));

val GCONTEXT3a = store_thm (
   "GCONTEXT3a",
  ``!a :'b Action. GCONTEXT (\t. prefix a t)``,
    ASSUME_TAC GCONTEXT1
 >> IMP_RES_TAC GCONTEXT3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

val GCONTEXT_combin = store_thm (
   "GCONTEXT_combin", ``!c1 c2. GCONTEXT c1 /\ GCONTEXT c2 ==> GCONTEXT (c1 o c2)``,
    REPEAT STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c1`, `c`)
 >> HO_MATCH_MP_TAC GCONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> rpt STRIP_TAC (* 6 sub-goals here *)
 >| [ REWRITE_TAC [GCONTEXT2],
      FULL_SIMP_TAC std_ss [GCONTEXT3],
      FULL_SIMP_TAC std_ss [GCONTEXT4],
      FULL_SIMP_TAC std_ss [GCONTEXT5],
      FULL_SIMP_TAC std_ss [GCONTEXT6],
      FULL_SIMP_TAC std_ss [GCONTEXT7] ]);

val GCONTEXT_IS_CONTEXT = store_thm (
   "GCONTEXT_IS_CONTEXT", ``!c. GCONTEXT c ==> CONTEXT c``,
    Induct_on `GCONTEXT`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      REWRITE_TAC [CONTEXT1],
      (* goal 2 (of 7) *)
      REWRITE_TAC [CONTEXT2],
      (* goal 3 (of 7) *)
      MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [],
      (* goal 4 (of 7) *)
      Know `CONTEXT (\t. (prefix a1 (e1 t)))`
      >- ( MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [] ) \\
      Know `CONTEXT (\t. (prefix a2 (e2 t)))`
      >- ( MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [] ) \\
      KILL_TAC \\
      NTAC 2 DISCH_TAC \\
      Know `CONTEXT (\t. (\t. (prefix a1 (e1 t))) t + (\t. (prefix a2 (e2 t))) t)`
      >- ( MATCH_MP_TAC CONTEXT4 >> ASM_REWRITE_TAC [] ) \\
      BETA_TAC >> REWRITE_TAC [],
      (* goal 5 (of 7) *)
      MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [],
      (* goal 6 (of 7) *)
      MATCH_MP_TAC CONTEXT6 >> ASM_REWRITE_TAC [],
      (* goal 7 (of 7) *)
      MATCH_MP_TAC CONTEXT7 >> ASM_REWRITE_TAC [] ]);

val WEAK_EQUIV_SUBST_GCONTEXT = store_thm (
   "WEAK_EQUIV_SUBST_GCONTEXT",
  ``!P Q. WEAK_EQUIV P Q ==> !E. GCONTEXT E ==> WEAK_EQUIV (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `GCONTEXT`
 >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [WEAK_EQUIV_REFL]
 >| [ (* goal 1 (of 5) *)
      MATCH_MP_TAC WEAK_EQUIV_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 2 (of 5) *)
      MATCH_MP_TAC WEAK_EQUIV_PRESD_BY_GUARDED_SUM \\
      ASM_REWRITE_TAC [],
      (* goal 3 (of 5) *)
      IMP_RES_TAC WEAK_EQUIV_PRESD_BY_PAR,
      (* goal 4 (of 5) *)
      MATCH_MP_TAC WEAK_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [],
      (* goal 5 (of 5) *)
      MATCH_MP_TAC WEAK_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ]);

(******************************************************************************)
(*                                                                            *)
(*                      congruence and precongruence                         *)
(*                                                                            *)
(******************************************************************************)

val precongruence_def = Define `
    precongruence R = !x y ctx. CONTEXT ctx ==> R x y ==> R (ctx x) (ctx y)`;

(* a special version of precongruence with only guarded sums *)
val precongruence1_def = Define `
    precongruence1 R = !x y ctx. GCONTEXT ctx ==> R x y ==> R (ctx x) (ctx y)`;

(* The definition of congruence for CCS, TODO: use precongruence *)
val congruence_def = Define `
    congruence R = equivalence R /\ precongruence R`;

(* a special version of congruence with only guarded sums *)
val congruence1_def = Define `
    congruence1 R = equivalence R /\ precongruence1 R`;

val STRONG_EQUIV_congruence = store_thm (
   "STRONG_EQUIV_congruence", ``congruence STRONG_EQUIV``,
    REWRITE_TAC [congruence_def, STRONG_EQUIV_equivalence]
 >> PROVE_TAC [precongruence_def, STRONG_EQUIV_SUBST_CONTEXT]);

val WEAK_EQUIV_congruence = store_thm (
   "WEAK_EQUIV_congruence", ``congruence1 WEAK_EQUIV``,
    REWRITE_TAC [congruence1_def, WEAK_EQUIV_equivalence]
 >> PROVE_TAC [precongruence1_def, WEAK_EQUIV_SUBST_GCONTEXT]);

val OBS_CONGR_congruence = store_thm (
   "OBS_CONGR_congruence", ``congruence OBS_CONGR``,
    REWRITE_TAC [congruence_def, OBS_CONGR_equivalence]
 >> PROVE_TAC [precongruence_def, OBS_CONGR_SUBST_CONTEXT]);

(* Building congruence closure from an equivalence relation *)
val CC_def = Define `
    CC R = (\g h. !c. CONTEXT c ==> R (c g) (c h))`;

val _ = add_rule { fixity = Suffix 2100,
                   block_style = (AroundEachPhrase, (Portable.CONSISTENT,0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "^c"],
                   term_name = "CC" };
val _ = TeX_notation { hol = "^c", TeX = ("\\HOLTokenSupC{}", 1) };

val GCC_def = Define `
    GCC R = (\g h. !c. GCONTEXT c ==> R (c g) (c h))`;

val _ = add_rule { fixity = Suffix 2100,
                   block_style = (AroundEachPhrase, (Portable.CONSISTENT,0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "^g"],
                   term_name = "GCC" };
val _ = TeX_notation { hol = "^g", TeX = ("\\HOLTokenSupG{}", 1) };

(* The built relation is indeed congruence *)
val CC_congruence = store_thm (
   "CC_congruence", ``!R. equivalence R ==> congruence (CC R)``,
    REWRITE_TAC [congruence_def, precongruence_def, CC_def]
 >> RW_TAC std_ss [] (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [equivalence_def] \\
      rpt STRIP_TAC >| (* 3 sub-goals here *)
      [ (* goal 1.1 (of 3) *)
        REWRITE_TAC [reflexive_def] >> BETA_TAC \\
        rpt STRIP_TAC \\
        PROVE_TAC [equivalence_def, reflexive_def],
        (* goal 1.2 (of 3) *)
        REWRITE_TAC [symmetric_def] >> BETA_TAC \\
        rpt GEN_TAC >> EQ_TAC >> rpt STRIP_TAC >> RES_TAC \\ (* 2 sub-goals here *)
        PROVE_TAC [equivalence_def, symmetric_def],
        (* goal 1.3 (of 3) *)
        REWRITE_TAC [transitive_def] >> BETA_TAC \\
        rpt STRIP_TAC >> RES_TAC \\
        PROVE_TAC [equivalence_def, transitive_def] ],
      (* goal 2 (of 2) *)
      `CONTEXT (c o ctx)` by PROVE_TAC [CONTEXT_combin] \\
      RES_TAC >> FULL_SIMP_TAC std_ss [o_THM] ]);

(* The congruence is finer than original relation *)
val CC_is_finer = store_thm (
   "CC_is_finer", ``!R. (CC R) RSUBSET R``,
    REWRITE_TAC [RSUBSET]
 >> REPEAT GEN_TAC
 >> REWRITE_TAC [CC_def]
 >> BETA_TAC
 >> REPEAT STRIP_TAC
 >> `CONTEXT (\x. x)` by PROVE_TAC [CONTEXT_rules]
 >> RES_TAC
 >> POP_ASSUM (ACCEPT_TAC o BETA_RULE));

(* The congruence built by above method is the coarsest congruence contained in R *)
val CC_is_coarsest = store_thm (
   "CC_is_coarsest",
  ``!R R'. congruence R' /\ R' RSUBSET R ==> R' RSUBSET (CC R)``,
    REWRITE_TAC [congruence_def, precongruence_def, RSUBSET, CC_def]
 >> RW_TAC std_ss []);

(******************************************************************************)
(*                                                                            *)
(*                  CCS Expressions (CONTEXT with constants)                  *)
(*                                                                            *)
(******************************************************************************)

val (EXPR_rules, EXPR_ind, EXPR_cases) = Hol_reln `
    (                      EXPR (\t. t)) /\		    (* EXPR1 *)
    (!p.                   EXPR (\t. p)) /\		    (* EXPR2 *)
    (!a e.   EXPR e    ==> EXPR (\t. prefix a (e t))) /\    (* EXPR3 *)
    (!e1 e2. EXPR e1 /\ EXPR e2
		       ==> EXPR (\t. sum (e1 t) (e2 t))) /\ (* EXPR4 *)
    (!e1 e2. EXPR e1 /\ EXPR e2
		       ==> EXPR (\t. par (e1 t) (e2 t))) /\ (* EXPR5 *)
    (!L e.   EXPR e    ==> EXPR (\t. restr L (e t))) /\	    (* EXPR6 *)
    (!rf e.  EXPR e    ==> EXPR (\t. relab (e t) rf)) /\    (* EXPR7 *)
    (!X e.   EXPR e /\ EXPR (\t. CCS_Subst (e t) (rec X (e t)) X)
		       ==> EXPR (\t. rec X (e t))) `;	    (* EXPR8 *)

val [EXPR1, EXPR2, EXPR3, EXPR4, EXPR5, EXPR6, EXPR7, EXPR8] =
    map save_thm
        (combine (["EXPR1", "EXPR2", "EXPR3", "EXPR4",
		   "EXPR5", "EXPR6", "EXPR7", "EXPR8"], CONJUNCTS EXPR_rules));

(* Some typical expressions containing constants (TODO) *)
val var_IS_EXPR = store_thm (
   "var_IS_EXPR", ``!X. EXPR (\t. var X)``,
    REWRITE_TAC [EXPR2]);

val CONTEXT_IS_EXPR = store_thm (
   "CONTEXT_IS_EXPR", ``!e. CONTEXT e ==> EXPR e``,
    Induct_on `CONTEXT`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ REWRITE_TAC [EXPR1],
      REWRITE_TAC [EXPR2],
      MATCH_MP_TAC EXPR3 >> art [],
      MATCH_MP_TAC EXPR4 >> art [],
      MATCH_MP_TAC EXPR5 >> art [],
      MATCH_MP_TAC EXPR6 >> art [],
      MATCH_MP_TAC EXPR7 >> art [] ]);

(******************************************************************************)
(*                                                                            *)
(*                     Weakly guarded (WG) expressions                        *)
(*                                                                            *)
(******************************************************************************)

val (WG_rules, WG_ind, WG_cases) = Hol_reln `
    (!p.                        WG (\t. p)) /\                   (* WG2 *)
    (!a e.   EXPR e         ==> WG (\t. prefix a (e t))) /\      (* WG3 *)
    (!e1 e2. WG e1 /\ WG e2 ==> WG (\t. sum (e1 t) (e2 t))) /\   (* WG4 *)
    (!e1 e2. WG e1 /\ WG e2 ==> WG (\t. par (e1 t) (e2 t))) /\   (* WG5 *)
    (!L e.   WG e           ==> WG (\t. restr L (e t))) /\       (* WG6 *)
    (!rf e.  WG e           ==> WG (\t. relab (e t) rf)) /\      (* WG7 *)
    (!X e.   WG e  /\ WG (\t. CCS_Subst (e t) (rec X (e t)) X)
			    ==> WG (\t. rec X (e t))) `;	 (* WG8 *)

val [WG2, WG3, WG4, WG5, WG6, WG7, WG8] =
    map save_thm
        (combine (["WG2", "WG3", "WG4", "WG5", "WG6", "WG7", "WG8"], CONJUNCTS WG_rules));

(** WG1 is derivable from WG3 *)
val WG1 = store_thm ("WG1",
  ``!a :'b Action. WG (\t. prefix a t)``,
    ASSUME_TAC EXPR1
 >> IMP_RES_TAC WG3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> art []);

(* Weakly guarded expressions are also expressions *)
val WG_IS_EXPR = store_thm (
   "WG_IS_EXPR", ``!e. WG e ==> EXPR e``,
    Induct_on `WG`
 >> rpt STRIP_TAC (* 6 sub-goals here *)
 >| [ REWRITE_TAC [EXPR2],
      MATCH_MP_TAC EXPR3 >> art [],
      MATCH_MP_TAC EXPR4 >> art [],
      MATCH_MP_TAC EXPR5 >> art [],
      MATCH_MP_TAC EXPR6 >> art [],
      MATCH_MP_TAC EXPR7 >> art [],
      MATCH_MP_TAC EXPR8 >> art [] ]);

(******************************************************************************)
(*                                                                            *)
(*                     Strongly guarded (SG) expressions                      *)
(*                                                                            *)
(******************************************************************************)

(* X is guarded in E if each occurrence of X is within some subexpression of E of
   the form l.F *)
val (SG_rules, SG_ind, SG_cases) = Hol_reln `
    (!p.                        SG (\t. p)) /\                      (* SG1 *)
    (!l e.   CONTEXT e      ==> SG (\t. prefix (label l) (e t))) /\ (* SG2 *)
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
val SG_IS_CONTEXT = store_thm (
   "SG_IS_CONTEXT", ``!e. SG e ==> CONTEXT e``,
    Induct_on `SG`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ REWRITE_TAC [CONTEXT2],
      MATCH_MP_TAC CONTEXT3 >> art [],
      MATCH_MP_TAC CONTEXT3 >> art [],
      MATCH_MP_TAC CONTEXT4 >> art [],
      MATCH_MP_TAC CONTEXT5 >> art [],
      MATCH_MP_TAC CONTEXT6 >> art [],
      MATCH_MP_TAC CONTEXT7 >> art [] ]);

(* Strong guardness implies weak guardness *)
val SG_IMP_WG = store_thm (
   "SG_IMP_WG", ``!e. SG e ==> WG e``,
    Induct_on `SG`
 >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ REWRITE_TAC [WG2],
      MATCH_MP_TAC WG3 >> IMP_RES_TAC CONTEXT_IS_EXPR,
      MATCH_MP_TAC WG3 >> IMP_RES_TAC WG_IS_EXPR,
      MATCH_MP_TAC WG4 >> art [],
      MATCH_MP_TAC WG5 >> art [],
      MATCH_MP_TAC WG6 >> art [],
      MATCH_MP_TAC WG7 >> art [] ]);

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
      Cases_on `p` (* 8 or 9 sub-goals here *)
      >- PROVE_TAC [CCS_distinct']
      >- PROVE_TAC [CCS_distinct']
      >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	   `(e = \t. C') \/ (e = \t. C)` by PROVE_TAC [] \\ (* 2 sub-goals *)
	   ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
      >> PROVE_TAC [CCS_distinct'],
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
    rpt STRIP_TAC \\ (* 2 sub-goals here, same tacticals *)
  ( POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
      Cases_on `p` (* 8 or 9 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	   `((e = \t. C) \/ (e = \t. C')) /\ (e' = \t. C0)` by PROVE_TAC [] \\
	   ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
      >> PROVE_TAC [CCS_distinct],
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
    rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [SG_cases])) >| (* 7 sub-goals here *)
      [ (* goal 1.1 (of 7) *)
        POP_ASSUM (ASSUME_TAC o BETA_RULE o (ONCE_REWRITE_RULE [FUN_EQ_THM])) \\
	Cases_on `p` (* 8 or 9 sub-goals here *)
	>- PROVE_TAC [CCS_distinct]
	>- PROVE_TAC [CCS_distinct]
	>- PROVE_TAC [CCS_distinct]
	>- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	     (TRY (Cases_on `C'`) >> TRY (Cases_on `C`)) (* 8 or 9 sub-goals here *)
	  >- PROVE_TAC [CCS_distinct]
	  >- PROVE_TAC [CCS_distinct]
	  >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	       `(e = \t. C'') \/ (e = \t. C')` by PROVE_TAC [] \\
	       ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
	  >> PROVE_TAC [CCS_distinct] )
	>> PROVE_TAC [CCS_distinct],
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
	Cases_on `p` (* 8 or 9 sub-goals here *)
	>- PROVE_TAC [CCS_distinct]
	>- PROVE_TAC [CCS_distinct]
	>- PROVE_TAC [CCS_distinct]
	>- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	     Cases_on `C0` (* 8 or 9 sub-goals here *)
	  >- PROVE_TAC [CCS_distinct]
	  >- PROVE_TAC [CCS_distinct]
	  >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	       `(e' = \t. C'') \/ (e' = \t. C')` by PROVE_TAC [] \\
	       ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
	  >> PROVE_TAC [CCS_distinct] )
	>> PROVE_TAC [CCS_distinct],
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
      Cases_on `p` (* 8 or 9 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	   (TRY (Cases_on `C'`) >> TRY (Cases_on `C`)) (* 8 or 9 sub-goals here *)
	>- PROVE_TAC [CCS_distinct]
	>- PROVE_TAC [CCS_distinct]
	>- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	     `(e = \t. C'') \/ (e = \t. C')` by PROVE_TAC [] \\
	     ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
	>> PROVE_TAC [CCS_distinct] )
      >> PROVE_TAC [CCS_distinct],
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
      Cases_on `p` (* 8 or 9 sub-goals here *)
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- PROVE_TAC [CCS_distinct]
      >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	   Cases_on `C0` (* 8 or 9 sub-goals here *)
	>- PROVE_TAC [CCS_distinct]
        >- PROVE_TAC [CCS_distinct]
        >- ( FULL_SIMP_TAC std_ss [CCS_11] \\
	     `(e' = \t. C'') \/ (e' = \t. C')` by PROVE_TAC [] \\
	     ASM_REWRITE_TAC [] >> REWRITE_TAC [SG1] )
        >> PROVE_TAC [CCS_distinct] )
      >> PROVE_TAC [CCS_distinct],
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

(******************************************************************************)
(*                                                                            *)
(*                        Sequential (SEQ) expressions                        *)
(*                                                                            *)
(******************************************************************************)

(* X is sequential in E if every subexpression of E which contains X, apart from
   X itself, is of the form a.F or Sigma F_i *)
val (SEQ_rules, SEQ_ind, SEQ_cases) = Hol_reln `
    (                             SEQ (\t. t)) /\                  (* SEQ1 *)
    (!p.                          SEQ (\t. p)) /\                  (* SEQ2 *)
    (!a e.   SEQ e            ==> SEQ (\t. prefix a (e t))) /\	   (* SEQ3 *)
    (!e1 e2. SEQ e1 /\ SEQ e2 ==> SEQ (\t. sum (e1 t) (e2 t))) `;  (* SEQ4 *)

val [SEQ1, SEQ2, SEQ3, SEQ4] =
    map save_thm (combine (["SEQ1", "SEQ2", "SEQ3", "SEQ4"], CONJUNCTS SEQ_rules));

val SEQ3a = store_thm ("SEQ3a",
  ``!a :'b Action. SEQ (\t. prefix a t)``,
    ASSUME_TAC SEQ1
 >> IMP_RES_TAC SEQ3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

val SEQ_IS_CONTEXT = store_thm (
   "SEQ_IS_CONTEXT", ``!e. SEQ e ==> CONTEXT e``,
    Induct_on `SEQ`
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ REWRITE_TAC [CONTEXT1],
      REWRITE_TAC [CONTEXT2],
      MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC CONTEXT4 >> ASM_REWRITE_TAC [] ]);

val SEQ_combin = store_thm (
   "SEQ_combin", ``!E. SEQ E ==> !E'. SEQ E' ==> SEQ (E o E')``,
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
      MATCH_MP_TAC OBS_CONGR_SUBST_PREFIX \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC OBS_CONGR_PRESD_BY_SUM ]);

(* Sequential expression with guarded sums *)
val (GSEQ_rules, GSEQ_ind, GSEQ_cases) = Hol_reln `
    (                             GSEQ (\t. t)) /\                 (* GSEQ1 *)
    (!p.                          GSEQ (\t. p)) /\                 (* GSEQ2 *)
    (!a e.            GSEQ e  ==> GSEQ (\t. prefix a (e t))) /\	   (* GSEQ3 *)
    (!a1 a2 e1 e2.
           GSEQ e1 /\ GSEQ e2 ==> GSEQ (\t. sum (prefix a1 (e1 t)) (* GSEQ4 *)
						(prefix a2 (e2 t))))`;

val [GSEQ1, GSEQ2, GSEQ3, GSEQ4] =
    map save_thm (combine (["GSEQ1", "GSEQ2", "GSEQ3", "GSEQ4"], CONJUNCTS GSEQ_rules));

val GSEQ3a = store_thm ("GSEQ3a",
  ``!a :'b Action. GSEQ (\t. prefix a t)``,
    ASSUME_TAC GSEQ1
 >> IMP_RES_TAC GSEQ3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> REWRITE_TAC []);

val GSEQ_IS_CONTEXT = store_thm (
   "GSEQ_IS_CONTEXT", ``!e. GSEQ e ==> CONTEXT e``,
    Induct_on `GSEQ`
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ REWRITE_TAC [CONTEXT1],
      REWRITE_TAC [CONTEXT2],
      MATCH_MP_TAC CONTEXT3 >> ASM_REWRITE_TAC [],
      Q.PAT_X_ASSUM `CONTEXT e1` (ASSUME_TAC o (Q.SPEC `a1`) o (MATCH_MP CONTEXT3)) \\
      Q.PAT_X_ASSUM `CONTEXT e2` (ASSUME_TAC o (Q.SPEC `a2`) o (MATCH_MP CONTEXT3)) \\
      MP_TAC (Q.SPECL [`\t. (prefix a1 (e1 t))`, `\t. (prefix a2 (e2 t))`] CONTEXT4) \\
      BETA_TAC >> RW_TAC std_ss [] ]);

val GSEQ_combin = store_thm (
   "GSEQ_combin", ``!E. GSEQ E ==> !E'. GSEQ E' ==> GSEQ (E o E')``,
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
 >> rpt STRIP_TAC >> FULL_SIMP_TAC std_ss []  (* 3 sub-goals here *)
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
      Rev (Cases_on `a`) >| (* 2 sub-goals here *)
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
 >> rpt STRIP_TAC >> FULL_SIMP_TAC std_ss [] (* 3 sub-goals here *)
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
      Rev (Cases_on `a`) >| (* 2 sub-goals here *)
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
        MATCH_MP_TAC SG11 >> take [`e'`, `x`] >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 4) *)
        Q.PAT_X_ASSUM `!l1 e1 e2. X ==> R (\t. prefix (label l1) (e1 t) + prefix tau (e2 t))`
	  MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] \\
        Suff `SG e'` >- ( STRIP_TAC >> ASM_REWRITE_TAC [] >> METIS_TAC [] ) \\
        POP_ASSUM MP_TAC >> KILL_TAC >> DISCH_TAC \\
        MATCH_MP_TAC SG11' >> take [`e`, `x`] >> ASM_REWRITE_TAC [],
        (* goal 3.4 (of 4) *)
        Q.PAT_X_ASSUM `!l1 l2 e1 e2. X ==> R (\t. prefix (label l1) (e1 t) + prefix (label l2) (e2 t))`
	  MATCH_MP_TAC \\
        ASM_REWRITE_TAC [] ] ]);

val SG_SEQ_combin = store_thm (
   "SG_SEQ_combin", ``!E. SG E /\ SEQ E ==> !H. SEQ H ==> (SG (H o E) /\ SEQ (H o E))``,
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
        IMP_RES_TAC SEQ_IS_CONTEXT \\
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
      ASSUME_TAC (Q.SPEC `H` SEQ_combin) \\
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
      ASSUME_TAC (Q.SPEC `H` SEQ_combin) \\
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
      ASSUME_TAC (Q.SPEC `H` SEQ_combin) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [] ]);

val SG_GSEQ_combin = store_thm (
   "SG_GSEQ_combin", ``!E. SG E /\ GSEQ E ==> !H. GSEQ H ==> (SG (H o E) /\ GSEQ (H o E))``,
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
        IMP_RES_TAC GSEQ_IS_CONTEXT \\
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
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
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
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
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
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [],
      (* goal 9 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 9.1 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `tau`)) \\
        IMP_RES_TAC GSEQ_IS_CONTEXT \\
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
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [],
      (* goal 11 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 11.1 (of 4) *)
        IMP_RES_TAC SG3 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `tau`)) \\
        IMP_RES_TAC GSEQ_IS_CONTEXT \\
        Q.PAT_X_ASSUM `CONTEXT E` K_TAC \\
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
      ASSUME_TAC (Q.SPEC `H` GSEQ_combin) \\
      RES_TAC >> NTAC 3 (POP_ASSUM K_TAC) \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC >> REWRITE_TAC [],
      (* goal 13 (of 14) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`H`, `H`) \\
      Induct_on `GSEQ` >> BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 13.1 (of 4) *)
        IMP_RES_TAC GSEQ_IS_CONTEXT \\
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
      MP_TAC (Q.SPEC `H` GSEQ_combin) \\
      RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!E'. GSEQ E' ==> X`
	(MP_TAC o (Q.SPEC `\t. (label l1)..(e1 t) + (label l2)..(e2 t)`)) \\
      REWRITE_TAC [o_DEF] >> BETA_TAC >> METIS_TAC [] ]);

(******************************************************************************)
(*                                                                            *)
(*               Weakly guarded expressions with guarded sums                 *)
(*                                                                            *)
(******************************************************************************)

(* The only difference from WG is at WGS4, in which the sum has prefixed args *)
val (WGS_rules, WGS_ind, WGS_cases) = Hol_reln `
    (!p.                          WGS (\t. p)) /\                   (* WGS2 *)
    (!a e.   GCONTEXT e       ==> WGS (\t. prefix a (e t))) /\      (* WGS3 *)
    (!a1 a2 e1 e2.
	     WGS e1 /\ WGS e2 ==> WGS (\t. sum (prefix a1 (e1 t))   (* WGS4 *)
					       (prefix a2 (e2 t)))) /\
    (!e1 e2. WGS e1 /\ WGS e2 ==> WGS (\t. par (e1 t) (e2 t))) /\   (* WGS5 *)
    (!L e.   WGS e            ==> WGS (\t. restr L (e t))) /\       (* WGS6 *)
    (!rf e.  WGS e            ==> WGS (\t. relab (e t) rf)) `;      (* WGS7 *)

val [WGS2, WGS3, WGS4, WGS5, WGS6, WGS7] =
    map save_thm
        (combine (["WGS2", "WGS3", "WGS4", "WGS5", "WGS6", "WGS7"],
		  CONJUNCTS WGS_rules));

(** WGS1 is derivable from WGS3 *)
val WGS1 = store_thm ("WGS1",
  ``!a :'b Action. WGS (\t. prefix a t)``,
    ASSUME_TAC GCONTEXT1
 >> IMP_RES_TAC WGS3
 >> POP_ASSUM MP_TAC
 >> BETA_TAC
 >> REWRITE_TAC []);

val WGS_IS_GCONTEXT = store_thm (
   "WGS_IS_GCONTEXT", ``!e. WGS e ==> GCONTEXT e``,
    Induct_on `WGS`
 >> !! STRIP_TAC (* 6 sub-goals here *)
 >| [ REWRITE_TAC [GCONTEXT2],
      MATCH_MP_TAC GCONTEXT3 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC GCONTEXT4 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC GCONTEXT5 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC GCONTEXT6 >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC GCONTEXT7 >> ASM_REWRITE_TAC [] ]);

val WGS_IS_CONTEXT = store_thm (
   "WGS_IS_CONTEXT", ``!e. WGS e ==> CONTEXT e``,
    !! STRIP_TAC
 >> MATCH_MP_TAC GCONTEXT_IS_CONTEXT
 >> IMP_RES_TAC WGS_IS_GCONTEXT);

val GCONTEXT_WGS_combin = store_thm (
   "GCONTEXT_WGS_combin", ``!c e. GCONTEXT c /\ WGS e ==> WGS (c o e)``,
    rpt STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c`, `c`)
 >> HO_MATCH_MP_TAC GCONTEXT_ind
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> REWRITE_TAC [ETA_AX]
 >> rpt STRIP_TAC >> RES_TAC (* 6 sub-goals here *)
 >| [ (* goal 1 (of 6) *)
      REWRITE_TAC [WGS2],
      (* goal 2 (of 6) *)
      IMP_RES_TAC WGS_IS_GCONTEXT \\
      MP_TAC (Q.SPECL [`a`, `(\x. (c :('a, 'b) context) (e x))`] WGS3) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 3 (of 6) *)
      MP_TAC (Q.SPECL [`a1`, `a2`, `(\x. (c :('a, 'b) context) (e x))`,
				   `(\x. (c' :('a, 'b) context) (e x))`] WGS4) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 4 (of 6) *)
      MP_TAC (Q.SPECL [`(\x. (c :('a, 'b) context) (e x))`,
		       `(\x. (c' :('a, 'b) context) (e x))`] WGS5) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 5 (of 6) *)
      MP_TAC (Q.SPECL [`L`, `(\x. (c :('a, 'b) context) (e x))`] WGS6) \\
      BETA_TAC >> RW_TAC std_ss [],
      (* goal 6 (of 6) *)
      MP_TAC (Q.SPECL [`rf`, `(\x. (c :('a, 'b) context) (e x))`] WGS7) \\
      BETA_TAC >> RW_TAC std_ss [] ]);

val _ = export_theory ();
val _ = html_theory "Congruence";

(* last updated: Oct 2, 2017 *)
