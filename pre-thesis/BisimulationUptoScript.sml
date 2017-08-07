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

val _ = new_theory "BisimulationUpto";

(******************************************************************************)
(*                                                                            *)
(*                     Strong Bisimulation Upto ~                             *)
(*                                                                            *)
(******************************************************************************)

(* Define the strong bisimulation relation up to STRONG_EQUIV *)
val STRONG_BISIM_UPTO = new_definition (
   "STRONG_BISIM_UPTO",
  ``STRONG_BISIM_UPTO (Bsm :('a, 'b) simulation) =
    !E E'.
	Bsm E E' ==>
	!u. (!E1. TRANS E u E1 ==> 
		  ?E2. TRANS E' u E2 /\ (STRONG_EQUIV O Bsm O STRONG_EQUIV) E1 E2) /\
	    (!E2. TRANS E' u E2 ==> 
		  ?E1. TRANS E u E1 /\ (STRONG_EQUIV O Bsm O STRONG_EQUIV) E1 E2)``);

val IDENTITY_STRONG_BISIM_UPTO_lemma = store_thm (
   "IDENTITY_STRONG_BISIM_UPTO_lemma",
  ``!E. (STRONG_EQUIV O (\x y. x = y) O STRONG_EQUIV) E E``,
    GEN_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC
 >> NTAC 2 (Q.EXISTS_TAC `E` >> REWRITE_TAC [STRONG_EQUIV_REFL]));

val IDENTITY_STRONG_BISIM_UPTO = store_thm (
   "IDENTITY_STRONG_BISIM_UPTO", ``STRONG_BISIM_UPTO (\x y. x = y)``,
    PURE_ONCE_REWRITE_TAC [STRONG_BISIM_UPTO]
 >> BETA_TAC
 >> REPEAT STRIP_TAC (* 2 sub-goals *)
 >| [ (* goal 1 *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E:('a, 'b) CCS = E'``]
			       (ASSUME ``TRANS E u E1``)) \\
      EXISTS_TAC ``E1 :('a, 'b) CCS`` \\
      ASM_REWRITE_TAC [] \\
      REWRITE_TAC [IDENTITY_STRONG_BISIM_UPTO_lemma],
      (* goal 2 *)
      PURE_ONCE_ASM_REWRITE_TAC [] \\
      EXISTS_TAC ``E2 :('a, 'b) CCS`` \\
      ASM_REWRITE_TAC [] \\
      REWRITE_TAC [IDENTITY_STRONG_BISIM_UPTO_lemma] ]);

val CONVERSE_STRONG_BISIM_UPTO_lemma = Q.prove (
   `!Wbsm E E'. (STRONG_EQUIV O (\x y. Wbsm y x) O STRONG_EQUIV) E E' =
		(STRONG_EQUIV O Wbsm O STRONG_EQUIV) E' E`,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      `STRONG_EQUIV y' E` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      `STRONG_EQUIV E' y` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      Q.EXISTS_TAC `y'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      `STRONG_EQUIV E y` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      `STRONG_EQUIV y' E'` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      Q.EXISTS_TAC `y'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [] ]);

val CONVERSE_STRONG_BISIM_UPTO = store_thm (
   "CONVERSE_STRONG_BISIM_UPTO",
  ``!Wbsm. STRONG_BISIM_UPTO Wbsm ==> STRONG_BISIM_UPTO (\x y. Wbsm y x)``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_BISIM_UPTO]
 >> BETA_TAC
 >> rpt STRIP_TAC
 >> RES_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [CONVERSE_STRONG_BISIM_UPTO_lemma] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [CONVERSE_STRONG_BISIM_UPTO_lemma] \\
      ASM_REWRITE_TAC [] ]);

val STRONG_BISIM_UPTO_LEMMA = store_thm (
   "STRONG_BISIM_UPTO_LEMMA",
  ``!Bsm. STRONG_BISIM_UPTO Bsm ==> STRONG_BISIM (STRONG_EQUIV O Bsm O STRONG_EQUIV)``,
    GEN_TAC
 >> REWRITE_TAC [STRONG_BISIM, O_DEF]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM `STRONG_EQUIV E y'`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `u`)) \\
      POP_ASSUM K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `STRONG_BISIM_UPTO Bsm`
	(STRIP_ASSUME_TAC o (REWRITE_RULE [STRONG_BISIM_UPTO])) \\
      RES_TAC \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF])) \\
      Q.PAT_X_ASSUM `STRONG_EQUIV y E'`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `u`)) \\
      POP_ASSUM K_TAC \\
      POP_ASSUM (STRIP_ASSUME_TAC o
		 (fn th => MATCH_MP th (ASSUME ``TRANS y u E2'``))) \\
(***
                  E    ~   y'    Bsm    y    ~   E'
                  |       /              \       |
                  u      u                u      u
                  |     /                  \     |
                  E1 ~ E2 ~ y''' Bsm y'' ~ E2' ~ E2''
 ***)
      `STRONG_EQUIV E1 y'''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      `STRONG_EQUIV y'' E2''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM `STRONG_EQUIV y E'`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `u`)) \\
      Q.PAT_X_ASSUM `!E1. TRANS y u E1 ==> P` K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `STRONG_BISIM_UPTO Bsm`
	(STRIP_ASSUME_TAC o (REWRITE_RULE [STRONG_BISIM_UPTO])) \\
      RES_TAC \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF])) \\
      Q.PAT_X_ASSUM `STRONG_EQUIV E y'`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `u`)) \\
      Q.PAT_X_ASSUM `!E1. TRANS E u E1 ==> P` K_TAC \\
      POP_ASSUM (STRIP_ASSUME_TAC o
		 (fn th => MATCH_MP th (ASSUME ``TRANS y' u E1'``))) \\
(***
               E    ~     y'     Bsm    y   ~   E'
               |         /               \      |
               u        u                 u     u
               |       /                   \    |
               E1'' ~ E1' ~ y''' Bsm y'' ~ E1 ~ E2
 ***)
      `STRONG_EQUIV E1'' y'''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      `STRONG_EQUIV y'' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      Q.EXISTS_TAC `E1''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] ]);

val STRONG_BISIM_UPTO_THM = store_thm (
   "STRONG_BISIM_UPTO_THM",
  ``!Bsm. STRONG_BISIM_UPTO Bsm ==> Bsm RSUBSET STRONG_EQUIV``,
    rpt STRIP_TAC
 >> IMP_RES_TAC STRONG_BISIM_UPTO_LEMMA
 >> IMP_RES_TAC STRONG_BISIM_SUBSET_STRONG_EQUIV
 >> Suff `Bsm RSUBSET (STRONG_EQUIV O Bsm O STRONG_EQUIV)`
 >- ( DISCH_TAC \\
      Know `transitive ((RSUBSET) :('a, 'b) simulation -> ('a, 'b) simulation -> bool)`
      >- PROVE_TAC [RSUBSET_WeakOrder, WeakOrder] \\
      RW_TAC std_ss [transitive_def] >> RES_TAC )
 >> KILL_TAC
 >> REWRITE_TAC [RSUBSET, O_DEF]
 >> rpt STRIP_TAC
 >> `STRONG_EQUIV x x /\ STRONG_EQUIV y y` by PROVE_TAC [STRONG_EQUIV_REFL]
 >> Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC []
 (* Hence, to prove P ~ Q, we only have to find a strong bisimulation up to ~
    which contains (P, Q) *));

(******************************************************************************)
(*                                                                            *)
(*                       Weak Bisimulation Upto ~                             *)
(*                                                                            *)
(******************************************************************************)

(* NOTE: the definition in Milner's book [1] is wrong, we use the one in Gorrieri's book [2],
         double-confirmed with Sangiorgi's book [3].

   IMPORTANT: in HOL's big "O", the second argument to composition acts on the "input" first,
         so we need to revert the order of (?a O Wbsm O ?b) when ?a and ?b are different.
 *)
val WEAK_BISIM_UPTO = new_definition (
   "WEAK_BISIM_UPTO",
  ``WEAK_BISIM_UPTO (Wbsm: ('a, 'b) simulation) =
    !E E'.
	Wbsm E E' ==>
	(!l.
	  (!E1. TRANS E  (label l) E1 ==>
		?E2. WEAK_TRANS E' (label l) E2 /\ (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2) /\
	  (!E2. TRANS E' (label l) E2 ==>
		?E1. WEAK_TRANS E  (label l) E1 /\ (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2)) /\
	(!E1. TRANS E  tau E1 ==> ?E2. EPS E' E2 /\ (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2) /\
	(!E2. TRANS E' tau E2 ==> ?E1. EPS E  E1 /\ (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2)``);

(* Extracted above definition into smaller pieces for easier uses *)
val WEAK_BISIM_UPTO_TRANS_label = store_thm (
   "WEAK_BISIM_UPTO_TRANS_label",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !l E1. TRANS E (label l) E1 ==>
		      ?E2. WEAK_TRANS E' (label l) E2 /\ (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO]);

val WEAK_BISIM_UPTO_TRANS_label' = store_thm (
   "WEAK_BISIM_UPTO_TRANS_label'",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !l E2. TRANS E' (label l) E2 ==>
		      ?E1. WEAK_TRANS E  (label l) E1 /\ (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO]);

val WEAK_BISIM_UPTO_TRANS_tau = store_thm (
   "WEAK_BISIM_UPTO_TRANS_tau",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E1. TRANS E tau E1 ==> ?E2. EPS E' E2 /\ (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO]);

val WEAK_BISIM_UPTO_TRANS_tau' = store_thm (
   "WEAK_BISIM_UPTO_TRANS_tau'",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E2. TRANS E' tau E2 ==> ?E1. EPS E  E1 /\ (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO]);

val IDENTITY_WEAK_BISIM_UPTO_lemma = store_thm (
   "IDENTITY_WEAK_BISIM_UPTO_lemma",
  ``!E. (WEAK_EQUIV O (\x y. x = y) O STRONG_EQUIV) E E``,
    GEN_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC
 >> Q.EXISTS_TAC `E` >> REWRITE_TAC [WEAK_EQUIV_REFL]
 >> Q.EXISTS_TAC `E` >> REWRITE_TAC [STRONG_EQUIV_REFL]);

val IDENTITY_WEAK_BISIM_UPTO_lemma' = store_thm (
   "IDENTITY_WEAK_BISIM_UPTO_lemma'",
  ``!E. (STRONG_EQUIV O (\x y. x = y) O WEAK_EQUIV) E E``,
    GEN_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC
 >> Q.EXISTS_TAC `E` >> REWRITE_TAC [STRONG_EQUIV_REFL]
 >> Q.EXISTS_TAC `E` >> REWRITE_TAC [WEAK_EQUIV_REFL]);

val IDENTITY_WEAK_BISIM_UPTO = store_thm (
   "IDENTITY_WEAK_BISIM_UPTO", ``WEAK_BISIM_UPTO (\x y. x = y)``,
    PURE_ONCE_REWRITE_TAC [WEAK_BISIM_UPTO]
 >> BETA_TAC
 >> REPEAT STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E :('a, 'b) CCS = E'``]
			       (ASSUME ``TRANS E (label l) E1``)) \\
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [IDENTITY_WEAK_BISIM_UPTO_lemma],
      (* goal 2 (of 4) *)
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [IDENTITY_WEAK_BISIM_UPTO_lemma'],
      (* goal 3 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E :('a, 'b) CCS = E'``]
			       (ASSUME ``TRANS E tau E1``)) \\
      IMP_RES_TAC ONE_TAU \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [IDENTITY_WEAK_BISIM_UPTO_lemma],
      (* goal 4 (of 4) *)
      IMP_RES_TAC ONE_TAU \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [IDENTITY_WEAK_BISIM_UPTO_lemma'] ]);

val CONVERSE_WEAK_BISIM_UPTO_lemma = store_thm (
   "CONVERSE_WEAK_BISIM_UPTO_lemma",
  ``!Wbsm E E'. (WEAK_EQUIV O (\x y. Wbsm y x) O STRONG_EQUIV) E E' =
		(STRONG_EQUIV O Wbsm O WEAK_EQUIV) E' E``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      `STRONG_EQUIV y' E` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      `WEAK_EQUIV E' y` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `y'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      `STRONG_EQUIV E y` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      `WEAK_EQUIV y' E'` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `y'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [] ]);

val CONVERSE_WEAK_BISIM_UPTO_lemma' = store_thm (
   "CONVERSE_WEAK_BISIM_UPTO_lemma'",
  ``!Wbsm E E'. (STRONG_EQUIV O (\x y. Wbsm y x) O WEAK_EQUIV) E E' =
		(WEAK_EQUIV O Wbsm O STRONG_EQUIV) E' E``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      `STRONG_EQUIV E' y` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      `WEAK_EQUIV y' E` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `y'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      `STRONG_EQUIV y' E'` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      `WEAK_EQUIV E y` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `y'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [] ]);

val CONVERSE_WEAK_BISIM_UPTO = store_thm (
   "CONVERSE_WEAK_BISIM_UPTO",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==> WEAK_BISIM_UPTO (\x y. Wbsm y x)``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_BISIM_UPTO]
 >> BETA_TAC
 >> rpt STRIP_TAC
 >> RES_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [CONVERSE_WEAK_BISIM_UPTO_lemma] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [CONVERSE_WEAK_BISIM_UPTO_lemma'] \\
      ASM_REWRITE_TAC [],
      (* goal 3 (of 4) *)
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [CONVERSE_WEAK_BISIM_UPTO_lemma] \\
      ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [CONVERSE_WEAK_BISIM_UPTO_lemma'] \\
      ASM_REWRITE_TAC [] ]);

val WEAK_BISIM_UPTO_EPS = store_thm ((* NEW *)
   "WEAK_BISIM_UPTO_EPS",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2``,
    rpt STRIP_TAC
 >> PAT_X_ASSUM ``WEAK_BISIM_UPTO Wbsm`` MP_TAC
 >> Q.PAT_X_ASSUM `Wbsm E E'` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`E1`, `E1`)
 >> Q.SPEC_TAC (`E`, `E`)
 >> HO_MATCH_MP_TAC EPS_ind_right (* must use right induct here! *)
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E'` \\
      RW_TAC std_ss [EPS_REFL] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `E'` >> REWRITE_TAC [WEAK_EQUIV_REFL] \\
      Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL],
      (* goal 2 (of 2) *)
      RES_TAC \\
      POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF])) \\
      STRIP_ASSUME_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
					  (ASSUME ``STRONG_EQUIV E1 y'``)) \\
      RES_TAC \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      STRIP_ASSUME_TAC (REWRITE_RULE [WEAK_BISIM_UPTO]
				     (ASSUME ``WEAK_BISIM_UPTO Wbsm``)) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`y'`, `y`])) \\
      RES_TAC \\
      NTAC 7 (POP_ASSUM K_TAC) \\
      Q.PAT_X_ASSUM `Wbsm y' y ==> X` K_TAC \\
      Q.PAT_X_ASSUM `!l E1. TRANS y' (label l) E1 ==> P` K_TAC \\
      Q.PAT_X_ASSUM `!l E2. TRANS y (label l) E2 ==> P` K_TAC \\
      IMP_RES_TAC WEAK_EQUIV_EPS \\
      Q.EXISTS_TAC `E2'''` \\
      CONJ_TAC >- IMP_RES_TAC EPS_TRANS \\
      Q.PAT_X_ASSUM `X E2' E2''` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
(* Induct case:
      E                Wbsm                E'
                                           ||
      ...                                 eps
                                           ||
      E1   ~    y'     Wbsm      y    =~   E2
      |        /                 \\        ||
     tau     tau                 eps      eps
      |      /                     \\      ||
      E1' ~ E2' ~ y''' Wbsm y'' =~ E2'' =~ E2'''
 *)
      `WEAK_EQUIV y'' E2'''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      `STRONG_EQUIV E1' y'''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] ]);

val WEAK_BISIM_UPTO_EPS' = store_thm ((* NEW *)
   "WEAK_BISIM_UPTO_EPS'",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP CONVERSE_WEAK_BISIM_UPTO))
 >> IMP_RES_TAC WEAK_BISIM_UPTO_EPS
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [GSYM CONVERSE_WEAK_BISIM_UPTO_lemma]
 >> ASM_REWRITE_TAC []);

(* Proof sketch:
      E            Wbsm              E'
      ||                             ||
      eps                            eps
      ||                             ||
      E1' ~ y'     Wbsm     y  =~    E2'    (WEAK_BISIM_UPTO_EPS)
      |     |               ||       ||
      |     l               l        ||
      l     |               ||       l
      |  ~ E2'' (~ Wbsm =~) E2''' =~ ||
      E2                             E2'''' (WEAK_BISIM_UPTO_TRANS_label)
      || ~  y'''   Wbsm     y''   =~ ||
      eps   ||              ||       eps
      ||    eps             eps      ||
      ||    ||              ||       ||
      E1 ~ E2'5 (~ Wbsm =~) E2'6  =~ E2'7   (WEAK_BISIM_UPTO_EPS)
 *)
val WEAK_BISIM_UPTO_WEAK_TRANS_label = store_thm ((* NEW *)
   "WEAK_BISIM_UPTO_WEAK_TRANS_label",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !l E1. WEAK_TRANS E (label l) E1 ==>
		      ?E2. WEAK_TRANS E' (label l) E2 /\
			   (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2``,
    rpt STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS
 >> IMP_RES_TAC (MATCH_MP WEAK_BISIM_UPTO_EPS (* lemma 1 used here *)
			  (ASSUME ``WEAK_BISIM_UPTO Wbsm``))
 >> POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF]))
 >> IMP_RES_TAC PROPERTY_STAR_TRANS
 >> IMP_RES_TAC WEAK_BISIM_UPTO_TRANS_label
 >> POP_ASSUM K_TAC
 >> IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_label
 >> Know `(WEAK_EQUIV O Wbsm O STRONG_EQUIV) E2 E2''''`
 >- ( Q.PAT_X_ASSUM `X E2'' E2'''` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      `STRONG_EQUIV E2 y'''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      `WEAK_EQUIV y'' E2''''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] )
 >> DISCH_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF]))
 >> IMP_RES_TAC (MATCH_MP STRONG_EQUIV_EPS
			  (ASSUME ``STRONG_EQUIV E2 y'''``))
 >> IMP_RES_TAC (Q.SPECL [`y'''`, `y''`]
			 (MATCH_MP WEAK_BISIM_UPTO_EPS (* lemma 1 used here *)
				   (ASSUME ``WEAK_BISIM_UPTO Wbsm``)))
 >> NTAC 3 (POP_ASSUM K_TAC)
 >> IMP_RES_TAC (MATCH_MP WEAK_EQUIV_EPS
			  (ASSUME ``WEAK_EQUIV y'' E2''''``))
 >> Know `(WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2'''''''`
 >- ( Q.PAT_X_ASSUM `X E2''''' E2''''''` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      `STRONG_EQUIV E1 y'''''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      `WEAK_EQUIV y'''' E2'''''''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''''` >> ASM_REWRITE_TAC [] )
 >> DISCH_TAC
 >> Q.EXISTS_TAC `E2'''''''`
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC EPS_AND_WEAK
 >> take [`E2'`, `E2''''`]
 >> ASM_REWRITE_TAC []);

val WEAK_BISIM_UPTO_WEAK_TRANS_label' = store_thm ((* NEW *)
   "WEAK_BISIM_UPTO_WEAK_TRANS_label'",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !l E2. WEAK_TRANS E' (label l) E2 ==>
		      ?E1. WEAK_TRANS E (label l) E1 /\
			   (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP CONVERSE_WEAK_BISIM_UPTO))
 >> IMP_RES_TAC WEAK_BISIM_UPTO_WEAK_TRANS_label
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [GSYM CONVERSE_WEAK_BISIM_UPTO_lemma]
 >> ASM_REWRITE_TAC []);

(* If S is a bisimulation up to WEAK_EQUIV, then (WEAK_EQUIV O S O WEAK_EQUIV) is
   a weak bisimultion. *)
val WEAK_BISIM_UPTO_LEMMA = store_thm (
   "WEAK_BISIM_UPTO_LEMMA",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==> WEAK_BISIM (WEAK_EQUIV O Wbsm O WEAK_EQUIV)``,
    GEN_TAC
 >> REWRITE_TAC [WEAK_BISIM, O_DEF]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_label (ASSUME ``WEAK_EQUIV E y'``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_BISIM_UPTO_WEAK_TRANS_label
			    (ASSUME ``WEAK_BISIM_UPTO Wbsm``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label
			    (ASSUME ``WEAK_EQUIV y E'``)) \\
      Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `X E2 E2'` (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF])) \\
(***
               E    ~=   y'    Wbsm     y    ~=   E'
               |        //              \\        ||
              !l       l                 l        l
               |      //                  \\      ||
               E1 ~= E2 ~ y''' Wbsm y'' ~= E2' ~= E2''
 ***)
      `WEAK_EQUIV E2 y'''` by PROVE_TAC [STRONG_IMP_WEAK_EQUIV] \\
      `WEAK_EQUIV E1 y'''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      `WEAK_EQUIV y'' E2''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_label' (ASSUME ``WEAK_EQUIV y E'``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_BISIM_UPTO_WEAK_TRANS_label'
			    (ASSUME ``WEAK_BISIM_UPTO Wbsm``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label'
			    (ASSUME ``WEAK_EQUIV E y'``)) \\
      Q.EXISTS_TAC `E1''` >> ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `X E1' E1` (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF])) \\
(***
               E    ~=     y'      Wbsm    y   ~=   E'
               ||         //               \\       |
               l         l                  l       l
               ||       //                   \\     |
               E1'' ~= E1' ~= y''' Wbsm y'' ~ E1 ~= E2
 ***)
      `WEAK_EQUIV E1'' y'''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      `WEAK_EQUIV y'' E1` by PROVE_TAC [STRONG_IMP_WEAK_EQUIV] \\
      `WEAK_EQUIV y'' E2` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [],
      (* goal 3 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau (ASSUME ``WEAK_EQUIV E y'``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_BISIM_UPTO_EPS (ASSUME ``WEAK_BISIM_UPTO Wbsm``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_EPS (ASSUME ``WEAK_EQUIV y E'``)) \\
      Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `X E2 E2'` (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF])) \\
(***
               E    ~=   y'    Wbsm     y    ~=   E'
               |        //              \\        ||
              tau      eps               eps      eps
               |      //                  \\      ||
               E1 ~= E2 ~ y''' Wbsm y'' ~= E2' ~= E2''
 ***)
      `WEAK_EQUIV E2 y'''` by PROVE_TAC [STRONG_IMP_WEAK_EQUIV] \\
      `WEAK_EQUIV E1 y'''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      `WEAK_EQUIV y'' E2''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau' (ASSUME ``WEAK_EQUIV y E'``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_BISIM_UPTO_EPS' (ASSUME ``WEAK_BISIM_UPTO Wbsm``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_EPS' (ASSUME ``WEAK_EQUIV E y'``)) \\
      Q.EXISTS_TAC `E1''` >> ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `X E1' E1` (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF])) \\
(***
               E    ~=     y'      Wbsm    y   ~=   E'
               ||         //               \\       |
               eps       eps                eps     tau
               ||       //                   \\     |
               E1'' ~= E1' ~= y''' Wbsm y'' ~ E1 ~= E2
 ***)
      `WEAK_EQUIV E1'' y'''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      `WEAK_EQUIV y'' E1` by PROVE_TAC [STRONG_IMP_WEAK_EQUIV] \\
      `WEAK_EQUIV y'' E2` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] ]);

val WEAK_BISIM_UPTO_THM = store_thm (
   "WEAK_BISIM_UPTO_THM",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==> Wbsm RSUBSET WEAK_EQUIV``,
    rpt STRIP_TAC
 >> IMP_RES_TAC WEAK_BISIM_UPTO_LEMMA
 >> IMP_RES_TAC WEAK_BISIM_SUBSET_WEAK_EQUIV
 >> Suff `Wbsm RSUBSET (WEAK_EQUIV O Wbsm O WEAK_EQUIV)`
 >- ( DISCH_TAC \\
      Know `transitive ((RSUBSET) :('a, 'b) simulation -> ('a, 'b) simulation -> bool)`
      >- PROVE_TAC [RSUBSET_WeakOrder, WeakOrder] \\
      RW_TAC std_ss [transitive_def] >> RES_TAC )
 >> KILL_TAC
 >> REWRITE_TAC [RSUBSET, O_DEF]
 >> rpt STRIP_TAC
 >> `WEAK_EQUIV x x /\ WEAK_EQUIV y y` by PROVE_TAC [WEAK_EQUIV_REFL]
 >> Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC []
 (* Hence, to prove P =~ Q, we only have to find a strong bisimulation up to =~
    which contains (P, Q) *));

(* Bibliography:
 *
 * [1] Milner, R.: Communication and concurrency. (1989).
.* [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer, Cham (2015).
 * [3] Sangiorgi, D.: Introduction to Bisimulation and Coinduction. Cambridge University Press (2011).
 * [4] Sangiorgi, D., Rutten, J.: Advanced Topics in Bisimulation and Coinduction.
				  Cambridge University Press (2011).
 *)

val _ = export_theory ();
val _ = print_theory_to_file "-" "BisimulationUpto.lst";
val _ = DB.html_theory "BisimulationUpto";

(* last updated: Aug 5, 2017 *)
