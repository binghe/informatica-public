(* ========================================================================== *)
(* FILE          : BisimulationUptoScript.sml                                 *)
(* DESCRIPTION   : Bisimulation up to Strong, weak (2 versions) and OBS_CONGR *)
(*                                                                            *)
(* THESIS        : A Formalization of Unique Solutions of Equations in        *)
(*                 Process Algebra                                            *)
(* AUTHOR        : (c) Chun Tian, University of Bologna                       *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open relationTheory CCSLib CCSTheory;
open StrongEQTheory StrongEQLib StrongLawsTheory;
open WeakEQTheory WeakEQLib WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory;
open CongruenceTheory;

val _ = new_theory "BisimulationUpto";

(******************************************************************************)
(*                                                                            *)
(*                    1. Bisimulation Upto STRONG_EQUIV                       *)
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

(* To prove (STRONG_EQUIV P Q), we only have to find a weak bisimulation up to STRONG_EQUIV
   which contains (P, Q) *)
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
 >> Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*                     2. Bisimulation Upto WEAK_EQUIV                        *)
(*                                                                            *)
(******************************************************************************)

(* NOTE: this is actually Proposition 5.12 (section 5.7) in the ERRATA (1990) of [1].

   IMPORTANT: in HOL's big "O", the second argument to composition acts on the "input" first,
         so we need to revert the order of (?a O Wbsm O ?b) when ?a and ?b are different.
 *)
val WEAK_BISIM_UPTO = new_definition ("WEAK_BISIM_UPTO",
  ``WEAK_BISIM_UPTO (Wbsm: ('a, 'b) simulation) =
    !E E'. Wbsm E E' ==>
	(!l.
	  (!E1. TRANS E  (label l) E1 ==>
		?E2. WEAK_TRANS E' (label l) E2 /\ (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2) /\
	  (!E2. TRANS E' (label l) E2 ==>
		?E1. WEAK_TRANS E  (label l) E1 /\ (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2)) /\
	(!E1. TRANS E  tau E1 ==>
	      ?E2. EPS E' E2 /\ (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2) /\
	(!E2. TRANS E' tau E2 ==>
	      ?E1. EPS E  E1 /\ (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2)``);

(* Extracted above definition into smaller pieces for easier uses *)
val WEAK_BISIM_UPTO_TRANS_label = store_thm (
   "WEAK_BISIM_UPTO_TRANS_label",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !l E1. TRANS E (label l) E1 ==>
		      ?E2. WEAK_TRANS E' (label l) E2 /\
			   (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO]);

val WEAK_BISIM_UPTO_TRANS_label' = store_thm (
   "WEAK_BISIM_UPTO_TRANS_label'",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !l E2. TRANS E' (label l) E2 ==>
		      ?E1. WEAK_TRANS E  (label l) E1 /\
			   (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO]);

val WEAK_BISIM_UPTO_TRANS_tau = store_thm (
   "WEAK_BISIM_UPTO_TRANS_tau",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E1. TRANS E tau E1 ==>
		    ?E2. EPS E' E2 /\ (WEAK_EQUIV O Wbsm O STRONG_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO]);

val WEAK_BISIM_UPTO_TRANS_tau' = store_thm (
   "WEAK_BISIM_UPTO_TRANS_tau'",
  ``!Wbsm. WEAK_BISIM_UPTO Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E2. TRANS E' tau E2 ==>
		    ?E1. EPS E  E1 /\ (STRONG_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
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
 >> MATCH_MP_TAC EPS_WEAK_EPS
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

(* To prove (WEAK_EQUIV P Q), we only have to find a weak bisimulation up to WEAK_EQUIV
   which contains (P, Q) *)
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
 >> Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*            3. Bisimulation Upto WEAK_EQUIV (double-weak version)           *)
(*                                                                            *)
(******************************************************************************)

(* NOTE: the (original) definition in Milner's 1989 book [1] is wrong, this is the
         corrected Definition 5.8 in the ERRATA (1990) of [1]. *)
val WEAK_BISIM_UPTO2 = new_definition ("WEAK_BISIM_UPTO2",
  ``WEAK_BISIM_UPTO2 (Wbsm: ('a, 'b) simulation) =
    !E E'. Wbsm E E' ==>
	(!l.
	  (!E1. WEAK_TRANS E  (label l) E1 ==>
		?E2. WEAK_TRANS E' (label l) E2 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2) /\
	  (!E2. WEAK_TRANS E' (label l) E2 ==>
		?E1. WEAK_TRANS E  (label l) E1 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2)) /\
	(!E1. WEAK_TRANS E  tau E1 ==>
	      ?E2. EPS E' E2 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2) /\
	(!E2. WEAK_TRANS E' tau E2 ==>
	      ?E1. EPS E  E1 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2)``);

(* Extracted above definition into smaller pieces for easier uses *)
val WEAK_BISIM_UPTO2_WEAK_TRANS_label = store_thm (
   "WEAK_BISIM_UPTO2_WEAK_TRANS_label",
  ``!Wbsm. WEAK_BISIM_UPTO2 Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !l E1. WEAK_TRANS E (label l) E1 ==>
		      ?E2. WEAK_TRANS E' (label l) E2 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO2]);

val WEAK_BISIM_UPTO2_WEAK_TRANS_label' = store_thm (
   "WEAK_BISIM_UPTO2_WEAK_TRANS_label'",
  ``!Wbsm. WEAK_BISIM_UPTO2 Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !l E2. WEAK_TRANS E' (label l) E2 ==>
		      ?E1. WEAK_TRANS E  (label l) E1 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO2]);

val WEAK_BISIM_UPTO2_WEAK_TRANS_tau = store_thm (
   "WEAK_BISIM_UPTO2_WEAK_TRANS_tau",
  ``!Wbsm. WEAK_BISIM_UPTO2 Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E1. WEAK_TRANS E tau E1 ==>
		    ?E2. EPS E' E2 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO2]);

val WEAK_BISIM_UPTO2_WEAK_TRANS_tau' = store_thm (
   "WEAK_BISIM_UPTO2_WEAK_TRANS_tau'",
  ``!Wbsm. WEAK_BISIM_UPTO2 Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E2. WEAK_TRANS E' tau E2 ==>
		    ?E1. EPS E  E1 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    PROVE_TAC [WEAK_BISIM_UPTO2]);

val WEAK_BISIM_UPTO2_EPS = store_thm ((* NEW *)
   "WEAK_BISIM_UPTO2_EPS",
  ``!Wbsm. WEAK_BISIM_UPTO2 Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    rpt STRIP_TAC
 >> IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E'` >> REWRITE_TAC [EPS_REFL] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `E'` >> REWRITE_TAC [WEAK_EQUIV_REFL] \\
      Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL],
      (* goal 2 (of 2) *)
      PROVE_TAC [WEAK_BISIM_UPTO2] ]);

val WEAK_BISIM_UPTO2_EPS' = store_thm ((* NEW *)
   "WEAK_BISIM_UPTO2_EPS'",
  ``!Wbsm. WEAK_BISIM_UPTO2 Wbsm ==>
	!E E'. Wbsm E E' ==>
	       !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ (WEAK_EQUIV O Wbsm O WEAK_EQUIV) E1 E2``,
    rpt STRIP_TAC
 >> IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E` >> REWRITE_TAC [EPS_REFL] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL] \\
      Q.EXISTS_TAC `E` >> REWRITE_TAC [WEAK_EQUIV_REFL] \\
      PROVE_TAC [],
      (* goal 2 (of 2) *)
      PROVE_TAC [WEAK_BISIM_UPTO2] ]);

(* If S is a bisimulation up to WEAK_EQUIV, then (WEAK_EQUIV O S O WEAK_EQUIV) is
   a weak bisimultion. *)
val WEAK_BISIM_UPTO2_LEMMA = store_thm (
   "WEAK_BISIM_UPTO2_LEMMA",
  ``!Wbsm. WEAK_BISIM_UPTO2 Wbsm ==> WEAK_BISIM (WEAK_EQUIV O Wbsm O WEAK_EQUIV)``,
    GEN_TAC
 >> REWRITE_TAC [WEAK_BISIM, O_DEF]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_label (ASSUME ``WEAK_EQUIV E y'``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_BISIM_UPTO2_WEAK_TRANS_label
			    (ASSUME ``WEAK_BISIM_UPTO2 Wbsm``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label
			    (ASSUME ``WEAK_EQUIV y E'``)) \\
      Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `X E2 E2'` (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF])) \\
(***
               E    ~=   y'     Wbsm     y    ~=   E'
               |        //               \\        ||
              !l       l                  l        l
               |      //                   \\      ||
               E1 ~= E2 ~~ y''' Wbsm y'' ~= E2' ~= E2''
 ***)
      `WEAK_EQUIV E1 y'''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      `WEAK_EQUIV y'' E2''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_label' (ASSUME ``WEAK_EQUIV y E'``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_BISIM_UPTO2_WEAK_TRANS_label'
			    (ASSUME ``WEAK_BISIM_UPTO2 Wbsm``)) \\
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
      `WEAK_EQUIV y'' E2` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [],
      (* goal 3 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau (ASSUME ``WEAK_EQUIV E y'``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_BISIM_UPTO2_EPS (ASSUME ``WEAK_BISIM_UPTO2 Wbsm``)) \\
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
      `WEAK_EQUIV E1 y'''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      `WEAK_EQUIV y'' E2''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau' (ASSUME ``WEAK_EQUIV y E'``)) \\
      IMP_RES_TAC (MATCH_MP WEAK_BISIM_UPTO2_EPS' (ASSUME ``WEAK_BISIM_UPTO2 Wbsm``)) \\
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
      `WEAK_EQUIV y'' E2` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] ]);

(* To prove (WEAK_EQUIV P Q), we only have to find a weak bisimulation up to WEAK_EQUIV
   which contains (P, Q) *)
val WEAK_BISIM_UPTO2_THM = store_thm (
   "WEAK_BISIM_UPTO2_THM",
  ``!Wbsm. WEAK_BISIM_UPTO2 Wbsm ==> Wbsm RSUBSET WEAK_EQUIV``,
    rpt STRIP_TAC
 >> IMP_RES_TAC WEAK_BISIM_UPTO2_LEMMA
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
 >> Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*          4. Bisimulation upto WEAK_EQUIV, contained in OBS_CONGR           *)
(*                                                                            *)
(******************************************************************************)

(* this work is now useless *)
val OBS_BISIM_UPTO = new_definition ("OBS_BISIM_UPTO",
  ``OBS_BISIM_UPTO (Obsm: ('a, 'b) simulation) =
    !E E'. Obsm E E' ==>
      !u. (!E1. TRANS E  u E1 ==>
		?E2. WEAK_TRANS E' u E2 /\ (WEAK_EQUIV O Obsm O STRONG_EQUIV) E1 E2) /\
	  (!E2. TRANS E' u E2 ==>
		?E1. WEAK_TRANS E  u E1 /\ (STRONG_EQUIV O Obsm O WEAK_EQUIV) E1 E2)``);

val OBS_BISIM_UPTO_TRANS = store_thm (
   "OBS_BISIM_UPTO_TRANS",
  ``!Obsm. OBS_BISIM_UPTO Obsm ==>
	!E E'. Obsm E E' ==>
	       !u E1. TRANS E u E1 ==>
		      ?E2. WEAK_TRANS E' u E2 /\ (WEAK_EQUIV O Obsm O STRONG_EQUIV) E1 E2``,
    PROVE_TAC [OBS_BISIM_UPTO]);

val OBS_BISIM_UPTO_TRANS' = store_thm (
   "OBS_BISIM_UPTO_TRANS'",
  ``!Obsm. OBS_BISIM_UPTO Obsm ==>
	!E E'. Obsm E E' ==>
	       !u E2. TRANS E' u E2 ==>
		      ?E1. WEAK_TRANS E  u E1 /\ (STRONG_EQUIV O Obsm O WEAK_EQUIV) E1 E2``,
    PROVE_TAC [OBS_BISIM_UPTO]);

val IDENTITY_OBS_BISIM_UPTO = store_thm (
   "IDENTITY_OBS_BISIM_UPTO", ``OBS_BISIM_UPTO (\x y. x = y)``,
    PURE_ONCE_REWRITE_TAC [OBS_BISIM_UPTO]
 >> BETA_TAC
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E :('a, 'b) CCS = E'``]
			       (ASSUME ``TRANS E u E1``)) \\
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [IDENTITY_WEAK_BISIM_UPTO_lemma],
      (* goal 2 (of 4) *)
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [IDENTITY_WEAK_BISIM_UPTO_lemma'] ]);

val CONVERSE_OBS_BISIM_UPTO = store_thm (
   "CONVERSE_OBS_BISIM_UPTO",
  ``!Obsm. OBS_BISIM_UPTO Obsm ==> OBS_BISIM_UPTO (\x y. Obsm y x)``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_BISIM_UPTO]
 >> BETA_TAC
 >> rpt STRIP_TAC
 >> RES_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [CONVERSE_WEAK_BISIM_UPTO_lemma] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [CONVERSE_WEAK_BISIM_UPTO_lemma'] \\
      ASM_REWRITE_TAC [] ]);

val OBS_BISIM_UPTO_EPS = store_thm ((* NEW *)
   "OBS_BISIM_UPTO_EPS",
  ``!Obsm. OBS_BISIM_UPTO Obsm ==>
	!E E'. Obsm E E' ==>
	       !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ (WEAK_EQUIV O Obsm O STRONG_EQUIV) E1 E2``,
    rpt STRIP_TAC
 >> PAT_X_ASSUM ``OBS_BISIM_UPTO Obsm`` MP_TAC
 >> Q.PAT_X_ASSUM `Obsm E E'` MP_TAC
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
      IMP_RES_TAC PROPERTY_STAR_TRANS \\
      IMP_RES_TAC OBS_BISIM_UPTO_TRANS \\
      IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_tau \\
      Q.EXISTS_TAC `E2'''` \\
      CONJ_TAC >- IMP_RES_TAC EPS_TRANS \\
      Q.PAT_X_ASSUM `X E2' E2''` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
(* Induct case:
      E                Obsm                E'
                                           ||
      ...                                 eps
                                           ||
      E1   ~    y'     Obsm      y    =~   E2
      |        /                 \\        ||
     tau     tau                 tau      eps
      |      /                     \\      ||
      E1' ~ E2' ~ y''' Obsm y'' =~ E2'' =~ E2'''
 *)
      `WEAK_EQUIV y'' E2'''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      `STRONG_EQUIV E1' y'''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] ]);

val OBS_BISIM_UPTO_EPS' = store_thm ((* NEW *)
   "OBS_BISIM_UPTO_EPS'",
  ``!Obsm. OBS_BISIM_UPTO Obsm ==>
	!E E'. Obsm E E' ==>
	       !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ (STRONG_EQUIV O Obsm O WEAK_EQUIV) E1 E2``,
    GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP CONVERSE_OBS_BISIM_UPTO))
 >> IMP_RES_TAC OBS_BISIM_UPTO_EPS
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [GSYM CONVERSE_WEAK_BISIM_UPTO_lemma]
 >> ASM_REWRITE_TAC []);

(* Proof sketch:
      E            Obsm              E'
      ||                             ||
      eps                            eps
      ||                             ||
      E1' ~ y'     Obsm     y  =~    E2'    (WEAK_BISIM_UPTO_EPS)
      |     |               ||       ||
      |     l               l        ||
      l     |               ||       l
      |  ~ E2'' (~ Obsm =~) E2''' =~ ||
      E2                             E2'''' (WEAK_BISIM_UPTO_TRANS_label)
      || ~  y'''   Obsm     y''   =~ ||
      eps   ||              ||       eps
      ||    eps             eps      ||
      ||    ||              ||       ||
      E1 ~ E2'5 (~ Obsm =~) E2'6  =~ E2'7   (WEAK_BISIM_UPTO_EPS)
 *)
val OBS_BISIM_UPTO_WEAK_TRANS_label = store_thm ((* NEW *)
   "OBS_BISIM_UPTO_WEAK_TRANS_label",
  ``!Obsm. OBS_BISIM_UPTO Obsm ==>
	!E E'. Obsm E E' ==>
	       !l E1. WEAK_TRANS E (label l) E1 ==>
		      ?E2. WEAK_TRANS E' (label l) E2 /\
			   (WEAK_EQUIV O Obsm O STRONG_EQUIV) E1 E2``,
    rpt STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS
 >> IMP_RES_TAC (MATCH_MP OBS_BISIM_UPTO_EPS (* lemma 1 used here *)
			  (ASSUME ``OBS_BISIM_UPTO Obsm``))
 >> POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [O_DEF]))
 >> IMP_RES_TAC PROPERTY_STAR_TRANS
 >> IMP_RES_TAC OBS_BISIM_UPTO_TRANS
 >> POP_ASSUM K_TAC
 >> IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_label
 >> Know `(WEAK_EQUIV O Obsm O STRONG_EQUIV) E2 E2''''`
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
			 (MATCH_MP OBS_BISIM_UPTO_EPS (* lemma 1 used here *)
				   (ASSUME ``OBS_BISIM_UPTO Obsm``)))
 >> NTAC 3 (POP_ASSUM K_TAC)
 >> IMP_RES_TAC (MATCH_MP WEAK_EQUIV_EPS
			  (ASSUME ``WEAK_EQUIV y'' E2''''``))
 >> Know `(WEAK_EQUIV O Obsm O STRONG_EQUIV) E1 E2'''''''`
 >- ( Q.PAT_X_ASSUM `X E2''''' E2''''''` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      `STRONG_EQUIV E1 y'''''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      `WEAK_EQUIV y'''' E2'''''''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y''''` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `y'''''` >> ASM_REWRITE_TAC [] )
 >> DISCH_TAC
 >> Q.EXISTS_TAC `E2'''''''`
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC EPS_WEAK_EPS
 >> take [`E2'`, `E2''''`]
 >> ASM_REWRITE_TAC []);

val OBS_BISIM_UPTO_WEAK_TRANS_label' = store_thm ((* NEW *)
   "OBS_BISIM_UPTO_WEAK_TRANS_label'",
  ``!Obsm. OBS_BISIM_UPTO Obsm ==>
	!E E'. Obsm E E' ==>
	       !l E2. WEAK_TRANS E' (label l) E2 ==>
		      ?E1. WEAK_TRANS E (label l) E1 /\
			   (STRONG_EQUIV O Obsm O WEAK_EQUIV) E1 E2``,
    GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP CONVERSE_OBS_BISIM_UPTO))
 >> IMP_RES_TAC OBS_BISIM_UPTO_WEAK_TRANS_label
 >> POP_ASSUM MP_TAC
 >> BETA_TAC >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [GSYM CONVERSE_WEAK_BISIM_UPTO_lemma]
 >> ASM_REWRITE_TAC []);

(* To prove (OBS_CONGR P Q), we only have to find a `Obs` bisimulation up to WEAK_EQUIV
   which contains (P, Q) *)
val OBS_BISIM_UPTO_THM = store_thm (
   "OBS_BISIM_UPTO_THM",
  ``!Obsm. OBS_BISIM_UPTO Obsm ==> Obsm RSUBSET OBS_CONGR``,
    REWRITE_TAC [RSUBSET]
 >> rpt STRIP_TAC
 >> STRIP_ASSUME_TAC (REWRITE_RULE [OBS_BISIM_UPTO] (ASSUME ``OBS_BISIM_UPTO Obsm``))
 >> RES_TAC
 >> Q.PAT_X_ASSUM `!E E'. Obsm E E' ==> P` K_TAC
 >> REWRITE_TAC [OBS_CONGR]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      RES_TAC \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      irule (REWRITE_RULE [RSUBSET] WEAK_BISIM_UPTO_THM) \\
      Q.EXISTS_TAC `(WEAK_EQUIV O Obsm O STRONG_EQUIV)` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [WEAK_BISIM_UPTO] >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 1.1 (of 4) *)
        Q.PAT_X_ASSUM `X E E'` (STRIP_ASSUME_TAC o BETA_RULE o (REWRITE_RULE [O_DEF])) \\
        IMP_RES_TAC PROPERTY_STAR_TRANS \\
        Q.PAT_X_ASSUM `Obsm x y` K_TAC \\
        IMP_RES_TAC OBS_BISIM_UPTO_TRANS \\
        Q.PAT_X_ASSUM `WEAK_TRANS y u E2` K_TAC \\
        IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_label \\
(***
	E    ~   y''    Obsm     y'   ~~   E'
	|        |               ||        || 
	l        l               l         l
	|        |               ||        ||
       !E1'  ~   E2' (~ Obsm ~~) E2'' ~~  E2'''
 ***)
        Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC [] \\
        NTAC 2 (ONCE_REWRITE_TAC [O_DEF]) \\
        Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [],
        (* goal 1.2 (of 4) *)
        Q.PAT_X_ASSUM `X E E'` (STRIP_ASSUME_TAC o BETA_RULE o (REWRITE_RULE [O_DEF])) \\
        IMP_RES_TAC WEAK_EQUIV_TRANS_label' \\
        Q.PAT_X_ASSUM `Obsm x y` K_TAC \\
        IMP_RES_TAC OBS_BISIM_UPTO_WEAK_TRANS_label' \\
        IMP_RES_TAC STRONG_EQUIV_WEAK_TRANS' \\
(***
	E    ~   y''          Obsm         y'   ~~   E'
	||       ||                        ||        |
	l        l                         l         l
	||       ||                        ||        |
	E1''' ~  E1'' ~ y'''' Obsm y''' ~~ E1'  ~~  !E2'
 ***)
        Q.EXISTS_TAC `E1'''` >> ASM_REWRITE_TAC [] \\
        Q.PAT_X_ASSUM `X E1'' E1'` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        IMP_RES_TAC STRONG_IMP_WEAK_EQUIV \\
        `WEAK_EQUIV E1''' y''''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
        `WEAK_EQUIV y''' E2'`  by PROVE_TAC [WEAK_EQUIV_TRANS] \\
        Q.EXISTS_TAC `E2'` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `y''''` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `y''''` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL],
        (* goal 1.3 (of 4) *)
        Q.PAT_X_ASSUM `X E E'` (STRIP_ASSUME_TAC o BETA_RULE o (REWRITE_RULE [O_DEF])) \\
        IMP_RES_TAC PROPERTY_STAR_TRANS \\
        Q.PAT_X_ASSUM `Obsm x y` K_TAC \\
        IMP_RES_TAC OBS_BISIM_UPTO_TRANS \\
        Q.PAT_X_ASSUM `WEAK_TRANS y u E2` K_TAC \\
        IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_tau \\
(***
	E    ~   y''    Obsm     y'   ~~   E'
	|        |               ||        || 
	tau     tau              tau       eps
	|        |               ||        ||
       !E1'  ~   E2' (~ Obsm ~~) E2'' ~~  E2'''
 ***)
        Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC [] \\
        NTAC 2 (ONCE_REWRITE_TAC [O_DEF]) \\
        Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [],
        (* goal 1.4 (of 4) *)
        Q.PAT_X_ASSUM `X E E'` (STRIP_ASSUME_TAC o BETA_RULE o (REWRITE_RULE [O_DEF])) \\
        IMP_RES_TAC WEAK_EQUIV_TRANS_tau' \\
        Q.PAT_X_ASSUM `Obsm x y` K_TAC \\
        IMP_RES_TAC OBS_BISIM_UPTO_EPS' \\
        IMP_RES_TAC STRONG_EQUIV_EPS' \\
(***
	E    ~   y''          Obsm         y'   ~~   E'
	||       ||                        ||        |
	eps      eps                       eps      tau
	||       ||                        ||        |
	E1''' ~  E1'' ~ y'''' Obsm y''' ~~ E1'  ~~  !E2'
 ***)
        Q.EXISTS_TAC `E1'''` >> ASM_REWRITE_TAC [] \\
        Q.PAT_X_ASSUM `X E1'' E1'` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        IMP_RES_TAC STRONG_IMP_WEAK_EQUIV \\
        `WEAK_EQUIV E1''' y''''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
        `WEAK_EQUIV y''' E2'`  by PROVE_TAC [WEAK_EQUIV_TRANS] \\
        Q.EXISTS_TAC `E2'` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `y''''` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `y''''` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ],
      (* goal 2 (of 2) *)
      RES_TAC \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      irule (REWRITE_RULE [RSUBSET] WEAK_BISIM_UPTO_THM) \\
      Q.EXISTS_TAC `(STRONG_EQUIV O Obsm O WEAK_EQUIV)` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [WEAK_BISIM_UPTO] >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        Q.PAT_X_ASSUM `X E E'` (STRIP_ASSUME_TAC o BETA_RULE o (REWRITE_RULE [O_DEF])) \\
        IMP_RES_TAC WEAK_EQUIV_TRANS_label \\
        Q.PAT_X_ASSUM `Obsm x y` K_TAC \\
        IMP_RES_TAC OBS_BISIM_UPTO_WEAK_TRANS_label \\
        Q.PAT_X_ASSUM `WEAK_TRANS x u E1` K_TAC \\
        IMP_RES_TAC STRONG_EQUIV_WEAK_TRANS \\
(***
	E    ~~  y''    Obsm     y'   ~    E'
	|        ||              ||        || 
	l        l               l         l
	|        ||              ||        ||
       !E1'  ~~  E2' (~ Obsm ~~) E2'' ~   E2'''
 ***)
        Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC [] \\
        Q.PAT_X_ASSUM `X E2' E2''` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        IMP_RES_TAC STRONG_IMP_WEAK_EQUIV \\
        `WEAK_EQUIV E1' y''''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
        `WEAK_EQUIV y''' E2'''`  by PROVE_TAC [WEAK_EQUIV_TRANS] \\
        Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `E1'` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `y'''` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `y''''` >> ASM_REWRITE_TAC [],
        (* goal 2.2 (of 4) *)
        Q.PAT_X_ASSUM `X E E'` (STRIP_ASSUME_TAC o BETA_RULE o (REWRITE_RULE [O_DEF])) \\
        IMP_RES_TAC PROPERTY_STAR_TRANS' \\
        Q.PAT_X_ASSUM `Obsm x y` K_TAC \\
        IMP_RES_TAC OBS_BISIM_UPTO_TRANS' \\
        IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_label' \\
(***
	E    ~~  y''          Obsm         y'   ~   E'
	||       ||                        |        |
	l        l                         l        l
	||       ||                        |        |
	E1''' ~~ E1'' ~ y'''' Obsm y''' ~~ E1'  ~  !E2'
 ***)
        Q.EXISTS_TAC `E1'''` >> ASM_REWRITE_TAC [] \\
        NTAC 2 (ONCE_REWRITE_TAC [O_DEF]) \\
        Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `E1''` >> ASM_REWRITE_TAC [],
        (* goal 2.3 (of 4) *)
        Q.PAT_X_ASSUM `X E E'` (STRIP_ASSUME_TAC o BETA_RULE o (REWRITE_RULE [O_DEF])) \\
        IMP_RES_TAC WEAK_EQUIV_TRANS_tau \\
        Q.PAT_X_ASSUM `Obsm x y` K_TAC \\
        IMP_RES_TAC OBS_BISIM_UPTO_EPS \\
        Q.PAT_X_ASSUM `WEAK_TRANS x u E1` K_TAC \\
        IMP_RES_TAC STRONG_EQUIV_EPS \\
(***
	E    ~~  y''    Obsm     y'   ~    E'
	|        ||              ||        || 
       tau       eps            eps        eps
	|        ||              ||        ||
       !E1'  ~~  E2' (~ Obsm ~~) E2'' ~   E2'''
 ***)
        Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC [] \\
        Q.PAT_X_ASSUM `X E2' E2''` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        IMP_RES_TAC STRONG_IMP_WEAK_EQUIV \\
        `WEAK_EQUIV E1' y''''` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
        `WEAK_EQUIV y''' E2'''`  by PROVE_TAC [WEAK_EQUIV_TRANS] \\
        Q.EXISTS_TAC `y'''` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `E1'` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `y'''` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `y''''` >> ASM_REWRITE_TAC [],
        (* goal 2.4 (of 4) *)
        Q.PAT_X_ASSUM `X E E'` (STRIP_ASSUME_TAC o BETA_RULE o (REWRITE_RULE [O_DEF])) \\
        IMP_RES_TAC PROPERTY_STAR_TRANS' \\
        Q.PAT_X_ASSUM `Obsm x y` K_TAC \\
        IMP_RES_TAC OBS_BISIM_UPTO_TRANS' \\
        IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_tau' \\
(***
	E    ~~  y''          Obsm         y'   ~   E'
	||       ||                        |        |
	eps      tau                       tau     tau
	||       ||                        |        |
	E1''' ~~ E1'' ~ y'''' Obsm y''' ~~ E1'  ~  !E2'
 ***)
        Q.EXISTS_TAC `E1'''` >> ASM_REWRITE_TAC [] \\
        NTAC 2 (ONCE_REWRITE_TAC [O_DEF]) \\
        Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `E1''` >> ASM_REWRITE_TAC [] ] ]);

(* Bibliography:
 *
 * [1] Milner, R.: Communication and concurrency. (1989).
.* [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer, Cham (2015).
 * [3] Sangiorgi, D.: Introduction to Bisimulation and Coinduction. Cambridge University Press (2011).
 * [4] Sangiorgi, D., Rutten, J.: Advanced Topics in Bisimulation and Coinduction.
				  Cambridge University Press (2011).
 *)

val _ = export_theory ();
val _ = html_theory "BisimulationUpto";

(* last updated: Aug 5, 2017 *)
