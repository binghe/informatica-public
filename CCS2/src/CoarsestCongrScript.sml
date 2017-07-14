(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pairTheory sumTheory listTheory;
open prim_recTheory arithmeticTheory;
open cardinalTheory ordinalTheory;

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory WeakEQTheory WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory ObsCongrConv;

val _ = new_theory "CoarsestCongr";

(******************************************************************************)
(*                                                                            *)
(*               A derived tau-law for observation congruence                 *)
(*                                                                            *)
(******************************************************************************)

(* Theorem TAU_STRAT:
   |- !E E'. OBS_CONGR (sum E (prefix tau (sum E' E))) (prefix tau (sum E' E))
 *)
val TAU_STRAT = store_thm (
   "TAU_STRAT",
  ``!E E'. OBS_CONGR (sum E (prefix tau (sum E' E))) (prefix tau (sum E' E))``,
    REPEAT GEN_TAC
 >> OC_LHS_SUBST1_TAC
       (SPEC ``sum E' E`` (GEN_ALL (OC_SYM (SPEC_ALL TAU2))))
 >> OC_SUM_IDEMP_TAC
 >> OC_LHS_SUBST1_TAC (SPEC ``sum E' E`` TAU2));

(******************************************************************************)
(*                                                                            *)
(*                      Deng Lemma and Hennessy Lemma			      *)
(*                                                                            *)
(******************************************************************************)

(* Lemma 4.2. (Deng Lemma) [Den07], the weak bisimularity version *)
val DENG_LEMMA = store_thm ((* NEW *)
   "DENG_LEMMA",
  ``!p q. WEAK_EQUIV p q ==> (?p'. TRANS p tau p' /\ WEAK_EQUIV p' q) \/
			     (?q'. TRANS q tau q' /\ WEAK_EQUIV p q') \/
			     OBS_CONGR p q``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC (DECIDE ``(~P /\ ~Q ==> R) ==> P \/ Q \/ R``)
 >> REPEAT STRIP_TAC
 >> REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        PAT_X_ASSUM ``WEAK_EQUIV p q``
		(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
        RES_TAC \\
        IMP_RES_TAC EPS_cases1 >- PROVE_TAC [] \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
        REWRITE_TAC [WEAK_TRANS] \\
        take [`q`, `u`] >> ASM_REWRITE_TAC [EPS_REFL, PREFIX],
        (* goal 1.2 (of 2) *)
        PAT_X_ASSUM ``WEAK_EQUIV p q``
		(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
        RES_TAC \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        PAT_X_ASSUM ``WEAK_EQUIV p q``
		  (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
        RES_TAC \\
        IMP_RES_TAC EPS_cases1 >- PROVE_TAC [] \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
        REWRITE_TAC [WEAK_TRANS] \\
        take [`p`, `u`] >> ASM_REWRITE_TAC [EPS_REFL, PREFIX],
        (* goal 1.2.2 (of 2) *)
        PAT_X_ASSUM ``WEAK_EQUIV p q``
		  (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
        RES_TAC \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ] ]);

(* Hennessy Lemma, the easy part *)
val HENNESSY_LEMMA_RL = store_thm ((* NEW *)
   "HENNESSY_LEMMA_RL",
  ``!p q. (OBS_CONGR p q \/ OBS_CONGR p (prefix tau q) \/
			    OBS_CONGR (prefix tau p) q) ==> WEAK_EQUIV p q``,
    REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 2.1 (of 3) *)
      IMP_RES_TAC OBS_CONGR_IMP_WEAK_EQUIV,
      (* goal 2.2 (of 3) *)
      IMP_RES_TAC OBS_CONGR_IMP_WEAK_EQUIV \\
      ASSUME_TAC (Q.SPEC `q` TAU_WEAK) \\
      IMP_RES_TAC WEAK_EQUIV_TRANS,
      (* goal 2.3 (of 3) *)
      IMP_RES_TAC OBS_CONGR_IMP_WEAK_EQUIV \\
      ASSUME_TAC (Q.SPEC `p` TAU_WEAK) \\
      POP_ASSUM (ASSUME_TAC o (MATCH_MP WEAK_EQUIV_SYM)) \\
      IMP_RES_TAC WEAK_EQUIV_TRANS ]);

(* Hennessy Lemma, the hard part *)
val HENNESSY_LEMMA_LR = store_thm ((* NEW *)
   "HENNESSY_LEMMA_LR",
  ``!p q. WEAK_EQUIV p q ==> (OBS_CONGR p q \/ OBS_CONGR p (prefix tau q)
					    \/ OBS_CONGR (prefix tau p) q)``,
    REPEAT STRIP_TAC
 >> Cases_on `?E. TRANS p tau E /\ WEAK_EQUIV E q` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISJ2_TAC >> DISJ1_TAC \\ (* CHOOSE ``p ~~c tau..q`` *)
      REWRITE_TAC [OBS_CONGR] >> // STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        Cases_on `u` \\ (* 2 sub-goals here, sharing initial tacticals *)
        PAT_X_ASSUM ``WEAK_EQUIV p q``
		    (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
        RES_TAC \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] >|
        [ (* goal 1.1.1 (of 2) *)
          REWRITE_TAC [WEAK_TRANS] \\
          take [`prefix tau q`, `q`] \\
          ASM_REWRITE_TAC [EPS_REFL, PREFIX],
          (* goal 1.1.2 (of 2) *)
          IMP_RES_TAC TAU_PREFIX_WEAK_TRANS ],
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> ASM_REWRITE_TAC [] \\
	PAT_X_ASSUM ``?E. TRANS p tau E /\ WEAK_EQUIV E q`` STRIP_ASSUME_TAC \\
        Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC [] \\
        IMP_RES_TAC TRANS_IMP_WEAK_TRANS ],
      (* goal 2 (of 2) *)
      Cases_on `?E. TRANS q tau E /\ WEAK_EQUIV p E` >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        NTAC 2 DISJ2_TAC \\ (* CHOOSE ``tau..p ~~c q`` *)
        REWRITE_TAC [OBS_CONGR] >> // STRIP_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          IMP_RES_TAC TRANS_PREFIX >> ONCE_ASM_REWRITE_TAC [] \\
          PAT_X_ASSUM ``?E. TRANS q tau E /\ WEAK_EQUIV p E`` STRIP_ASSUME_TAC \\
          Q.EXISTS_TAC `E` >> ONCE_ASM_REWRITE_TAC [] \\
          IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
          ASM_REWRITE_TAC [],
          (* goal 2.1.2 (of 2) *)
          Cases_on `u` \\ (* 2 sub-goals here, sharing initial tacticals *)
          PAT_X_ASSUM ``WEAK_EQUIV p q``
		      (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
          RES_TAC \\
          Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] >|
          [ (* goal 2.1.2.1 (of 2) *)
            REWRITE_TAC [WEAK_TRANS] \\
            take [`prefix tau p`, `p`] \\
            ASM_REWRITE_TAC [EPS_REFL, PREFIX],
            (* goal 2.1.2.2 (of 2) *)
            IMP_RES_TAC TAU_PREFIX_WEAK_TRANS ] ],
        (* goal 2.2 (of 2) *)
        DISJ1_TAC \\ (* CHOOSE ``p ~~c q``, then use Deng Lemma *)
        IMP_RES_TAC DENG_LEMMA \\ (* 2 sub-goals here, same tactical *)
        RES_TAC ] ]);

(* Lemma 4.1. (Hennessy Lemma) [Mil89] *)
val HENNESSY_LEMMA = store_thm ((* NEW *)
   "HENNESSY_LEMMA",
  ``!p q. WEAK_EQUIV p q = (OBS_CONGR p q \/ OBS_CONGR p (prefix tau q)
					  \/ OBS_CONGR (prefix tau p) q)``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2), hard part *)
      REWRITE_TAC [HENNESSY_LEMMA_LR],
      (* goal 2 (of 2), easy part *)
      REWRITE_TAC [HENNESSY_LEMMA_RL] ]);

(******************************************************************************)
(*                                                                            *)
(*                Coarsest congruence contained in WEAK_EQUIV		      *)
(*                                                                            *)
(******************************************************************************)

val COARSEST_CONGR_LR = store_thm ((* NEW *)
   "COARSEST_CONGR_LR",
  ``!p q. OBS_CONGR p q ==> !r. WEAK_EQUIV (sum p r) (sum q r)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC OBS_CONGR_IMP_WEAK_EQUIV
 >> RW_TAC std_ss [OBS_CONGR_SUBST_SUM_R]);

(* The property as assumptions on processes in COARSEST_CONGR_THM *)
val free_action_def = Define `
    free_action p = ?a. !p'. ~(WEAK_TRANS p (label a) p')`;

val COARSEST_CONGR_RL = store_thm ((* NEW *)
   "COARSEST_CONGR_RL",
  ``!p q. free_action p /\ free_action q ==>
	  (!r. WEAK_EQUIV (sum p r) (sum q r)) ==> OBS_CONGR p q``,
    REWRITE_TAC [free_action_def, OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      ASSUME_TAC (Q.SPEC `prefix (label a) nil`
			 (ASSUME ``!r. WEAK_EQUIV (sum p r) (sum q r)``)) \\
      IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `prefix (label a) nil`)) \\
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        STRIP_ASSUME_TAC
          (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR]
			     (ASSUME ``WEAK_EQUIV (sum p (prefix (label a) nil))
						  (sum q (prefix (label a) nil))``)) \\
        RES_TAC \\
        IMP_RES_TAC EPS_cases1 >| (* 2 sub-goals here *)
        [ (* goal 1.1.1 (of 2) *)
          `TRANS E2 (label a) nil` by RW_TAC std_ss [SUM2, PREFIX] \\
          STRIP_ASSUME_TAC
            (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR] (ASSUME ``WEAK_EQUIV E1 E2``)) \\
          RES_TAC \\
          IMP_RES_TAC TRANS_TAU_AND_WEAK \\
          RES_TAC,				(* initial assumption of `p` is used here *)
          (* goal 1.1.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum q (prefix (label a) nil)) tau u``
		      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 1.1.2.1 (of 4) *)
            Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
            REWRITE_TAC [WEAK_TRANS] \\
            take [`q`, `u`] >> ASM_REWRITE_TAC [EPS_REFL],
            (* goal 1.1.2.2 (of 4) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct] ] ],
        (* goal 1.2 (of 2) *)
        STRIP_ASSUME_TAC
          (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR]
			     (ASSUME ``WEAK_EQUIV (sum p (prefix (label a) nil))
						  (sum q (prefix (label a) nil))``)) \\
        RES_TAC \\
        IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
        [ (* goal 1.2.1 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum q (prefix (label a) nil)) tau E'``
		      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 1.2.1.1 (of 2) *)
            Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
            IMP_RES_TAC TRANS_TAU_AND_WEAK,
            (* goal 1.2.1.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct] ],
          (* goal 1.2.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum q (prefix (label a) nil)) (label L) E'``
		      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 1.2.2.1 (of 2) *)
            Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
            REWRITE_TAC [WEAK_TRANS] \\
            take [`q`, `E'`] >> ASM_REWRITE_TAC [EPS_REFL],
            (* goal 1.2.2.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            PAT_X_ASSUM ``label L = label a``
			(ASSUME_TAC o (REWRITE_RULE [Action_11])) \\
            `TRANS p (label a) E1` by RW_TAC std_ss [] \\
            POP_ASSUM (ASSUME_TAC o (MATCH_MP TRANS_IMP_WEAK_TRANS)) \\
            RES_TAC ] ] ],			(* initial assumption of `p` is used here *)
      (* goal 2, completely symmetric with goal 1 *)
      ASSUME_TAC (Q.SPEC `prefix (label a') nil`
			 (ASSUME ``!r. WEAK_EQUIV (sum p r) (sum q r)``)) \\
      IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `prefix (label a') nil`)) \\
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        STRIP_ASSUME_TAC
          (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR]
			     (ASSUME ``WEAK_EQUIV (sum p (prefix (label a') nil))
						  (sum q (prefix (label a') nil))``)) \\
        RES_TAC \\
        IMP_RES_TAC EPS_cases1 >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          `TRANS E1 (label a') nil` by RW_TAC std_ss [SUM2, PREFIX] \\
          STRIP_ASSUME_TAC
            (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR] (ASSUME ``WEAK_EQUIV E1 E2``)) \\
          RES_TAC \\
          IMP_RES_TAC TRANS_TAU_AND_WEAK \\
          RES_TAC,				(* initial assumption of `q` is used here *)
          (* goal 2.1.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum p (prefix (label a') nil)) tau u``
		      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 4) *)
            Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
            REWRITE_TAC [WEAK_TRANS] \\
            take [`p`, `u`] >> ASM_REWRITE_TAC [EPS_REFL],
            (* goal 2.1.2.2 (of 4) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct] ] ],
        (* goal 2.2 (of 2) *)
        STRIP_ASSUME_TAC
          (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR]
			     (ASSUME ``WEAK_EQUIV (sum p (prefix (label a') nil))
						  (sum q (prefix (label a') nil))``)) \\
        RES_TAC \\
        IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum p (prefix (label a') nil)) tau E'``
		      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 2.2.1.1 (of 2) *)
            Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
            IMP_RES_TAC TRANS_TAU_AND_WEAK,
            (* goal 2.2.1.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct] ],
          (* goal 2.2.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum p (prefix (label a') nil)) (label L) E'``
		      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 2.2.2.1 (of 2) *)
            Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
            REWRITE_TAC [WEAK_TRANS] \\
            take [`p`, `E'`] >> ASM_REWRITE_TAC [EPS_REFL],
            (* goal 2.2.2.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            PAT_X_ASSUM ``label L = label a'`` (ASSUME_TAC o (REWRITE_RULE [Action_11])) \\
            `TRANS q (label a') E2` by RW_TAC std_ss [] \\
            POP_ASSUM (ASSUME_TAC o (MATCH_MP TRANS_IMP_WEAK_TRANS)) \\
            RES_TAC ] ] ] ] );			(* initial assumption of `q` is used here *)

(* Theorem 4.5. (Coarsest congruence contained in WEAK_EQUIV) in Gorrieri's book.
   OBS_CONGR congruences theorems shouldn't depend on this result.
 *)
val COARSEST_CONGR_THM = store_thm ((* NEW *)
   "COARSEST_CONGR_THM",
  ``!p q. free_action p /\ free_action q ==>
	  (OBS_CONGR p q = !r. WEAK_EQUIV (sum p r) (sum q r))``,
    REPEAT STRIP_TAC
 >> EQ_TAC
 >- REWRITE_TAC [COARSEST_CONGR_LR]
 >> MATCH_MP_TAC COARSEST_CONGR_RL
 >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*                        The reachability relation                           *)
(*                                                                            *)
(******************************************************************************)

local
    val defn = ``(\E E'. ?u. TRANS E u E')``
in
  val Reachable_def = Define `Reachable = RTC ^defn`;
  val trans = (REWRITE_RULE [GSYM Reachable_def]) o BETA_RULE o (ISPEC defn);
end;

val Reachable_one = store_thm ((* NEW *)
   "Reachable_one", ``!E E'. (?u. TRANS E u E') ==> Reachable E E'``,
    REWRITE_TAC [Reachable_def]
 >> REPEAT STRIP_TAC
 >> MATCH_MP_TAC RTC_SINGLE
 >> BETA_TAC
 >> Q.EXISTS_TAC `u`
 >> ASM_REWRITE_TAC []);

val Reachable_self = store_thm ((* NEW *)
   "Reachable_self", ``!E. Reachable E E``,
    REWRITE_TAC [Reachable_def, RTC_REFL]);

val Reachable_trans = save_thm ((* NEW *)
   "Reachable_trans", trans (REWRITE_RULE [transitive_def] RTC_TRANSITIVE));

val Reachable_ind = save_thm ((* NEW *)
   "Reachable_ind", trans RTC_INDUCT);

val Reachable_strongind = save_thm ((* NEW *)
   "Reachable_strongind", trans RTC_STRONG_INDUCT);

val Reachable_ind_right = save_thm ((* NEW *)
   "Reachable_ind_right", trans RTC_INDUCT_RIGHT1);

val Reachable_strongind_right = save_thm ((* NEW *)
   "Reachable_strongind_right", trans RTC_STRONG_INDUCT_RIGHT1);

val Reachable_cases1 = save_thm ((* NEW *)
   "Reachable_cases1", trans RTC_CASES1);

val Reachable_cases2 = save_thm ((* NEW *)
   "Reachable_cases2", trans RTC_CASES2);

(* Define the set of states reachable from any CCS process *)
val NODES_def = Define `
    NODES (p :('a, 'b) CCS) = { q | Reachable p q }`;

val Reachable_NODES = store_thm (
   "Reachable_NODES", ``!p q. Reachable p q ==> q IN (NODES p)``,
    REPEAT STRIP_TAC
 >> SRW_TAC [] [NODES_def]);

val SELF_NODES = store_thm (
   "SELF_NODES", ``!p. p IN (NODES p)``,
    REPEAT STRIP_TAC
 >> SRW_TAC [] [NODES_def]
 >> REWRITE_TAC [Reachable_self]);

val MORE_NODES = store_thm (
   "MORE_NODES", ``!p q q'. q IN (NODES p) /\ Reachable q q' ==> q' IN (NODES p)``,
    REPEAT GEN_TAC
 >> SRW_TAC [] [NODES_def]
 >> IMP_RES_TAC Reachable_trans);

val TRANS_IN_NODES = store_thm (
   "TRANS_IN_NODES", ``!p q u. TRANS p u q ==> q IN (NODES p)``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [NODES_def]
 >> SRW_TAC [] []
 >> MATCH_MP_TAC Reachable_one
 >> Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC []);

val EPS_Reachable = store_thm ((* NEW *)
   "EPS_Reachable", ``!p q. EPS p q ==> Reachable p q``,
    HO_MATCH_MP_TAC EPS_ind_right
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >- REWRITE_TAC [Reachable_self]
 >> IMP_RES_TAC Reachable_one
 >> IMP_RES_TAC Reachable_trans);

val EPS_IN_NODES = store_thm (
   "EPS_IN_NODES", ``!p q. EPS p q ==> q IN (NODES p)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC Reachable_NODES
 >> IMP_RES_TAC EPS_Reachable);

val WEAK_TRANS_Reachable = store_thm (
   "WEAK_TRANS_Reachable", ``!p q u. WEAK_TRANS p u q ==> Reachable p q``,
    REWRITE_TAC [WEAK_TRANS]
 >> REPEAT STRIP_TAC
 >> IMP_RES_TAC EPS_Reachable
 >> IMP_RES_TAC Reachable_one
 >> IMP_RES_TAC Reachable_trans);

val WEAK_TRANS_IN_NODES = store_thm (
   "WEAK_TRANS_IN_NODES", ``!p q u. WEAK_TRANS p u q ==> q IN (NODES p)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC Reachable_NODES
 >> IMP_RES_TAC WEAK_TRANS_Reachable);

val FINITE_STATE_def = Define `
    FINITE_STATE (p :('a, 'b) CCS) = FINITE (NODES p)`;

(******************************************************************************)
(*                                                                            *)
(*       Coarsest congruence contained in WEAK_EQUIV (finite version)         *)
(*                                                                            *)
(******************************************************************************)

(* The shared core lemma used in PROP3's proof *)
val PROP3_COMMON = store_thm ((* NEW *)
   "PROP3_COMMON",
  ``!g h. (?k. STABLE k /\
	       (!g' u. WEAK_TRANS g u g' ==> ~(WEAK_EQUIV g' k)) /\
	       (!h' u. WEAK_TRANS h u h' ==> ~(WEAK_EQUIV h' k))) ==>
          (!r. WEAK_EQUIV (sum g r) (sum h r)) ==> OBS_CONGR g h``,
    REPEAT STRIP_TAC
 >> PAT_X_ASSUM ``!r. WEAK_EQUIV (sum g r) (sum h r)``
		(ASSUME_TAC o (Q.SPEC `prefix (label a) k`))
 >> REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `prefix (label a) k`)) \\
      PAT_X_ASSUM ``WEAK_EQUIV (sum g (prefix (label a) k)) (sum h (prefix (label a) k))``
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        RES_TAC \\
        PAT_X_ASSUM ``EPS (sum h (prefix (label a) k)) E2``
	  (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [EPS_cases1])) >| (* 2 sub-goals here *)
        [ (* goal 1.1.1 (of 2) *)
          `TRANS E2 (label a) k` by PROVE_TAC [PREFIX, SUM2] \\
          PAT_X_ASSUM ``WEAK_EQUIV E1 E2``
	    (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
          RES_TAC \\
          IMP_RES_TAC TRANS_TAU_AND_WEAK \\
          PROVE_TAC [],
          (* goal 1.1.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum h (prefix (label a) k)) tau u``
            (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 1.1.2.1 (of 2) *)
            Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
            IMP_RES_TAC TRANS_AND_EPS,
            (* goal 1.1.2.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct_label] ] ],
        (* goal 1.2 (of 2) *)
        Cases_on `L = a` >| (* 2 sub-goals here *)
        [ (* goal 1.2.1 (of 2) *)
          FULL_SIMP_TAC std_ss [] >> RES_TAC \\
          Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
          [ (* goal 1.2.1.1 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum h (prefix (label a) k)) tau E'``
		(STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 1.2.1.1.1 (of 2) *)
              IMP_RES_TAC TRANS_TAU_AND_WEAK,
              (* goal 1.2.1.1.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              RW_TAC std_ss [Action_distinct] ],
            (* goal 1.2.1.2 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum h (prefix (label a) k)) (label a) E'``
		(STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 1.2.1.2.1 (of 2) *)
              IMP_RES_TAC TRANS_AND_EPS,
              (* goal 1.2.1.2.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              `WEAK_EQUIV E1 k` by PROVE_TAC [EPS_STABLE'] \\
              IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
              RES_TAC ] ],
          (* goal 1.2.2 (of 2) *)
          RES_TAC \\
          Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
          [ (* goal 1.2.2.1 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum h (prefix (label a) k)) tau E'``
		(STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 1.2.2.1.1 (of 2) *)
              IMP_RES_TAC TRANS_TAU_AND_WEAK,
              (* goal 1.2.2.1.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              RW_TAC std_ss [Action_distinct] ],
            (* goal 1.2.2.2 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum h (prefix (label a) k)) (label L) E'``
		(STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 1.2.2.2.1 (of 2) *)
              IMP_RES_TAC TRANS_AND_EPS,
              (* goal 1.2.2.2.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              RW_TAC std_ss [Action_11] ] ] ] ],
      (* goal 2 (of 2), almost symmetric with goal 1 *)
      IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `prefix (label a) k`)) \\
      PAT_X_ASSUM ``WEAK_EQUIV (sum g (prefix (label a) k)) (sum h (prefix (label a) k))``
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        RES_TAC \\
        PAT_X_ASSUM ``EPS (sum g (prefix (label a) k)) E1``
	  (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [EPS_cases1])) >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          `TRANS E1 (label a) k` by PROVE_TAC [PREFIX, SUM2] \\
          PAT_X_ASSUM ``WEAK_EQUIV E1 E2``
	    (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
          RES_TAC \\
          IMP_RES_TAC TRANS_TAU_AND_WEAK \\
          `WEAK_EQUIV E2' k` by PROVE_TAC [WEAK_EQUIV_SYM] \\ (* one extra step *)
          PROVE_TAC [],
          (* goal 2.1.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum g (prefix (label a) k)) tau u``
            (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 2) *)
            Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
            IMP_RES_TAC TRANS_AND_EPS,
            (* goal 2.1.2.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct_label] ] ],
        (* goal 2.2 (of 2) *)
        Cases_on `L = a` >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          FULL_SIMP_TAC std_ss [] >> RES_TAC \\
          Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
          [ (* goal 2.2.1.1 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum g (prefix (label a) k)) tau E'``
		(STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 2.2.1.1.1 (of 2) *)
              IMP_RES_TAC TRANS_TAU_AND_WEAK,
              (* goal 2.2.1.1.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              RW_TAC std_ss [Action_distinct] ],
            (* goal 2.2.1.2 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum g (prefix (label a) k)) (label a) E'``
		(STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 2.2.1.2.1 (of 2) *)
              IMP_RES_TAC TRANS_AND_EPS,
              (* goal 2.2.1.2.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              `WEAK_EQUIV E2 k` by PROVE_TAC [EPS_STABLE', WEAK_EQUIV_SYM] \\
              IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
              RES_TAC ] ],
          (* goal 2.2.2 (of 2) *)
          RES_TAC \\
          Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
          [ (* goal 2.2.2.1 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum g (prefix (label a) k)) tau E'``
		(STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 2.2.2.1.1 (of 2) *)
              IMP_RES_TAC TRANS_TAU_AND_WEAK,
              (* goal 2.2.2.1.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              RW_TAC std_ss [Action_distinct] ],
            (* goal 2.2.2.2 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum g (prefix (label a) k)) (label L) E'``
		(STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 2.2.2.2.1 (of 2) *)
              IMP_RES_TAC TRANS_AND_EPS,
              (* goal 2.2.2.2.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              RW_TAC std_ss [Action_11] ] ] ] ] ]);

(* A variant of Proposition 9 (Jan Willem Klop) from [vGl05]. In this theory, all CCS
   processes are finitary, and this makes the lemma relatively easy. *)

(* (KLOP :'b Label -> num -> ('a, 'b) CCS) *)
val KLOP_def = Define `
   (KLOP (a: 'b Label) (0 :num) = nil) /\
   (KLOP a (SUC n) = sum (KLOP a n) (prefix (label a) (KLOP a n))) `;

val K0_NO_TRANS = store_thm (
   "K0_NO_TRANS", ``!(a :'b Label) u E. ~(TRANS (KLOP a 0) u E)``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [KLOP_def]
 >> REWRITE_TAC [NIL_NO_TRANS]);

(* Klop processes are STABLE. *)
val KLOP_PROP0 = store_thm ((* NEW *)
   "KLOP_PROP0", ``!(a :'b Label) n. STABLE (KLOP a n)``,
    GEN_TAC
 >> Induct_on `n` (* 2 sub-goals here *)
 >- REWRITE_TAC [STABLE, KLOP_def, NIL_NO_TRANS]
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [STABLE, KLOP_def]
 >> REPEAT STRIP_TAC
 >> IMP_RES_TAC TRANS_SUM (* 2 sub-goals here *)
 >- PROVE_TAC []
 >> IMP_RES_TAC TRANS_PREFIX
 >> PROVE_TAC [Action_distinct]);

(* Any transition of Klop processes is still a Klop process. Together with Prop 0,
   this also implies that Klop processes are tau-free. *)
val KLOP_PROP1_LR = store_thm ((* NEW *)
   "KLOP_PROP1_LR",
  ``!(a :'b Label) n E. TRANS (KLOP a n) (label a) E ==> ?m. m < n /\ (E = KLOP a m)``,
    GEN_TAC
 >> Induct_on `n` (* 2 sub-goals here, sharing initial tacticals *)
 >> REWRITE_TAC [KLOP_def]
 >> REPEAT STRIP_TAC
 >- PROVE_TAC [NIL_NO_TRANS]
 >> IMP_RES_TAC TRANS_SUM (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      RES_TAC \\
      Q.EXISTS_TAC `m` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ \\
      IMP_RES_TAC LESS_EQ_IMP_LESS_SUC,
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `n` >> ASM_REWRITE_TAC [] \\
      ASSUME_TAC (Q.SPEC `n` LESS_EQ_REFL) \\
      IMP_RES_TAC LESS_EQ_IFF_LESS_SUC ]);

val KLOP_PROP1_RL = store_thm ((* NEW *)
   "KLOP_PROP1_RL",
  ``!(a :'b Label) n E. (?m. m < n /\ (E = KLOP a m)) ==> TRANS (KLOP a n) (label a) E``,
    GEN_TAC
 >> Induct_on `n` (* 2 sub-goals here *)
 >> REPEAT STRIP_TAC
 >- IMP_RES_TAC NOT_LESS_0
 >> REWRITE_TAC [KLOP_def]
 >> IMP_RES_TAC LESS_LEMMA1 (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [PREFIX],
      (* goal 2 (of 2) *)
      RES_TAC \\
      MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [] ]);

(* Klop processes are closed under transition *)
val KLOP_PROP1 = store_thm ((* NEW *)
   "KLOP_PROP1",
  ``!(a :'b Label) n E. TRANS (KLOP a n) (label a) E = (?m. m < n /\ (E = KLOP a m))``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [KLOP_PROP1_LR],
      (* goal 2 (of 2) *)
      REWRITE_TAC [KLOP_PROP1_RL] ]);

(* Klop processes are closed under weak transition *)
val KLOP_PROP1_WK = store_thm ((* NEW *)
   "KLOP_PROP1_WK",
  ``!(a :'b Label) n E.	WEAK_TRANS (KLOP a n) (label a) E = (?m. m < n /\ (E = KLOP a m))``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        ASSUME_TAC (Q.SPECL [`a`, `n`] KLOP_PROP0) \\
        IMP_RES_TAC STABLE_NO_TRANS_TAU,
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC KLOP_PROP1_LR \\
        IMP_RES_TAC EPS_cases1 >| (* 2 sub-goals here *)
        [ (* goal 1.2.1 (of 2) *)
          Q.EXISTS_TAC `m` >> PROVE_TAC [],
          (* goal 1.2.2 (of 2) *)
          ASSUME_TAC (Q.SPECL [`a`, `m`] KLOP_PROP0) \\
          PROVE_TAC [STABLE_NO_TRANS_TAU] ] ],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      MATCH_MP_TAC TRANS_IMP_WEAK_TRANS \\
      RW_TAC std_ss [Q.SPECL [`a`, `n`, `E`] KLOP_PROP1_RL] ]);

(* Klop processes are strongly distinct with each other *)
val KLOP_PROP2 = store_thm ((* NEW *)
   "KLOP_PROP2",
  ``!(a :'b Label) n m. m < n ==> ~(STRONG_EQUIV (KLOP a m) (KLOP a n))``,
    GEN_TAC
 >> completeInduct_on `n`
 >> REPEAT STRIP_TAC
 >> `TRANS (KLOP a n) (label a) (KLOP a m)` by PROVE_TAC [KLOP_PROP1]
 >> STRIP_ASSUME_TAC
	(((Q.SPEC `label a`) o (ONCE_REWRITE_RULE [PROPERTY_STAR]))
	     (ASSUME ``STRONG_EQUIV (KLOP (a :'b Label) m) (KLOP a n)``))
 >> RES_TAC
 >> PAT_X_ASSUM ``TRANS (KLOP (a :'b Label) m) (label a) E1``
	(STRIP_ASSUME_TAC o (REWRITE_RULE [KLOP_PROP1]))
 >> PROVE_TAC []);

(* Klop processes are weakly distinct with each other *)
val KLOP_PROP2_WK = store_thm ((* NEW *)
   "KLOP_PROP2_WK",
  ``!(a :'b Label) n m. m < n ==> ~(WEAK_EQUIV (KLOP a m) (KLOP a n))``,
    GEN_TAC
 >> completeInduct_on `n`
 >> REPEAT STRIP_TAC
 >> `TRANS (KLOP a n) (label a) (KLOP a m)` by PROVE_TAC [KLOP_PROP1]
 >> STRIP_ASSUME_TAC
	(ONCE_REWRITE_RULE [OBS_PROPERTY_STAR]
			   (ASSUME ``WEAK_EQUIV (KLOP (a :'b Label) m) (KLOP a n)``))
 >> RES_TAC
 >> PAT_X_ASSUM ``WEAK TRANS (KLOP (a :'b Label) m) (label a) E1``
	(STRIP_ASSUME_TAC o (REWRITE_RULE [KLOP_PROP1_WK]))
 >> PROVE_TAC []);

val KLOP_ONE_ONE = store_thm ((* NEW *)
   "KLOP_ONE_ONE", ``!(a :'b Label). ONE_ONE (KLOP a)``,
    REWRITE_TAC [ONE_ONE_DEF]
 >> BETA_TAC
 >> REPEAT STRIP_TAC
 >> IMP_RES_TAC EQUAL_IMP_STRONG_EQUIV
 >> CCONTR_TAC
 >> `x1 < x2 \/ x2 < x1` by PROVE_TAC [LESS_LESS_CASES] (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC KLOP_PROP2,
      (* goal 2 (of 2) *)
      IMP_RES_TAC KLOP_PROP2 \\
      PROVE_TAC [STRONG_EQUIV_SYM] ]);

(* The finite version of Klop's Lemma:

          +----------------------------------- =~ ------------+
          |                                                   |
+---+---+-|-+---+---+---+---+---+---+---+---+                 |
|   |   | n |   |   |   |   |   |   |   |   |                 |
+---+---+-|-+---+---+---+---+---+---+---+---+                 |
          |        (nodes)              /   /                 |
         map                           /   /                  |
          |                           /   /                   |
          |                          /   /                    |
+---+---+-|-+---+---+---+---+---+---+---+---+---+---+---+---+-|-+---+---+---+---+--
|   |   | y |   |   |   |   |   |   |   |   |   |   |   |   | k |   |   |   |   | ....
+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+--
                   (klop0)              |                                (klops)

 Proof stretch:

 1. Build nodes = (NODES g) UNION (NODES h)
 2. Build klops = IMAGE KLOP univ(:num)
 3. Define map x = if (?y. y IN klops /\ WEAK_EQUIV x y) THEN y ELSE (CHOICE klops)
 4. Map nodes to klop0, which must be FINITE
 5. Choose `k` from (klops DIFF klops0)
 6. For all n in nodes, we prove that n =~ k can't hold. Because if it holds,
    (y = map n) by definition has two cases:

   a) y =~ n, in this case we have y =~ k, two equivalent elements in klops
   b) there's no `y` equivalent with n in klops, but we know there is x

 *)

(* The pure Math part in the proof of KLOP_LEMMA_FINITE *)
val KLOP_EXISTS_LEMMA = store_thm ((* NEW *)
   "KLOP_EXISTS_LEMMA",
  ``!R A B. equivalence (R :'a -> 'a -> bool) ==>
         FINITE (A :'a -> bool) /\ INFINITE (B :'a -> bool) /\
         (!x y. x IN B /\ y IN B /\ x <> y ==> ~(R x y)) ==>
       ?k. k IN B /\ (!n. n IN A ==> ~(R n k))``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [equivalence_def]
 >> REPEAT STRIP_TAC

 >> Q.ABBREV_TAC `map = (\x. if (?y. y IN B /\ R x y) then
				(@y. y IN B /\ R x y) else (CHOICE B))`
 >> POP_ASSUM (ASSUME_TAC o (* GSYM o *)
	       SIMP_RULE bool_ss [FUN_EQ_THM, markerTheory.Abbrev_def])
 >> Know `!x. map x IN B`
 >- ( GEN_TAC >> ASM_REWRITE_TAC [] \\
      RW_TAC std_ss [IN_DEF] >| (* 2 sub-goals here *)
      [ (* goal 1 (of 2) *)
        MATCH_MP_TAC SELECT_ELIM_THM \\ (* eliminated `Q (@P)` here !! *)
        RW_TAC std_ss [] \\
        Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [],
        (* goal 2 (of 2) *)
        ONCE_REWRITE_TAC [GSYM IN_APP] \\
        MATCH_MP_TAC CHOICE_DEF \\
        PROVE_TAC [FINITE_EMPTY] ] )
 >> DISCH_TAC

 >> Q.ABBREV_TAC `B0 = IMAGE map A`
 >> `FINITE B0` by PROVE_TAC [IMAGE_FINITE]
 >> Know `B0 SUBSET B`
 >- ( REWRITE_TAC [SUBSET_DEF] \\
      REPEAT STRIP_TAC \\
      `x IN (IMAGE map A)` by PROVE_TAC [] \\
      POP_ASSUM MP_TAC \\
      REWRITE_TAC [IN_IMAGE] >> PROVE_TAC [] )
 >> DISCH_TAC

 >> `?k. k IN B /\ k NOTIN B0`
	by PROVE_TAC [Q.SPECL [`B`, `B0`] IN_INFINITE_NOT_FINITE]
 >> Q.EXISTS_TAC `k`
 >> `!n. n IN A ==> map n IN B0` by PROVE_TAC [IN_IMAGE]

 >> Know `!n. n IN A ==> R n (map n) \/ (~?x. x IN B /\ R n x)`
 >- ( REPEAT STRIP_TAC \\
      PAT_X_ASSUM ``!x. map x = P`` (ASSUME_TAC o (Q.SPEC `n`)) \\
      Cases_on `?y. y IN B /\ R n y` >| (* 2 sub-goals here *)
      [ (* goal 1 (of 2) *)
        FULL_SIMP_TAC std_ss [] \\
        DISJ1_TAC \\
	METIS_TAC [], (* PROVE_TAC doesn't work here *)
        (* goal 2 (of 2) *)
        FULL_SIMP_TAC std_ss [] ] )
 >> DISCH_TAC

 >> Know `!n. n IN A ==> ~(R n k)`
 >- ( REPEAT STRIP_TAC \\
      `map n IN B0` by PROVE_TAC [IMAGE_IN] \\
      Q.ABBREV_TAC `y = map n` \\
      RES_TAC >| (* 2 sub-goals here *)
      [ (* goal 1 (of 2) *)
        `y IN B` by PROVE_TAC [SUBSET_DEF] \\
        `R k y` by PROVE_TAC [transitive_def, symmetric_def] \\
        Cases_on `k = y` >- PROVE_TAC [] \\
        `~(R k y)` by PROVE_TAC [],
        (* goal 2 (of 2) *)
        `B k /\ R n k` by PROVE_TAC [IN_DEF] \\
        RES_TAC ] )
 >> DISCH_TAC
 >> ASM_REWRITE_TAC []);

val KLOP_LEMMA_FINITE = store_thm ((* NEW *)
   "KLOP_LEMMA_FINITE",
  ``!g h. FINITE_STATE g /\ FINITE_STATE h ==>
	  ?k. STABLE k /\
	      (!g' u. WEAK_TRANS g u g' ==> ~(WEAK_EQUIV g' k)) /\
	      (!h' u. WEAK_TRANS h u h' ==> ~(WEAK_EQUIV h' k))``,
    REPEAT STRIP_TAC
 (* Part 1: assert that the union of all nodes in g and h is finite *)
 >> PAT_X_ASSUM ``FINITE_STATE g``
	(ASSUME_TAC o (REWRITE_RULE [FINITE_STATE_def]))
 >> PAT_X_ASSUM ``FINITE_STATE h``
	(ASSUME_TAC o (REWRITE_RULE [FINITE_STATE_def]))
 >> Q.ABBREV_TAC `nodes = (NODES g) UNION (NODES h)`
 >> `FINITE nodes` by PROVE_TAC [FINITE_UNION]
(*
  0.  FINITE (NODES g)
  1.  FINITE (NODES h)
  2.  Abbrev (nodes = NODES g ∪ NODES h)
  3.  FINITE nodes
 *)
 (* Part 2: assert an infinite set of Klop processes *)
 >> Q.ABBREV_TAC `a = (ARB :'b Label)`
 >> Q.ABBREV_TAC `f = KLOP a`
 >> `!x y. (f x = f y) ==> (x = y)` by PROVE_TAC [KLOP_ONE_ONE, ONE_ONE_DEF]
 >> Q.ABBREV_TAC `klops = IMAGE f (UNIV :num set)`
 >> `INFINITE klops` by PROVE_TAC [IMAGE_11_INFINITE, INFINITE_NUM_UNIV]
(*
  4.  Abbrev (a = ARB)
  5.  Abbrev (f = KLOP a)
  6.  ∀x y. f x = f y ⇒ x = y
  7.  Abbrev (klops = IMAGE f 𝕌(:num))
  8.  INFINITE klops
*)
 (* Part 3: assert the distincity of elements in the infinite set *)
 >> Know `!x y. x IN klops /\ y IN klops /\ x <> y ==> ~(WEAK_EQUIV x y)`
 >- ( REPEAT STRIP_TAC \\
      `?n. x = KLOP a n` by PROVE_TAC [IN_UNIV, IN_IMAGE] \\
      `?m. y = KLOP a m` by PROVE_TAC [IN_UNIV, IN_IMAGE] \\
      STRIP_ASSUME_TAC (Q.SPECL [`m`, `n`] LESS_LESS_CASES) >| (* 3 sub-goals here *)
      [ (* goal 1 (of 3) *)
        PROVE_TAC [],
        (* goal 2 (of 3) *)
        PROVE_TAC [KLOP_PROP2_WK, WEAK_EQUIV_SYM],
        (* goal 3 (of 3) *)
        PROVE_TAC [KLOP_PROP2_WK] ] )
 >> DISCH_TAC
 (* Part 4: assert the existence of k *)
 >> ASSUME_TAC WEAK_EQUIV_equivalence
 >> POP_ASSUM (MP_TAC o
	       (MATCH_MP (ISPECL [``WEAK_EQUIV :('a, 'b) simulation``,
				  ``nodes :('a, 'b) CCS -> bool``,
				  ``klops :('a, 'b) CCS -> bool``] KLOP_EXISTS_LEMMA)))
 >> RW_TAC std_ss []
(*
  9.  ∀x y. x ∈ klops ∧ y ∈ klops ∧ x ≠ y ⇒ ¬(x ≈ y)
  10.  k ∈ klops
  11.  ∀n. n ∈ nodes ⇒ ¬(n ≈ k)
 *)
 >> Q.EXISTS_TAC `k`
 >> CONJ_TAC (* 2 sub-goals here *)
 >- ( `k IN IMAGE f UNIV` by PROVE_TAC [] \\
      POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_IMAGE])) \\
      PROVE_TAC [KLOP_PROP0] )
 (* Part 5: final check *)
 >> `!n. n IN (NODES g) ==> ~(WEAK_EQUIV n k)` by PROVE_TAC [IN_UNION]
 >> `!n. n IN (NODES h) ==> ~(WEAK_EQUIV n k)` by PROVE_TAC [IN_UNION]
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REPEAT STRIP_TAC \\
      IMP_RES_TAC WEAK_TRANS_IN_NODES \\
      PROVE_TAC [],
      (* goal 2 (of 2) *)
      REPEAT STRIP_TAC \\
      IMP_RES_TAC WEAK_TRANS_IN_NODES \\
      PROVE_TAC [] ]);

(* The finite version of COARSEST_CONGR_THM (PROP3) *)
val COARSEST_CONGR_FINITE = store_thm ((* NEW *)
   "COARSEST_CONGR_FINITE",
  ``!g h. FINITE_STATE g /\ FINITE_STATE h ==>
	  (OBS_CONGR g h = (!r. WEAK_EQUIV (sum g r) (sum h r)))``,
    REPEAT STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [COARSEST_CONGR_LR]
 >> MP_TAC (Q.SPECL [`g`, `h`] KLOP_LEMMA_FINITE)
 >> RW_TAC std_ss [PROP3_COMMON]);

(******************************************************************************)
(*                                                                            *)
(*       Coarsest congruence contained in WEAK_EQUIV (full version)           *)
(*                                                                            *)
(******************************************************************************)

val _ = new_constant ("summ", ``:('a, 'b) CCS set -> ('a, 'b) CCS``);

val summ_Axiom = new_axiom ((* NEW *)
   "summ_Axiom", ``!rs u E. TRANS (summ rs) u E = ?r. r IN rs /\ TRANS r u E``);

val Klop_def = new_specification (
   "Klop_def", ["Klop"],
    ord_RECURSION |> INST_TYPE [``:'a`` |-> ``:'c``]
		  |> ISPEC ``nil :('a, 'b) CCS``		(* z *)
		  |> Q.SPEC `\x r. sum r (prefix (label a) r)`	(* sf *)
		  |> Q.SPEC `\x rs. summ rs`			(* lf *)
		  |> SIMP_RULE (srw_ss()) []
		  |> Q.GEN `a`
		  |> CONV_RULE SKOLEM_CONV );

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
 >> RW_TAC std_ss [Klop_def, summ_Axiom]
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
val Klop_PROP1_WK = store_thm ((* NEW *)
   "Klop_PROP1_WK",
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
val Klop_PROP2_WK = store_thm ((* NEW *)
   "Klop_PROP2_WK",
  ``!(a :'b Label) (n :'c ordinal) m. m < n ==> ~(WEAK_EQUIV (Klop a m) (Klop a n))``,
    GEN_TAC
 >> HO_MATCH_MP_TAC ord_induction
 >> REPEAT STRIP_TAC
 >> `TRANS (Klop a n) (label a) (Klop a m)` by PROVE_TAC [Klop_PROP1]
 >> PAT_X_ASSUM ``WEAK_EQUIV (Klop a m) (Klop a n)``
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR]))
 >> RES_TAC
 >> PAT_X_ASSUM ``WEAK_TRANS (Klop a m) (label a) E1``
	(STRIP_ASSUME_TAC o (REWRITE_RULE [Klop_PROP1_WK]))
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

(* TODO: use ONE_ONE_IMP_NOTIN in this proof *)
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
        IMP_RES_TAC Klop_PROP2_WK,
        (* goal 2.2 (of 2) *)
        IMP_RES_TAC WEAK_EQUIV_SYM \\
        IMP_RES_TAC Klop_PROP2_WK ] ]);

(* The full version of Klop's Lemma *)
val KLOP_LEMMA = store_thm ((* NEW *)
   "KLOP_LEMMA", ``!g h. ?k. STABLE k /\ (!g' u. WEAK_TRANS g u g' ==> ~(WEAK_EQUIV g' k)) /\
					 (!h' u. WEAK_TRANS h u h' ==> ~(WEAK_EQUIV h' k))``,
    REPEAT STRIP_TAC
 >> Q.ABBREV_TAC `nodes = (NODES g) UNION (NODES h)`
 >> Cases_on `FINITE nodes` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC KLOP_LEMMA_FINITE \\
      `FINITE (NODES g) /\ FINITE (NODES h)` by PROVE_TAC [FINITE_UNION] \\
      PROVE_TAC [FINITE_STATE_def],
      (* goal 2 (of 2) *)
      Q.ABBREV_TAC `a = (ARB :'b Label)` \\
      ASSUME_TAC (Q.SPECL [`a`, `nodes`] INFINITE_KLOP_EXISTS_LEMMA) \\
      POP_ASSUM MP_TAC >> STRIP_TAC \\
      Q.EXISTS_TAC `Klop a n` \\
      REWRITE_TAC [Klop_PROP0] \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        `!x. x IN (NODES g) ==> ~(WEAK_EQUIV x (Klop a n))` by PROVE_TAC [IN_UNION] \\
        REPEAT STRIP_TAC \\
        IMP_RES_TAC WEAK_TRANS_IN_NODES \\
        PROVE_TAC [],
        (* goal 2.2 (of 2) *)
        `!x. x IN (NODES h) ==> ~(WEAK_EQUIV x (Klop a n))` by PROVE_TAC [IN_UNION] \\
        REPEAT STRIP_TAC \\
        IMP_RES_TAC WEAK_TRANS_IN_NODES \\
        PROVE_TAC [] ] ]);

(* A stronger version of COARSEST_CONGR_THM from [vGl05], without any assumption.
   Noticed that, HOL type system automatically guarantees that any type must have
   at least one instance, so there's always at least one action a IN Act - {tau},
   no matter what Act type 'b is there.
 *)
val COARSEST_CONGR_FULL = store_thm ((* NEW *)
   "COARSEST_CONGR_FULL",
  ``!g h. OBS_CONGR g h = (!r. WEAK_EQUIV (sum g r) (sum h r))``,
    REPEAT STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [COARSEST_CONGR_LR]
 >> MP_TAC (Q.SPECL [`g`, `h`] KLOP_LEMMA)
 >> RW_TAC std_ss [PROP3_COMMON]);

(** Bibliography:

[Den07] Y. Deng, “A simple completeness proof for the axiomatisations of weak behavioural
    equivalences”, Bulletin of the EATCS, 93:207-219, 2007.

[Mil89] R. Milner, Communication and Concurrency, Prentice-Hall, 1989.

[vGl05] R.J. van Glabbeek, “A characterisation of weak bisimulation congruence”, in Processes,
    Terms and Cycles: Steps on the Road to Infinity, Essays dedicated to Jan Willem Klop, on the
    occasion of his 60th birthday, LNCS 3838, 26-39. Springer-Verlag, 2005.
 *)

val _ = export_theory ();
val _ = DB.html_theory "CoarsestCongr";

(* last updated: Jun 24, 2017 *)
