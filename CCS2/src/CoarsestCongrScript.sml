(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pairTheory listTheory;
open prim_recTheory arithmeticTheory;
open ordinalTheory;

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
      Cases_on `u` \\ (* 2 sub-goals here, sharing initial tacticals *)
      PAT_X_ASSUM ``WEAK_EQUIV p q``
		  (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
      RES_TAC >|
      [ (* goal 1.1.1 (of 2) *)
        IMP_RES_TAC EPS_cases1 >- PROVE_TAC [] \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
        REWRITE_TAC [WEAK_TRANS] \\
        take [`q`, `u`] >> ASM_REWRITE_TAC [EPS_REFL, PREFIX],
        (* goal 1.1.2 (of 2) *)
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ],
      (* goal 1.2 (of 2) *)
      Cases_on `u` \\ (* 2 sub-goals here, sharing initial tacticals *)
      PAT_X_ASSUM ``WEAK_EQUIV p q``
		  (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR])) \\
      RES_TAC >|
      [ (* goal 1.2.1 (of 2) *)
        IMP_RES_TAC EPS_cases1 >- PROVE_TAC [] \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
        REWRITE_TAC [WEAK_TRANS] \\
        take [`p`, `u`] >> ASM_REWRITE_TAC [EPS_REFL, PREFIX],
        (* goal 1.2.2 (of 2) *)
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ] ]);

(* Hennessy Lemma, the easy part *)
val HENNESSY_LEMMA_RL = store_thm ((* NEW *)
   "HENNESSY_LEMMA_RL",
  ``!p q. (OBS_CONGR p q \/ OBS_CONGR p (prefix tau q) \/
			    OBS_CONGR (prefix tau p) q) ==> WEAK_EQUIV p q``,
    REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 2.1 (of 3) *)
      IMP_RES_TAC OBS_CONGR_IMP_OBS_EQUIV,
      (* goal 2.2 (of 3) *)
      IMP_RES_TAC OBS_CONGR_IMP_OBS_EQUIV \\
      ASSUME_TAC (Q.SPEC `q` TAU_WEAK) \\
      IMP_RES_TAC OBS_EQUIV_TRANS,
      (* goal 2.3 (of 3) *)
      IMP_RES_TAC OBS_CONGR_IMP_OBS_EQUIV \\
      ASSUME_TAC (Q.SPEC `p` TAU_WEAK) \\
      POP_ASSUM (ASSUME_TAC o (MATCH_MP OBS_EQUIV_SYM)) \\
      IMP_RES_TAC OBS_EQUIV_TRANS ]);

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
(*                        Free and Bound names                                *)
(*                                                                            *)
(******************************************************************************)

val delete_def = Define `
    delete x ls = FILTER ((<>) x) ls`;

(*
val delete_LENGTH = store_thm (
   "delete_LENGTH", ``!x ls. MEM x ls ==> LENGTH (delete x ls) < LENGTH ls``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [delete_def]
 >> cheat);
 *)

(* (size :(α, β) CCS -> num) *)
val size_def = Define `
    size (p :('a, 'b) CCS) = CCS_size (\x. 0) (\x. 0) p`;

(* (constants :('a, 'b) CCS -> 'a list) *)
val constants_def = Define `
   (constants (nil :('a, 'b) CCS)	= []) /\
   (constants (prefix u p)		= constants p) /\
   (constants (sum p q)			= (constants p) ++ (constants q)) /\
   (constants (par p q)			= (constants p) ++ (constants q)) /\
   (constants (restr L p)		= constants p) /\
   (constants (relab p rf)		= constants p) /\
   (constants (var x)			= []) /\
   (constants (rec x p)			= [x])`;

(* (FN :('a, 'b) CCS -> ('a -> bool) -> 'b Label -> bool) *)
val FN_definition = `
   (FN (nil :('a, 'b) CCS) (J: 'a list)	= (EMPTY :'b Label set)) /\
   (FN (prefix (label l) p) J		= l INSERT (FN p J)) /\
   (FN (prefix tau p) J			= FN p J) /\
   (FN (sum p q) J			= (FN p J) UNION (FN q J)) /\
   (FN (par p q) J			= (FN p J) UNION (FN q J)) /\
   (FN (restr L p) J			= (FN p J) DIFF (L UNION (IMAGE COMPL_LAB L))) /\
   (FN (relab p rf) J			= IMAGE (REP_Relabeling rf) (FN p J)) /\
   (FN (var x) J			= EMPTY) /\
   (FN (rec x p) J			= if (MEM x J)
					  then FN (CCS_Subst p (rec x p) x) (delete x J)
					  else EMPTY)`;

val FN_defn = Hol_defn "FN" FN_definition;

(* Defn.tgoal FN_defn;
val FN_tacticals =
    WF_REL_TAC `inv_image ($< LEX $<) (\x. (size (FST x), LENGTH (SND x)))`
 >> REPEAT STRIP_TAC (* 9 sub-goals here *)
 >| [ (* goal 1 (of 9) *)
      Q.SPEC_TAC (`p`, `p`) \\
      Induct_on `p` >| (* 8 sub-goals here *)
      [ (* goal 1.1 (of 8) *)
        DISJ1_TAC \\
        ONCE_REWRITE_TAC [CCS_Subst_def] \\
        REWRITE_TAC [size_def, CCS_size_def] \\
        RW_TAC arith_ss [],
        (* goal 1.2 (of 8) *)
	GEN_TAC \\
        RW_TAC arith_ss [CCS_Subst_def, size_def, CCS_size_def] \\
        PROVE_TAC [delete_LENGTH],
        (* goal 1.3 (of 8) *)
        GEN_TAC >> DISJ1_TAC \\
        ONCE_REWRITE_TAC [CCS_Subst_def] \\
 *)

(*
val free_names = new_definition ("free_names",
  ``free_names p = FN p (constants p)``);

(* some lemmas related to free/bound names *)
val FN_UNIV1 = store_thm ("FN_UNIV1",
  ``!p. ~(free_names(p) = (UNIV :'b Label set)) ==> ?a. ~(a IN free_names(p))``,
    PROVE_TAC [EQ_UNIV]);

val FN_UNIV2 = store_thm ("FN_UNIV2",
  ``!p q. ~(free_names(p) UNION free_names(q) = (UNIV :'b Label set)) ==>
	  ?a. ~(a IN free_names(p)) /\ ~(a IN free_names(q))``,
    PROVE_TAC [EQ_UNIV, IN_UNION]);

val FN_TRANS = store_thm ("FN_TRANS",
  ``!p l p'. TRANS p (label l) p' ==> l IN free_names(p)``,
    REWRITE_TAC [free_names]
 >> Induct_on `p` (* 8 sub-goals here *)
 >| [ (* goal 1 (of 8) *)
      REWRITE_TAC [NIL_NO_TRANS],
      (* goal 2 (of 8) *)
      REWRITE_TAC [VAR_NO_TRANS],
      (* goal 3 (of 8) *)
      REPEAT STRIP_TAC \\
      IMP_RES_TAC TRANS_PREFIX \\
      Cases_on `A` >- PROVE_TAC [Action_distinct_label] \\
      PAT_X_ASSUM ``label (l :'b Label) = label l'``
		  (ASSUME_TAC o (REWRITE_RULE [Action_11])) \\
      ASM_REWRITE_TAC [] \\
      ONCE_REWRITE_TAC [FN_def] \\
      PROVE_TAC [IN_INSERT],
      (* goal 4 (of 8) *)
      REPEAT STRIP_TAC \\
      IMP_RES_TAC TRANS_SUM \\ (* 2 sub-goals here, same tacticals *)
      RES_TAC \\
      ONCE_REWRITE_TAC [FN_def] \\
      PROVE_TAC [IN_UNION, IN_INSERT],
      (* goal 5 (of 8) *)
      REPEAT STRIP_TAC \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 5.1 (of 3) *)
        RES_TAC \\
        ONCE_REWRITE_TAC [FN_def] \\
        PROVE_TAC [IN_UNION, IN_INSERT],
        (* goal 5.2 (of 3) *)
        RES_TAC \\
        ONCE_REWRITE_TAC [FN_def] \\
        PROVE_TAC [IN_UNION, IN_INSERT],
        (* goal 5.3 (of 3) *)
        PROVE_TAC [Action_distinct_label] ],
      (* goal 6 (of 8) *)
      REPEAT STRIP_TAC \\
      IMP_RES_TAC TRANS_RESTR >- PROVE_TAC [Action_distinct_label] \\
      RES_TAC \\
      ONCE_REWRITE_TAC [FN_def] \\
      REWRITE_TAC [IN_DIFF] >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [IN_UNION] \\
      PAT_X_ASSUM ``label (l :'b Label) = label l'``
		  (ASSUME_TAC o (REWRITE_RULE [Action_11])) \\
      ASM_REWRITE_TAC [] \\
      RW_TAC std_ss [IN_IMAGE] \\
      CCONTR_TAC \\
      POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP (DECIDE ``~(~A \/ ~B) ==> A /\ B``))) \\
      Cases_on `x` >| (* 2 sub-goals here *)
      [ (* goal 6.1 (of 2) *)
        Cases_on `l` >|
        [ (* goal 6.1.1 (of 2) *)
          PROVE_TAC [COMPL_LAB_def, Label_distinct],
          (* goal 6.1.2 (of 2) *)
          PROVE_TAC [COMPL_LAB_def, Label_11] ],
        (* goal 6.2 (of 2) *)
        Cases_on `l` >|
        [ (* goal 6.2.1 (of 2) *)
          PROVE_TAC [COMPL_LAB_def, Label_11],
          (* goal 6.2.2 (of 2) *)
          PROVE_TAC [COMPL_LAB_def, Label_distinct] ] ],
      (* goal 7 (of 8) *)
      cheat,
      (* goal 8 (of 8) *)
      REPEAT STRIP_TAC \\
      IMP_RES_TAC TRANS_REC \\
      cheat ]);

val FN_NO_TRANS = store_thm (
   "FN_NO_TRANS", ``!p l. ~(l IN free_names(p)) ==> !p'. ~(TRANS p (label l) p')``,
    PROVE_TAC [FN_TRANS]);

val FN_NO_WEAK_TRANS = store_thm (
   "FN_NO_WEAK_TRANS", ``!p l. ~(l IN free_names(p)) ==> !p'. ~(WEAK_TRANS p (label l) p')``,
    cheat);
 *)

(******************************************************************************)
(*                                                                            *)
(*                Coarsest congruence contained in WEAK_EQUIV		      *)
(*                                                                            *)
(******************************************************************************)

val COARSEST_CONGR_LR = store_thm ((* NEW *)
   "COARSEST_CONGR_LR",
  ``!p q. OBS_CONGR p q ==> !r. WEAK_EQUIV (sum p r) (sum q r)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC OBS_CONGR_IMP_OBS_EQUIV
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

val defn = ``(\E E'. ?u. TRANS E u E')``;
val Reachable_def = Define `Reachable = RTC ^defn`;

val trans = (REWRITE_RULE [GSYM Reachable_def]) o BETA_RULE o (ISPEC defn);

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

val Reachable_cases_rtc_twice = save_thm ((* NEW *)
   "Reachable_cases_rtc_twice", trans RTC_CASES_RTC_TWICE);

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
   "MODE_NODES", ``!p q q'. q IN (NODES p) /\ Reachable q q' ==> q' IN (NODES p)``,
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

(* (branches :('a, 'b) CCS -> ('a, 'b) CCS -> bool) *)
val branches_def = Define `
    branches (p :('a, 'b) CCS) = { q | ?u. TRANS p u q }`;

val TRANS_IN_branches = store_thm (
   "TRANS_IN_branches", ``!p u q. TRANS p u q ==> q IN (branches p)``,
    REPEAT STRIP_TAC
 >> SRW_TAC [] [branches_def]
 >> Q.EXISTS_TAC `u`
 >> ASM_REWRITE_TAC []);

val branches_NIL = store_thm (
   "branches_NIL", ``branches nil = EMPTY``,
    SRW_TAC [] [branches_def]
 >> REWRITE_TAC [EMPTY_DEF, GSPECIFICATION, EXTENSION, IN_APP]
 >> BETA_TAC
 >> RW_TAC std_ss [PAIR_EQ]
 >> REWRITE_TAC [NIL_NO_TRANS]);

val branches_VAR = store_thm (
   "branches_VAR", ``!x. branches (var x) = EMPTY``,
    SRW_TAC [] [branches_def]
 >> REWRITE_TAC [EMPTY_DEF, GSPECIFICATION, EXTENSION, IN_APP]
 >> BETA_TAC
 >> RW_TAC std_ss [PAIR_EQ]
 >> REWRITE_TAC [VAR_NO_TRANS]);

val weak_branches_def = Define `
    weak_branches (p :('a, 'b) CCS) = { q | ?u. WEAK_TRANS p u q }`;

(******************************************************************************)
(*                                                                            *)
(*       Coarsest congruence contained in WEAK_EQUIV (stronger version)       *)
(*                                                                            *)
(******************************************************************************)

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
val KLOP_PROP1_WEAK = store_thm ((* NEW *)
   "KLOP_PROP1_WEAK",
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

(* Klop processes are strong distinct with each other *)
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

(* Klop processes are weak distinct with each other *)
val KLOP_PROP2_WEAK = store_thm ((* NEW *)
   "KLOP_PROP2_WEAK",
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
	(STRIP_ASSUME_TAC o (REWRITE_RULE [KLOP_PROP1_WEAK]))
 >> PROVE_TAC []);

(* The shared core lemma used in PROP3's proof *)
val PROP3_SHARED = store_thm ((* NEW *)
   "PROP3_SHARED",
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
          `WEAK_EQUIV E2' k` by PROVE_TAC [OBS_EQUIV_SYM] \\ (* one extra step *)
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
              `WEAK_EQUIV E2 k` by PROVE_TAC [EPS_STABLE', OBS_EQUIV_SYM] \\
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

(* The finite version of Klop's Lemma *)
val KLOP_LEMMA_FINITE = store_thm ((* NEW *)
   "KLOP_LEMMA_FINITE",
  ``!g h. FINITE_STATE g /\ FINITE_STATE h ==>
	  ?k. STABLE k /\
	      (!g' u. WEAK_TRANS g u g' ==> ~(WEAK_EQUIV g' k)) /\
	      (!h' u. WEAK_TRANS h u h' ==> ~(WEAK_EQUIV h' k))``,
    REPEAT STRIP_TAC
 (* Part 1: assert that the union of all nodes in g and h is finite *)
 >> PAT_X_ASSUM ``FINITE_STATE g`` (ASSUME_TAC o (REWRITE_RULE [FINITE_STATE_def]))
 >> PAT_X_ASSUM ``FINITE_STATE h`` (ASSUME_TAC o (REWRITE_RULE [FINITE_STATE_def]))
 >> Q.ABBREV_TAC `nodes = (NODES g) UNION (NODES h)`
 >> `FINITE nodes` by PROVE_TAC [FINITE_UNION]
 (* Part 2: assert the infinite set of Klop processes *)
 >> Q.ABBREV_TAC `klops = IMAGE (\n:num. KLOP (ARB :'b Label) n) (UNIV :num set)`
 >> cheat
 );

(* The finite version of COARSEST_CONGR_THM *)
val PROP3_FINITE = store_thm ((* NEW *)
   "PROP3_FINITE",
  ``!g h. FINITE_STATE g /\ FINITE_STATE h ==>
	  (OBS_CONGR g h = (!r. WEAK_EQUIV (sum g r) (sum h r)))``,
    REPEAT STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [COARSEST_CONGR_LR]
 >> MP_TAC (Q.SPECL [`g`, `h`] KLOP_LEMMA_FINITE)
 >> RW_TAC std_ss [PROP3_SHARED]);

(* The full version of Klop's Lemma *)
val KLOP_LEMMA = store_thm ((* NEW *)
   "KLOP_LEMMA",
  ``!g h. ?k. STABLE k /\
	      (!g' u. WEAK_TRANS g u g' ==> ~(WEAK_EQUIV g' k)) /\
	      (!h' u. WEAK_TRANS h u h' ==> ~(WEAK_EQUIV h' k))``,
    REPEAT GEN_TAC
 >> cheat);

(* A stronger version of COARSEST_CONGR_THM from [vGl05], without any assumption.
   Noticed that, HOL type system automatically guarantees that any type must have
   at least one instance, so there's always at least one action a IN Act - {tau},
   no matter what Act type 'b is there.
 *)
val PROP3 = store_thm ((* NEW *)
   "PROP3", ``!g h. OBS_CONGR g h = (!r. WEAK_EQUIV (sum g r) (sum h r))``,
    REPEAT STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [COARSEST_CONGR_LR]
 >> MP_TAC (Q.SPECL [`g`, `h`] KLOP_LEMMA)
 >> RW_TAC std_ss [PROP3_SHARED]);

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
