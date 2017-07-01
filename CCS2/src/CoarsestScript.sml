(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pairTheory prim_recTheory;

open CCSLib CCSTheory CCSSimps;
open StrongEQTheory StrongEQLib StrongLawsTheory StrongLawsConv;
open WeakEQTheory WeakEQLib WeakLawsTheory WeakLawsConv;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory ObsCongrConv;

val _ = new_theory "Coarsest";

(******************************************************************************)
(*                                                                            *)
(*               A derived tau-law for observation congruence                 *)
(*                                                                            *)
(******************************************************************************)

(* Theorem TAU_STRAT:
   |- !E E'. OBS_CONGR (sum E (prefix tau (sum E' E))) (prefix tau (sum E' E))

val TAU_STRAT = store_thm (
   "TAU_STRAT",
  ``!E E'. OBS_CONGR (sum E (prefix tau (sum E' E))) (prefix tau (sum E' E))``,
    REPEAT GEN_TAC
 >> OC_LHS_SUBST1_TAC
       (SPEC ``sum E' E`` (GEN_ALL (OC_SYM (SPEC_ALL TAU2))))
 >> SUM_IDEMP_TAC THEN
       OC_LHS_SUBST1_TAC (SPEC "sum E' E" TAU2));;
*)

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
        DISJ1_TAC \\ (* CHOOSE ``p ~~c q`` *)
        PROVE_TAC [DENG_LEMMA] ] ]);

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

(* (FN :('a, 'b) CCS -> ('a -> bool) -> 'b Label -> bool) *)
val FN_defn = Hol_defn "FN" `
   (FN (nil :('a, 'b) CCS) (J: 'a list)	= (EMPTY :'b Label set)) /\
   (FN (prefix (label l) p) J		= l INSERT (FN p J)) /\
   (FN (prefix tau p) J			= FN p J) /\
   (FN (sum p q) J			= (FN p J) UNION (FN q J)) /\
   (FN (par p q) J			= (FN p J) UNION (FN q J)) /\
   (FN (restr L p) J			= (FN p J) DIFF (L UNION (IMAGE COMPL_LAB L))) /\
   (FN (relab p rf) J			= IMAGE (REP_Relabeling rf) (FN p J)) /\
   (FN (var x) J			= EMPTY) /\
   (FN (rec x p) J			= if (EXISTS (\i. i = x) J)
					  then FN (CCS_Subst p (rec x p) x)
						  (FILTER (\i. ~(i = x)) J)
					  else EMPTY) `;

(* (size :(α, β) CCS -> num) *)
val size_def = Define `size (p :('a, 'b) CCS) = CCS_size (\x. 0) (\x. 0) p`;

(* (constants :('a, 'b) CCS -> 'a list) *)
val constants_def = Define `
   (constants (nil :('a, 'b) CCS)	= []) /\
   (constants (prefix u p)		= constants p) /\
   (constants (sum p q)			= (constants p) ++ (constants q)) /\
   (constants (par p q)			= (constants p) ++ (constants q)) /\
   (constants (restr L p)		= constants p) /\
   (constants (relab p rf)		= constants p) /\
   (constants (var x)			= []) /\
   (constants (rec x p)			= [x]) `;

(*
Defn.tgoal FN_defn;
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
        RW_TAC arith_ss [CCS_Subst_def, size_def, CCS_size_def]
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

val COARSEST_CONGR_RL = store_thm ((* NEW *)
   "COARSEST_CONGR_RL",
  ``!p q. (?a. !p'. ~(WEAK_TRANS p (label a) p')) /\
	  (?a. !q'. ~(WEAK_TRANS q (label a) q')) ==>
	  (!r. WEAK_EQUIV (sum p r) (sum q r)) ==> OBS_CONGR p q``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [OBS_CONGR]
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
   OBS_CONGR congruences theorems shouldn't depend on this result. *)
val COARSEST_CONGR_THM = store_thm ((* NEW *)
   "COARSEST_CONGR_THM",
  ``!p q. (?a. !p'. ~(WEAK_TRANS p (label a) p')) /\
	  (?a. !q'. ~(WEAK_TRANS q (label a) q')) ==>
	  (OBS_CONGR p q = !r. WEAK_EQUIV (sum p r) (sum q r))``,
    REPEAT STRIP_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [COARSEST_CONGR_LR],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC COARSEST_CONGR_RL \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        Q.EXISTS_TAC `a` >> ASM_REWRITE_TAC [],
        (* goal 2.2 (of 2) *)
        Q.EXISTS_TAC `a'` >> ASM_REWRITE_TAC [] ] ]);

(* A more difficult result from [vGl05], without cardinality assumptions:
val PROP3 = store_thm ((* NEW *)
   "PROP3",
  ``!p q. OBS_CONGR p q = (!r. WEAK_EQUIV (sum p r) (sum q r))``,
   cheat);
 *)

(** Bibliography:

[Den07] Y. Deng, “A simple completeness proof for the axiomatisations of weak behavioural
    equivalences”, Bulletin of the EATCS, 93:207-219, 2007.

[Mil89] R. Milner, Communication and Concurrency, Prentice-Hall, 1989.

[vGl05] R.J. van Glabbeek, “A characterisation of weak bisimulation congruence”, in Processes,
    Terms and Cycles: Steps on the Road to Infinity, Essays dedicated to Jan Willem Klop, on the
    occasion of his 60th birthday, LNCS 3838, 26-39. Springer-Verlag, 2005.

*)

val _ = export_theory ();
val _ = DB.html_theory "Coarsest";

(* last updated: Jun 24, 2017 *)
