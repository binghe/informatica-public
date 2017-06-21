(*
 * Copyright 1991  University of Cambridge (Author: Monica Nesi)
 * Copyright 2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory listTheory IndDefRules; (* none is actually used *)
open CCSLib CCSTheory StrongEQTheory WeakEQTheory WeakEQLib;

val _ = new_theory "ObsCongr";

(******************************************************************************)
(*                                                                            *)
(*          Operational definition of observation congruence for CCS	      *)
(*                  and related properties				      *)
(*                                                                            *)
(******************************************************************************)

(* Define the observation congruence over CCS agents expressions. *)
val OBS_CONGR = new_definition ("OBS_CONGR",
  ``OBS_CONGR (E :('a, 'b) CCS) (E' :('a, 'b) CCS) =
       (!(u :'b Action).
	 (!E1. TRANS E u E1 ==>
	       (?E2. WEAK_TRANS E' u E2 /\ WEAK_EQUIV E1 E2)) /\
	 (!E2. TRANS E' u E2 ==>
	       (?E1. WEAK_TRANS E  u E1 /\ WEAK_EQUIV E1 E2)))``);

val _ = set_mapped_fixity { fixity = Infix (NONASSOC, 450),
			    tok = "~~c", term_name = "OBS_CONGR" };

val _ = Unicode.unicode_version { u = UTF8.chr 0x2248 ^ UTF8.chr 0x02B3, tmnm = "OBS_CONGR"};
val _ = TeX_notation { hol = UTF8.chr 0x2248 ^ UTF8.chr 0x02B3, (* double-tilde ^ r *)
		       TeX = ("\\HOLTokenObsCongr", 1) };

(* Prove that observation congruence implies observation equivalence. *)
val OBS_CONGR_IMP_OBS_EQUIV = store_thm (
   "OBS_CONGR_IMP_OBS_EQUIV", ``!E E'. OBS_CONGR E E' ==> OBS_EQUIV E E'``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [OBS_CONGR, OBS_PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 4 sub-goals here, sharing initial & end tactical *)
 >> RES_TAC
 >| [ Q.EXISTS_TAC `E2`,
      Q.EXISTS_TAC `E1`,
      IMP_RES_TAC WEAK_TRANS_TAU >> Q.EXISTS_TAC `E2`,
      IMP_RES_TAC WEAK_TRANS_TAU >> Q.EXISTS_TAC `E1` ]
 >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*             Observation congruence is an equivalence relation	      *)
(*                                                                            *)
(******************************************************************************)

(* Observation congruence is a reflexive relation. *)
val OBS_CONGR_REFL = store_thm (
   "OBS_CONGR_REFL", ``!E. OBS_CONGR E E``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here, sharing begin & end tacticals *)
 >> IMP_RES_TAC TRANS_IMP_WEAK_TRANS
 >| [ (* goal 1 (of 2) *) Q.EXISTS_TAC `E1`,
      (* goal 2 (of 2) *) Q.EXISTS_TAC `E2` ]
 >> ASM_REWRITE_TAC [OBS_EQUIV_REFL]);

(* Observation congruence is a symmetric relation. *)
val OBS_CONGR_SYM = store_thm (
   "OBS_CONGR_SYM", ``!E E'. OBS_CONGR E E' ==> OBS_CONGR E' E``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here, sharing begin & end tacticals *)
 >> RES_TAC
 >> IMP_RES_TAC OBS_EQUIV_SYM
 >| [ (* goal 1 (of 2) *) Q.EXISTS_TAC `E1'`,
      (* goal 1 (of 2) *) Q.EXISTS_TAC `E2'` ]
 >> ASM_REWRITE_TAC []);

(* Syntactic equivalence implies observation congruence. *)
val EQUAL_IMP_OBS_CONGR = store_thm (
   "EQUAL_IMP_OBS_CONGR", ``!E E'. (E = E') ==> OBS_CONGR E E'``,
    REPEAT STRIP_TAC
 >> PURE_ASM_REWRITE_TAC [OBS_CONGR_REFL]);

(* Lemma 1: `EPS E E1` implies zero or more tau transitions, and this leads to zero or
   at least one tau transition on the other side, which implies `EPS E' E2` in any case. *)
val OBS_CONGR_EPS = store_thm ((* NEW *)
   "OBS_CONGR_EPS",
  ``!E E'. OBS_CONGR E E' ==>
	  (!E1. EPS E E1 ==> ?E2. EPS E' E2 /\ WEAK_EQUIV E1 E2)``,
    REPEAT STRIP_TAC
 >> PAT_X_ASSUM ``OBS_CONGR E E'`` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`E1`, `E1`)
 >> Q.SPEC_TAC (`E`, `E`)
 >> HO_MATCH_MP_TAC EPS_strongind_right (* must use right induct here! *)
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC OBS_CONGR_IMP_OBS_EQUIV \\
      Q.EXISTS_TAC `E'` \\
      RW_TAC std_ss [EPS_REFL],
      (* goal 2 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC (ONCE_REWRITE_RULE [OBS_PROPERTY_STAR] (ASSUME ``OBS_EQUIV E1 E2``)) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EPS_TRANS ]);

(* Lemma 2: in any case, `WEAK_TRANS E u E1` implies at least one transition, and this leads
   to `WEAK_TRANS E' u E2` on the other side, by definition of OBS_CONGR *)
val OBS_CONGR_WEAK_TRANS = store_thm ((* NEW *)
   "OBS_CONGR_WEAK_TRANS",
  ``!E E'. OBS_CONGR E E' ==>
	  (!u E1. WEAK_TRANS E u E1 ==> ?E2. WEAK_TRANS E' u E2 /\ WEAK_EQUIV E1 E2)``,
    REPEAT STRIP_TAC
 >> Cases_on `u` (* 2 sub-goals here *)
 >| [ (* case 1 (of 2): u = tau *)
      IMP_RES_TAC WEAK_TRANS_TAU_IMP_TRANS_TAU \\
      IMP_RES_TAC (REWRITE_RULE [OBS_CONGR] (ASSUME ``OBS_CONGR E E'``)) \\
      IMP_RES_TAC (REWRITE_RULE [WEAK_EQUIV_IS_WEAK_BISIM]
		       (Q.SPECL [`OBS_EQUIV`, `E2`]
				(MATCH_MP EPS_TRANS_AUX (ASSUME ``EPS E1' E1``)))) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      ASSUME_TAC (Q.SPEC `E'` EPS_REFL) \\
      IMP_RES_TAC EPS_AND_WEAK,
      (* case 2 (of 2): ~(u = tau) *)
      IMP_RES_TAC WEAK_TRANS \\
      IMP_RES_TAC (MATCH_MP OBS_CONGR_EPS (* lemma 1 used here *)
			    (ASSUME ``OBS_CONGR E E'``)) \\
      IMP_RES_TAC (CONJUNCT1
		       (PURE_ONCE_REWRITE_RULE [OBS_PROPERTY_STAR]
					       (ASSUME ``OBS_EQUIV E1' E2'``))) \\
      IMP_RES_TAC (REWRITE_RULE [WEAK_EQUIV_IS_WEAK_BISIM]
		       (Q.SPECL [`OBS_EQUIV`, `E2''`]
				(MATCH_MP EPS_TRANS_AUX (ASSUME ``EPS E2 E1``)))) \\
      Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EPS_AND_WEAK ]);

(* Observation congruence is a transitive relation.
   Proof hints:
               +-------- ~~ ------+  --->  (sub-goal 1)
               |                  |             ||
              !E1  ~~   ?E2  ~~  ?E3 (lemma 2)  ||
               /\        /\       /\            ||
               |         ||       ||            ||
              !u         u        u             \/
               |         ||       ||            
               E   ~~c   E'  ~~c  E''   ==>   E ~~c E'' (goal)
            ||  ||     |  ||      |             
            ||   u     u  ||      |             /\
            u   ||     |   u     !u             ||
            ||  \/     \/ ||      |             ||
            || ?E1 ~~ !E2 ||      |             ||
            \/            \/      \/            ||
 (lemma 2) ?E1'    ~~    ?E2' ~~ !E3            ||
            |                     |             ||
            +--------- ~~ --------+  --->  (sub-goal 2)
 *)
val OBS_CONGR_TRANS = store_thm ((* NEW *)
   "OBS_CONGR_TRANS",
  ``!E E' E''. OBS_CONGR E E' /\ OBS_CONGR E' E'' ==> OBS_CONGR E E''``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (REWRITE_RULE [OBS_CONGR] (ASSUME ``OBS_CONGR E E'``)) \\
      IMP_RES_TAC (MATCH_MP OBS_CONGR_WEAK_TRANS (* lemma 2 used here *)
			    (ASSUME ``OBS_CONGR E' E''``)) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC OBS_EQUIV_TRANS,
      (* goal 2 (of 2) *)
      IMP_RES_TAC OBS_CONGR_SYM \\
      IMP_RES_TAC (REWRITE_RULE [OBS_CONGR] (ASSUME ``OBS_CONGR E'' E'``)) \\
      IMP_RES_TAC (MATCH_MP OBS_CONGR_WEAK_TRANS (* lemma 2 used here *)
			    (ASSUME ``OBS_CONGR E' E``)) \\
      Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC OBS_EQUIV_SYM \\
      IMP_RES_TAC OBS_EQUIV_TRANS ]);

val _ = export_theory ();
val _ = DB.html_theory "ObsCongr";

(* last updated: Jun 20, 2017 *)
