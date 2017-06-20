(*
 * Copyright 1991  University of Cambridge (Author: Monica Nesi)
 * Copyright 2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory listTheory IndDefRules;
open CCSLib CCSTheory WeakEQTheory;

val _ = new_theory "ObsCongr";

(******************************************************************************)
(*                                                                            *)
(*          Operational definition of observation congruence for CCS	      *)
(*                 and related properties				      *)
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

(* Observation congruence is an equivalence relation. *)



val _ = export_theory ();
val _ = DB.html_theory "ObsCongr";

(* last updated: Jun 20, 2017 *)
