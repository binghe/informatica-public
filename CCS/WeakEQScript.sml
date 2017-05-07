(*
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open stringTheory pred_setTheory relationTheory;
open CCSLib CCSTheory StrongEQTheory StrongEQLib;

(* Set PAT_X_ASSUM to PAT_ASSUM if it's not defined yet *)
local
    val PAT_X_ASSUM = PAT_ASSUM
    open Tactical
in
    val PAT_X_ASSUM = PAT_X_ASSUM
end;

val _ = new_theory "WeakEQ";

fun fix  ts = MAP_EVERY Q.X_GEN_TAC ts;	 (* from HOL Light *)
fun set  ts = MAP_EVERY Q.ABBREV_TAC ts; (* from mizar mode *)
fun take ts = MAP_EVERY Q.EXISTS_TAC ts; (* from mizar mode *)
val op// = op REPEAT;			 (* from Matita *)

(* Define the weak bisimulation relation on CCS processes. *)
val WEAK_BISIM = new_definition ("WEAK_BISIM",
  ``WEAK_BISIM (Wbsm: CCS -> CCS -> bool) =
    (!E E'.
       Wbsm E E' ==>
       (!l.
         (!E1. TRANS E (label l) E1 ==>
               (?E2. WEAK_TRANS E' [l] E2 /\ Wbsm E1 E2)) /\
         (!E2. TRANS E' (label l) E2 ==>
               (?E1. WEAK_TRANS E [l] E1 /\ Wbsm E1 E2))) /\
       (!E1. TRANS E tau E1 ==> 
             (?E2. WEAK_TRANS E' epsilon E2 /\ Wbsm E1 E2)) /\
       (!E2. TRANS E' tau E2 ==>
             (?E1. WEAK_TRANS E epsilon E1 /\ Wbsm E1 E2)))``);

val WEAK_EQUIV = new_definition (
   "WEAK_EQUIV",
  ``WEAK_EQUIV E E' = (?Bsm. Bsm E E' /\ WEAK_BISIM Bsm)``);

val _ = set_mapped_fixity { fixity = Infix (NONASSOC, 450),
			    tok = "~~~", term_name = "WEAK_EQUIV" };

val _ = Unicode.unicode_version { u = UTF8.chr 0x2248, tmnm = "WEAK_EQUIV"};
val _ = TeX_notation { hol = UTF8.chr 0x2248,
                       TeX = ("\\HOLTokenWeakEquiv", 1) }

(* An equivalent WEAK_EQUIV definition based on HOL's coinductive relation *)
val (WEAK_EQ_rules, WEAK_EQ_coind, WEAK_EQ_cases) = Hol_coreln `
    (!E E'.
       (!l.
         (!E1. TRANS E (label l) E1 ==>
               (?E2. WEAK_TRANS E' [l] E2 /\ WEAK_EQ E1 E2)) /\
         (!E2. TRANS E' (label l) E2 ==>
               (?E1. WEAK_TRANS E [l] E1 /\ WEAK_EQ E1 E2))) /\
       (!E1. TRANS E tau E1 ==> 
             (?E2. WEAK_TRANS E' epsilon E2 /\ WEAK_EQ E1 E2)) /\
       (!E2. TRANS E' tau E2 ==>
             (?E1. WEAK_TRANS E epsilon E1 /\ WEAK_EQ E1 E2)) ==> WEAK_EQ E E')`;

val _ = export_theory ();
val _ = DB.html_theory "WeakEQ";

(* last updated: April 19, 2017 *)
