(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure WeakEQLib :> WeakEQLib =
struct

open HolKernel Parse boolLib bossLib;

open CCSLib CCSTheory StrongEQLib WeakEQTheory;

infix 0 OE_THENC OE_ORELSEC;

(******************************************************************************)
(*                                                                            *)
(*              Basic functions and conversions for rewriting		      *)
(*               with the laws for observational equivalence		      *)
(*                                                                            *)
(******************************************************************************)

(* Define OE_SYM such that, when given a theorem A |- OBS_EQUIV t1 t2,
   returns the theorem A |- OBS_EQUIV t2 t1. *)
fun OE_SYM thm = MATCH_MP OBS_EQUIV_SYM thm;

(* Define OE_TRANS such that, when given the theorems thm1 and thm2, applies
   OBS_EQUIV_TRANS on them, if possible.
 *)
fun OE_TRANS thm1 thm2 =
    if (rhs_tm thm1 = lhs_tm thm2) then
	MATCH_MP OBS_EQUIV_TRANS (CONJ thm1 thm2)
    else
	failwith "transitivity of observation equivalence not applicable";

(* When applied to a term "t: CCS", the conversion OE_ALL_CONV returns the
   theorem: |- OBS_EQUIV t t
 *)
fun OE_ALL_CONV t = ISPEC t OBS_EQUIV_REFL;

(* Define the function OE_THENC. *)
fun op OE_THENC ((c1, c2) :conv * conv) :conv =
  fn t => let
      val thm1 = c1 t;
      val thm2 = c2 (rhs_tm thm1)
  in OE_TRANS thm1 thm2 end;

(* Define the function OE_ORELSEC. *)
fun op OE_ORELSEC ((c1, c2) :conv * conv) :conv =
  fn t => c1 t handle HOL_ERR _ => c2 t;

(* Define the function OE_REPEATC *)
fun OE_REPEATC (c :conv) (t :term) :thm =
  ((c OE_THENC (OE_REPEATC c)) OE_ORELSEC OE_ALL_CONV) t;

(* Convert a conversion for the application of the laws for STRONG_EQUIV to a
   tactic applying the laws for OBS_EQUIV (i.e. c is a conversion for strong
   equivalence). *)
fun OE_LHS_CONV_TAC (c :conv) :tactic =
  fn (asl, w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if (opt = ``OBS_EQUIV``) then
	  let val thm = MATCH_MP STRONG_IMP_OBS_EQUIV ((S_DEPTH_CONV c) t1);
	      val (t1', t') = args_thm thm (* t1' = t1 *)
	  in
	      if (t' = t2) then
		  ([], fn [] => OE_TRANS thm (ISPEC t' OBS_EQUIV_REFL))
	      else
		  ([(asl, ``OBS_EQUIV ^t' ^t2``)],
		   fn [thm'] => OE_TRANS thm thm')
	  end
      else
	  failwith "the goal is not an OBS_EQUIV relation"
  end;

fun OE_RHS_CONV_TAC (c :conv) :tactic =
  fn (asl,w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if (opt = ``OBS_EQUIV``) then
	  let val thm = MATCH_MP STRONG_IMP_OBS_EQUIV ((S_DEPTH_CONV c) t2);
	      val (t2', t') = args_thm thm (* t2' = t2 *)
	  in
	      if (t' = t1) then
		  ([], fn [] => OE_SYM thm)
	      else
		  ([(asl, ``OBS_EQUIV ^t1 ^t'``)],
		   fn [thm'] => OE_TRANS thm' (OE_SYM thm))
	  end
      else
	  failwith "the goal is not an OBS_EQUIV relation"
  end;

val STRONG_IMP_OBS_EQUIV_RULE =
    STRIP_FORALL_RULE (MATCH_MP STRONG_IMP_OBS_EQUIV);

end (* struct *)

(* last updated: Jun 18, 2017 *)
