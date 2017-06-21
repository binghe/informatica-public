(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2017  University of Bologna   (Author: Chun Tian)
 *)

signature WeakEQLib =
sig
  include Abbrev

  val OE_SYM			: thm -> thm
  val OE_TRANS			: thm -> thm -> thm
  val OE_ALL_CONV		: conv
  val OE_THENC			: conv * conv -> conv
  val OE_ORELSEC		: conv * conv -> conv
  val OE_REPEATC		: conv -> conv
  val OE_LHS_CONV_TAC		: conv -> tactic
  val OE_RHS_CONV_TAC		: conv -> tactic

  val EPS_INDUCT_TAC		: tactic
end

(* last updated: Jun 18, 2017 *)
