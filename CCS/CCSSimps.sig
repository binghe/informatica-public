(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

signature CCSSimps =
sig
  include Abbrev

  val PAR1_TAC			: tactic
  val PAR2_TAC			: tactic
  val PAR3_TAC			: tactic
  val PREFIX_TAC		: tactic
  val REC_TAC			: tactic
  val RELAB_TAC			: tactic
  val RESTR_TAC			: tactic
  val SUM1_TAC			: tactic
  val SUM2_TAC			: tactic

  val CCS_TRANS_CONV		: conv
  val CCS_TRANS_CONV'		: conv
  val CCS_TRANS			: term -> thm * (term * term) list
  val CCS_TRANS'		: term -> thm * (term * term) list

end
