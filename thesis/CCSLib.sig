(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

signature CCSLib =
sig
  include Abbrev

  val PAT_X_ASSUM		: term -> thm_tactic -> tactic
  val qpat_x_assum		: term quotation -> thm_tactic -> tactic
  val Q_GENL			: Q.tmquote list -> thm -> thm
  val fix			: Q.tmquote list -> tactic
  val set			: Q.tmquote list -> tactic
  val take			: Q.tmquote list -> tactic
  val !!			: tactic -> tactic
  val Know			: Q.tmquote -> tactic
  val Suff			: Q.tmquote -> tactic
  val K_TAC			: 'a -> tactic
  val KILL_TAC			: tactic
  val wrap			: 'a -> 'a list
  val art			: thm list -> tactic
  val PRINT_TAC			: string -> tactic
  val COUNT_TAC			: tactic -> tactic
  val Rewr			: tactic
  val Rewr'			: tactic
  val STRONG_CONJ_TAC		: tactic
  val Rev			: tactic -> tactic

  val ONCE_REWRITE_RHS_RULE	: thm list -> thm -> thm
  val PURE_REWRITE_RHS_RULE	: thm list -> thm -> thm
  val REWRITE_RHS_RULE		: thm list -> thm -> thm
  val ONCE_REWRITE_RHS_TAC	: thm list -> tactic
  val REWRITE_RHS_TAC		: thm list -> tactic
  val ONCE_REWRITE_LHS_RULE	: thm list -> thm -> thm
  val PURE_REWRITE_LHS_RULE	: thm list -> thm -> thm
  val REWRITE_LHS_RULE		: thm list -> thm -> thm
  val ONCE_REWRITE_LHS_TAC	: thm list -> tactic
  val REWRITE_LHS_TAC		: thm list -> tactic
  val ONCE_ASM_REWRITE_LHS_RULE	: thm list -> thm -> thm
  val ONCE_ASM_REWRITE_LHS_TAC	: thm list -> tactic
  val SWAP_FORALL_CONV		: term -> thm
  val STRIP_FORALL_RULE		: (thm -> thm) -> thm -> thm
  val EQ_IMP_LR			: thm -> thm
  val EQ_IMP_RL			: thm -> thm
  val lconcl			: thm -> term
  val rconcl			: thm -> term

  val args_thm			: thm -> term * term
  val lhs_tm			: thm -> term
  val rhs_tm			: thm -> term
  val args_equiv		: term -> term * term * term
  val elim			: term -> term list -> term list
  val list_apply_tac		: ('a -> tactic) -> 'a list -> tactic list

end

(* last updated: May 14, 2017 *)
