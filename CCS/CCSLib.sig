(*
 * A formalization of the process algebra CCS in HOL4
 *
 * (based on the HOL proof code written by Prof. Monica Nesi in 1992)
 *
 * Copyright 1992  University of Cambridge, England (Author: Monica Nesi)
 * Copyright 2017  University of Bologna, Italy (Author: Chun Tian)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 * THIS CODE IS PROVIDED *AS IS* BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, EITHER EXPRESS OR IMPLIED, INCLUDING WITHOUT LIMITATION ANY IMPLIED
 * WARRANTIES OR CONDITIONS OF TITLE, FITNESS FOR A PARTICULAR PURPOSE,
 * MERCHANTABLITY OR NON-INFRINGEMENT.
 * See the Apache 2 License for the specific language governing permissions and
 * limitations under the License.
 *)

signature CCSLib =
sig
  include Abbrev

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
  val EQ_IMP_LR			: thm -> thm
  val EQ_IMP_RL			: thm -> thm
  val lconcl			: thm -> term
  val rconcl			: thm -> term
end
