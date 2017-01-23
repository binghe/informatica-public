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

structure CCSLib :> CCSLib =
struct

open HolKernel Parse boolLib bossLib;

(******************************************************************************)
(*                                                                            *)
(*          Basic rules and tactics for particular forms of rewriting         *)
(*                                                                            *)
(******************************************************************************)

(* Rule for rewriting only the right-hand side on an equation once. *)
val ONCE_REWRITE_RHS_RULE =
    GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites;

(* Rule for rewriting only the right-hand side on an equation (pure version). *)
val PURE_REWRITE_RHS_RULE =
    GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) empty_rewrites;

(* Rule for rewriting only the right-hand side on an equation
   (basic rewrites included) *)
val REWRITE_RHS_RULE =
    GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) (implicit_rewrites ());

(* Tactic for rewriting only the right-hand side on an equation once. *)
val ONCE_REWRITE_RHS_TAC =
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites; 

(* Tactic for rewriting only the right-hand side on an equation. *)
val REWRITE_RHS_TAC =
    GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) (implicit_rewrites ());

(* Rule for rewriting only the left-hand side on an equation once. *)
val ONCE_REWRITE_LHS_RULE =
    GEN_REWRITE_RULE (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites;

(* Rule for rewriting only the left-hand side on an equation (pure version). *)
val PURE_REWRITE_LHS_RULE =
    GEN_REWRITE_RULE (RATOR_CONV o TOP_DEPTH_CONV) empty_rewrites;

(* Rule for rewriting only the left-hand side on an equation
   (basic rewrites included). *)
val REWRITE_LHS_RULE =
    GEN_REWRITE_RULE (RATOR_CONV o TOP_DEPTH_CONV) (implicit_rewrites ());

(* Tactic for rewriting only the left-hand side on an equation once. *)
val ONCE_REWRITE_LHS_TAC =
    GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites;

(* Tactic for rewriting only the left-hand side on an equation. *)
val REWRITE_LHS_TAC =
    GEN_REWRITE_TAC (RATOR_CONV o TOP_DEPTH_CONV) (implicit_rewrites ());

(* Rule for rewriting only the left-hand side of an equation once with the
   assumptions. *)
fun ONCE_ASM_REWRITE_LHS_RULE thl th =
    ONCE_REWRITE_LHS_RULE (append (map ASSUME (hyp th)) thl) th;

(* Tactic for rewriting only the left-hand side of an equation once with the
   assumptions. *)
fun ONCE_ASM_REWRITE_LHS_TAC thl =
    ASSUM_LIST (fn asl => ONCE_REWRITE_LHS_TAC (append asl thl));

(* Conversion to swap two universally quantified variables. *)
fun SWAP_FORALL_CONV tm = let
    val (v1, body) = dest_forall tm;
    val v2 = fst (dest_forall body);
    val tl1 = [v1, v2] and tl2 = [v2, v1];
    val th1 = GENL tl2 (SPECL tl1 (ASSUME tm));
    val th2 = GENL tl1 (SPECL tl2 (ASSUME (concl th1)))
in
    IMP_ANTISYM_RULE (DISCH_ALL th1) (DISCH_ALL th2)
end;

(* The rule EQ_IMP_LR returns the implication from left to right of a given
   equational theorem. *)
fun EQ_IMP_LR thm = GEN_ALL (fst (EQ_IMP_RULE (SPEC_ALL thm)));

(* The rule EQ_IMP_RL returns the implication from right to left of a given
   equational theorem. *)
fun EQ_IMP_RL thm = GEN_ALL (snd (EQ_IMP_RULE (SPEC_ALL thm)));

(* Functions to get the left and right hand side of the equational conclusion
   of a theorem. *)
val lconcl = fst o dest_eq o concl o SPEC_ALL;
val rconcl = snd o dest_eq o concl o SPEC_ALL;

end (* struct *)
