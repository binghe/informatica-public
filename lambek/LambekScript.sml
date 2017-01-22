(*
 * A HOL Toolkit for Lambek Calculus & Categorial Type Logics
 *
 * (based on `A Coq Toolkit for Lambek Calculus` (https://github.com/coq-contribs/lambek)
 *
 * Copyright 2016-2017  University of Bologna, Italy (Author: Chun Tian)
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

open HolKernel Parse boolLib bossLib;

open relationTheory listTheory arithmeticTheory;

val _ = new_theory "Lambek";

(*** Module: Form ***)

val _ = Datatype `Form = Atom 'a | Slash Form Form | Backslash Form Form | Dot Form Form`;

(* or val _ = overload_on ("*", Term `Dot`); *)
val _ = set_mapped_fixity { fixity = Infix(NONASSOC, 450), tok = ".", term_name = "Dot" };
val _ = set_mapped_fixity { fixity = Infix(LEFT, 1000), tok = "/", term_name = "Slash" };
val _ = set_mapped_fixity { fixity = Infix(RIGHT, 1500), tok = "\\", term_name = "Backslash" };

(** The arrow relationship and its extensions (like associativity, commutativity  etc.) **)

val _ = type_abbrev ("arrow_extension", ``:'a Form -> 'a Form -> bool``);

val _ = overload_on("add_extension", ``relation$RUNION``);

val extends_def = Define `extends X X' = X RSUBSET X'`;

val no_extend = store_thm ("no_extend", ``!X. extends X X``,
    RW_TAC bool_ss [extends_def, RSUBSET]);

val add_extend_l = store_thm ("add_extend_l", ``!X X'. extends X (add_extension X X')``,
    RW_TAC bool_ss [extends_def, RSUBSET, RUNION]);

val add_extend_r = store_thm ("add_extend_r", ``!X X'. extends X' (add_extension X X')``,
    RW_TAC bool_ss [extends_def, RSUBSET, RUNION]);

val extends_trans = store_thm ("extends_trans",
  ``!X Y Z. extends X Y /\ extends Y Z ==> extends X Z``,
    RW_TAC bool_ss [extends_def, RSUBSET]);

val extends_transitive = store_thm ("extends_trans", ``transitive extends``,
    REWRITE_TAC [transitive_def, extends_trans]);

(* Rules of Lambek's syntactic calculus (non-associative) *)
val (Arrow_rules, Arrow_ind, _) = Hol_reln `
    (!X A. Arrow X A A) /\						(* a  / one    *)
    (!X A B C. Arrow X (Dot A B) C ==> Arrow X A (Slash C B)) /\	(* c  / beta   *)
    (!X A B C. Arrow X A (Slash C B) ==> Arrow X (Dot A B) C) /\	(* d  / beta'  *)
    (!X A B C. Arrow X (Dot A B) C ==> Arrow X B (Backslash A C)) /\	(* c' / gamma  *)
    (!X A B C. Arrow X B (Backslash A C) ==> Arrow X (Dot A B) C) /\	(* d' / gamma' *)
    (!X A B C. Arrow X A B /\ Arrow X B C ==> Arrow X A C) /\		(* e  / comp   *)
    (!X A B. X A B ==> Arrow X A B)`;					(* arrow_plus  *)

val [one, beta, beta', gamma, gamma', comp, arrow_plus] = CONJ_LIST 7 Arrow_rules;

(** most popular extensions **)

val NL_def = Define `NL = EMPTY_REL`;

val (L_rules, _ , _) = Hol_reln `
    (!A B C. L (Dot A (Dot B C)) (Dot (Dot A B) C)) /\
    (!A B C. L (Dot (Dot A B) C) (Dot A (Dot B C)))`;

val [L_rule_rl, L_rule_lr] = CONJ_LIST 2 L_rules;

val (NLP_rules, _, _) = Hol_reln `(!A B. NLP (Dot A B) (Dot B A))`;

val LP_def = Define `LP = add_extension NLP L`;

val NL_X = store_thm ("NL_X", ``!X. extends NL X``,
    RW_TAC bool_ss [extends_def, NL_def, EMPTY_REL_DEF, RSUBSET]);

val NLP_LP = store_thm ("NLP_LP", ``extends NLP LP``,
    REWRITE_TAC [LP_def, add_extend_l]);

val L_LP = store_thm ("L_LP", ``extends L LP``,
    REWRITE_TAC [LP_def, add_extend_r]);

(* Some derived rules for arrow.
   Note: all theorems here can be simply proved by PROVE_TAC [Arrow_rules]. *)

val Dot_mono_right = store_thm ("Dot_mono_right",
  ``!X A B B'. Arrow X B' B ==> Arrow X (Dot A B') (Dot A B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC gamma'
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `B`
 >> CONJ_TAC
 >| [ ASM_REWRITE_TAC [],
      MATCH_MP_TAC gamma >> RW_TAC bool_ss [one] ]);

val Dot_mono_left = store_thm ("Dot_mono_left",
  ``!X A B A'. Arrow X A' A ==> Arrow X (Dot A' B) (Dot A B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC beta'
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `A`
 >> CONJ_TAC
 >| [ ASM_REWRITE_TAC [],
      MATCH_MP_TAC beta >> RW_TAC bool_ss [one] ]);

val Dot_mono = store_thm ("Dot_mono",
  ``!X A B C D. Arrow X A C /\ Arrow X B D ==> Arrow X (Dot A B) (Dot C D)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC comp
 >> EXISTS_TAC ``(Dot C B)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC Dot_mono_left >> RW_TAC bool_ss [],
      MATCH_MP_TAC Dot_mono_right >> RW_TAC bool_ss [] ]);

val Slash_mono_left = store_thm ("Slash_mono_left",
  ``!X C B C'. Arrow X C' C ==> Arrow X (Slash C' B) (Slash C B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC beta
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `C'`
 >> CONJ_TAC
 >| [ MATCH_MP_TAC beta' >> RW_TAC bool_ss [one], RW_TAC bool_ss [] ]);

val Slash_antimono_right = store_thm ("Slash_antimono_right",
  ``!X C B B'. Arrow X B' B ==> Arrow X (Slash C B) (Slash C B')``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC beta
 >> MATCH_MP_TAC gamma'
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `B`
 >> CONJ_TAC
 >| [ ASM_REWRITE_TAC [],
      MATCH_MP_TAC gamma >> MATCH_MP_TAC beta' >> RW_TAC bool_ss [one] ]);

val Backslash_antimono_left = store_thm ("Backslash_antimono_left",
  ``!X A C A'. Arrow X A A' ==> Arrow X (Backslash A' C) (Backslash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC gamma
 >> MATCH_MP_TAC beta'
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `A'`
 >> CONJ_TAC
 >| [ ASM_REWRITE_TAC [],
      MATCH_MP_TAC beta >> MATCH_MP_TAC gamma' >> RW_TAC bool_ss [one] ]);

val Backslash_mono_right = store_thm ("Backslash_mono_right",
  ``!X A C C'. Arrow X C' C ==> Arrow X (Backslash A C') (Backslash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC gamma
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `C'`
 >> CONJ_TAC
 >| [ MATCH_MP_TAC beta' >> MATCH_MP_TAC beta >>
      MATCH_MP_TAC gamma' >> RW_TAC bool_ss [one],
      ASM_REWRITE_TAC [] ]);

val mono_X = store_thm ("mono_X",
  ``!X' X A B. Arrow X A B ==> extends X X' ==> Arrow X' A B``,
    GEN_TAC
 >> HO_MATCH_MP_TAC Arrow_ind (* or stronger: Induct_on `Arrow` *)
 >> REPEAT STRIP_TAC (* 7 sub-goals *)
 >| [ REWRITE_TAC [one],
      RW_TAC bool_ss [beta],
      RW_TAC bool_ss [beta'],
      RW_TAC bool_ss [gamma],
      RW_TAC bool_ss [gamma'],
      PROVE_TAC [comp],
      PROVE_TAC [arrow_plus, extends_def, RSUBSET] ]);

val pi = store_thm ("pi", ``!X. extends NLP X ==> (!A B. Arrow X (Dot A B) (Dot B A))``,
    REPEAT STRIP_TAC
 >> `NLP (Dot A B) (Dot B A)` by REWRITE_TAC [NLP_rules]
 >> `Arrow NLP (Dot A B) (Dot B A)` by RW_TAC bool_ss [arrow_plus]
 >> PROVE_TAC [mono_X]);

val pi_NLP = store_thm ("pi_NLP", ``!A B. Arrow NLP (Dot A B) (Dot B A)``,
    MATCH_MP_TAC pi
 >> REWRITE_TAC [no_extend]);

val pi_LP = store_thm ("pi_LP", ``!A B. Arrow LP (Dot A B) (Dot B A)``,
    MATCH_MP_TAC pi
 >> REWRITE_TAC [NLP_LP]);

(* original name: alpha in Coq version *)
val aleph = store_thm ("aleph",
  ``!X. extends L X ==> (!A B C. Arrow X (Dot A (Dot B C)) (Dot (Dot A B) C))``,
    REPEAT STRIP_TAC
 >> `L (Dot A (Dot B C)) (Dot (Dot A B) C)` by REWRITE_TAC [L_rule_rl]
 >> `Arrow L (Dot A (Dot B C)) (Dot (Dot A B) C)` by RW_TAC bool_ss [arrow_plus]
 >> PROVE_TAC [mono_X]);

val aleph_L = store_thm ("aleph_L", ``!A B C. Arrow L (Dot A (Dot B C)) (Dot (Dot A B) C)``,
    MATCH_MP_TAC aleph
 >> REWRITE_TAC [no_extend]);

val aleph_LP = store_thm ("aleph_LP", ``!A B C. Arrow LP (Dot A (Dot B C)) (Dot (Dot A B) C)``,
    MATCH_MP_TAC aleph
 >> REWRITE_TAC [L_LP]);

val aleph' = store_thm ("aleph'",
  ``!X. extends L X ==> (!A B C. Arrow X (Dot (Dot A B) C) (Dot A (Dot B C)))``,
    REPEAT STRIP_TAC
 >> `L (Dot (Dot A B) C) (Dot A (Dot B C))` by REWRITE_TAC [L_rule_lr]
 >> `Arrow L (Dot (Dot A B) C) (Dot A (Dot B C))` by RW_TAC bool_ss [arrow_plus]
 >> PROVE_TAC [mono_X]);

val aleph'_L = store_thm ("aleph'_L", ``!A B C. Arrow L (Dot (Dot A B) C) (Dot A (Dot B C))``,
    MATCH_MP_TAC aleph'
 >> REWRITE_TAC [no_extend]);

val aleph'_LP = store_thm ("aleph'_LP", ``!A B C. Arrow LP (Dot (Dot A B) C) (Dot A (Dot B C))``,
    MATCH_MP_TAC aleph'
 >> REWRITE_TAC [L_LP]);

(* Arrow for Standard (full) Lambek calculus, here we recover all lemmas in Lambek (1958) *)

val arrow_def = Define `arrow = Arrow L`;

val _ = set_mapped_fixity { fixity = Infix(NONASSOC, 450), tok = "-->", term_name = "arrow" };
val _ = Unicode.unicode_version {u = UnicodeChars.rightarrow, tmnm = "arrow"};

val L_a = store_thm ("L_a", ``!x. arrow x x``, REWRITE_TAC [arrow_def, one]);
val L_b = store_thm ("L_b",  ``!x y z. arrow (Dot (Dot x y) z) (Dot x (Dot y z))``,
    REWRITE_TAC [arrow_def, aleph'_L]);
val L_b' = store_thm ("L_b'", ``!x y z. arrow (Dot x (Dot y z)) (Dot (Dot x y) z)``,
    REWRITE_TAC [arrow_def, aleph_L, aleph'_L]);
val L_c  = store_thm ("L_c",  ``!x y z. arrow (Dot x y) z ==> arrow x (Slash z y)``,
    REWRITE_TAC [arrow_def, beta]);
val L_c' = store_thm ("L_c'", ``!x y z. arrow (Dot x y) z ==> arrow y (Backslash x z)``,
    REWRITE_TAC [arrow_def, gamma]);
val L_d  = store_thm ("L_d",  ``!x y z. arrow x (Slash z y) ==> arrow (Dot x y) z``,
    REWRITE_TAC [arrow_def, beta']);
val L_d' = store_thm ("L_d'", ``!x y z. arrow y (Backslash x z) ==> arrow (Dot x y) z``,
    REWRITE_TAC [arrow_def, gamma']);
val L_e  = store_thm ("L_e",  ``!x y z. arrow x y /\ arrow y z ==> arrow x z``,
    REWRITE_TAC [arrow_def, comp]);

val arrow_rules = LIST_CONJ [L_a, L_b, L_b', L_c, L_c', L_d, L_d', L_e];

local
  val t = PROVE_TAC [arrow_rules]
in
  val L_f  = store_thm ("L_f",  ``!x y. arrow x (Slash (Dot x y) y)``, t)
  and L_g  = store_thm ("L_g",  ``!y z. arrow (Dot (Slash z y) y) z``, t)
  and L_h  = store_thm ("L_h",  ``!y z. arrow y (Backslash (Slash z y) z)``, t)
  and L_i  = store_thm ("L_i",  ``!x y z. arrow (Dot (Slash z y) (Slash y x)) (Slash z x)``, t)
  and L_j  = store_thm ("L_j",  ``!x y z. arrow (Slash z y) (Slash (Slash z x) (Slash y x))``, t)
  and L_k  = store_thm ("L_k",  ``!x y z. arrow (Slash (Backslash x y) z) (Backslash x (Slash y z))``, t)
  and L_k' = store_thm ("L_k'", ``!x y z. arrow (Backslash x (Slash y z)) (Slash (Backslash x y) z)``, t)
  and L_l  = store_thm ("L_l",  ``!x y z. arrow (Slash (Slash x y) z) (Slash x (Dot z y))``, t)
  and L_l' = store_thm ("L_l'", ``!x y z. arrow (Slash x (Dot z y)) (Slash (Slash x y) z)``, t)
  and L_m  = store_thm ("L_m",  ``!x x' y y'. arrow x x' /\ arrow y y'
					  ==> arrow (Dot x y) (Dot x' y')``, t)
  and L_n  = store_thm ("L_n",  ``!x x' y y'. arrow x x' /\ arrow y y'
					  ==> arrow (Slash x y') (Slash x' y)``, t);

  val arrow_rules_ex = LIST_CONJ [L_f, L_g, L_h, L_i, L_j, L_k, L_k', L_l, L_l', L_m, L_n]
end;

local
  val t = PROVE_TAC [L_a, L_c, L_c', L_d, L_d', L_e] (* L_b and L_b' are not used *)
in
  val L_dot_mono_r = store_thm ("L_dot_mono_r",
      ``!A B B'. arrow B B' ==> arrow (Dot A B) (Dot A B')``, t)
  and L_dot_mono_l = store_thm ("L_dot_mono_l",
      ``!A B A'. arrow A A' ==> arrow (Dot A B) (Dot A' B)``, t)
  and L_slash_mono_l = store_thm ("L_slash_mono_l",
      ``!C B C'. arrow C C' ==> arrow (Slash C B) (Slash C' B)``, t)
  and L_slash_antimono_r = store_thm ("L_slash_antimono_r",
      ``!C B B'. arrow B B' ==> arrow (Slash C B') (Slash C B)``, t)
  and L_backslash_antimono_l = store_thm ("L_backslash_antimono_l",
      ``!A C A'. arrow A A' ==> arrow (Backslash A' C) (Backslash A C)``, t)
  and L_backslash_mono_r = store_thm ("L_backslash_mono_r",
      ``!A C C'. arrow C C' ==> arrow (Backslash A C) (Backslash A C')``, t);

  val arrow_rules_mono = LIST_CONJ [L_dot_mono_r, L_dot_mono_l,
				    L_slash_mono_l, L_slash_antimono_r,
				    L_backslash_antimono_l, L_backslash_mono_r]
end;

(*** Module: Terms ***)

val _ = Datatype `Term = OneForm ('a Form) | Comma Term Term`;

(*
val _ = add_rule { term_name = "Comma", fixity = Infix(LEFT, 500),
		   pp_elements = [HardSpace 0, TOK "," , BreakSpace(1,0)],
		   paren_style = Always,
		   block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)) };
*)

val _ = type_abbrev ("gentzen_extension", ``:'a Term -> 'a Term -> bool``);

(* Definition of the recursive function that translates Terms to Forms *)
val deltaTranslation_def = Define `
   (deltaTranslation (OneForm f) = f) /\
   (deltaTranslation (Comma t1 t2) = Dot (deltaTranslation t1) (deltaTranslation t2))`;

(* Definition of the relation that connects arrow_extension with gentzen_extension *)
val implements_def = Define
   `implements (X:'a arrow_extension) (E:'a gentzen_extension) =
    (!(A:'a Term) (B:'a Term). E A B = X (deltaTranslation A) (deltaTranslation B))`;

(* NL Sequent extension, an empty relation actually *)
val NL_Sequent_def = Define `NL_Sequent A B = NL (deltaTranslation A) (deltaTranslation B)`;

val NLimplementsSequent = store_thm ("NLimplementsSequent",
  ``implements NL NL_Sequent``,
    RW_TAC bool_ss [NL_Sequent_def, implements_def]);

(* NLP Sequent extension *)
val NLP_Sequent_def = Define `NLP_Sequent A B = NLP (deltaTranslation A) (deltaTranslation B)`;

val NLPimplementsSequent = store_thm ("NLPimplementsSequent",
  ``implements NLP NLP_Sequent``,
    RW_TAC bool_ss [NLP_Sequent_def, implements_def]);

val NLP_Intro = store_thm ("NLP_Intro", ``!A B. NLP_Sequent (Comma A B) (Comma B A)``,
    RW_TAC bool_ss [deltaTranslation_def, NLP_Sequent_def, NLP_rules]);

(* L Sequent extension, the Full Lambek Sequent Calculus extension *)
val L_Sequent_def = Define `L_Sequent A B = L (deltaTranslation A) (deltaTranslation B)`;

val LimplementsSequent = store_thm ("LimplementsSequent",
  ``implements L L_Sequent``,
    RW_TAC bool_ss [L_Sequent_def, implements_def]);

(* two important L_Intro rules now become theorems *)
local
  val t = RW_TAC bool_ss [deltaTranslation_def, L_Sequent_def, L_rules]
in
  val L_Intro_lr = store_thm ("L_Intro_lr",
    ``!A B C. L_Sequent (Comma A (Comma B C)) (Comma (Comma A B) C)``, t)
  and L_Intro_rl = store_thm ("L_Intro_rl",
    ``!A B C. L_Sequent (Comma (Comma A B) C) (Comma A (Comma B C))``, t)
end;

val LP_Sequent_def = Define `LP_Sequent = add_extension NLP_Sequent L_Sequent`;

val LPextendsL = store_thm ("LPextendsL",
  ``!E. extends LP_Sequent E ==> extends L_Sequent E``,
    RW_TAC bool_ss [LP_Sequent_def, extends_def, RSUBSET, RUNION]);

val LPextendsNLP = store_thm ("LPextendsNLP",
  ``!E. extends LP_Sequent E ==> extends NLP_Sequent E``,
    RW_TAC bool_ss [LP_Sequent_def, extends_def, RSUBSET, RUNION]);

val LPimplementsSequent = store_thm ("LPimplementsSequent",
  ``implements LP LP_Sequent``,
    REWRITE_TAC [implements_def]
 >> RW_TAC bool_ss [LP_def, LP_Sequent_def]
 >> REWRITE_TAC [RUNION]
 >> RW_TAC bool_ss [NLP_Sequent_def, L_Sequent_def]);

(*** Module: ReplaceProp ***)

(* The `replace` operator has the type ('a ReplaceProp) *)
val _ = type_abbrev ("ReplaceProp", ``:'a Term -> 'a Term -> 'a Term -> 'a Term -> bool``);

(* Inductive definition of `replace` such that when ``replace Gamma Gamma' Delta Delta'``
   then Gamma' results from replacing a distinguished occurrence of the subterm Delta in
   the term Gamma by Delta' *)

val (replace_rules, replace_ind, _) = Hol_reln `
    (!F1 F2. replace F1 F2 F1 F2) /\					(* replaceRoot *)
    (!Gamma1 Gamma2 Delta F1 F2.
     replace Gamma1 Gamma2 F1 F2 ==>
     replace (Comma Gamma1 Delta) (Comma Gamma2 Delta) F1 F2) /\	(* replaceLeft *)
    (!Gamma1 Gamma2 Delta F1 F2.
     replace Gamma1 Gamma2 F1 F2 ==>
     replace (Comma Delta Gamma1) (Comma Delta Gamma2) F1 F2)`;		(* replaceRight *)

val [replaceRoot, replaceLeft, replaceRight] = CONJ_LIST 3 replace_rules;

(* Definition of `replaceCommaDot` such that when ``replaceCommaDot Gamma Gamma'``
   then Gamma' is the result of replacing a number of commas in Gamma by the connector dot.

   Example: ``!A B. replaceCommaDot (A , (A , B)) (A , (A . B)))`` where in this case only
   one occurrence of comma is replaced by a dot. *)

val (replaceCommaDot1_rules, _ , replaceCommaDot1_cases) = Hol_reln `
    (!T1 T2 A B.
     replace T1 T2 (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) ==>
     replaceCommaDot1 T1 T2)`;

val replaceCommaDot_def = Define `replaceCommaDot = RTC replaceCommaDot1`;

val replaceCommaDot_rule = store_thm ("replaceCommaDot_rule",
  ``!T1 T2 A B.
    replace T1 T2 (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) ==>
    replaceCommaDot T1 T2``,
    PROVE_TAC [replaceCommaDot_def, replaceCommaDot1_rules, RTC_SINGLE]);

val replaceTransitive = store_thm ("replaceTransitive", ``transitive replaceCommaDot``,
    REWRITE_TAC [replaceCommaDot_def, RTC_TRANSITIVE]);

(* a more practical version *)
val replaceTransitive' = store_thm ("replaceTransitive'",
  ``!T1 T2 T3. replaceCommaDot T1 T2 /\ replaceCommaDot T2 T3 ==> replaceCommaDot T1 T3``,
    PROVE_TAC [replaceTransitive, transitive_def]);

val noReplace = store_thm ("noReplace", ``!T. replaceCommaDot T T``,
    PROVE_TAC [replaceCommaDot_def, RTC_REFLEXIVE, reflexive_def]);

local
  val t = PROVE_TAC [replaceCommaDot1_rules, replaceCommaDot_def, replaceTransitive,
		     transitive_def, RTC_SINGLE]
in
  val replaceOneComma = store_thm ("replaceOneComma",
    ``!T1 T2 T3 A B.
      replaceCommaDot T1 T2 /\
      replace T2 T3 (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B))
      ==> replaceCommaDot T1 T3``, t)

  and replaceOneComma' = store_thm ("replaceOneComma'",
    ``!T1 T2 T3 A B.
      replace T1 T2 (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) /\
      replaceCommaDot T2 T3
      ==> replaceCommaDot T1 T3``, t);

  val replaceCommaDot_rules = LIST_CONJ [noReplace, replaceCommaDot_rule,
					 replaceOneComma, replaceOneComma']
end;

(* An induction theorem for RTC replaceCommaDot1, similar to those generated by Hol_reln *)
val replaceCommaDot_ind = store_thm ("replaceCommaDot_ind",
  ``!(P:'a gentzen_extension).
     (!x. P x x) /\
     (!x y z A B.
       replace x y (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) /\ P y z ==> P x z)
     ==> (!x y. replaceCommaDot x y ==> P x y)``,
 (* The idea is to use RTC_INDUCT thm to prove induct theorems for RTCs *)
    REWRITE_TAC [replaceCommaDot_def]
 >> GEN_TAC   (* remove outer !P *)
 >> STRIP_TAC (* prepare for higher order matching *)
 >> HO_MATCH_MP_TAC (ISPEC ``replaceCommaDot1:'a gentzen_extension`` RTC_INDUCT)
 >> PROVE_TAC [replaceCommaDot1_cases]);

local
  val t = GEN_TAC (* prepare for higher order matching and induction *)
	  >> HO_MATCH_MP_TAC replaceCommaDot_ind
	  >> PROVE_TAC [replace_rules, replaceCommaDot_rules]
in
  val replaceMonoRight = store_thm ("replaceMonoRight",
    ``!T3 T1 T2. replaceCommaDot T1 T2 ==> replaceCommaDot (Comma T1 T3) (Comma T2 T3)``, t)
  and replaceMonoLeft = store_thm ("replaceMonoLeft",
    ``!T3 T1 T2. replaceCommaDot T1 T2 ==> replaceCommaDot (Comma T3 T1) (Comma T3 T2)``, t)
end;

val replaceMono = store_thm ("replaceMono",
  ``!T1 T2 T3 T4. replaceCommaDot T1 T2 /\ replaceCommaDot T3 T4 ==>
		  replaceCommaDot (Comma T1 T3) (Comma T2 T4)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC replaceTransitive'
 >> EXISTS_TAC ``Comma T2 T3``
 >> PROVE_TAC [replaceMonoLeft, replaceMonoRight]);

val replaceTranslation = store_thm ("replaceTranslation",
  ``!T. replaceCommaDot T (OneForm (deltaTranslation T))``,
    Induct
 >| [ PROVE_TAC [deltaTranslation_def, noReplace], (* base case *)
      REWRITE_TAC [deltaTranslation_def]         (* induct case *)
   >> MATCH_MP_TAC replaceTransitive'
   >> EXISTS_TAC ``Comma (OneForm (deltaTranslation T')) (OneForm (deltaTranslation T''))``
   >> PROVE_TAC [replaceOneComma, noReplace, replaceRoot, replaceMono] ]);

(* TODO / remain theorems: replace_inv1, replace_inv2, doubleReplace, replaceSameP, replaceTrans *)

(*** Module: NaturalDeduction ***)

val (natDed_rules, _ , _) = Hol_reln `
    (!(E:'a gentzen_extension) A . natDed E (OneForm A) A) /\			(* NatAxiom *)
    (!E Gamma A B.								(* SlashIntro *)
      natDed E (Comma Gamma (OneForm B)) A ==> natDed E Gamma (Slash A B)) /\
    (!E Gamma A B.								(* BackslashIntro *)
      natDed E (Comma (OneForm B) Gamma) A ==> natDed E Gamma (Backslash B A)) /\
    (!E Gamma Delta A B.							(* DotIntro *)
      natDed E Gamma A /\ natDed E Delta B ==> natDed E (Comma Gamma Delta) (Dot A B)) /\
    (!E Gamma Delta A B.							(* SlashElim *)
      natDed E Gamma (Slash A B) /\ natDed E Delta B ==> natDed E (Comma Gamma Delta) A) /\
    (!E Gamma Delta A B.						 	(* BackslashElim *)
      natDed E Gamma B /\ natDed E Delta (Backslash B A) ==> natDed E (Comma Gamma Delta) A) /\
    (!E Gamma Gamma' Delta A B C.						(* DotElim *)
      replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) Delta /\
      natDed E Delta (Dot A B) /\ natDed E Gamma C ==> natDed E Gamma' C) /\
    (!(E:'a gentzen_extension) C Gamma Gamma' Delta Delta'.			(* NatExt *)
      replace Gamma Gamma' Delta Delta' /\ E Delta Delta' /\
      natDed E Gamma C ==> natDed E Gamma' C)`;

val [NatAxiom, SlashIntro, BackslashIntro, DotIntro, SlashElim, BackslashElim, DotElim, NatExt] =
    (CONJ_LIST 8 natDed_rules);

(* Alternative definition, above natDed_rules then become deriable theorems from Arrow_rules
val natDed_def = Define `
    natDed E Gamma A = (!X. implements X E ==> Arrow X (deltaTranslation Gamma) A)`;

val NatAxiom = store_thm ("NatAxiom", ``!E A. natDed E (OneForm A) A``,
    REWRITE_TAC [natDed_def, deltaTranslation_def]
 >> REPEAT STRIP_TAC
 >> REWRITE_TAC [one]);

val SlashIntro = store_thm ("SlashIntro",
  ``(!E Gamma A B. natDed E (Comma Gamma (OneForm B)) A ==> natDed E Gamma (Slash A B))``,
    REWRITE_TAC [natDed_def, deltaTranslation_def]
 >> PROVE_TAC [beta]);

val BackslashIntro = store_thm ("BackslashIntro",
  ``(!E Gamma A B. natDed E (Comma (OneForm B) Gamma) A ==> natDed E Gamma (Backslash B A))``,
    REWRITE_TAC [natDed_def, deltaTranslation_def]
 >> PROVE_TAC [gamma]);

(* this is rule (5) in Lambek (1958), from arrow rule (L_m) *)
val DotIntro = store_thm ("DotIntro'",
  ``!E Gamma Delta A B. natDed E Gamma A /\ natDed E Delta B
		    ==> natDed E (Comma Gamma Delta) (Dot A B)``,
    RW_TAC bool_ss [natDed_def, deltaTranslation_def]
 >> PROVE_TAC [Arrow_rules]);

val SlashElim = store_thm ("SlashElim",
  ``!E Gamma Delta A B. natDed E Gamma (Slash A B) /\ natDed E Delta B
		    ==> natDed E (Comma Gamma Delta) A``,
    RW_TAC bool_ss [natDed_def, deltaTranslation_def]
 >> PROVE_TAC [Arrow_rules]);

val BackslashElim = store_thm ("BackslashElim'",
  ``!E Gamma Delta A B. natDed E Gamma B /\ natDed E Delta (Backslash B A)
		    ==> natDed E (Comma Gamma Delta) A``,
    RW_TAC bool_ss [natDed_def, deltaTranslation_def]
 >> PROVE_TAC [Arrow_rules]);
 *)

val NatAxiomGen = store_thm ("NatAxiomGen", ``!E Gamma. natDed E Gamma (deltaTranslation Gamma)``,
    Induct_on `Gamma:'a Term`
 >| [ PROVE_TAC [deltaTranslation_def, NatAxiom], (* base case *)
      REWRITE_TAC [deltaTranslation_def]        (* induct case *)
   >> PROVE_TAC [DotIntro] ]);

(* from GentzenDed.v, induction required, to be used for proving DotElim *)
val replaceNatDed = store_thm ("replaceNatDed",
  ``!E Gamma Gamma' Delta Delta'.
    replace Gamma Gamma' Delta Delta' ==>
    natDed E Delta' (deltaTranslation Delta) ==>
    natDed E Gamma' (deltaTranslation Gamma)``,
    GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> CONJ_TAC THEN1 RW_TAC bool_ss []
 >> REWRITE_TAC [deltaTranslation_def]
 >> CONJ_TAC
 >> REPEAT STRIP_TAC
 >> MATCH_MP_TAC DotIntro
 >> RW_TAC bool_ss [NatAxiomGen]);

(* 
val DotElim = store_thm ("DotElim",
  ``!E Gamma Gamma' Delta' A B C.
     replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) Delta' ==>
     natDed E Delta' (Dot A B) ==>
     natDed E Gamma C ==>
     natDed E Gamma' C``,
    REPEAT STRIP_TAC
 >> `natDed E Gamma' (deltaTranslation Gamma)` by PROVE_TAC [replaceNatDed, deltaTranslation_def]
 >> `natDed E Gamma (deltaTranslation Gamma)` by PROVE_TAC [NatAxiomGen]
 >> PROVE_TAC [natDed_def, Arrow_rules]);
*)

(* TODO: NatExt should be proved using arrow_plus or nothing ...
val NatExt = store_thm ("NatExt",
  ``!E C Gamma Gamma' Delta Delta'.
    replace Gamma Gamma' Delta Delta' ==> E Delta Delta' ==> natDed E Gamma C ==> natDed E Gamma' C``,
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ UNDISCH_TAC ``natDed E Gamma C``
   >> RW_TAC bool_ss [natDed_def] 
   >> `Arrow X (deltaTranslation Gamma) C` by PROVE_TAC []
   >> `X (deltaTranslation Gamma) (deltaTranslation Gamma')` by PROVE_TAC [implements_def]
   >> `Arrow X (deltaTranslation Gamma) (deltaTranslation Gamma')` by PROVE_TAC [arrow_plus]
   >> PROVE_TAC [Arrow_rules]
   >> , , ] );

val natDed_rules = LIST_CONJ [NatAxiom, SlashIntro, BackslashIntro, DotIntro,
			      SlashElim, BackslashElim, DotElim]; (* NatExt *)
 *)

val DotElimGeneralized = store_thm ("DotElimGeneralized",
  ``!E C Gamma Gamma'. replaceCommaDot Gamma Gamma' ==> natDed E Gamma C ==> natDed E Gamma' C``,
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC replaceCommaDot_ind
 >> REPEAT STRIP_TAC
 >> `natDed E (OneForm (Dot A B)) (Dot A B)` by PROVE_TAC [NatAxiomGen, deltaTranslation_def]
 >> `natDed E Gamma' C` by PROVE_TAC [DotElim]
 >> RW_TAC bool_ss []);

val TermToFormDed = store_thm ("TermToFormDed",
  ``!E Gamma C. natDed E Gamma C ==> natDed E (OneForm (deltaTranslation Gamma)) C``,
    REPEAT STRIP_TAC
 >> PROVE_TAC [DotElimGeneralized, replaceTranslation]);

(*** Module: Sequent Calculus ***)

(* NOTE: it's a little meaningless to try to derive these rules from Arrow rules or NatDed rules,
   because after all the CutRule cannot be proved inside these systems (however, we're going to
   prove any gentzenSequent proof has a corresponding Cut-free proof, thus CutRule can be eliminated *)

(* gentzen presentation using sequents: sequent is a pair (Gamma, A) where: *)
val (gentzenSequent_rules, gentzenSequent_ind, _) = Hol_reln `
    (!(E:'a gentzen_extension) A. gentzenSequent E (OneForm A) A) /\	(* SeqAxiom = NatAxiom *)
    (!E Gamma A B.							(* RightSlash = SlashIntro *)
      gentzenSequent E (Comma Gamma (OneForm B)) A ==>
      gentzenSequent E Gamma (Slash A B)) /\
    (!E Gamma A B.							(* RightBackslash = BackslashIntro *)
      gentzenSequent E (Comma (OneForm B) Gamma) A ==>
      gentzenSequent E Gamma (Backslash B A)) /\
    (!E Gamma Delta A B.						(* RightDot = DotIntro *)
      gentzenSequent E Gamma A /\ gentzenSequent E Delta B
      ==> gentzenSequent E (Comma Gamma Delta) (Dot A B)) /\
    (!E Gamma Gamma' Delta A B C.					(* LeftSlash != SlashElim *)
      replace Gamma Gamma' (OneForm A) (Comma (OneForm (Slash A B)) Delta) /\
      gentzenSequent E Delta B /\ gentzenSequent E Gamma C
      ==> gentzenSequent E Gamma' C) /\
    (!E Gamma Gamma' Delta A B C.					(* LeftBackslash != BackslashElim *)
      replace Gamma Gamma' (OneForm A) (Comma Delta (OneForm (Backslash B A))) /\
      gentzenSequent E Delta B /\ gentzenSequent E Gamma C
      ==> gentzenSequent E Gamma' C) /\
    (!E Gamma Gamma' A B C.						(* LeftDot != DotElim *)
      replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) /\
      gentzenSequent E Gamma C
      ==> gentzenSequent E Gamma' C) /\
    (!E Delta Gamma Gamma' A C.						(* CutRule is new *)
      replace Gamma Gamma' (OneForm A) Delta /\
      gentzenSequent E Delta A /\ gentzenSequent E Gamma C
      ==> gentzenSequent E Gamma' C) /\
    (!(E:'a gentzen_extension) Gamma Gamma' Delta Delta' C.		(* SequentExtension = NatExt *)
      replace Gamma Gamma' Delta Delta' /\ E Delta Delta' /\ gentzenSequent E Gamma C
      ==> gentzenSequent E Gamma' C)`;

val [SeqAxiom, RightSlash, RightBackslash, RightDot, LeftSlash, LeftBackslash, LeftDot,
     CutRule, SequentExtension] = CONJ_LIST 9 gentzenSequent_rules;

(* NOTE: deltaTranslation connects two operators Dot (in Forms) and Comma (in Terms).
         the theorem SeqAxiomGen seems essential for proving some foundamental theorems about
         Lambek calculu in gentzen's Sequent Calculus form. This made me think that, the above
         gentzenSequent_rules shouldn't be primitive, at least not all! *)

val SeqAxiomGen = store_thm ("SeqAxiomGen",
  ``!E Gamma. gentzenSequent E Gamma (deltaTranslation Gamma)``,
    Induct_on `Gamma:'a Term`
 >| [ PROVE_TAC [deltaTranslation_def, SeqAxiom], (* base case *)
      REWRITE_TAC [deltaTranslation_def] >>     (* induct case *)
      PROVE_TAC [RightDot] ]);

(* Some derived properties concerning gentzenSequent *)

val LeftDotSimpl = store_thm ("LeftDotSimpl",
  ``!E A B C. gentzenSequent E (Comma (OneForm A) (OneForm B)) C ==>
	      gentzenSequent E (OneForm (Dot A B)) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDot
 >> EXISTS_TAC ``(Comma (OneForm A) (OneForm B))``
 >> Q.EXISTS_TAC `A`
 >> Q.EXISTS_TAC `B`
 >> PROVE_TAC [replaceRoot]);

val LeftDotGeneralized = store_thm ("LeftDotGeneralized",
  ``!E C T1 T2. replaceCommaDot T1 T2 ==> gentzenSequent E T1 C ==> gentzenSequent E T2 C``,
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC replaceCommaDot_ind
 >> REPEAT STRIP_TAC
 >> PROVE_TAC [LeftDot]);

val TermToForm = store_thm ("TermToForm",
  ``!E Gamma C. gentzenSequent E Gamma C
	    ==> gentzenSequent E (OneForm (deltaTranslation Gamma)) C``,
    REPEAT GEN_TAC
 >> MATCH_MP_TAC LeftDotGeneralized
 >> RW_TAC bool_ss [replaceTranslation]);

val LeftSlashSimpl = store_thm ("LeftSlashSimpl",
  ``!E Gamma A B C. gentzenSequent E Gamma B /\ gentzenSequent E (OneForm A) C
	        ==> gentzenSequent E (Comma (OneForm (Slash A B)) Gamma) C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, LeftSlash]);

val LeftBackslashSimpl = store_thm ("LeftBackslashSimpl",
  ``!E Gamma A B C. gentzenSequent E Gamma B /\ gentzenSequent E (OneForm A) C
	        ==> gentzenSequent E (Comma Gamma (OneForm (Backslash B A))) C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, LeftBackslash]);

val CutRuleSimpl = store_thm ("CutRuleSimpl",
  ``!E Gamma A C. gentzenSequent E Gamma A /\ gentzenSequent E (OneForm A) C
	      ==> gentzenSequent E Gamma C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, CutRule]);

val DotRightSlash' = store_thm ("DotRightSlash'",
  ``!E A B C. gentzenSequent E (OneForm A) (Slash C B)
	  ==> gentzenSequent E (OneForm (Dot A B)) C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, gentzenSequent_rules]);

val DotRightBackslash' = store_thm ("DotRightBackslash'",
  ``!E A B C. gentzenSequent E (OneForm B) (Backslash A C)
	  ==> gentzenSequent E (OneForm (Dot A B)) C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, gentzenSequent_rules]);

(* some definitions concerning extensions *)

val LextensionSimpl = store_thm ("LextensionSimpl",
  ``!E T1 T2 T3 C. extends L_Sequent E /\
		   gentzenSequent E (Comma T1 (Comma T2 T3)) C
	       ==> gentzenSequent E (Comma (Comma T1 T2) T3) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC SequentExtension
 >> EXISTS_TAC ``(Comma T1 (Comma T2 T3))``       (* Gamma *)
 >> EXISTS_TAC ``(Comma T1 (Comma T2 T3))``       (* Delta *)
 >> EXISTS_TAC ``(Comma (Comma T1 T2) T3)``       (* Delta' *)
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ REWRITE_TAC [replaceRoot],
      PROVE_TAC [extends_def, RSUBSET, L_Intro_lr],
      ASM_REWRITE_TAC [] ]);

val LextensionSimpl' = store_thm ("LextensionSimpl'", (* dual theorem of above *)
  ``!E T1 T2 T3 C. extends L_Sequent E /\
		   gentzenSequent E (Comma (Comma T1 T2) T3) C
	       ==> gentzenSequent E (Comma T1 (Comma T2 T3)) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC SequentExtension
 >> EXISTS_TAC ``(Comma (Comma T1 T2) T3)``       (* Gamma *)
 >> EXISTS_TAC ``(Comma (Comma T1 T2) T3)``       (* Delta *)
 >> EXISTS_TAC ``(Comma T1 (Comma T2 T3))``       (* Delta' *)
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ REWRITE_TAC [replaceRoot],
      PROVE_TAC [extends_def, RSUBSET, L_Intro_rl],
      ASM_REWRITE_TAC [] ]);

val LextensionSimplDot = store_thm ("LextensionSimplDot",
  ``!E A B C D. extends L_Sequent E /\
		gentzenSequent E (OneForm (Dot A (Dot B C))) D
	    ==> gentzenSequent E (OneForm (Dot (Dot A B) C)) D``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDotSimpl
 >> MATCH_MP_TAC LeftDot
 >> EXISTS_TAC ``(Comma (Comma (OneForm A) (OneForm B)) (OneForm C))``
 >> Q.EXISTS_TAC `A`
 >> Q.EXISTS_TAC `B`
 >> STRIP_TAC
 >| [ RW_TAC bool_ss [replaceLeft, replaceRoot],
      MATCH_MP_TAC LextensionSimpl
   >> STRIP_TAC
   >| [ ASM_REWRITE_TAC [],
	MATCH_MP_TAC CutRuleSimpl
     >> EXISTS_TAC ``(deltaTranslation (Comma (OneForm A) (Comma (OneForm B) (OneForm C))))``
     >> RW_TAC bool_ss [SeqAxiomGen, deltaTranslation_def] ] ]);

val LextensionSimplDot' = store_thm ("LextensionSimplDot'", (* dual theorem of above *)
  ``!E A B C D. extends L_Sequent E /\
		gentzenSequent E (OneForm (Dot (Dot A B) C)) D
	    ==> gentzenSequent E (OneForm (Dot A (Dot B C))) D``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDotSimpl
 >> MATCH_MP_TAC LeftDot
 >> EXISTS_TAC ``(Comma (OneForm A) (Comma (OneForm B) (OneForm C)))``
 >> Q.EXISTS_TAC `B`
 >> Q.EXISTS_TAC `C`
 >> STRIP_TAC
 >| [ RW_TAC bool_ss [replaceRight, replaceRoot],
      MATCH_MP_TAC LextensionSimpl'
   >> STRIP_TAC
   >| [ ASM_REWRITE_TAC [],
	MATCH_MP_TAC CutRuleSimpl
     >> EXISTS_TAC ``(deltaTranslation (Comma (Comma (OneForm A) (OneForm B)) (OneForm C)))``
     >> RW_TAC bool_ss [SeqAxiomGen, deltaTranslation_def] ] ]);

val NLPextensionSimpl = store_thm ("NLPextensionSimpl",
  ``!E T1 T2 C. extends NLP_Sequent E /\
		gentzenSequent E (Comma T1 T2) C
	    ==> gentzenSequent E (Comma T2 T1) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC SequentExtension
 >> EXISTS_TAC ``(Comma T1 T2)``
 >> EXISTS_TAC ``(Comma T1 T2)``
 >> EXISTS_TAC ``(Comma T2 T1)``
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ REWRITE_TAC [replaceRoot],
      PROVE_TAC [extends_def, RSUBSET, NLP_Intro],
      ASM_REWRITE_TAC [] ]);

val NLPextensionSimplDot = store_thm ("NLPextensionSimplDot",
  ``!E A B C. extends NLP_Sequent E /\
	      gentzenSequent E (OneForm (Dot A B)) C
	  ==> gentzenSequent E (OneForm (Dot B A)) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDotSimpl
 >> MATCH_MP_TAC NLPextensionSimpl
 >> STRIP_TAC
 >| [ ASM_REWRITE_TAC [],
      MATCH_MP_TAC CutRuleSimpl
   >> EXISTS_TAC ``(deltaTranslation (Comma (OneForm A) (OneForm B)))``
   >> RW_TAC bool_ss [SeqAxiomGen, deltaTranslation_def] ]);

(* original name: gentzenExtends, see also mono_X *)
val mono_E = store_thm ("mono_E",
  ``!E' E Gamma A. gentzenSequent E Gamma A ==> extends E E' ==> gentzenSequent E' Gamma A``,
    GEN_TAC
 >> HO_MATCH_MP_TAC gentzenSequent_ind
 >> REPEAT STRIP_TAC (* 9 goals here, from easy to hard *)
 >| [ REWRITE_TAC [SeqAxiom],
      RW_TAC bool_ss [RightSlash],
      RW_TAC bool_ss [RightBackslash],
      RW_TAC bool_ss [RightDot],
      PROVE_TAC [LeftSlash],
      PROVE_TAC [LeftBackslash],
      PROVE_TAC [LeftDot],
      PROVE_TAC [CutRule],
      `E' Delta Delta'` by PROVE_TAC [extends_def, RSUBSET]
   >> `gentzenSequent E' Gamma A` by RW_TAC bool_ss []
   >> PROVE_TAC [SequentExtension] ]);

(* Some theorems and derived properties
   These definitions can be applied for all gentzen extensions,
   we can see how CutRuleSimpl gets used in most of time. *)

val application = store_thm ("application",
  ``!E A B. gentzenSequent E (OneForm (Dot (Slash A B) B)) A``,
    PROVE_TAC [LeftDotSimpl, LeftSlashSimpl, SeqAxiom]);

val application' = store_thm ("application'",
  ``!E A B. gentzenSequent E (OneForm (Dot B (Backslash B A))) A``,
    PROVE_TAC [LeftDotSimpl, LeftBackslashSimpl, SeqAxiom]);

val RightSlashDot = store_thm ("RightSlashDot",
  ``!E A B C. gentzenSequent E (OneForm (Dot A C)) B
	  ==> gentzenSequent E (OneForm A) (Slash B C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(deltaTranslation (Comma (OneForm A) (OneForm C)))``
 >> RW_TAC bool_ss [SeqAxiomGen, deltaTranslation_def]);

val RightBackslashDot = store_thm ("RightBackslashDot",
  ``!E A B C. gentzenSequent E (OneForm (Dot B A)) C
	  ==> gentzenSequent E (OneForm A) (Backslash B C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(deltaTranslation (Comma (OneForm B) (OneForm A)))``
 >> RW_TAC bool_ss [SeqAxiomGen, deltaTranslation_def]);

val coApplication = store_thm ("coApplication",
  ``!E A B. gentzenSequent E (OneForm A) (Slash (Dot A B) B)``,
    PROVE_TAC [RightSlash, RightDot, SeqAxiom]);

val coApplication' = store_thm ("coApplication'",
  ``!E A B. gentzenSequent E (OneForm A) (Backslash B (Dot B A))``,
    PROVE_TAC [RightBackslash, RightDot, SeqAxiom]);

val monotonicity = store_thm ("monotonicity",
  ``!E A B C D. gentzenSequent E (OneForm A) B /\
		gentzenSequent E (OneForm C) D
	    ==> gentzenSequent E (OneForm (Dot A C)) (Dot B D)``,
    PROVE_TAC [LeftDotSimpl, RightDot]);

val isotonicity = store_thm ("isotonicity",
  ``!E A B C. gentzenSequent E (OneForm A) B
	  ==> gentzenSequent E (OneForm (Slash A C)) (Slash B C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC CutRuleSimpl
 >> Q.EXISTS_TAC `A`
 >> PROVE_TAC [LeftSlashSimpl, SeqAxiom]);

val isotonicity' = store_thm ("isotonicity'",
  ``!E A B C. gentzenSequent E (OneForm A) B
	  ==> gentzenSequent E (OneForm (Backslash C A)) (Backslash C B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC CutRuleSimpl
 >> Q.EXISTS_TAC `A`
 >> PROVE_TAC [LeftBackslashSimpl, SeqAxiom]);

val antitonicity = store_thm ("antitonicity",
  ``!E A B C. gentzenSequent E (OneForm A) B
	  ==> gentzenSequent E (OneForm (Slash C B)) (Slash C A)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash C B) B)``
 >> STRIP_TAC
 >| [ PROVE_TAC [RightDot, SeqAxiom],
      REWRITE_TAC [application] ]);

val antitonicity' = store_thm ("antitonicity'",
  ``!E A B C. gentzenSequent E (OneForm A) B
	  ==> gentzenSequent E (OneForm (Backslash B C)) (Backslash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Backslash B C))``
 >> STRIP_TAC
 >| [ PROVE_TAC [RightDot, SeqAxiom],
      REWRITE_TAC [application'] ]);

val lifting = store_thm ("lifting",
  ``!E A B C. gentzenSequent E (OneForm A) (Slash B (Backslash A B))``,
    REPEAT GEN_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot A (Backslash A B))``
 >> STRIP_TAC
 >| [ PROVE_TAC [RightDot, SeqAxiom],
      REWRITE_TAC [application'] ]);

val lifting' = store_thm ("lifting'",
  ``!E A B C. gentzenSequent E (OneForm A) (Backslash (Slash B A) B)``,
    REPEAT GEN_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash B A) A)``
 >> STRIP_TAC
 >| [ PROVE_TAC [RightDot, SeqAxiom],
      REWRITE_TAC [application] ]);

(* These definitions can be applied iff associativity is supported by our logical system *)

val mainGeach = store_thm ("mainGeach",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Slash A B))
						       (Slash (Slash A C) (Slash B C))``,
    REPEAT STRIP_TAC
 >> NTAC 2 (MATCH_MP_TAC RightSlash)
 >> MATCH_MP_TAC LextensionSimpl
 >> CONJ_TAC THEN1 (POP_ASSUM ACCEPT_TAC)
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash A B) B)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot
   >> CONJ_TAC
   >| [ REWRITE_TAC [SeqAxiom],
        MATCH_MP_TAC LeftSlashSimpl >> STRIP_TAC >> REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val mainGeach' = store_thm ("mainGeach'",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Backslash B A))
						       (Backslash (Backslash C B) (Backslash C A))``,
    REPEAT STRIP_TAC
 >> NTAC 2 (MATCH_MP_TAC RightBackslash)
 >> MATCH_MP_TAC LextensionSimpl'
 >> CONJ_TAC THEN1 (POP_ASSUM ACCEPT_TAC)
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Backslash B A))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot
   >> CONJ_TAC
   >| [ MATCH_MP_TAC LeftBackslashSimpl >> STRIP_TAC >> REWRITE_TAC [SeqAxiom],
	REWRITE_TAC [SeqAxiom] ] ,
      REWRITE_TAC [application'] ]);

val secondaryGeach = store_thm ("secondaryGeach",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Slash B C))
						       (Backslash (Slash A B) (Slash A C))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC LextensionSimpl
 >> CONJ_TAC THEN1 (POP_ASSUM ACCEPT_TAC)
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash A B) B)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot
   >> CONJ_TAC
   >| [ REWRITE_TAC [SeqAxiom],
	MATCH_MP_TAC LeftSlashSimpl >> STRIP_TAC >> REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val secondaryGeach' = store_thm ("secondaryGeach'",
``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Backslash C B))
						     (Slash (Backslash C A) (Backslash B A))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC LextensionSimpl'
 >> CONJ_TAC THEN1 (POP_ASSUM ACCEPT_TAC)
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Backslash B A))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot >> STRIP_TAC >|
      [ MATCH_MP_TAC LeftBackslashSimpl >> STRIP_TAC >> REWRITE_TAC [SeqAxiom],
	REWRITE_TAC [SeqAxiom] ] ,
      REWRITE_TAC [application'] ]);

val composition = store_thm ("composition",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Dot (Slash A B) (Slash B C)))
						       (Slash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash (Slash A C) (Slash B C)) (Slash B C))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity
   >> CONJ_TAC >| [ RW_TAC bool_ss [mainGeach], REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val composition' = store_thm ("composition'",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Dot (Backslash C B) (Backslash B A)))
						       (Backslash C A)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash (Backslash C A) (Backslash B A)) (Backslash B A))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity
   >> CONJ_TAC >| [ RW_TAC bool_ss [secondaryGeach'], REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val restructuring = store_thm ("restructuring",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Slash (Backslash A B) C))
						       (Backslash A (Slash B C))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC LextensionSimpl
 >> CONJ_TAC THEN1 (POP_ASSUM ACCEPT_TAC)
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot A (Backslash A B))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot
   >> CONJ_TAC THEN1 REWRITE_TAC [SeqAxiom]
   >> MATCH_MP_TAC LeftSlashSimpl
   >> REWRITE_TAC [SeqAxiom],
      REWRITE_TAC [application'] ]);

val restructuring' = store_thm ("restructuring'",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Backslash A (Slash B C)))
						       (Slash (Backslash A B) C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC LextensionSimpl'
 >> CONJ_TAC THEN1 POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash B C) C)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot
   >> CONJ_TAC >| [ MATCH_MP_TAC LeftBackslashSimpl >> REWRITE_TAC [SeqAxiom],
		    REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val currying = store_thm ("currying",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Slash A (Dot B C)))
						       (Slash (Slash A C) B)``,
    REPEAT STRIP_TAC
 >> NTAC 2 (MATCH_MP_TAC RightSlashDot)
 >> MATCH_MP_TAC LextensionSimplDot
 >> CONJ_TAC THEN1 POP_ASSUM ACCEPT_TAC
 >> REWRITE_TAC [application]);

val currying' = store_thm ("currying'",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Slash (Slash A C) B))
						       (Slash A (Dot B C))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlashDot
 >> MATCH_MP_TAC LextensionSimplDot'
 >> CONJ_TAC THEN1 POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash A C) C)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity
   >> CONJ_TAC
   >> REWRITE_TAC [application, SeqAxiom],
      REWRITE_TAC [application] ]);

val decurrying = store_thm ("decurrying",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Backslash (Dot A B) C))
						       (Backslash B (Backslash A C))``,
    REPEAT STRIP_TAC
 >> NTAC 2 (MATCH_MP_TAC RightBackslashDot)
 >> MATCH_MP_TAC LextensionSimplDot'
 >> CONJ_TAC THEN1 POP_ASSUM ACCEPT_TAC
 >> REWRITE_TAC [application']);

val decurrying' = store_thm ("decurrying'",
  ``!E A B C. extends L_Sequent E ==> gentzenSequent E (OneForm (Backslash B (Backslash A C)))
						       (Backslash (Dot A B) C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC LextensionSimplDot
 >> CONJ_TAC THEN1 POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot A (Backslash A C))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity
   >> REWRITE_TAC [application', SeqAxiom],
      REWRITE_TAC [application'] ]);

(* Theorem for systems that support commutativity: if its extension extends NLP_Sequent *)

val permutation = store_thm ("permutation",
  ``!E A B C. extends NLP_Sequent E
	  ==> gentzenSequent E (OneForm A) (Backslash B C)
	  ==> gentzenSequent E (OneForm B) (Backslash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> CONJ_TAC THEN1 ASM_REWRITE_TAC []
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Backslash B C))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity >> ASM_REWRITE_TAC [SeqAxiom],
      REWRITE_TAC [application'] ]);

val exchange = store_thm ("exchange",
  ``!E A B. extends NLP_Sequent E ==> gentzenSequent E (OneForm (Slash A B)) (Backslash B A)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> RW_TAC bool_ss [application]);

val exchange' = store_thm ("exchange'",
  ``!E A B. extends NLP_Sequent E ==> gentzenSequent E (OneForm (Backslash B A)) (Slash A B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> RW_TAC bool_ss [application']);

val preposing = store_thm ("preposing",
  ``!E A B. extends NLP_Sequent E ==> gentzenSequent E (OneForm A) (Slash B (Slash B A))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> RW_TAC bool_ss [application]);

val postposing = store_thm ("postposing",
  ``!E A B. extends NLP_Sequent E ==> gentzenSequent E (OneForm A) (Backslash (Backslash A B) B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> RW_TAC bool_ss [application']);

(* For systems that support both commutativity and associativity *)

val mixedComposition = store_thm ("mixedComposition",
  ``!E A B C. extends LP_Sequent E
	  ==> gentzenSequent E (OneForm (Dot (Slash A B) (Backslash C B))) (Backslash C A)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> CONJ_TAC THEN1 (RW_TAC bool_ss [LPextendsNLP])
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC LextensionSimplDot'
 >> CONJ_TAC THEN1 (RW_TAC bool_ss [LPextendsL])
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Slash A B))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity
   >> RW_TAC bool_ss [application', SeqAxiom],
      MATCH_MP_TAC NLPextensionSimplDot
   >> RW_TAC bool_ss [application, LPextendsNLP] ]);

val mixedComposition' = store_thm ("mixedComposition'",
  ``!E A B C. extends LP_Sequent E
	 ==>  gentzenSequent E (OneForm (Dot (Slash B C) (Backslash B A))) (Slash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> CONJ_TAC THEN1 (RW_TAC bool_ss [LPextendsNLP])
 >> MATCH_MP_TAC RightSlashDot
 >> MATCH_MP_TAC LextensionSimplDot
 >> CONJ_TAC THEN1 (RW_TAC bool_ss [LPextendsL])
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Backslash B A) B)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity
   >> RW_TAC bool_ss [application, SeqAxiom],
      MATCH_MP_TAC NLPextensionSimplDot
   >> RW_TAC bool_ss [application', LPextendsNLP] ]);

val _ = export_theory ();

(* last updated: January 18, 2017 *)
