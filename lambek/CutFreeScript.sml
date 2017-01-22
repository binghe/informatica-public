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

open relationTheory arithmeticTheory LambekTheory;

val _ = new_theory "CutFree";

(*** Module: CutSequent ***)

(* This calls temp_set_fixity "=" (Infix(NONASSOC, 450).
   By default, "=" works as "<==>" (logical equivalence) for boolean values, its priority is 100,
   but it's rarely used in this way.  More ofter, we use "=" just for numbers. "==>" has priority 200.
   To express things like ``m=n ==> n=m`` without parenthesis, we need to give "=" a higher priority,
   e.g. 450. This is called "tight" equality in HOL. And we set it only temporary when building the
   current theory. *)
val _ = temp_tight_equality();

(* TODO: remove them, use MAX_EQ_0 directly *)
val maxNatL = store_thm ("maxNatL", ``(MAX n m = 0) ==> (n = 0)``, RW_TAC std_ss [MAX_EQ_0]);
val maxNatR = store_thm ("maxNatR", ``(MAX n m = 0) ==> (m = 0)``, RW_TAC std_ss [MAX_EQ_0]);

val degreeFormula_def = Define `
   (degreeFormula (Atom C) = 1) /\
   (degreeFormula (Slash F1 F2) = SUC (MAX (degreeFormula F1) (degreeFormula F2))) /\
   (degreeFormula (Backslash F1 F2) = SUC (MAX (degreeFormula F1) (degreeFormula F2))) /\
   (degreeFormula (Dot F1 F2) = SUC (MAX (degreeFormula F1) (degreeFormula F2))) `;

val degreeForm_0 = store_thm ("degreeForm_0", ``!F0. 1 <= (degreeFormula F0)``,
    Induct >> rw [degreeFormula_def]);

(* Deep Embeddings for Lambek's Sequent Calculus *)

val _ = Datatype `Sequent = Sequent ('a gentzen_extension) ('a Term) ('a Form)`;

val _ = Datatype `Rule = SeqAxiom   | CutRule        | SequentExtension
		       | RightSlash | RightBackslash | RightDot
		       | LeftSlash  | LeftBackslash  | LeftDot `;

val _ = Datatype `Dertree = Der ('a Sequent) Rule (Dertree list)
			  | Unf ('a Sequent)`;

val _ = set_mapped_fixity { fixity = Infix(NONASSOC, 450), tok = "|-", term_name = "deriv" };

(* deriv (proof): Dertree -> Dertree -> bool *)
val (deriv_rules, deriv_ind, deriv_cases) = Hol_reln `
    (!E A.
     deriv (Unf (Sequent E (OneForm A) A))
	   (Der (Sequent E (OneForm A) A) SeqAxiom [])) /\
    (!E Gamma A B.
     deriv (Unf (Sequent E Gamma (Slash A B)))
	   (Der (Sequent E Gamma (Slash A B)) RightSlash
	        [Unf (Sequent E (Comma Gamma (OneForm B)) A)])) /\
    (!E Gamma A B.
     deriv (Unf (Sequent E Gamma (Backslash B A)))
	   (Der (Sequent E Gamma (Backslash B A)) RightBackslash
	        [Unf (Sequent E (Comma (OneForm B) Gamma) A)])) /\
    (!E Gamma Delta A B.
     deriv (Unf (Sequent E (Comma Gamma Delta) (Dot A B)))
	   (Der (Sequent E (Comma Gamma Delta) (Dot A B)) RightDot
		[Unf (Sequent E Gamma A); Unf (Sequent E Delta B)])) /\
    (!E Gamma Gamma' Delta A B C.
     replace Gamma Gamma' (OneForm A) (Comma (OneForm (Slash A B)) Delta) ==>
     deriv (Unf (Sequent E Gamma' C))
	   (Der (Sequent E Gamma' C) LeftSlash
		[Unf (Sequent E Gamma A); Unf (Sequent E Delta B)])) /\
    (!E Gamma Gamma' Delta A B C.
     replace Gamma Gamma' (OneForm A) (Comma Delta (OneForm (Backslash B A))) ==>
     deriv (Unf (Sequent E Gamma' C))
	   (Der (Sequent E Gamma' C) LeftBackslash
		[Unf (Sequent E Delta B); Unf (Sequent E Gamma C)])) /\
    (!E Gamma Gamma' A B C.
     replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) ==>
     deriv (Unf (Sequent E Gamma' C))
	   (Der (Sequent E Gamma' C) LeftDot
		[Unf (Sequent E Gamma C)])) /\
    (!E Delta Gamma Gamma' A C.
     replace Gamma Gamma' (OneForm A) Delta ==>
     deriv (Unf (Sequent E Gamma' C))
	   (Der (Sequent E Gamma' C) CutRule
		[Unf (Sequent E Delta A); Unf (Sequent E Gamma C)])) /\
    (!E Gamma Gamma' Delta Delta' C.
     replace Gamma Gamma' Delta Delta' /\ E Delta Delta' ==>
     deriv (Unf (Sequent E Gamma' C))
	   (Der (Sequent E Gamma' C) SequentExtension
		[Unf (Sequent E Gamma C)]))`;

val degreeProof_def = Define `
   (degreeProof (Der _ SeqAxiom [])		= 0) /\
   (degreeProof (Der _ RightSlash [H])		= degreeProof H) /\
   (degreeProof (Der _ RightBackslash [H])	= degreeProof H) /\
   (degreeProof (Der _ RightDot [H1; H2])	= MAX (degreeProof H1) (degreeProof H2)) /\
   (degreeProof (Der _ LeftSlash [H1; H2])	= MAX (degreeProof H1) (degreeProof H2)) /\
   (degreeProof (Der _ LeftBackslash [H1; H2])	= MAX (degreeProof H1) (degreeProof H2)) /\
   (degreeProof (Der _ LeftDot [H])		= degreeProof H) /\
   (degreeProof (Der _ SequentExtension [H])	= degreeProof H) /\
   (* CutRule is special *)
   (degreeProof (Der _ CutRule [Der (Sequent E Delta A) rule derlist; H2]) =
	MAX (MAX (degreeFormula A) (degreeProof (Der (Sequent E Delta A) rule derlist)))
	    (degreeProof H2))`;

(* subFormula and their theorems *)

val (subFormula_rules, subFormula_ind, subFormula_cases) = Hol_reln `
    (!(A:'a Form). subFormula A A) /\						(* equalForm *)
    (!(A:'a Form) B C. subFormula A B ==> subFormula A (Slash B C)) /\		(* slashL *)
    (!(A:'a Form) B C. subFormula A B ==> subFormula A (Slash C B)) /\		(* slashR *)
    (!(A:'a Form) B C. subFormula A B ==> subFormula A (Backslash B C)) /\	(* backslashL *)
    (!(A:'a Form) B C. subFormula A B ==> subFormula A (Backslash C B)) /\	(* backslashR *)
    (!(A:'a Form) B C. subFormula A B ==> subFormula A (Dot B C)) /\		(* dotL *)
    (!(A:'a Form) B C. subFormula A B ==> subFormula A (Dot C B))`;		(* dotR *)

val [equalForm, slashL, slashR, backslashL, backslashR, dotL, dotR] = CONJ_LIST 7 subFormula_rules;

(* The simp set related to Form *)
val form_ss = DatatypeSimps.type_rewrites_ss [``:'a Form``];

(* or use: DB.fetch "Lambek" "Form_distinct" *)
val form_distinct = TypeBase.distinct_of ``:'a Form``;

val subAt = store_thm ("subAt", ``!A a. subFormula A (Atom a) ==> (A = Atom a)``,
    ONCE_REWRITE_TAC [subFormula_cases]
 >> SIMP_TAC bool_ss [form_distinct]); (* or: SIMP_TAC (bool_ss ++ form_ss) [] *)

val subSlash = store_thm ("subSlash",
  ``!A B C. subFormula A (Slash B C) ==> A = Slash B C \/ subFormula A B \/ subFormula A C``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [Q.SPECL [`A`, `(Slash B C)`] subFormula_cases]
 >> SIMP_TAC (bool_ss ++ form_ss) [EQ_SYM_EQ]);

val subBackslash = store_thm ("subBackslash",
  ``!A B C. subFormula A (Backslash B C) ==> A = Backslash B C \/ subFormula A B \/ subFormula A C``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [Q.SPECL [`A`, `(Backslash B C)`] subFormula_cases]
 >> SIMP_TAC (bool_ss ++ form_ss) [EQ_SYM_EQ]);

val subDot = store_thm ("subDot",
  ``!A B C. subFormula A (Dot B C) ==> A = Dot B C \/ subFormula A B \/ subFormula A C``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [Q.SPECL [`A`, `(Dot B C)`] subFormula_cases]
 >> SIMP_TAC (bool_ss ++ form_ss) [EQ_SYM_EQ]);

(* all previous theorems and rules were used in this proof ... *)
val subFormulaTrans = store_thm ("subFormulaTrans",
  ``!A B C. subFormula A B ==> subFormula B C ==> subFormula A C``,
    Induct_on `C`
 >| [ (* case 1 *)
      PROVE_TAC [subAt],
      (* case 2, can be proved by PROVE_TAC [subSlash, slashL, slashR] *)
      REPEAT STRIP_TAC
   >> POP_ASSUM (STRIP_ASSUME_TAC o MATCH_MP subSlash)
   >| [ PROVE_TAC [], PROVE_TAC [slashL], PROVE_TAC [slashR] ],
      (* case 3 *)
      PROVE_TAC [subBackslash, backslashL, backslashR],
      (* case 4 *)
      PROVE_TAC [subDot, dotL, dotR] ]);

val subFormulaTrans' = store_thm ("subFormulaTrans", ``transitive subFormula``,
    PROVE_TAC [subFormulaTrans, transitive_def]);

(* subFormTerm *)
val (subFormTerm_rules, subFormTerm_ind, subFormTerm_cases) = Hol_reln `
    (!A B. subFormula A B ==> subFormTerm A (OneForm B)) /\		(* eqFT *)
    (!A T1 T2. subFormTerm A T1 ==> subFormTerm A (Comma T1 T2)) /\	(* comL *)
    (!A T1 T2. subFormTerm A T1 ==> subFormTerm A (Comma T2 T1))`;	(* comR *)

val [eqFT, comL, comR] = CONJ_LIST 3 subFormTerm_rules;

val term_one_one = TypeBase.one_one_of ``:'a Term``;
val term_distinct = TypeBase.distinct_of ``:'a Term``;

val oneFormSub = store_thm ("oneFormSub", ``!A B. subFormTerm A (OneForm B) ==> subFormula A B``,
    ONCE_REWRITE_TAC [subFormTerm_cases]
 >> REPEAT STRIP_TAC
 >| [ PROVE_TAC [term_one_one],
      PROVE_TAC [term_distinct],
      PROVE_TAC [term_distinct] ]);

val comSub = store_thm ("comSub",
  ``!f T1 T2. subFormTerm f (Comma T1 T2) ==> subFormTerm f T1 \/ subFormTerm f T2``,
    REPEAT GEN_TAC
 >> GEN_REWRITE_TAC LAND_CONV empty_rewrites [Once subFormTerm_cases]
 >> REPEAT STRIP_TAC
 >| [ PROVE_TAC [term_distinct],
      PROVE_TAC [term_one_one],
      PROVE_TAC [term_one_one] ]);

val subReplace1 = store_thm ("subReplace1",
  ``!F T1 T2 T3 T4. replace T1 T2 T3 T4 ==> subFormTerm F T3 ==> subFormTerm F T1``,
    GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> REPEAT STRIP_TAC
 >| [ PROVE_TAC [comL], PROVE_TAC [comR] ]);

val subReplace2 = store_thm ("subReplace2",
  ``!F T1 T2 T3 T4. replace T1 T2 T3 T4 ==> subFormTerm F T4 ==> subFormTerm F T2``,
    GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> REPEAT STRIP_TAC
 >| [ PROVE_TAC [comL], PROVE_TAC [comR] ]);

val subReplace3 = store_thm ("subReplace3",
  ``!X T1 T2 T3 T4. replace T1 T2 T3 T4 ==> subFormTerm X T1 ==> subFormTerm X T2 \/ subFormTerm X T3``,
    GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> REPEAT STRIP_TAC
 >| [ (* case 1 *)
      ASM_REWRITE_TAC [],
      (* case 2 *)
      `subFormTerm X T1 \/ subFormTerm X Delta` by PROVE_TAC [comSub]
   >| [ `subFormTerm X T2 \/ subFormTerm X T3` by PROVE_TAC [] >> PROVE_TAC [comL],
	PROVE_TAC [comR] ],
      (* case 3 *)
      `subFormTerm X Delta \/ subFormTerm X T1` by PROVE_TAC [comSub]
   >| [ PROVE_TAC [comL], 
        `subFormTerm X T2 \/ subFormTerm X T3` by PROVE_TAC [] >> PROVE_TAC [comR] ] ]);

val CutFreeProof_def = Define `CutFreeProof p = (degreeProof p = 0)`;

(* rest lemmas:

1. notCutFree
2. subProofOne
3. subProof
4. CutFreeSubProofOne
5. CutFreeSubProof

extensionSub (definition)
6. subFormulaPropertyOne
7. subFormulaProperty
 *)

val _ = export_theory ();

(* last updated: January 18, 2017 *)
