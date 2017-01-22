(*
 * A formalization of the process algebra CCS in high order logic
 *
 * (ported from the code of Monica Nesi written in 1992)
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

open HolKernel Parse boolLib bossLib;

open stringTheory pred_setTheory;

val _ = new_theory "CCS";

(*** syntax.ml ***)

(* Define the set of labels as the union of names (`in`) (strings) and
   co-names (`out`) (complement of names) *)
val _ = Datatype `Label = name string | coname string`;

(* Define structural induction on labels   
   |- ∀P. (∀s. P (name s)) ∧ (∀s. P (coname s)) ⇒ ∀L. P L
 *)
val Label_induct = TypeBase.induction_of ``:Label``;

(* The structural cases theorem for the type Label
   |- ∀LL. (∃s. LL = name s) ∨ ∃s. LL = coname s
 *)
val Label_cases = TypeBase.nchotomy_of ``:Label``;

(* The distinction and injectivity theorems for the type Label
   |- ∀a' a. name a ≠ coname a'
   |- (∀a a'. (name a = name a') ⇔ (a = a')) ∧
       ∀a a'. (coname a = coname a') ⇔ (a = a')
 *)
val Label_distinct = TypeBase.distinct_of ``:Label``;
val Label_distinct' = GSYM Label_distinct;
val Label_one_one = TypeBase.one_one_of ``:Label``;

(* Define the set of actions as the union of the internal action tau and the labels. *)
val _ = Datatype `Action = tau | label Label`;

(* Define structural induction on actions
   |- ∀P. P tau ∧ (∀L. P (label L)) ⇒ ∀A. P A 
 *)
val Action_induct = TypeBase.induction_of ``:Action``;

(* The structural cases theorem for the type Action
   |- ∀AA. (AA = tau) ∨ ∃L. AA = label L
 *)
val Action_cases = TypeBase.nchotomy_of ``:Action``;

(* The distinction and injectivity theorems for the type Action
   |- ∀a. tau ≠ label a
   |- ∀a a'. (label a = label a') ⇔ (a = a')
 *)
val Action_distinct = TypeBase.distinct_of ``:Action``;
val Action_distinct_label = GSYM Action_distinct;
val Action_one_one = TypeBase.one_one_of ``:Action``;

val Action_not_tau_is_Label = store_thm ("Action_not_tau_is_Label",
  ``!A. ~(A = tau) ==> (?L. A = label L)``, PROVE_TAC [Action_cases]);

(* Extract the label from a visible action, LABEL: Action -> Label. *)
val    LABEL_def = Define `    LABEL (label l) = l`;
val IS_LABEL_def = Define `(IS_LABEL (label l) = T) /\
			   (IS_LABEL tau       = F)`;

(* Define the complement of a label, COMPL: Label -> Label. *)
val COMPL_def = Define `(COMPL (name s) = (coname s)) /\
			(COMPL (coname s) = (name s))`;

val COMPL_COMPL = store_thm ("COMPL_COMPL", ``!l. COMPL (COMPL l) = l``,
    Induct >> REWRITE_TAC [COMPL_def]);

(* Extend the complement to actions, COMPL_ACT: Action -> Action. *)
val COMPL_ACT_def = Define `COMPL_ACT (label l) = label (COMPL l)`;

(* Auxiliary theorem about complementary labels. *)
val COMPL_THM = store_thm ("COMPL_THM",
  ``!l s. (~(l = name s) ==> ~(COMPL l = coname s)) /\
	  (~(l = coname s) ==> ~(COMPL l = name s))``,
    Induct >> PROVE_TAC [Label_one_one, Label_distinct, COMPL_def]);

val Is_Relabelling_def = Define `
    Is_Relabelling (f: Label -> Label) = (!s. f (coname s) = COMPL (f (name s)))`;

val EXISTS_Relabelling = store_thm ("EXISTS_Relabelling", ``?f. Is_Relabelling f``,
    Q.EXISTS_TAC `\a. a`
 >> PURE_ONCE_REWRITE_TAC [Is_Relabelling_def]
 >> BETA_TAC
 >> REWRITE_TAC [COMPL_def]);

(* Relabelling_TY_DEF =
   |- ∃rep. TYPE_DEFINITION Is_Relabelling rep
 *)
val Relabelling_TY_DEF = new_type_definition ("Relabelling", EXISTS_Relabelling);

(* Relabelling_ISO_DEF =
   |- (∀a. ABS_Relabelling (REP_Relabelling a) = a) ∧
       ∀r. Is_Relabelling r ⇔ (REP_Relabelling (ABS_Relabelling r) = r)
 *)
val Relabelling_ISO_DEF = define_new_type_bijections
			      { ABS  = "ABS_Relabelling",
				REP  = "REP_Relabelling",
				name = "Relabelling_ISO_DEF",
				tyax =  Relabelling_TY_DEF };

(* ABS_Relabelling_one_one =
   |- ∀r r'.
      Is_Relabelling r ⇒ Is_Relabelling r' ⇒
      ((ABS_Relabelling r = ABS_Relabelling r') ⇔ (r = r'))

   ABS_Relabelling_onto =
   |- ∀a. ∃r. (a = ABS_Relabelling r) ∧ Is_Relabelling r

   REP_Relabelling_one_one =
   |- ∀a a'. (REP_Relabelling a = REP_Relabelling a') ⇔ (a = a')

   REP_Relabelling_onto =
   |- ∀r. Is_Relabelling r ⇔ ∃a. r = REP_Relabelling a
 *)
val [ABS_Relabelling_one_one,
     ABS_Relabelling_onto,
     REP_Relabelling_one_one,
     REP_Relabelling_onto] =
    map (fn f => f Relabelling_ISO_DEF)
	[prove_abs_fn_one_one,
	 prove_abs_fn_onto,
	 prove_rep_fn_one_one,
	 prove_rep_fn_onto];

val REP_Relabelling_THM = store_thm ("REP_Relabelling_THM",
  ``!rf: Relabelling. Is_Relabelling (REP_Relabelling rf)``,
    GEN_TAC
 >> REWRITE_TAC [REP_Relabelling_onto]
 >> Q.EXISTS_TAC `rf`
 >> REWRITE_TAC []);

(* Relabelling labels is extended to actions by renaming tau as tau. *)
val relabel_def = Define `(relabel (rf: Relabelling) tau = tau) /\
			  (relabel rf (label l) = label (REP_Relabelling rf l))`;

(* If the renaming of an action is a label, that action is a label. *)
val Relab_label = prove (``!rf u l. (relabel rf u = label l) ==> ?l'. u = label l'``,
    Induct_on `u`
 >| [ REWRITE_TAC [relabel_def, Action_distinct],
      REWRITE_TAC [relabel_def]
   >> REPEAT STRIP_TAC
   >> Q.EXISTS_TAC `L`
   >> REWRITE_TAC [] ]);

(* If the renaming of an action is tau, that action is tau. *)
val Relab_tau = prove (``!rf u. (relabel rf u = tau) ==> (u = tau)``,
    Induct_on `u`
 >> REWRITE_TAC [relabel_def, Action_distinct_label]);

(* Apply_Relab: ((Label # Label) list) -> Label -> Label
   (SND of any pair is a name, FST can be either name or coname)
 *)
val Apply_Relab_def = Define `
   (Apply_Relab ([]: (Label # Label) list) l = l) /\
   (Apply_Relab (CONS (newold: Label # Label) ls) l =
	  if (SND newold = l)         then (FST newold)
     else if (COMPL (SND newold) = l) then (COMPL (FST newold))
     else (Apply_Relab ls l))`;

val Apply_Relab_COMPL_THM = store_thm ("Apply_Relab_COMPL_THM",
  ``!labl s. Apply_Relab labl (coname s) = COMPL (Apply_Relab labl (name s))``,
    Induct THEN1 REWRITE_TAC [Apply_Relab_def, COMPL_def]
 >> REPEAT GEN_TAC
 >> REWRITE_TAC [Apply_Relab_def]
 >> COND_CASES_TAC THEN1 ASM_REWRITE_TAC [Label_distinct', COMPL_def, COMPL_COMPL]
 >> ASM_CASES_TAC ``SND (h:Label # Label) = name s`` THEN1 ASM_REWRITE_TAC [COMPL_def]
 >> IMP_RES_TAC COMPL_THM
 >> ASM_REWRITE_TAC []);

val IS_RELABELLING = prove (``!labl. Is_Relabelling (Apply_Relab labl)``,
    Induct THEN1 REWRITE_TAC [Is_Relabelling_def, Apply_Relab_def, COMPL_def]
 >> GEN_TAC
 >> REWRITE_TAC [Is_Relabelling_def, Apply_Relab_def]
 >> GEN_TAC
 >> COND_CASES_TAC THEN1 ASM_REWRITE_TAC [Label_distinct', COMPL_def, COMPL_COMPL]
 >> ASM_CASES_TAC ``SND (h:Label # Label) = name s`` THEN1 ASM_REWRITE_TAC [COMPL_def]
 >> IMP_RES_TAC COMPL_THM
 >> ASM_REWRITE_TAC [Apply_Relab_COMPL_THM]);

(* Defining a relabelling function through substitution-like notation.
   RELAB: (Label # Label)list -> Relabelling
 *)
val RELAB_def = Define `RELAB labl = ABS_Relabelling (Apply_Relab labl)`;

(* Define the type of (pure) CCS agent expressions. *)
val _ = Datatype `CCS = nil
		      | var string
		      | prefix Action CCS
		      | sum CCS CCS
		      | par CCS CCS
		      | restr CCS (Label set)
		      | relab CCS Relabelling
		      | rec string CCS`;

(* Define structural induction on CCS agent expressions. *)
val CCS_induct = TypeBase.induction_of ``:CCS``;

(* The structural cases theorem for the type CCS. *)
val CCS_cases = TypeBase.nchotomy_of ``:CCS``;

(* Prove that the constructors of the type CCS are distinct. *)
val CCS_distinct1 = TypeBase.distinct_of ``:CCS``;

val CCS_distinct_LIST = let
    val thm = CONJUNCTS CCS_distinct1
    in append thm (map GSYM thm) end;

val CCS_distinct = LIST_CONJ CCS_distinct_LIST;

(* Prove that the constructors of the type CCS are one-to-one. *)
val CCS_one_one = TypeBase.one_one_of ``:CCS``;

val CCS_Subst_def = Define `
   (CCS_Subst nil E' X = nil) /\
   (CCS_Subst (prefix u E) E' X = prefix u (CCS_Subst E E' X)) /\
   (CCS_Subst (sum E1 E2) E' X = sum (CCS_Subst E1 E' X)
				     (CCS_Subst E2 E' X)) /\
   (CCS_Subst (restr E L) E' X = restr (CCS_Subst E E' X) L) /\
   (CCS_Subst (relab E f) E' X = relab (CCS_Subst E E' X) f) /\
   (CCS_Subst (par E1 E2) E' X = par (CCS_Subst E1 E' X)
				     (CCS_Subst E2 E' X)) /\
   (CCS_Subst (var Y) E' X = if (Y = X) then E' else (var Y)) /\ 
   (CCS_Subst (rec Y E) E' X =
	if (Y = X) then (rec Y E)
	else rec Y (CCS_Subst E E' X))`;

(* Note that in the rec clause, if Y = X then all occurrences of Y in E are X 
   and bound, so there exist no free variables X in E to be replaced with E'.
   Hence, the term rec Y E is returned. *)

(* Define an arbitrary CCS agent. *)
val ARB' = Define `ARB' = @x:CCS. T`;

val _ = export_theory ();

(* last updated: January 22, 2017 *)
