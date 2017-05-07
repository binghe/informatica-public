(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open stringTheory pred_setTheory IndDefRules CCSLib;

val _ = new_theory "CCS";

(******************************************************************************)
(*                                                                            *)
(*              Syntax of pure CCS (string based formalization)               *)
(*                                                                            *)
(******************************************************************************)

(* Define the set of labels as the union of names (`in`) (strings) and
   co-names (`out`) (complement of names) *)
val _ = Datatype `Label = name string | coname string`;

(* Define structural induction on labels   
   |- ∀P. (∀s. P (name s)) ∧ (∀s. P (coname s)) ⇒ ∀L. P L
 *)
val Label_induction = TypeBase.induction_of ``:Label``;

(* The structural cases theorem for the type Label
   |- ∀LL. (∃s. LL = name s) ∨ ∃s. LL = coname s
 *)
val Label_nchotomy = TypeBase.nchotomy_of ``:Label``;

(* The distinction and injectivity theorems for the type Label
   |- ∀a' a. name a ≠ coname a'
   |- (∀a a'. (name a = name a') ⇔ (a = a')) ∧
       ∀a a'. (coname a = coname a') ⇔ (a = a')
 *)
val Label_distinct = TypeBase.distinct_of ``:Label``;
val Label_distinct' = save_thm ("Label_distinct'", GSYM Label_distinct);

val Label_not_eq = save_thm (
   "Label_not_eq",
    GEN_ALL (EQF_INTRO (SPEC_ALL Label_distinct)));

val Label_not_eq' = save_thm (
   "Label_not_eq'",
    GEN_ALL (PURE_REWRITE_RULE [SYM_CONV ``name s = coname s'``]
			       (SPEC_ALL Label_not_eq)));

val Label_11 = TypeBase.one_one_of ``:Label``;

(* Define the set of actions as the union of the internal action tau and the labels. *)
val _ = Datatype `Action = tau | label Label`;
val _ = Unicode.unicode_version { u = UnicodeChars.tau, tmnm = "tau"};

val  In_def = Define  `In act = label (name   act)`;
val Out_def = Define `Out act = label (coname act)`;
val _ = export_rewrites ["In_def", "Out_def"];

(* Define structural induction on actions
   |- ∀P. P tau ∧ (∀L. P (label L)) ⇒ ∀A. P A 
 *)
val Action_induction = TypeBase.induction_of ``:Action``;

(* The structural cases theorem for the type Action
   |- ∀AA. (AA = tau) ∨ ∃L. AA = label L
 *)
val Action_nchotomy = TypeBase.nchotomy_of ``:Action``;

(* The distinction and injectivity theorems for the type Action
   |- ∀a. tau ≠ label a
   |- ∀a a'. (label a = label a') ⇔ (a = a')
 *)
val Action_distinct = TypeBase.distinct_of ``:Action``;
val Action_distinct_label = save_thm ("Action_distinct_label", GSYM Action_distinct);
val Action_11 = TypeBase.one_one_of ``:Action``;

(* |- ∀A. A ≠ tau ⇒ ∃L. A = label L *)
val Action_not_tau_is_Label = save_thm ("Action_not_tau_is_Label",
    GEN ``A :Action`` (DISJ_IMP (SPEC ``A :Action`` Action_nchotomy)));

(* Extract the label from a visible action, LABEL: Action -> Label. *)
val    LABEL_def = Define `    LABEL (label l) = l`;
val IS_LABEL_def = Define `(IS_LABEL (label l) = T) /\
			   (IS_LABEL tau       = F)`;
val _ = export_rewrites ["LABEL_def", "IS_LABEL_def"];

(* Define the complement of a label, COMPL: Label -> Label. *)
val Lab_COMPL_def = Define `(Lab_COMPL (name s) = (coname s)) /\
			    (Lab_COMPL (coname s) = (name s))`;

val _ = overload_on ("COMPL", ``Lab_COMPL``);
val _ = export_rewrites ["Lab_COMPL_def"];

val coname_COMPL = store_thm ("coname_COMPL", 
  ``!s. coname s = COMPL (name s)``,
    REWRITE_TAC [Lab_COMPL_def]);

val Lab_COMPL_COMPL = store_thm (
   "Lab_COMPL_COMPL", ``!(l :Label). COMPL (COMPL l) = l``,
    Induct >> REWRITE_TAC [Lab_COMPL_def]);

(* Extend the complement to actions, COMPL_ACT: Action -> Action. *)
val COMPL_ACT_def = Define `
   (COMPL_ACT (label l) = label (COMPL l)) /\
   (COMPL_ACT tau = tau)`;
val _ = export_rewrites ["COMPL_ACT_def"];

(* Auxiliary theorem about complementary labels. *)
val COMPL_THM = store_thm ("COMPL_THM",
  ``!l s. (~(l = name s) ==> ~(COMPL l = coname s)) /\
	  (~(l = coname s) ==> ~(COMPL l = name s))``,
    Induct_on `l`
 >| [ (* case 1 *)
      REPEAT GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_11, Lab_COMPL_def],
        REWRITE_TAC [Label_distinct, Lab_COMPL_def, Label_distinct'] ] ,
      (* case 2 *)
      REPEAT GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_distinct, Lab_COMPL_def, Label_distinct'],
        REWRITE_TAC [Label_11, Lab_COMPL_def] ] ]);

val Is_Relabelling_def = Define `
    Is_Relabelling (f: Label -> Label) = (!s. f (coname s) = COMPL (f (name s)))`;

val EXISTS_Relabelling = store_thm ("EXISTS_Relabelling", ``?f. Is_Relabelling f``,
    Q.EXISTS_TAC `\a. a`
 >> PURE_ONCE_REWRITE_TAC [Is_Relabelling_def]
 >> BETA_TAC
 >> REWRITE_TAC [Lab_COMPL_def]);

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
 >- REWRITE_TAC [relabel_def, Action_distinct]
 >> REWRITE_TAC [relabel_def]
 >> REPEAT STRIP_TAC
 >> Q.EXISTS_TAC `L`
 >> REWRITE_TAC []);

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
    Induct
 >- REWRITE_TAC [Apply_Relab_def, Lab_COMPL_def]
 >> REPEAT GEN_TAC
 >> REWRITE_TAC [Apply_Relab_def]
 >> COND_CASES_TAC
 >- ASM_REWRITE_TAC [Label_distinct', Lab_COMPL_def, Lab_COMPL_COMPL]
 >> ASM_CASES_TAC ``SND (h:Label # Label) = name s``
 >- ASM_REWRITE_TAC [Lab_COMPL_def]
 >> IMP_RES_TAC COMPL_THM
 >> ASM_REWRITE_TAC []);

val IS_RELABELLING = prove (``!labl. Is_Relabelling (Apply_Relab labl)``,
    Induct
 >- REWRITE_TAC [Is_Relabelling_def, Apply_Relab_def, Lab_COMPL_def]
 >> GEN_TAC
 >> REWRITE_TAC [Is_Relabelling_def, Apply_Relab_def]
 >> GEN_TAC
 >> COND_CASES_TAC
 >- ASM_REWRITE_TAC [Label_distinct', Lab_COMPL_def, Lab_COMPL_COMPL]
 >> ASM_CASES_TAC ``SND (h :Label # Label) = name s``
 >- ASM_REWRITE_TAC [Lab_COMPL_def]
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
		      | restr (Label set) CCS
		      | relab CCS Relabelling
		      | rec string CCS`;

val _ = overload_on ("nu", ``restr``);
val _ = Unicode.unicode_version { u = UnicodeChars.nu, tmnm = "nu" };

val _ = overload_on ("+", ``sum``); (* priority: 500 *)
val _ = set_mapped_fixity { fixity = Infix(LEFT, 600), tok = "||", term_name = "par" };
val _ =
    add_rule { term_name = "prefix", fixity = Infix(RIGHT, 700),
	pp_elements = [ BreakSpace(0,0), TOK "..", BreakSpace(0,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundSamePrec, (PP.CONSISTENT, 0)) };

(* Define structural induction on CCS agent expressions. *)
val CCS_induct = TypeBase.induction_of ``:CCS``;

(* The structural cases theorem for the type CCS. *)
val CCS_cases = TypeBase.nchotomy_of ``:CCS``;

(* Prove that the constructors of the type CCS are distinct. *)
val CCS_distinct = TypeBase.distinct_of ``:CCS``;

local
    val thm = CONJUNCTS CCS_distinct;
    val CCS_distinct_LIST = thm @ (map GSYM thm);
in
    val CCS_distinct' = save_thm ("CCS_distinct'", LIST_CONJ CCS_distinct_LIST);
end

(* Prove that the constructors of the type CCS are one-to-one. *)
val CCS_11 = TypeBase.one_one_of ``:CCS``;

(* Given any agent expression, define the substitution of an agent expression
   E' for an agent variable X.

   This works under the hypothesis that the Barendregt convention holds. *)

val CCS_Subst_def = Define `
   (CCS_Subst nil E' X = nil) /\
   (CCS_Subst (prefix u E) E' X = prefix u (CCS_Subst E E' X)) /\
   (CCS_Subst (sum E1 E2) E' X = sum (CCS_Subst E1 E' X)
				     (CCS_Subst E2 E' X)) /\
   (CCS_Subst (restr L E) E' X = restr L (CCS_Subst E E' X)) /\
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

(* Define an arbitrary CCS agent. This finished porting of syntax.ml *)
val ARB'_def = Define `ARB' = @x:CCS. T`;

(* |- !t1 t2. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2) *)
val CCS_COND_CLAUSES = save_thm (
   "CCS_COND_CLAUSES", INST_TYPE [``:'a`` |-> ``:CCS``] COND_CLAUSES);

(******************************************************************************)
(*                                                                            *)
(*            Definition of the transition relation for pure CCS              *)
(*                                                                            *)
(******************************************************************************)

(* Inductive definition of the transition relation TRANS for CCS.
   TRANS: Action -> CCS -> CCS -> bool
 *)
val (TRANS_rules, TRANS_ind, TRANS_cases) = Hol_reln `
    (!E u. TRANS (prefix u E) u E) /\					(* PREFIX *)
    (!E u E1 E'. TRANS E u E1 ==> TRANS (sum E E') u E1) /\		(* SUM1 *)
    (!E u E1 E'. TRANS E u E1 ==> TRANS (sum E' E) u E1) /\		(* SUM2 *)
    (!E u E1 E'. TRANS E u E1 ==> TRANS (par E E') u (par E1 E')) /\	(* PAR1 *)
    (!E u E1 E'. TRANS E u E1 ==> TRANS (par E' E) u (par E' E1)) /\	(* PAR2 *)
    (!E l E1 E' E2.
		 TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2
	     ==> TRANS (par E E') tau (par E1 E2)) /\			(* PAR3 (COM) *)
    (!E u E' l L. 
		 TRANS E u E' /\ ((u = tau) \/
				  ((u = label l) /\ (~(l IN L)) /\ (~((COMPL l) IN L))))
	     ==> TRANS (restr L E) u (restr L E')) /\			(* RESTR *)
    (!E u E' rf. TRANS E u E'
	     ==> TRANS (relab E rf) (relabel rf u) (relab E' rf)) /\	(* RELAB *)
    (!E u X E1.  TRANS (CCS_Subst E (rec X E) X) u E1
	     ==> TRANS (rec X E) u E1)`;				(* REC (CONS) *)

val _ =
    add_rule { term_name = "TRANS", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK "--", HardSpace 0, TM, HardSpace 0, TOK "->",
			BreakSpace(1,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

(* The rules for the transition relation TRANS as individual theorems. *)
val [PREFIX, SUM1, SUM2, PAR1, PAR2, PAR3, RESTR, RELAB, REC] =
    map (fn (s, thm) => save_thm (s, thm))
        (combine (["PREFIX", "SUM1", "SUM2", "PAR1", "PAR2", "PAR3", "RESTR", "RELAB", "REC"],
                  CONJUNCTS TRANS_rules));

(* Tactics for proofs about the transition relation TRANS, re-defined in CCSSimps *)
val [PREFIX_TAC, SUM1_TAC, SUM2_TAC,
     PAR1_TAC, PAR2_TAC, PAR3_TAC,
     RESTR_TAC, RELAB_TAC, REC_TAC] = map RULE_TAC (CONJUNCTS TRANS_rules);

(* The process nil has no transitions.
   |- ∀u E. ¬TRANS nil u E
 *)
val NIL_NO_TRANS = save_thm ("NIL_NO_TRANS",
  ((GEN ``u :Action``) o
   (GEN ``E: CCS``) o
   (REWRITE_RULE [CCS_distinct]))
      (SPECL [``nil``, ``u :Action``, ``E :CCS``] TRANS_cases));

(* |- ∀u E. nil --u-> E ⇔ F *)
val NIL_NO_TRANS_EQF = save_thm (
   "NIL_NO_TRANS_EQF",
  ((GEN ``u :Action``) o
   (GEN ``E: CCS``) o EQF_INTRO o SPEC_ALL) NIL_NO_TRANS);

(* Prove that if a process can do an action, then the process is not nil.
   |- ∀E u E'. TRANS E u E' ⇒ E ≠ nil:
 *)
val TRANS_IMP_NO_NIL = store_thm ("TRANS_IMP_NO_NIL",
  ``!E u E'. TRANS E u E' ==> ~(E = nil)``,
    HO_MATCH_MP_TAC TRANS_ind
 >> REWRITE_TAC [CCS_distinct']);

(* Above theorem can be proved without using TRANS_ind *)
val TRANS_IMP_NO_NIL' = store_thm ("TRANS_IMP_NO_NIL'",
  ``!E u E'. TRANS E u E' ==> ~(E = nil)``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [TRANS_cases]
 >> REPEAT STRIP_TAC
 >> PROVE_TAC [CCS_distinct']);

(* An agent variable has no transitions.
   |- !X u E'. ~TRANS (var X) u E'
 *)
val VAR_NO_TRANS = save_thm ("VAR_NO_TRANS",
  ((GEN ``X :string``) o
   (GEN ``u :Action``) o
   (GEN ``E :CCS``) o
   (REWRITE_RULE [CCS_distinct', CCS_11]) o
   (SPECL [``var X``, ``u :Action``, ``E: CCS``]))
      TRANS_cases);

(* |- !u E u' E'. TRANS (prefix u E) u' E' = (u' = u) /\ (E' = E) *)
val TRANS_PREFIX_EQ = save_thm ("TRANS_PREFIX_EQ",
  ((GEN ``u :Action``) o
   (GEN ``E :CCS``) o
   (GEN ``u' :Action``) o
   (GEN ``E' :CCS``) o
   (ONCE_REWRITE_RHS_RULE [EQ_SYM_EQ]) o
   SPEC_ALL o
   (REWRITE_RULE [CCS_distinct', CCS_11]) o
   (SPECL [``prefix u E``, ``u' :Action``, ``E' :CCS``]))
      TRANS_cases);

(* |- ∀u' u E' E. TRANS (prefix u E) u' E' ⇒ (u' = u) ∧ (E' = E) *)
val TRANS_PREFIX = save_thm ("TRANS_PREFIX", EQ_IMP_LR TRANS_PREFIX_EQ);

(******************************************************************************)
(*                                                                            *)
(*                The transitions of a binary summation                       *)
(*                                                                            *)
(******************************************************************************)

(* |- !E E' u E''. TRANS(sum E E')u E'' = TRANS E u E'' \/ TRANS E' u E'' *)
val SUM_cases_EQ = save_thm ("SUM_cases_EQ",
  ((GEN ``D :CCS``) o
   (GEN ``D' :CCS``) o
   (GEN ``u :Action``) o
   (GEN ``D'' :CCS``) o
   (REWRITE_RULE [CCS_distinct', CCS_11]) o
   (SPECL [``sum D D'``, ``u :Action``, ``D'' :CCS``]))
      TRANS_cases);

val SUM_cases = save_thm ("SUM_cases", EQ_IMP_LR SUM_cases_EQ);

val TRANS_SUM_EQ = store_thm ("TRANS_SUM_EQ",
  ``!E E' u E''. TRANS (sum E E') u E'' = TRANS E u E'' \/ TRANS E' u E''``, 
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC SUM_cases \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      STRIP_TAC >| [SUM1_TAC, SUM2_TAC] \\
      ASM_REWRITE_TAC [] ]);

(* for CCS_TRANS_CONV *)
val TRANS_SUM_EQ' = store_thm (
   "TRANS_SUM_EQ'",
  ``!E1 E2 u E. TRANS (sum E1 E2) u E = TRANS E1 u E \/ TRANS E2 u E``, 
    REWRITE_TAC [TRANS_SUM_EQ]);

val TRANS_SUM = store_thm ("TRANS_SUM",
  ``!E E' u E''. TRANS (sum E E') u E'' ==> TRANS E u E'' \/ TRANS E' u E''``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [fst (EQ_IMP_RULE (SPEC_ALL TRANS_SUM_EQ))]);

val TRANS_COMM_EQ = store_thm ("TRANS_COMM_EQ",
  ``!E E' E'' u. TRANS (sum E E') u E'' = TRANS (sum E' E) u E''``,
    REPEAT GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ SUM2_TAC, SUM1_TAC ] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ SUM2_TAC, SUM1_TAC ] \\
      ASM_REWRITE_TAC [] ]);

val TRANS_ASSOC_EQ = store_thm ("TRANS_ASSOC_EQ",
  ``!E E' E'' E1 u. TRANS (sum (sum E E') E'') u E1 = TRANS (sum E (sum E' E'')) u E1``,
    REPEAT GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ (* goal 1.1 (of 2) *)
	IMP_RES_TAC TRANS_SUM >| (* 4 sub-goals here *)
        [ SUM1_TAC,
	  SUM1_TAC,
	  SUM2_TAC >> SUM1_TAC,
	  SUM2_TAC >> SUM1_TAC ] \\
        ASM_REWRITE_TAC [],
	(* goal 1.2 (of 2) *)
        SUM2_TAC >> SUM2_TAC \\
        ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ SUM1_TAC >> SUM1_TAC \\
        ASM_REWRITE_TAC [],
        IMP_RES_TAC TRANS_SUM >| (* 4 sub-goals here *)
        [ SUM1_TAC >> SUM1_TAC,
	  SUM1_TAC >> SUM2_TAC,
	  SUM2_TAC,
	  SUM2_TAC ] \\
	ASM_REWRITE_TAC [] ] ]);

val TRANS_ASSOC_RL = save_thm (
   "TRANS_ASSOC_RL", EQ_IMP_RL TRANS_ASSOC_EQ);

val TRANS_SUM_NIL_EQ = store_thm (
   "TRANS_SUM_NIL_EQ",
  ``!E u E'. TRANS (sum E nil) u E' = TRANS E u E'``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM \\
      IMP_RES_TAC NIL_NO_TRANS,
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      SUM1_TAC >> ASM_REWRITE_TAC [] ]);   

(* |- ∀E u E'. E + nil --u-> E' ⇒ E --u-> E' *)
val TRANS_SUM_NIL = save_thm ("TRANS_SUM_NIL",
  ((GEN ``E :CCS``) o
   (GEN ``u :Action``) o
   (GEN ``E' :CCS``))
      (EQ_IMP_LR' TRANS_SUM_NIL_EQ));

val TRANS_P_SUM_P_EQ = store_thm ("TRANS_P_SUM_P_EQ",
  ``!E u E'. TRANS (sum E E) u E' = TRANS E u E'``,
    REPEAT GEN_TAC
 >> EQ_TAC
 >| [ DISCH_TAC >> IMP_RES_TAC TRANS_SUM,
      DISCH_TAC >> SUM1_TAC >> ASM_REWRITE_TAC [] ]);

val TRANS_P_SUM_P = save_thm ("TRANS_P_SUM_P",
  ((GEN ``E :CCS``) o
   (GEN ``u :Action``) o
   (GEN ``E' :CCS``))
      (EQ_IMP_LR' TRANS_P_SUM_P_EQ));

val PAR_cases_EQ = save_thm ("PAR_cases_EQ",
  ((GEN ``D :CCS``) o
   (GEN ``D' :CCS``) o
   (GEN ``u :Action``) o
   (GEN ``D'' :CCS``) o
   (REWRITE_RULE [CCS_distinct', CCS_11]) o
   (SPECL [``par D D'``, ``u :Action``, ``D'' :CCS``]))
      TRANS_cases);

val PAR_cases = save_thm ("PAR_cases",
  ((GEN ``D :CCS``) o
   (GEN ``D' :CCS``) o
   (GEN ``u :Action``) o
   (GEN ``D'' :CCS``))
      (EQ_IMP_LR' PAR_cases_EQ));

(* NOTE: the shape of this theorem can be easily got from above definition by replacing
         REWRITE_RULE to SIMP_RULE, however the inner existential variable (E1) has a
         different name. *)
val TRANS_PAR_EQ = store_thm ("TRANS_PAR_EQ",
  ``!E E' u E''. TRANS (par E E') u E'' =
		 (?E1. (E'' = par E1 E') /\ TRANS E u E1) \/
		 (?E1. (E'' = par E E1) /\ TRANS E' u E1) \/
		 (?E1 E2 l. (u = tau) /\ (E'' = par E1 E2) /\
			    TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2)``,
    REPEAT GEN_TAC
 >> EQ_TAC (* two goals here *)
 >| [ (* case 1 (LR) *)
      STRIP_TAC \\
      IMP_RES_TAC PAR_cases >| (* 3 sub-goals here *)
      [ (* goal 1.1 *)
	DISJ1_TAC \\
	Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
	(* goal 1.2 *)
	DISJ2_TAC \\
	DISJ1_TAC \\
	Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
	(* goal 1.3 *)
	DISJ2_TAC \\
	DISJ2_TAC \\
	take [`E1`, `E2`, `l`] \\
	ASM_REWRITE_TAC [] ],
      (* case 2 (RL) *)
      STRIP_TAC (* 3 sub-goals here, but they share the first and last steps *)
   >> ASM_REWRITE_TAC []
   >| [ PAR1_TAC, PAR2_TAC, PAR3_TAC ]
   >> ASM_REWRITE_TAC [] ]);

val TRANS_PAR = save_thm ("TRANS_PAR",
  ((GEN ``E :CCS``) o
   (GEN ``E' :CCS``) o
   (GEN ``u :Action``) o
   (GEN ``E'' :CCS``))
      (EQ_IMP_LR' TRANS_PAR_EQ));

val TRANS_PAR_P_NIL = store_thm ("TRANS_PAR_P_NIL",
  ``!E u E'. TRANS (par E nil) u E' ==> (?E''. TRANS E u E'' /\ (E' = par E'' nil))``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR
 >| [ Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      IMP_RES_TAC NIL_NO_TRANS,
      IMP_RES_TAC NIL_NO_TRANS ]);

val TRANS_PAR_NO_SYNCR = store_thm ("TRANS_PAR_NO_SYNCR",
  ``!l l'. ~(l = COMPL l') ==>
	   (!E E' E''. ~(TRANS (par (prefix (label l) E) (prefix (label l') E')) tau E''))``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR
 >| [ IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_11 \\
      CHECK_ASSUME_TAC
        (REWRITE_RULE [SYM (Q.ASSUME `l'' = l`),
		       SYM (Q.ASSUME `COMPL l'' = l'`), Lab_COMPL_COMPL]
		      (ASSUME ``~(l = COMPL l')``)) \\
      RW_TAC bool_ss [] ]);

val RESTR_cases_EQ = save_thm ("RESTR_cases_EQ",
  ((GEN ``D :CCS``) o
   (GEN ``L :Label set``) o
   (GEN ``u: Action``) o
   (GEN ``D' :CCS``))
      (REWRITE_RULE [CCS_distinct', CCS_11, Action_distinct, Action_11]
		    (SPECL [``restr L D``, ``u :Action``, ``D' :CCS``]
			   TRANS_cases)));

val RESTR_cases = save_thm ("RESTR_cases",
  ((GEN ``D :CCS``) o
   (GEN ``L :Label set``) o
   (GEN ``u: Action``) o
   (GEN ``D' :CCS``))
      (EQ_IMP_LR' RESTR_cases_EQ));

val TRANS_RESTR_EQ = store_thm ("TRANS_RESTR_EQ",
  ``!E L u E'.
     TRANS (restr L E) u E' = 
     (?E'' l. (E' = restr L E'') /\ TRANS E u E'' /\
	      ((u = tau) \/ ((u = label l) /\ ~(l IN L) /\ ~((COMPL l) IN L))))``,
  let val a1 = ASSUME ``u = tau``
      and a2 = ASSUME ``u = label l``
      and a3 = ASSUME ``TRANS E'' u E'''``
      and a4 = ASSUME ``TRANS E u E''``
  in
    REPEAT GEN_TAC
 >> EQ_TAC >| (* two goals here *)
    [ (* case 1 (LR) *)
      STRIP_TAC \\
      IMP_RES_TAC RESTR_cases \\ (* two sub-goals here, first two steps are shared *)
      Q.EXISTS_TAC `E'''` \\
      Q.EXISTS_TAC `l` >|
      [ (* goal 1.1 *)
	ASM_REWRITE_TAC [REWRITE_RULE [a1] a3],
	(* goal 1.2 *)
	ASM_REWRITE_TAC [REWRITE_RULE [a2] a3] ],
      (* case 2 (RL) *)
      STRIP_TAC >|			(* two sub-goals here *)
      [ (* sub-goal 2.1 *)
	ASM_REWRITE_TAC [] \\
	RESTR_TAC \\
	ASM_REWRITE_TAC [REWRITE_RULE [a1] a4],
	(* sub-goal 2.2 *)
	ASM_REWRITE_TAC [] \\
	RESTR_TAC \\
	ASM_REWRITE_TAC [REWRITE_RULE [a2] a4] ] ]
  end);

val TRANS_RESTR = save_thm ("TRANS_RESTR",
  ((GEN ``E :CCS``) o
   (GEN ``L :Label set``) o
   (GEN ``u: Action``) o
   (GEN ``E' :CCS``))
      (EQ_IMP_LR' TRANS_RESTR_EQ));

val TRANS_P_RESTR = store_thm ("TRANS_P_RESTR",
  ``!E u E' L. TRANS (restr L E) u (restr L E') ==> TRANS E u E'``,
  let
      val thm = REWRITE_RULE [CCS_11] (ASSUME ``restr L E' = restr L E''``)
  in
      REPEAT STRIP_TAC \\
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ FILTER_ASM_REWRITE_TAC (fn t => not (t = ``u = tau``)) [thm],
        FILTER_ASM_REWRITE_TAC (fn t => not (t = ``u = label l``)) [thm] ]
  end);

val RESTR_NIL_NO_TRANS = store_thm ("RESTR_NIL_NO_TRANS",
  ``!L u E. ~(TRANS (restr L nil) u E)``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC TRANS_RESTR (* two sub-goals here, but same proofs *)
 >> IMP_RES_TAC NIL_NO_TRANS);

val TRANS_IMP_NO_RESTR_NIL = store_thm ("TRANS_IMP_NO_RESTR_NIL",
  ``!E u E'. TRANS E u E' ==> !L. ~(E = restr L nil)``,
    REPEAT STRIP_TAC
 >> ASSUME_TAC (REWRITE_RULE [ASSUME ``E = restr L nil``]
			     (ASSUME ``TRANS E u E'``))
 >> IMP_RES_TAC RESTR_NIL_NO_TRANS);

val TRANS_RESTR_NO_NIL = store_thm ("TRANS_RESTR_NO_NIL",
  ``!E L u E'. TRANS (restr L E) u (restr L E') ==> ~(E = nil)``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC TRANS_RESTR
 >> ASSUME_TAC (REWRITE_RULE [ASSUME ``E = nil``]
			     (ASSUME ``TRANS E u E''``))
 >> IMP_RES_TAC NIL_NO_TRANS);

val RESTR_LABEL_NO_TRANS = store_thm ("RESTR_LABEL_NO_TRANS",
  ``!l L. (l IN L) \/ ((COMPL l) IN L) ==>
	  (!E u E'. ~(TRANS (restr L (prefix (label l) E)) u E'))``,
    REPEAT STRIP_TAC (* 2 goals here *)
 >| [ (* goal 1 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 1.1 *)
	IMP_RES_TAC TRANS_PREFIX \\
	CHECK_ASSUME_TAC
	  (REWRITE_RULE [ASSUME ``u = tau``, Action_distinct]
			(ASSUME ``u = label l``)),
	(* goal 1.2 *)
	IMP_RES_TAC TRANS_PREFIX \\
	CHECK_ASSUME_TAC
	  (MP (REWRITE_RULE
		[REWRITE_RULE [ASSUME ``u = label l'``, Action_11]
			      (ASSUME ``u = label l``)]
		(ASSUME ``~((l':Label) IN L)``))
	      (ASSUME ``(l:Label) IN L``)) ],
      (* goal 2 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 2.1 *)
	IMP_RES_TAC TRANS_PREFIX \\
	CHECK_ASSUME_TAC
	  (REWRITE_RULE [ASSUME ``u = tau``, Action_distinct]
			(ASSUME ``u = label l``)),
	(* goal 2.2 *)        
	IMP_RES_TAC TRANS_PREFIX \\
	CHECK_ASSUME_TAC
	  (MP (REWRITE_RULE
		[REWRITE_RULE [ASSUME ``u = label l'``, Action_11]
			      (ASSUME ``u = label l``)]
		(ASSUME ``~((COMPL (l':Label)) IN L)``))
	      (ASSUME ``(COMPL (l:Label)) IN L``)) ] ]);

val RELAB_cases_EQ = save_thm ("RELAB_cases_EQ",
    GEN_ALL (REWRITE_RULE [CCS_distinct', CCS_11] (SPEC ``relab E rf`` TRANS_cases)));

val RELAB_cases = save_thm ("RELAB_cases", EQ_IMP_LR RELAB_cases_EQ);

val TRANS_RELAB_EQ = store_thm ("TRANS_RELAB_EQ",
  ``!E rf u E'. TRANS (relab E rf) u E' =
		(?u' E''. (u = relabel rf u') /\ 
			  (E' = relab E'' rf) /\ TRANS E u' E'')``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC	\\
      IMP_RES_TAC RELAB_cases \\
      take [`u'`, `E'''`] >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      STRIP_TAC \\
      PURE_ONCE_ASM_REWRITE_TAC [] \\
      RELAB_TAC \\
      PURE_ONCE_ASM_REWRITE_TAC [] ]);

val TRANS_RELAB = save_thm ("TRANS_RELAB",
  ((GEN ``E :CCS``) o
   (GEN ``rf :Relabelling``) o
   (GEN ``u :Action``) o
   (GEN ``E' :CCS``))
      (EQ_IMP_LR' TRANS_RELAB_EQ));

val TRANS_RELAB_labl = save_thm ("TRANS_RELAB_labl",
    GEN_ALL (Q.SPECL [`E`, `RELAB labl`] TRANS_RELAB));

val RELAB_NIL_NO_TRANS = store_thm ("RELAB_NIL_NO_TRANS",
  ``!rf u E. ~(TRANS (relab nil rf) u E)``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC TRANS_RELAB
 >> IMP_RES_TAC NIL_NO_TRANS);

(* |- ∀labl' labl.
     (RELAB labl' = RELAB labl) ⇔ (Apply_Relab labl' = Apply_Relab labl)
 *)
val APPLY_RELAB_THM = save_thm ("APPLY_RELAB_THM",
    GEN_ALL
      (REWRITE_RULE [GSYM RELAB_def]
	(MATCH_MP (MATCH_MP ABS_Relabelling_one_one
			    (Q.SPEC `labl` IS_RELABELLING))
		  (Q.SPEC `labl` IS_RELABELLING))));

val REC_cases_EQ = save_thm ("REC_cases_EQ",
    GEN_ALL (REWRITE_RULE [CCS_distinct', CCS_11] (SPEC ``rec X E`` TRANS_cases)));

val REC_cases = save_thm ("REC_cases", EQ_IMP_LR REC_cases_EQ);

val TRANS_REC_EQ = store_thm ("TRANS_REC_EQ",
  ``!X E u E'. TRANS (rec X E) u E' = TRANS (CCS_Subst E (rec X E) X) u E'``,
    REPEAT GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      PURE_ONCE_REWRITE_TAC [REC_cases_EQ] \\
      REPEAT STRIP_TAC \\
      PURE_ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [REC] ]);

val TRANS_REC = save_thm ("TRANS_REC",
  ((GEN ``X :string``) o
   (GEN ``E :CCS``) o
   (GEN ``u :Action``) o
   (GEN ``E' :CCS``))
      (EQ_IMP_LR' TRANS_REC_EQ));

(******************************************************************************)
(*                                                                            *)
(*         Mini support for weak transitions (no other theorems)              *)
(*                                                                            *)
(******************************************************************************)

val epsilon_def = Define `epsilon = []`;
val _ = Unicode.unicode_version { u = UTF8.chr 0x03B5, tmnm = "epsilon"};
val _ = TeX_notation { hol = UTF8.chr 0x03B5,
                       TeX = ("\\HOLepsilon", 1) }

(* Weak transition relation *)
val (WEAK_TRANS_rules, WEAK_TRANS_ind, WEAK_TRANS_cases) = Hol_reln `
    (!E E' l. TRANS E (label l) E' ==> WEAK_TRANS E [l] E') /\
    (!E E'.   TRANS E tau E'       ==> WEAK_TRANS E epsilon E') /\
    (!E.                               WEAK_TRANS E epsilon E) /\
    (!E1 E2 E3 l1 l2.
               WEAK_TRANS E1 l1 E2 /\
               WEAK_TRANS E2 l2 E3 ==> WEAK_TRANS E1 (l1 ++ l2) E3)`;

val _ =
    add_rule { term_name = "WEAK_TRANS", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK "==", HardSpace 0, TM, HardSpace 0, TOK "=>>",
			BreakSpace(1,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

(* by definition, TRANS implies WEAK_TRANS *)
val TRANS_IMP_WEAK_TRANS = store_thm (
   "TRANS_IMP_WEAK_TRANS", ``!E l E'. TRANS E (label l) E' ==> WEAK_TRANS E [l] E'``,
    PROVE_TAC [WEAK_TRANS_rules]);

val _ = export_theory ();
val _ = DB.html_theory "CCS";

(* last updated: March 20, 2017 *)
