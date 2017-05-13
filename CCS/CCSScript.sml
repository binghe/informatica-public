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
    STRIP_FORALL_RULE EQF_INTRO Label_distinct);

val Label_not_eq' = save_thm (
   "Label_not_eq'",
    STRIP_FORALL_RULE (PURE_REWRITE_RULE [SYM_CONV ``name s = coname s'``])
		      Label_not_eq);

val Label_11 = TypeBase.one_one_of ``:Label``;

(* Define the set of actions as the union of the internal action tau and the labels. *)
val _ = Datatype `Action = tau | label Label`;
val _ = Unicode.unicode_version { u = UnicodeChars.tau, tmnm = "tau"};

(* also see functions {from,to}_compat(_tm) in CCSSimps *)
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
val COMPL_LAB_def = Define `(COMPL_LAB (name s) = (coname s)) /\
			    (COMPL_LAB (coname s) = (name s))`;

val _ = overload_on ("COMPL", ``COMPL_LAB``);
val _ = export_rewrites ["COMPL_LAB_def"];

val coname_COMPL = store_thm ("coname_COMPL", 
  ``!s. coname s = COMPL (name s)``,
    REWRITE_TAC [COMPL_LAB_def]);

val COMPL_COMPL_LAB = store_thm (
   "COMPL_COMPL_LAB", ``!(l :Label). COMPL_LAB (COMPL_LAB l) = l``,
    Induct >> REWRITE_TAC [COMPL_LAB_def]);

(* Extend the complement to actions, COMPL_ACT: Action -> Action. *)
val COMPL_ACT_def = Define `
   (COMPL_ACT (label l) = label (COMPL l)) /\
   (COMPL_ACT tau = tau)`;

val _ = overload_on ("COMPL", ``COMPL_ACT``);
val _ = export_rewrites ["COMPL_ACT_def"];

val COMPL_COMPL_ACT = store_thm (
   "COMPL_COMPL_ACT", ``!(a :Action). COMPL_ACT (COMPL_ACT a) = a``,
    Induct
 >| [ REWRITE_TAC [COMPL_ACT_def],
      REWRITE_TAC [COMPL_ACT_def, COMPL_COMPL_LAB] ]);

(* Auxiliary theorem about complementary labels. *)
val COMPL_THM = store_thm ("COMPL_THM",
  ``!l s. (~(l = name s) ==> ~(COMPL l = coname s)) /\
	  (~(l = coname s) ==> ~(COMPL l = name s))``,
    Induct_on `l`
 >| [ (* case 1 *)
      REPEAT GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_11, COMPL_LAB_def],
        REWRITE_TAC [Label_distinct, COMPL_LAB_def, Label_distinct'] ] ,
      (* case 2 *)
      REPEAT GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_distinct, COMPL_LAB_def, Label_distinct'],
        REWRITE_TAC [Label_11, COMPL_LAB_def] ] ]);

val Is_Relabeling_def = Define `
    Is_Relabeling (f: Label -> Label) = (!s. f (coname s) = COMPL (f (name s)))`;

val EXISTS_Relabeling = store_thm ("EXISTS_Relabeling", ``?f. Is_Relabeling f``,
    Q.EXISTS_TAC `\a. a`
 >> PURE_ONCE_REWRITE_TAC [Is_Relabeling_def]
 >> BETA_TAC
 >> REWRITE_TAC [COMPL_LAB_def]);

(* Relabeling_TY_DEF =
   |- ∃rep. TYPE_DEFINITION Is_Relabeling rep
 *)
val Relabeling_TY_DEF = new_type_definition ("Relabeling", EXISTS_Relabeling);

(* Relabeling_ISO_DEF =
   |- (∀a. ABS_Relabeling (REP_Relabeling a) = a) ∧
       ∀r. Is_Relabeling r ⇔ (REP_Relabeling (ABS_Relabeling r) = r)
 *)
val Relabeling_ISO_DEF = define_new_type_bijections
			      { ABS  = "ABS_Relabeling",
				REP  = "REP_Relabeling",
				name = "Relabeling_ISO_DEF",
				tyax =  Relabeling_TY_DEF };

(* ABS_Relabeling_one_one =
   |- ∀r r'.
      Is_Relabeling r ⇒ Is_Relabeling r' ⇒
      ((ABS_Relabeling r = ABS_Relabeling r') ⇔ (r = r'))

   ABS_Relabeling_onto =
   |- ∀a. ∃r. (a = ABS_Relabeling r) ∧ Is_Relabeling r

   REP_Relabeling_one_one =
   |- ∀a a'. (REP_Relabeling a = REP_Relabeling a') ⇔ (a = a')

   REP_Relabeling_onto =
   |- ∀r. Is_Relabeling r ⇔ ∃a. r = REP_Relabeling a
 *)
val [ABS_Relabeling_one_one,
     ABS_Relabeling_onto,
     REP_Relabeling_one_one,
     REP_Relabeling_onto] =
    map (fn f => f Relabeling_ISO_DEF)
	[prove_abs_fn_one_one,
	 prove_abs_fn_onto,
	 prove_rep_fn_one_one,
	 prove_rep_fn_onto];

val REP_Relabeling_THM = store_thm ("REP_Relabeling_THM",
  ``!rf: Relabeling. Is_Relabeling (REP_Relabeling rf)``,
    GEN_TAC
 >> REWRITE_TAC [REP_Relabeling_onto]
 >> Q.EXISTS_TAC `rf`
 >> REWRITE_TAC []);

(* Relabeling labels is extended to actions by renaming tau as tau. *)
val relabel_def = Define `(relabel (rf: Relabeling) tau = tau) /\
			  (relabel rf (label l) = label (REP_Relabeling rf l))`;

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
 >- REWRITE_TAC [Apply_Relab_def, COMPL_LAB_def]
 >> REPEAT GEN_TAC
 >> REWRITE_TAC [Apply_Relab_def]
 >> COND_CASES_TAC
 >- ASM_REWRITE_TAC [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :Label # Label) = name s``
 >- ASM_REWRITE_TAC [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM
 >> ASM_REWRITE_TAC []);

val IS_RELABELING = store_thm (
   "IS_RELABELING" ,``!labl. Is_Relabeling (Apply_Relab labl)``,
    Induct
 >- REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def, COMPL_LAB_def]
 >> GEN_TAC
 >> REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def]
 >> GEN_TAC
 >> COND_CASES_TAC
 >- ASM_REWRITE_TAC [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :Label # Label) = name s``
 >- ASM_REWRITE_TAC [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM
 >> ASM_REWRITE_TAC [Apply_Relab_COMPL_THM]);

(* Defining a relabelling function through substitution-like notation.
   RELAB: (Label # Label)list -> Relabeling
 *)
val RELAB_def = Define `RELAB labl = ABS_Relabeling (Apply_Relab labl)`;

(* Define the type of (pure) CCS agent expressions. *)
val _ = Datatype `CCS = nil
		      | var string
		      | prefix Action CCS
		      | sum CCS CCS
		      | par CCS CCS
		      | restr (Label set) CCS
		      | relab CCS Relabeling
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

(* Single-label restriction *)
val restr1_def = Define `
    restr1 (n: string) (P :CCS) = restr {name n} P`;

val _ = export_rewrites ["restr1_def"]
val _ = overload_on ("nu", ``restr1``);

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

(* |- ∀u E u' E'. u..E --u'-> E' ⇒ (u' = u) ∧ (E' = E) *)
val TRANS_PREFIX = save_thm ("TRANS_PREFIX", EQ_IMP_LR TRANS_PREFIX_EQ);

(******************************************************************************)
(*                                                                            *)
(*                The transitions of a binary summation                       *)
(*                                                                            *)
(******************************************************************************)

val SUM_cases_EQ = save_thm ("SUM_cases_EQ",
    GENL [``D :CCS``, ``D' :CCS``, ``u :Action``, ``D'' :CCS``]
	 (REWRITE_RULE [CCS_distinct', CCS_11]
		       (SPECL [``sum D D'``, ``u :Action``, ``D'' :CCS``] TRANS_cases)));

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

val TRANS_SUM = save_thm ("TRANS_SUM", EQ_IMP_LR TRANS_SUM_EQ);

val TRANS_COMM_EQ = store_thm ("TRANS_COMM_EQ",
  ``!E E' E'' u. TRANS (sum E E') u E'' = TRANS (sum E' E) u E''``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
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
val TRANS_SUM_NIL = save_thm ("TRANS_SUM_NIL", EQ_IMP_LR TRANS_SUM_NIL_EQ);

val TRANS_P_SUM_P_EQ = store_thm ("TRANS_P_SUM_P_EQ",
  ``!E u E'. TRANS (sum E E) u E' = TRANS E u E'``,
    REPEAT GEN_TAC
 >> EQ_TAC
 >| [ DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM,
      DISCH_TAC \\
      SUM1_TAC >> ASM_REWRITE_TAC [] ]);

val TRANS_P_SUM_P = save_thm ("TRANS_P_SUM_P", EQ_IMP_LR TRANS_P_SUM_P_EQ);

val PAR_cases_EQ = save_thm ("PAR_cases_EQ",
    GENL [``D :CCS``, ``D' :CCS``, ``u :Action``, ``D'' :CCS``]
	 (REWRITE_RULE [CCS_distinct', CCS_11]
		       (SPECL [``par D D'``, ``u :Action``, ``D'' :CCS``] TRANS_cases)));

val PAR_cases = save_thm ("PAR_cases", EQ_IMP_LR PAR_cases_EQ);

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

val TRANS_PAR = save_thm ("TRANS_PAR", EQ_IMP_LR TRANS_PAR_EQ);

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
        (REWRITE_RULE [SYM (ASSUME ``(l'': Label) = l``),
		       SYM (ASSUME ``COMPL (l'' :Label) = l'``), COMPL_COMPL_LAB]
		      (ASSUME ``~(l = COMPL (l' :Label))``)) \\
      RW_TAC bool_ss [] ]);

val RESTR_cases_EQ = save_thm ("RESTR_cases_EQ",
    GENL [``D :CCS``, ``L :Label set``, ``u: Action``, ``D' :CCS``]
	 (REWRITE_RULE [CCS_distinct', CCS_11, Action_distinct, Action_11]
		       (SPECL [``restr L D``, ``u :Action``, ``D' :CCS``]
			      TRANS_cases)));

val RESTR_cases = save_thm ("RESTR_cases", EQ_IMP_LR RESTR_cases_EQ);

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

val TRANS_RESTR = save_thm ("TRANS_RESTR", EQ_IMP_LR TRANS_RESTR_EQ);

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

val TRANS_RELAB = save_thm ("TRANS_RELAB", EQ_IMP_LR TRANS_RELAB_EQ);

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
	(MATCH_MP (MATCH_MP ABS_Relabeling_one_one
			    (Q.SPEC `labl` IS_RELABELING))
		  (Q.SPEC `labl` IS_RELABELING))));

val REC_cases_EQ = save_thm ("REC_cases_EQ",
    GENL [``X :string``, ``E :CCS``, ``u :Action``, ``E'' :CCS``]
	 (SPECL [``u :Action``, ``E'' :CCS``]
		(REWRITE_RULE [CCS_distinct', CCS_11] (SPEC ``rec X E`` TRANS_cases))));

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

val TRANS_REC = save_thm ("TRANS_REC", EQ_IMP_LR TRANS_REC_EQ);

val _ = export_theory ();
val _ = DB.html_theory "CCS";

(* last updated: May 7, 2017 *)
