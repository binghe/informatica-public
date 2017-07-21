% =========================================================================== %
% FILE          : syntax.ml                                                   %
% DESCRIPTION   : Syntax of pure CCS (string based formalization)             %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : August 1995                                                 %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `syntax`;;

% --------------------------------------------------------------------------- %
% Load the libraries for string and sets.                                     %
% --------------------------------------------------------------------------- %
map load_library [`string`; `sets`];;

% --------------------------------------------------------------------------- %
% Define the set of labels as the union of names (`in`) (strings) and   (386) %
% co-names (`out`) (complement of names).                                     %
% --------------------------------------------------------------------------- %
let Label = define_type `Label` `Label = name string | coname string`;;

% --------------------------------------------------------------------------- %
%  Define structural induction on labels                                (118) %
%     |- !P. (!s. P(name s)) /\ (!s. P(coname s)) ==> (!L. P L))              %
% --------------------------------------------------------------------------- %
let Label_Induct = save_thm(`Label_Induct`, prove_induction_thm Label);; 

% --------------------------------------------------------------------------- %
% The structural cases theorem for the type Label                        (91) %
%     |- !L. (?s. L = name s) \/ (?s. L = coname s)                           %
% --------------------------------------------------------------------------- %
let Label_Cases = save_thm(`Label_Cases`, prove_cases_thm Label_Induct);;

% --------------------------------------------------------------------------- %
% Prove that the labels are distinct, i.e. an input label (name) cannot       %
% be equal to an output label (coname):                                       %
%  Label_Distinct = |- !s s'. ~(name s = coname s')                     (152) %
%  Label_Distinct' = |- !s s'. ~(coname s' = name s)                          %
%  Label_Not_Eq = |- !s s'. (name s = coname s') = F                          %
%  Label_Not_Eq' = |- !s' s. (coname s' = name s) = F                         %
% --------------------------------------------------------------------------- %
let Label_Distinct =
     save_thm(`Label_Distinct`, prove_constructors_distinct Label);;

let Label_Distinct' =
     save_thm(`Label_Distinct'`, GSYM Label_Distinct);; 

let Label_Not_Eq =
     save_thm
      (`Label_Not_Eq`,
       GEN_ALL (EQF_INTRO (SPEC_ALL Label_Distinct)));;

let Label_Not_Eq' =
     save_thm
      (`Label_Not_Eq'`,
       GEN_ALL (SUBS [SYM_CONV "name s = coname s'"]
                     (SPEC_ALL Label_Not_Eq)));;

% --------------------------------------------------------------------------- %
% Prove that the constructors of the type Label are one-to-one:         (217) %
%  Label_One_One = |- (!s s'. (name s = name s') = (s = s')) /\               %
%                     (!s s'. (coname s = coname s') = (s = s'))              %
% --------------------------------------------------------------------------- %
let Label_One_One =
     save_thm(`Label_One_One`, prove_constructors_one_one Label);;

% --------------------------------------------------------------------------- %
% Define the set of actions as the union of the internal action tau and  (368)%
% the labels.                                                                 %
% --------------------------------------------------------------------------- %
let Action = define_type `Action` `Action = tau | label Label`;;

% --------------------------------------------------------------------------- %
% Define structural induction on actions                                (102) %
%     |- !P. P tau /\ (!L. P(label L)) ==> (!A. P A)                          %
% --------------------------------------------------------------------------- %
let Action_Induct = save_thm(`Action_Induct`, prove_induction_thm Action);; 

% --------------------------------------------------------------------------- %
% The structural cases theorem for the type Action                       (63) %
%     |- !A. (A = tau) \/ (?L. A = label L)                                   %
% --------------------------------------------------------------------------- %
let Action_Cases = save_thm(`Action_Cases`, prove_cases_thm Action_Induct);;

% --------------------------------------------------------------------------- %
%  Prove that tau is distinct from any label.                           (135) %
%   |- !L. ~(tau = label L)       and     |- !L. ~(label L = tau)             %
% --------------------------------------------------------------------------- %
let Action_Distinct =
     save_thm(`Action_Distinct`, prove_constructors_distinct Action);;

let Action_Distinct_label =
     save_thm(`Action_Distinct_label`, GSYM Action_Distinct);; 

% --------------------------------------------------------------------------- %
% Prove that the constructors of the type Action are one-to-one:        (108) %
%  Action_One_One = |- !L L'. (label L = label L') = (L = L')                 %
% --------------------------------------------------------------------------- %
let Action_One_One =
     save_thm(`Action_One_One`, prove_constructors_one_one Action);;

% --------------------------------------------------------------------------- %
%  Action_No_Tau_Is_Label = |- !A. ~(A = tau) ==> (?L. A = label L)           %
% --------------------------------------------------------------------------- %
let Action_No_Tau_Is_Label =
     save_thm
      (`Action_No_Tau_Is_Label`,
       GEN_ALL (DISJ_IMP (SPEC_ALL Action_Cases)));;

% --------------------------------------------------------------------------- %
% Extract the label from a visible action, LABEL: Action -> Label.    (91+119)%
% --------------------------------------------------------------------------- %
let LABEL =
     new_recursive_definition false Action `LABEL` "LABEL (label l) = l";;

let IS_LABEL = 
     new_recursive_definition 
      false 
      Action 
      `IS_LABEL` 
      "(IS_LABEL (label l) = T) /\ (IS_LABEL tau = F)";;      

% --------------------------------------------------------------------------- %
% Define the complement of a label, COMPL: Label -> Label.               (135)%
% --------------------------------------------------------------------------- %
let COMPL =
     new_recursive_definition
      false
      Label
      `COMPL`
      "(COMPL (name s) = (coname s)) /\ (COMPL (coname s) = (name s))";; 

% --------------------------------------------------------------------------- %
% COMPL_COMPL: |- !l. COMPL (COMPL l) = l                                (72) %
% --------------------------------------------------------------------------- %
let COMPL_COMPL =
     prove_thm
      (`COMPL_COMPL`,
       "!l. COMPL (COMPL l) = l",
       INDUCT_THEN Label_Induct ASSUME_TAC THEN REWRITE_TAC [COMPL]);;

% --------------------------------------------------------------------------- %
% Extend the complement to actions, COMPL_ACT: Action -> Action.         (91) %
% --------------------------------------------------------------------------- %
let COMPL_ACT =
     new_recursive_definition
      false
      Action
      `COMPL_ACT`
      "COMPL_ACT (label l) = label(COMPL l)";;

% --------------------------------------------------------------------------- %
% Auxiliary theorem about complementary labels.                         (194) %
% --------------------------------------------------------------------------- %
let COMPL_THM =
     prove_thm
      (`COMPL_THM`,
       "!l s.
         (~(l = name s) ==> ~(COMPL l = coname s)) /\
         (~(l = coname s) ==> ~(COMPL l = name s))",
       INDUCT_THEN Label_Induct ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN CONJ_TAC THENL
        [REWRITE_TAC [Label_One_One; COMPL] ;
         REWRITE_TAC [Label_Distinct; COMPL; Label_Distinct'] ]
        ;
        REPEAT GEN_TAC THEN CONJ_TAC THENL
        [REWRITE_TAC [Label_Distinct'; COMPL; Label_Distinct] ;
         REWRITE_TAC [Label_One_One; COMPL] ] ]);;

% --------------------------------------------------------------------------- %
% Definition of the type Relabelling as the subset of the functions from      %
% Label to Label such that relabelling respects the complement operation on   %
% labels.                                                                     %
% --------------------------------------------------------------------------- %

% --------------------------------------------------------------------------- %
% Is_Relabelling =                                                            %
% |- !f. Is_Relabelling f = (!s. f(coname s) = COMPL(f(name s)))              %
% --------------------------------------------------------------------------- %
let Is_Relabelling =
     new_definition
      (`Is_Relabelling`,
       "Is_Relabelling (f: Label -> Label) =
        (!s. f(coname s) = COMPL(f(name s)))");;

% --------------------------------------------------------------------------- %
% EXISTS_Relabelling = |- ?f. Is_Relabelling f                           (38) %
% --------------------------------------------------------------------------- %
let EXISTS_Relabelling =
     prove
      ("?f: Label -> Label. Is_Relabelling f",
       EXISTS_TAC "\a: Label. a" THEN
       PURE_ONCE_REWRITE_TAC [Is_Relabelling] THEN
       BETA_TAC THEN REWRITE_TAC [COMPL]);;

% --------------------------------------------------------------------------- %
% Relabelling_TY_DEF = |- ?rep. TYPE_DEFINITION Is_Relabelling rep            %
% --------------------------------------------------------------------------- %
let Relabelling_TY_DEF =
     new_type_definition
      (`Relabelling`,
       "Is_Relabelling: (Label -> Label) -> bool",
       EXISTS_Relabelling);;

% --------------------------------------------------------------------------- %
% Relabelling_ISO_DEF =                                                       %
% |- (!a. ABS_Relabelling(REP_Relabelling a) = a) /\                          %
%    (!r. Is_Relabelling r = (REP_Relabelling(ABS_Relabelling r) = r))        %
% --------------------------------------------------------------------------- %
let Relabelling_ISO_DEF =
     define_new_type_bijections
      `Relabelling_ISO_DEF`
      `ABS_Relabelling`
      `REP_Relabelling`
      Relabelling_TY_DEF;;

% --------------------------------------------------------------------------- %
%  ABS_Relabelling_one_one =                                             (65) %
%  |- !r r'.                                                                  %
%      Is_Relabelling r ==>                                                   %
%      Is_Relabelling r' ==>                                                  %
%      ((ABS_Relabelling r = ABS_Relabelling r') = (r = r'))                  %
%  ABS_Relabelling_onto =                                                     %
%  |- !a. ?r. (a = ABS_Relabelling r) /\ Is_Relabelling r                     %
%  REP_Relabelling_one_one =                                                  %
%  |- !a a'. (REP_Relabelling a = REP_Relabelling a') = (a = a')              %
%  REP_Relabelling_onto =                                                     %
%  |- !r. Is_Relabelling r = (?a. r = REP_Relabelling a)                      %
% --------------------------------------------------------------------------- %
let [ABS_Relabelling_one_one;      
     ABS_Relabelling_onto;      
     REP_Relabelling_one_one;    
     REP_Relabelling_onto] =
 map (\f. f  Relabelling_ISO_DEF)
     [prove_abs_fn_one_one;      
      prove_abs_fn_onto;  
      prove_rep_fn_one_one;    
      prove_rep_fn_onto];;

% --------------------------------------------------------------------------- %
%  |- !rf. Is_Relabelling(REP_Relabelling rf)                            (12) %
% --------------------------------------------------------------------------- %
let REP_Relabelling_THM =
     prove_thm
      (`REP_Relabelling_THM`,
       "!rf: Relabelling.
         Is_Relabelling(REP_Relabelling rf)",
       GEN_TAC THEN REWRITE_TAC [REP_Relabelling_onto] THEN
       EXISTS_TAC "rf: Relabelling" THEN REWRITE_TAC[]);;

% --------------------------------------------------------------------------- %
% Relabelling labels is extended to actions by renaming tau as tau.     (155) %
% --------------------------------------------------------------------------- %
let relabel =
     new_recursive_definition
      false
      Action
      `relabel`
      "(relabel (rf: Relabelling) tau = tau) /\
       (relabel rf (label l) = label (REP_Relabelling rf l))";;

% --------------------------------------------------------------------------- %
% If the renaming of an action is a label, that action is a label.      (107) %
% --------------------------------------------------------------------------- %
let Relab_Label =
     prove
      ("!rf u l. (relabel rf u = label l) ==> ?l'. u = label l'", 
       GEN_TAC THEN
       INDUCT_THEN Action_Induct ASSUME_TAC THENL
       [REWRITE_TAC [relabel; Action_Distinct] ;
        REWRITE_TAC [relabel] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC "L: Label" THEN REWRITE_TAC[] ]);;

% --------------------------------------------------------------------------- %
% If the renaming of an action is tau, that action is tau.               (78) %
% --------------------------------------------------------------------------- %
let Relab_Tau =
     prove
      ("!rf u. (relabel rf u = tau) ==> (u = tau)", 
       GEN_TAC THEN
       INDUCT_THEN Action_Induct ASSUME_TAC THEN
       REWRITE_TAC [relabel; Action_Distinct_label]);;

% --------------------------------------------------------------------------- %
% Apply_Relab: ((Label # Label)list) -> Label -> Label                  (178) %
% (SND of any pair is a name, FST can be either name or coname)               %
% --------------------------------------------------------------------------- %
let Apply_Relab =
     new_list_rec_definition
      (`Apply_Relab`,
       "(Apply_Relab ([]: (Label#Label)list) l = l) /\
        (Apply_Relab (CONS (newold: Label#Label) ls) l =
         ((SND newold = l) => FST newold |
          ((COMPL (SND newold) = l) => COMPL (FST newold) |
                                       Apply_Relab ls l)))");;

% --------------------------------------------------------------------------- %
% Apply_Relab satisfies the definition of relabelling.              (337+349) %
% --------------------------------------------------------------------------- %
let Apply_Relab_COMPL_THM =
     prove_thm
      (`Apply_Relab_COMPL_THM`,
       "!labl s.
         Apply_Relab labl(coname s) = COMPL(Apply_Relab labl(name s))",
       LIST_INDUCT_TAC THENL
       [REWRITE_TAC [Apply_Relab; COMPL]
        ;
        REPEAT GEN_TAC THEN REWRITE_TAC [Apply_Relab] THEN
        COND_CASES_TAC THENL
        [ASM_REWRITE_TAC [Label_Distinct'; COMPL; COMPL_COMPL] ;
         ASM_CASES_TAC "SND(h:Label#Label) = name s" THENL
         [ASM_REWRITE_TAC [COMPL] ;
          IMP_RES_TAC COMPL_THM THEN ASM_REWRITE_TAC[] ]]]);;

let IS_RELABELLING =
     prove
      ("!labl. Is_Relabelling (Apply_Relab labl)", 
       LIST_INDUCT_TAC THENL
       [REWRITE_TAC [Is_Relabelling; Apply_Relab; COMPL]
        ;
        GEN_TAC THEN REWRITE_TAC [Is_Relabelling; Apply_Relab] THEN
        GEN_TAC THEN COND_CASES_TAC THENL
        [ASM_REWRITE_TAC [Label_Distinct'; COMPL; COMPL_COMPL]
         ;
         ASM_CASES_TAC "SND(h:Label#Label) = name s" THENL
         [ASM_REWRITE_TAC [COMPL] ;
          IMP_RES_TAC COMPL_THM THEN
          ASM_REWRITE_TAC [Apply_Relab_COMPL_THM] ]]]);;

% --------------------------------------------------------------------------- %
% Defining a relabelling function through substitution-like notation.         %
%  RELAB: (Label # Label)list -> Relabelling                                  %
% --------------------------------------------------------------------------- %
let RELAB =
     new_definition
      (`RELAB`,
       "RELAB (labl: (Label # Label)list) =
        ABS_Relabelling (Apply_Relab labl)");;

% --------------------------------------------------------------------------- %
% Define the type of (pure) CCS agent expressions.                     (2684) %
% --------------------------------------------------------------------------- %
let CCS =
     define_type
      `CCS`
      `CCS = nil |
             var string | 
             prefix Action CCS |
             sum CCS CCS |
             par CCS CCS | 
             restr CCS (Label)set |
             relab CCS Relabelling |
             rec string CCS`;;

% --------------------------------------------------------------------------- %
%  Define structural induction on CCS agent expressions.                (602) %
% --------------------------------------------------------------------------- %
let CCS_Induct = save_thm(`CCS_Induct`, prove_induction_thm CCS);; 

% --------------------------------------------------------------------------- %
% The structural cases theorem for the type CCS.                        (519) %
% --------------------------------------------------------------------------- %
let CCS_Cases = save_thm(`CCS_Cases`, prove_cases_thm CCS_Induct);;

% --------------------------------------------------------------------------- %
% Prove that the constructors of the type CCS are distinct.      (1032+376+55)%
% --------------------------------------------------------------------------- %
let CCS_Distinct1 =
     save_thm(`CCS_Distinct1`, prove_constructors_distinct CCS);;

let CCS_Distinct_LIST = 
     let thm = CONJUNCTS CCS_Distinct1  
     in append thm (map GSYM thm);; 

let CCS_Distinct = LIST_CONJ CCS_Distinct_LIST;; 

% --------------------------------------------------------------------------- %
% Prove that the constructors of the type CCS are one-to-one.          (1074) %
% --------------------------------------------------------------------------- %
let CCS_One_One = save_thm(`CCS_One_One`, prove_constructors_one_one CCS);; 

% --------------------------------------------------------------------------- %
% Given any agent expression, define the substitution of an agent expression  %
% E' for an agent variable X.                                           (929) %
% This works under the hypothesis that the Barendregt convention holds.       %
% --------------------------------------------------------------------------- %
let CCS_Subst =
     new_recursive_definition
      false
      CCS
      `CCS_Subst`
      "(CCS_Subst nil E' X = nil) /\
       (CCS_Subst (prefix u E) E' X = prefix u (CCS_Subst E E' X)) /\
       (CCS_Subst (sum E1 E2) E' X = sum (CCS_Subst E1 E' X)
                                         (CCS_Subst E2 E' X)) /\
       (CCS_Subst (restr E L) E' X = restr (CCS_Subst E E' X) L) /\
       (CCS_Subst (relab E f) E' X = relab (CCS_Subst E E' X) f) /\
       (CCS_Subst (par E1 E2) E' X = par (CCS_Subst E1 E' X)
                                         (CCS_Subst E2 E' X)) /\
       (CCS_Subst (var Y) E' X = ((Y = X) => E' | (var Y))) /\ 
       (CCS_Subst (rec Y E) E' X =
                  ((Y = X) => rec Y E | rec Y (CCS_Subst E E' X)))";;

% Note that in the rec clause, if Y = X then all occurrences of Y in E are X 
and bound, so there exist no free variables X in E to be replaced with E'.
Hence, the term rec Y E is returned. % 

% --------------------------------------------------------------------------- %
% Define an arbitrary CCS agent.                                              %
% --------------------------------------------------------------------------- %
let ARB' = new_definition (`ARB'`, "ARB' = @x:CCS. T");;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

