% =========================================================================== %
% FILE          : mod_logic.ml                                                %
% DESCRIPTION   : Hennessy-Milner logic for CCS                               %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 20 January 1992                                             %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `mod_logic`;;    

% --------------------------------------------------------------------------- %
% Define the formulas of (a slightly generalized) Hennessy-Milner logic. (996)%
% --------------------------------------------------------------------------- %
let eHML = 
     define_type
      `eHML`      
      `eHML = tt | 
              neg eHML | 
              conj eHML eHML | 
              box (Action)set eHML`;;   

% --------------------------------------------------------------------------- %
% Prove that the constructors of the type eHML are distinct.         (364+81) %
% --------------------------------------------------------------------------- %
let eHML_Distinct1 =
     save_thm(`eHML_Distinct1`, prove_constructors_distinct eHML);;

let eHML_Distinct =
     let thm = CONJUNCTS eHML_Distinct1 in  
     LIST_CONJ (append thm (map GSYM thm));; 

% --------------------------------------------------------------------------- %
% Prove that the constructors of the type eHML are one-to-one.          (412) %
% --------------------------------------------------------------------------- %
let eHML_One_One = save_thm(`eHML_One_One`, prove_constructors_one_one eHML);;

% --------------------------------------------------------------------------- %
%  Define structural induction on eHML formulas:                        (296) %
%  |- !P.                                                                     %
%      P tt /\                                                                %
%      (!e'. P e' ==> P(neg e')) /\                                           %
%      (!e1 e2. P e1 /\ P e2 ==> P(conj e1 e2)) /\                            %
%      (!e'. P e' ==> (!s. P(box s e'))) ==>                                  %
%      (!e. P e)                                                              %
% --------------------------------------------------------------------------- %
let eHML_Induct = save_thm(`eHML_Induct`, prove_induction_thm eHML);;

% --------------------------------------------------------------------------- %
% Define the satisfaction relation SAT: CCS -> eHML -> bool.            (405) %
% --------------------------------------------------------------------------- %
let SAT =
     new_recursive_definition
      false
      eHML
      `SAT`
      "(SAT E tt = T) /\
       (SAT E (neg Fm) = ~(SAT E Fm)) /\
       (SAT E (conj Fm1 Fm2) = (SAT E Fm1) /\ (SAT E Fm2)) /\
       (SAT E (box A Fm) =
       (!u E'. (u IN A) /\ (TRANS E u E') ==> SAT E' Fm))";;

% --------------------------------------------------------------------------- %
% The satisfaction relation SAT as individual theorems.                       %
% --------------------------------------------------------------------------- %
let [SAT_tt; SAT_neg; SAT_conj; SAT_box] = CONJUNCTS SAT;;

% --------------------------------------------------------------------------- %
% The satisfaction relation SAT as individual inference rules.                %
% --------------------------------------------------------------------------- %
let [SAT_tt_r; SAT_neg_r; SAT_conj_r; SAT_box_r] = 
     map EQ_IMP_RL (CONJUNCTS SAT);;      

% --------------------------------------------------------------------------- %
% Tactics for proofs about the satisfaction relation SAT.                     %
% --------------------------------------------------------------------------- %
let [SAT_tt_TAC; SAT_neg_TAC; SAT_conj_TAC; SAT_box_TAC] = 
     map RULE_TAC [SAT_tt_r; SAT_neg_r; SAT_conj_r; SAT_box_r] ;;

% --------------------------------------------------------------------------- %
% Define some derived operators of the logic and prove the related theorem,   %
% inference rule and tactic for the satisfaction relation.                    %
% --------------------------------------------------------------------------- %

% --------------------------------------------------------------------------- %
% The operator `ff` (false).                                             (23) %
% --------------------------------------------------------------------------- %
let ff = new_definition (`ff`, "ff = neg tt");;

let SAT_ff =
     prove_thm
      (`SAT_ff`,
       "!E. SAT E ff = F",
       GEN_TAC THEN REWRITE_TAC [ff; SAT_neg; SAT_tt]);;

let SAT_ff_r = save_thm(`SAT_ff_r`, EQ_IMP_RL SAT_ff);;  

let SAT_ff_TAC = RULE_TAC SAT_ff_r;; 

% --------------------------------------------------------------------------- %
% The operator `disj` (disjunction).                                     (80) %
% --------------------------------------------------------------------------- %
let disj =  
     new_definition (`disj`,     
                     "disj Fm1 Fm2 = neg (conj (neg Fm1) (neg Fm2))");;

let SAT_disj =
     prove_thm
      (`SAT_disj`,
       "!E Fm1 Fm2.
         SAT E (disj Fm1 Fm2) = SAT E Fm1 \/ SAT E Fm2",
       REPEAT GEN_TAC THEN
       REWRITE_TAC [disj; SAT; DE_MORGAN_THM]);;    

let SAT_disj_r = save_thm(`SAT_disj_r`, EQ_IMP_RL SAT_disj);;

let SAT_disj_TAC = RULE_TAC SAT_disj_r;;

% --------------------------------------------------------------------------- %
% The operator `dmd` (diamond).                                         (178) %
% --------------------------------------------------------------------------- %
let dmd =
     new_definition (`dmd`, "dmd A Fm = neg (box A (neg Fm))");;      

let SAT_dmd =
     prove_thm
      (`SAT_dmd`,
       "!E A Fm.  
         SAT E (dmd A Fm) = ?u E'. u IN A /\ TRANS E u E' /\ SAT E' Fm", 
       REPEAT GEN_TAC THEN 
       REWRITE_TAC [dmd; SAT] THEN
       CONV_TAC (TOP_DEPTH_CONV NOT_FORALL_CONV) THEN
       REWRITE_TAC [IMP_DISJ_THM; DE_MORGAN_THM; CONJ_ASSOC]);; 

let SAT_dmd_r = save_thm(`SAT_dmd_r`, EQ_IMP_RL SAT_dmd);;

let SAT_dmd_TAC = RULE_TAC SAT_dmd_r;;

% --------------------------------------------------------------------------- %
% The formula <A>tt expresses a capacity to perform an action in A.      (32) %
% --------------------------------------------------------------------------- % 
let SAT_capc = 
     prove_thm
      (`SAT_capc`,
       "!E A. SAT E (dmd A tt) = ?u E'. u IN A /\ TRANS E u E'", 
       REPEAT GEN_TAC THEN
       REWRITE_TAC [SAT_dmd; SAT_tt]);; 

% --------------------------------------------------------------------------- %
% The formula [A]ff expresses an inability to perform any action in A.   (80) %
% --------------------------------------------------------------------------- %
let SAT_inab =
     prove_thm
      (`SAT_inab`,
       "!E A. SAT E (box A ff) = ~(?u E'. u IN A /\ TRANS E u E')", 
       REPEAT GEN_TAC THEN   
       REWRITE_TAC [SAT_box; SAT_ff] THEN 
       CONV_TAC (TOP_DEPTH_CONV NOT_EXISTS_CONV) THEN ONCE_REWRITE_TAC[]);; 

% --------------------------------------------------------------------------- %
% The formula <->tt /\ [-u]ff expresses a necessity to perform a given   (347)%
% action u, where <-> stands for <Action> and [-u] for [Action - {u}].        %
% --------------------------------------------------------------------------- %
let nec =
     new_definition 
     (`nec`, "nec u = conj (dmd UNIV tt) (box (UNIV DIFF {u}) ff)");; 

let SAT_nec = 
     prove_thm
      (`SAT_nec`, 
       "!E u. 
         SAT E (nec u) = 
         (?E'. TRANS E u E') /\ ~(?u' E'. ~(u' = u) /\ TRANS E u' E')", 
       REPEAT GEN_TAC THEN 
       REWRITE_TAC [nec; SAT_conj; SAT_capc; SAT_inab; 
                    IN_UNIV; IN_DIFF; IN_SING] THEN 
       CONV_TAC (TOP_DEPTH_CONV NOT_EXISTS_CONV) THEN 
       REWRITE_TAC [DE_MORGAN_THM] THEN EQ_TAC THENL  
       [REPEAT STRIP_TAC THENL  
        [DISJ_CASES_TAC 
         (SPEC_ALL (ASSUME "!u' E'. (u' = u) \/ ~TRANS E u' E'")) THENL
         [EXISTS_TAC "E': CCS" THEN 
          REWRITE_TAC [REWRITE_RULE [ASSUME "u' = u: Action"] 
                       (ASSUME "TRANS E u' E'")] ; 
          RES_TAC ] ;  
         ASM_REWRITE_TAC[] ] 
        ; 
        REPEAT STRIP_TAC THENL 
        [EXISTS_TAC "u: Action" THEN EXISTS_TAC "E': CCS" THEN 
         ASM_REWRITE_TAC[] ;  
         ASM_REWRITE_TAC[] ]]);;  
 
% --------------------------------------------------------------------------- %
% Tactic to manipulate assumptions when proving modal properties.             %
% --------------------------------------------------------------------------- %
let MODAL_TAC as1 as2 =
    IMP_RES_TAC TRANS_PREFIX THEN
    CHECK_ASSUME_TAC
    (REWRITE_RULE [ASSUME as1;
                   Action_IN_CONV (snd(dest_eq as1)) (snd(dest_comb as2))]
            (ASSUME as2));;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;
 
