% =========================================================================== %
% FILE          : counter.ml                                                  %
% DESCRIPTION   : Proof by induction of a counter (see HUG '92 paper)         %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 12 June 1992                                                %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `counter`;;

% --------------------------------------------------------------------------- %
% Specification of a family of processes Counter(n), (n:Nat).                 %
%      Counter(0)   = up.Counter(1) + around.Counter(0)                       %
%      Counter(n+1) = up.Counter(n+2) + down.Counter(n)                       %
% --------------------------------------------------------------------------- %
new_constant(`Counter`, ":num -> CCS");;

let Counter =
    new_axiom
     (`Counter`,
      "(Counter 0 = sum (prefix (label(name `up`)) (Counter (SUC 0)))
                        (prefix (label(name `around`)) (Counter 0))) /\
       (Counter (SUC m) = sum (prefix (label(name `up`)) (Counter (SUC(SUC m))))
                              (prefix (label(name `down`)) (Counter m)))");;

% --------------------------------------------------------------------------- %
% Selecting the clauses of the definition of Counter.                         %
% --------------------------------------------------------------------------- %
let (Counter0, CounterSUC) =
  let thm = SPEC_ALL Counter in (CONJUNCT1 thm, GEN_ALL (CONJUNCT2 thm));;

% --------------------------------------------------------------------------- %
% Specification of a family of formulas [{up}](n) Fm  and <{down}>(n) Fm      %
% (n:Nat, Fm:eHML) (in my version it's f(n+1) = f(f(n)), while Stirling's     %
% version is f(n+1) = f(n)(f) ):                                              %
%      [{up}](0) Fm = Fm                                                      %
%      [{up}](n) Fm = [{up}] ([{up}](n-1) Fm)   n>0                           %
%                                                                             %
% Idem for <{down}>(n) Fm:                                                    %
%      <{down}>(0) Fm = Fm                                                    %
%      <{down}>(n) Fm = <{down}> (<{down}>(n-1) Fm)   n>0                     %
% --------------------------------------------------------------------------- %
let Raise =
    new_prim_rec_definition
    (`Raise`,
     "(Raise (f:(Action)set -> (eHML -> eHML)) A 0 Fm = Fm) /\
      (Raise f A (SUC n) Fm = (f A (Raise f A n Fm)))");;

% --------------------------------------------------------------------------- %
% Permutation-like property for Raise, i.e. f(n+1) = f(f(n)) = f(n)(f):  (111)%
%  Raise_Perm:                                                                %
%  |- !n f A Fm. f A (n+1) Fm = f A n (f A Fm)                                %
% --------------------------------------------------------------------------- %
let Raise_Perm =
     prove_thm
      (`Raise_Perm`,
       "!n f A Fm.
         Raise f A (SUC n) Fm = Raise f A n (f A Fm)",
       INDUCT_TAC THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [Raise]
        ;
        REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [Raise] THEN
        ASM_REWRITE_TAC[] ]);;              %apply inductive hp. on the lhs%

% --------------------------------------------------------------------------- %
% Proving some auxiliary results.                                             %
% --------------------------------------------------------------------------- %

% --------------------------------------------------------------------------- %
% The tactic Lemma1_TAC solves the two cases of the proof of Lemma1.          %
%  Inputs are a theorem thm (a clause of the definition of Counter),          %
%  two terms m, n (which will be either "0", or "SUC n" or "n"),              %
%  and a term s (which will be the string of an action).                      %
%      Lemma1_TAC = - : (thm -> term -> term -> term -> tactic)               %
% --------------------------------------------------------------------------- %
let Lemma1_TAC thm m n s =
     GEN_TAC THEN EQ_TAC THENL
     [PURE_ONCE_REWRITE_TAC [thm] THEN
      PURE_REWRITE_TAC [SAT_box] THEN DISCH_TAC THEN
      PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL thm)] THEN 
      ASSUME_TAC 
      (REWRITE_RULE [Action_IN_CONV "label(name `up`)" "{label(name `up`)}"; 
                     TRANS_SUM_EQ; PREFIX]
       (SPECL ["Counter(SUC ^m)"; "label(name `up`)"]
              (ASSUME "!E' u.
                        u IN {label(name `up`)} /\
                        TRANS
                        (sum(prefix(label(name `up`))(Counter(SUC ^m)))
                            (prefix(label(name ^s))(Counter ^n)))u E' ==>
                        SAT E' Fm"))) THEN
      ASM_REWRITE_TAC[]
      ;
      DISCH_TAC THEN PURE_ONCE_REWRITE_TAC [thm] THEN
      PURE_REWRITE_TAC [SAT_box] THEN REPEAT STRIP_TAC THEN
      IMP_RES_TAC TRANS_SUM THENL
      [IMP_RES_TAC PREFIX_cases THEN
       ASSUME_TAC (ONCE_REWRITE_RULE [ASSUME "Counter(SUC ^m) = E'"]
                       (ASSUME "SAT(Counter(SUC ^m))Fm")) THEN
       ASM_REWRITE_TAC[]
       ;
       MODAL_TAC "label(name ^s) = u" "u IN {label(name `up`)}" ]];; 

% --------------------------------------------------------------------------- %
%  Lemma1:                                                              (682) %
%  |- !m Fm. SAT (Counter m) ([{up}] Fm) = SAT (Counter(m+1)) Fm              %
% --------------------------------------------------------------------------- %
let Lemma1 = 
     prove_thm
      (`Lemma1`,
       "!m Fm.
         SAT (Counter m) (box {(label(name `up`))} Fm) =
         SAT (Counter (SUC m)) Fm",
       GEN_TAC THEN 
       STRUCT_CASES_TAC (SPEC "m:num" num_CASES) THENL
       [Lemma1_TAC Counter0 "0" "0" "`around`" 
        ; 
        Lemma1_TAC CounterSUC "SUC n" "n: num" "`down`" ]);;  

% --------------------------------------------------------------------------- %
%  Lemma2:                                                              (308) %
%  |- !m Fm. SAT (Counter(m+1)) (<{down}> Fm) = SAT (Counter m) Fm            %
% --------------------------------------------------------------------------- %
let Lemma2 =
     prove_thm
      (`Lemma2`,
       "!m Fm.
         SAT (Counter (SUC m)) (dmd {(label(name `down`))} Fm) =
         SAT (Counter m) Fm",
       REPEAT GEN_TAC THEN EQ_TAC THENL
       [PURE_ONCE_REWRITE_TAC [CounterSUC] THEN
        PURE_ONCE_REWRITE_TAC [SAT_dmd] THEN STRIP_TAC THEN
        IMP_RES_TAC TRANS_SUM THENL
        [MODAL_TAC "label(name `up`) = u" "u IN {label(name `down`)}" 
         ;
         IMP_RES_TAC PREFIX_cases THEN
         ASSUME_TAC (ONCE_REWRITE_RULE [SYM (ASSUME "Counter m = E'")]
                         (ASSUME "SAT E' Fm")) THEN
         ASM_REWRITE_TAC[]
        ];
        DISCH_TAC THEN PURE_ONCE_REWRITE_TAC [Counter] THEN
        PURE_ONCE_REWRITE_TAC [SAT_dmd] THEN
        EXISTS_TAC "Counter m" THEN EXISTS_TAC "label(name `down`)" THEN
        ASM_REWRITE_TAC
           [Action_IN_CONV "label(name `down`)" "{label(name `down`)}"] THEN
        SUM2_TAC THEN PREFIX_TAC ]);;

% --------------------------------------------------------------------------- %
% The tactic Lemma3_TAC solves the two cases of the proof of Lemma3.          %
%  Inputs are a theorem thm (a clause of the definition of Counter),          %
%  two terms m, n (which will be either "0", or "SUC n" or "n"),              %
%  and a term s (which will be the string of an action).                      %
%     Lemma3_TAC = - : (thm -> term -> term -> term -> tactic)                %
% --------------------------------------------------------------------------- %
let Lemma3_TAC thm m n s =
     GEN_TAC THEN EQ_TAC THENL
     [PURE_ONCE_REWRITE_TAC [thm] THEN
      PURE_ONCE_REWRITE_TAC [SAT_box] THEN
      STRIP_TAC THEN PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL thm)] THEN
      ASSUME_TAC 
      (REWRITE_RULE [Action_IN_CONV "label(name `up`)" "{label(name `up`)}"; 
                     TRANS_SUM_EQ; PREFIX; Lemma2]
       (SPECL ["Counter(SUC ^m)"; "label(name `up`)"]
              (ASSUME "!E' u.
                        u IN {label(name `up`)} /\
                        TRANS
                        (sum (prefix(label(name `up`))(Counter(SUC ^m)))
                             (prefix(label(name ^s))(Counter ^n)))u E' ==>
                        SAT E'(dmd{label(name `down`)}Fm)"))) THEN
      ASM_REWRITE_TAC[]
      ;
      DISCH_TAC THEN PURE_ONCE_REWRITE_TAC [thm] THEN
      PURE_ONCE_REWRITE_TAC [SAT_box] THEN REPEAT STRIP_TAC THEN
      IMP_RES_TAC TRANS_SUM THENL
      [IMP_RES_TAC PREFIX_cases THEN
       ASSUME_TAC (SYM (ASSUME "Counter(SUC ^m) = E'")) THEN
       PURE_ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC [Lemma2]
       ;
       MODAL_TAC "label(name ^s) = u" "u IN {label(name `up`)}" ]];;

% --------------------------------------------------------------------------- %
%  Lemma3:                                                              (737) %
%  |- !m Fm. SAT (Counter m) ([{up}] (<{down}> Fm)) = SAT (Counter m) Fm      %
% --------------------------------------------------------------------------- %
let Lemma3 =
     prove_thm
      (`Lemma3`,
       "!m Fm.
         SAT (Counter m) (box {(label(name `up`))}
                              (dmd {(label(name `down`))} Fm)) =
         SAT (Counter m) Fm",
       GEN_TAC THEN
       STRUCT_CASES_TAC (SPEC "m:num" num_CASES) THENL
       [Lemma3_TAC Counter0 "0" "0" "`around`"
        ;
        Lemma3_TAC CounterSUC "SUC n" "n: num" "`down`"]);;

% --------------------------------------------------------------------------- %
%  Key_Lemma:                                                           (200) %
%  |- !m n Fm.                                                                %
%      SAT (Counter m) ([{up}](n+1) (<{down}>(n+1) Fm)) =                     %
%      SAT (Counter m) ([{up}](n) (<{down}>(n) Fm))                           %
% --------------------------------------------------------------------------- %
let Key_Lemma =
     prove_thm
      (`Key_Lemma`,
       "!n m Fm.
         SAT (Counter m) (Raise box {(label(name `up`))} (SUC n)    
                            (Raise dmd {(label(name `down`))} (SUC n) Fm)) =
         SAT (Counter m) (Raise box {(label(name `up`))} n    
                             (Raise dmd {(label(name `down`))} n Fm))",
       INDUCT_TAC THENL
       [REWRITE_TAC [Raise; Lemma3]
        ;
        REPEAT GEN_TAC THEN
        ONCE_REW_LHS_TAC [SPEC "box" (CONJUNCT2 Raise)] THEN
        PURE_ONCE_REWRITE_TAC [Lemma1] THEN
        ONCE_REW_LHS_TAC [SPECL ["SUC n"; "dmd"] Raise_Perm] THEN
        ONCE_ASM_REW_LHS_TAC [] THEN       %apply inductive hp. only on lhs%  
        PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL Raise_Perm)] THEN
        PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL Lemma1)] THEN
        REWRITE_TAC [SPEC "box" (CONJUNCT2 Raise)] ]);;

% --------------------------------------------------------------------------- %
% Prove that whatever goes up may come down in equal proportions, i.e.   (95) %
% for all m,n:   (Counter m) satifies [{up}](n) (<{down}>(n) tt).             %
% --------------------------------------------------------------------------- %
let Counter_Proof =
     prove_thm
      (`Counter_Proof`,
       "!n m. SAT (Counter m) (Raise box {label(name `up`)} n   
                                 (Raise dmd {label(name `down`)} n tt))",
       INDUCT_TAC THENL
       [REWRITE_TAC [Raise; SAT_tt]
        ;
        PURE_ONCE_REWRITE_TAC [Key_Lemma] THEN             % apply ind. hp.%
        ASM_REWRITE_TAC[] ]);;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;
 
