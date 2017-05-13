% =========================================================================== %
% FILE          : parallel.ml                                                 %
% DESCRIPTION   : The law for the parallel operator (wrt strong equivalence)  %
%                 in the general form                                         %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : November 1994                                               %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `parallel`;;

% --------------------------------------------------------------------------- %
% PREF_ACT: |- !u E. PREF_ACT(prefix u E) = u                           (127) %
% --------------------------------------------------------------------------- % 
let PREF_ACT =
     new_recursive_definition
      false CCS `PREF_ACT` "PREF_ACT (prefix u E) = u";;

% --------------------------------------------------------------------------- %
% PREF_PROC: |- !u E. PREF_PROC(prefix u E) = E                         (127) %
% --------------------------------------------------------------------------- % 
let PREF_PROC =
     new_recursive_definition
      false CCS `PREF_PROC` "PREF_PROC (prefix u E) = E";;

% --------------------------------------------------------------------------- %
% Prefixed agents.                                                       (14) %
% --------------------------------------------------------------------------- %
let Is_Prefix =
     new_definition(`Is_Prefix`, "Is_Prefix E = (?u E'. (E = prefix u E'))");;

let PREF_IS_PREFIX =
     prove_thm
      (`PREF_IS_PREFIX`,
       "!u E. Is_Prefix (prefix u E)",
       REPEAT GEN_TAC THEN
       REWRITE_TAC [Is_Prefix] THEN EXISTS_TAC "u: Action" THEN
       EXISTS_TAC "E: CCS" THEN REWRITE_TAC[]);;

% --------------------------------------------------------------------------- %
% Define the notation used for indexed summations:                      (176) %
% given a function f: num->CCS and an index n:num, the primitive recursive    %
% function SIGMA is such that SIGMA f n denotes the summation                 %
% (f 0) + (f 1) + ... + (f n).                                                %
% --------------------------------------------------------------------------- %
let SIGMA =
     new_prim_rec_definition
      (`SIGMA`,
       "(SIGMA f 0 = f 0) /\
        (SIGMA f (SUC n) = sum (SIGMA f n) (f (SUC n)))");;  

let [SIGMA_BASE; SIGMA_INDUCT] = 
    map (\(s,thm). save_thm(s, thm)) 
        (combine ([`SIGMA_BASE`; `SIGMA_INDUCT`], CONJUNCTS SIGMA));; 

% --------------------------------------------------------------------------- %
% Define the functions to compute the summation of the synchronizing summands %
% of two summations of prefixed processes in parallel.                        %
% SYNC computes the synchronizations between a summand u.P and the summation  %
% f: num -> CCS representing the other process in parallel.             (303) %
% --------------------------------------------------------------------------- %
let SYNC =
     new_prim_rec_definition
      (`SYNC`,
       "(SYNC u P f 0 = (((u = tau) \/ (PREF_ACT(f 0) = tau)) => nil | 
                         ((LABEL u = COMPL(LABEL(PREF_ACT(f 0)))) =>
                            (prefix tau (par P (PREF_PROC(f 0)))) | nil))) /\ 
        (SYNC u P f (SUC n) =
         (((u = tau) \/ (PREF_ACT(f (SUC n)) = tau)) => (SYNC u P f n) | 
           ((LABEL u = COMPL(LABEL(PREF_ACT(f (SUC n))))) =>
            (sum (prefix tau (par P (PREF_PROC(f (SUC n))))) (SYNC u P f n)) | 
            (SYNC u P f n))))");;

let [SYNC_BASE; SYNC_INDUCT] = 
    map (\(s,thm). save_thm(s, thm)) 
        (combine ([`SYNC_BASE`; `SYNC_INDUCT`], CONJUNCTS SYNC));;

% --------------------------------------------------------------------------- %
% ALL_SYNC computes the summation of all the possible synchronizations between%
% two process summations f, f': num -> CCS of length n, m respectively.       %
% This is done using the function SYNC.                                 (228) %
% --------------------------------------------------------------------------- %
let ALL_SYNC =
     new_prim_rec_definition
      (`ALL_SYNC`,
       "(ALL_SYNC f 0 f' m = SYNC (PREF_ACT(f 0)) (PREF_PROC(f 0)) f' m) /\
        (ALL_SYNC f (SUC n) f' m =
         sum (ALL_SYNC f n f' m) 
             (SYNC (PREF_ACT(f (SUC n))) (PREF_PROC(f (SUC n))) f' m))");; 

let [ALL_SYNC_BASE; ALL_SYNC_INDUCT] = 
    map (\(s,thm). save_thm(s, thm)) 
        (combine ([`ALL_SYNC_BASE`; `ALL_SYNC_INDUCT`], CONJUNCTS ALL_SYNC));;

% --------------------------------------------------------------------------- %
% LESS_SUC_LESS_EQ': |- !m n. m < (SUC n) = m <= n                       (36) %
% --------------------------------------------------------------------------- %
let LESS_SUC_LESS_EQ' =
     prove_thm (`LESS_SUC_LESS_EQ'`,
                "!m n. m < SUC n = m <= n",
                REWRITE_TAC [LESS_EQ; LESS_EQ_MONO]);;

let LESS_SUC_LESS_EQ = 
     save_thm(`LESS_SUC_LESS_EQ`, EQ_IMP_LR LESS_SUC_LESS_EQ');;

% --------------------------------------------------------------------------- %
% LESS_EQ_ZERO_EQ: |- !n. n <= 0 ==> (n = 0)                                  % 
% --------------------------------------------------------------------------- %
let LESS_EQ_ZERO_EQ = save_thm(`LESS_EQ_ZERO_EQ`, EQ_IMP_LR LESS_EQ_0);; 
 
% --------------------------------------------------------------------------- %
% LESS_EQ_LESS_EQ_SUC: |- !m n. m <= n ==> m <= (SUC n)                  (35) %
% --------------------------------------------------------------------------- %
let LESS_EQ_LESS_EQ_SUC =
     prove_thm (`LESS_EQ_LESS_EQ_SUC`,  
                "!m n. m <= n ==> (m <= (SUC n))", 
                REPEAT STRIP_TAC THEN 
                IMP_RES_TAC LESS_EQ_IMP_LESS_SUC THEN
                IMP_RES_TAC LESS_IMP_LESS_OR_EQ);;   

% --------------------------------------------------------------------------- %
% SIGMA_TRANS_THM_EQ:                                                   (345) %
% |- !n f u E. TRANS(SIGMA f n)u E = (?k. k <= n /\ TRANS(f k)u E)            %
% --------------------------------------------------------------------------- %
let SIGMA_TRANS_THM_EQ =
     prove_thm
      (`SIGMA_TRANS_THM_EQ`,
       "!n f u E.
         TRANS (SIGMA f n) u E = (?k. k <= n /\ TRANS (f k) u E)",
       INDUCT_TAC THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [LESS_EQ_0; SIGMA_BASE] THEN
        EQ_TAC THENL
        [DISCH_TAC THEN EXISTS_TAC "0" THEN ASM_REWRITE_TAC[]
         ;
         STRIP_TAC THEN 
         REWRITE_TAC [REWRITE_RULE [ASSUME "k = 0"]
                             (ASSUME "TRANS((f: num -> CCS) k)u E")] ]  
        ;
        REPEAT GEN_TAC THEN REWRITE_TAC [SIGMA_INDUCT; TRANS_SUM_EQ] THEN
        EQ_TAC THENL
        [STRIP_TAC THENL
         [STRIP_ASSUME_TAC
          (MATCH_MP (EQ_IMP_LR (ASSUME "!f u E. TRANS(SIGMA f n)u E = 
                                                (?k. k <= n /\ TRANS(f k)u E)"))
           (ASSUME "TRANS(SIGMA f n)u E")) THEN 
          IMP_RES_TAC LESS_EQ_LESS_EQ_SUC THEN
          EXISTS_TAC "k: num" THEN ASM_REWRITE_TAC[]
          ;
          EXISTS_TAC "SUC n" THEN ASM_REWRITE_TAC [LESS_EQ_REFL] ]
         ;
         STRIP_TAC THEN IMP_RES_TAC LESS_OR_EQ THENL
         [DISJ1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] THEN
          EXISTS_TAC "k: num" THEN IMP_RES_TAC LESS_SUC_LESS_EQ THEN
          ASM_REWRITE_TAC[]
          ;
          DISJ2_TAC THEN
          REWRITE_TAC [REWRITE_RULE [ASSUME "k = SUC n"]
                       (ASSUME "TRANS((f: num -> CCS) k)u E")] ] ]]);;

let SIGMA_TRANS_THM = 
     save_thm(`SIGMA_TRANS_THM`, EQ_IMP_LR SIGMA_TRANS_THM_EQ);;

% --------------------------------------------------------------------------- %
% SYNC_TRANS_THM_EQ:                                                   (2387) %
%  |- !m u P f v Q.                                                           %
%      TRANS(SYNC u P f m)v Q =                                               %
%      (?j l. j <= m /\ (u = label l) /\ (PREF_ACT(f j) = label(COMPL l)) /\  % 
%             (v = tau) /\ (Q = par P(PREF_PROC(f j))))                       % 
% --------------------------------------------------------------------------- %
let SYNC_TRANS_THM_EQ = 
     prove_thm
      (`SYNC_TRANS_THM_EQ`,
       "!m u P f v Q.
         TRANS(SYNC u P f m) v Q =
         (?j l. j <= m /\ 
                (u = label l) /\ (PREF_ACT(f j) = label (COMPL l)) /\
                (v = tau) /\ (Q = par P (PREF_PROC(f j))))", 
       INDUCT_TAC THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [LESS_EQ_0; SYNC_BASE] THEN  
        COND_CASES_TAC THENL
        [REWRITE_TAC [NIL_NO_TRANS] THEN STRIP_TAC THEN  
         DISJ_CASES_TAC (ASSUME "(u = tau) \/ (PREF_ACT(f 0) = tau)") THENL 
         [ASSUME_TAC (REWRITE_RULE [ASSUME "u = tau"] 
                             (ASSUME "u = label l")) THEN 
          IMP_RES_TAC Action_Distinct 
          ; 
          CHECK_ASSUME_TAC 
          (REWRITE_RULE [ASSUME "j = 0"; 
                         ASSUME "PREF_ACT((f: num -> CCS) 0) = tau"; 
                         Action_Distinct] 
           (ASSUME "PREF_ACT((f: num -> CCS) j) = label(COMPL l)")) ] 
         ; 
         STRIP_ASSUME_TAC 
         (REWRITE_RULE [DE_MORGAN_THM]
          (ASSUME "~((u = tau) \/ (PREF_ACT(f 0) = tau))")) THEN
         IMP_RES_TAC Action_No_Tau_Is_Label THEN 
         ASM_REWRITE_TAC [LABEL] THEN COND_CASES_TAC THENL   
         [EQ_TAC THENL 
          [DISCH_TAC THEN IMP_RES_TAC TRANS_PREFIX THEN 
           EXISTS_TAC "0" THEN EXISTS_TAC "L': Label" THEN 
           ASM_REWRITE_TAC [COMPL_COMPL]  
           ; 
           STRIP_TAC THEN ASM_REWRITE_TAC [PREFIX] ]  
          ; 
          REWRITE_TAC [NIL_NO_TRANS] THEN STRIP_TAC THEN  
          ASSUME_TAC (REWRITE_RULE [ASSUME "j = 0"; 
                                    ASSUME "PREF_ACT(f 0) = label L"]  
           (ASSUME "PREF_ACT((f: num -> CCS) j) = label(COMPL l)")) THEN 
          IMP_RES_TAC Action_One_One THEN 
          CHECK_ASSUME_TAC 
          (REWRITE_RULE [ASSUME "L = COMPL l"; COMPL_COMPL; 
                         ASSUME "L': Label = l"] 
                  (ASSUME "~(L' = COMPL L)")) ] ] ;
 %inductive case% 
        REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [SYNC_INDUCT] THEN
        COND_CASES_TAC THENL
        [EQ_TAC THENL
         [DISCH_TAC THEN 
          STRIP_ASSUME_TAC                              %apply ind. hp.%
          (MATCH_MP
           (EQ_IMP_LR (ASSUME "!u P f v Q.
                                TRANS(SYNC u P f m)v Q =
                                (?j l.
                                  j <= m /\ (u = label l) /\
                                  (PREF_ACT(f j) = label(COMPL l)) /\
                                  (v = tau) /\ (Q = par P(PREF_PROC(f j))))"))
           (ASSUME "TRANS(SYNC u P f m)v Q")) THEN 
          IMP_RES_TAC LESS_EQ_LESS_EQ_SUC THEN 
          EXISTS_TAC "j: num" THEN EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[] 
          ; 
          STRIP_TAC THEN 
          DISJ_CASES_TAC (ASSUME "(u = tau) \/ (PREF_ACT(f(SUC m)) = tau)") 
          THENL
          [CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct]
                                    (ASSUME "u = label l")) 
           ;
           ASM_REWRITE_TAC[] THEN IMP_RES_TAC LESS_OR_EQ THENL  
           [IMP_RES_TAC LESS_SUC_LESS_EQ THEN EXISTS_TAC "j: num" THEN 
            EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[]
            ; 
            CHECK_ASSUME_TAC
            (REWRITE_RULE [ASSUME "j = SUC m";
                           ASSUME "PREF_ACT((f: num -> CCS) (SUC m)) = tau"; 
                           Action_Distinct]
               (ASSUME "PREF_ACT((f: num -> CCS) j) = label(COMPL l)")) ]]]
         ;
         STRIP_ASSUME_TAC 
         (REWRITE_RULE [DE_MORGAN_THM]
          (ASSUME "~((u = tau) \/ (PREF_ACT(f(SUC m)) = tau))")) THEN
         IMP_RES_TAC Action_No_Tau_Is_Label THEN
         ASM_REWRITE_TAC [LABEL] THEN COND_CASES_TAC THENL  
         [EQ_TAC THENL 
          [DISCH_TAC THEN IMP_RES_TAC TRANS_SUM THENL      
           [IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "SUC m" THEN
            EXISTS_TAC "L': Label" THEN 
            ASM_REWRITE_TAC [LESS_EQ_REFL; COMPL_COMPL]
            ;
            STRIP_ASSUME_TAC                              %apply ind. hp.%
            (MATCH_MP
             (EQ_IMP_LR (ASSUME "!u P f v Q.
                                  TRANS(SYNC u P f m)v Q =
                                  (?j l.
                                    j <= m /\ (u = label l) /\
                                    (PREF_ACT(f j) = label(COMPL l)) /\
                                    (v = tau) /\ (Q = par P(PREF_PROC(f j))))"))
             (ASSUME "TRANS(SYNC(label L')P f m)v Q")) THEN 
            IMP_RES_TAC LESS_EQ_LESS_EQ_SUC THEN
            EXISTS_TAC "j: num" THEN EXISTS_TAC "l: Label" THEN 
            ASM_REWRITE_TAC[] ]  
           ;
           STRIP_TAC THEN IMP_RES_TAC LESS_OR_EQ THENL 
           [SUM2_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] THEN
            IMP_RES_TAC LESS_SUC_LESS_EQ THEN EXISTS_TAC "j: num" THEN 
            EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[] 
            ;
            SUM1_TAC THEN 
            ASM_REWRITE_TAC 
            [REWRITE_RULE [ASSUME "j = SUC m"] 
             (ASSUME "Q = par P(PREF_PROC((f: num -> CCS) j))"); PREFIX] ]] 
         ; 
         ASM_REWRITE_TAC[] THEN EQ_TAC THENL
         [STRIP_TAC THEN IMP_RES_TAC LESS_EQ_LESS_EQ_SUC THEN
          EXISTS_TAC "j: num" THEN EXISTS_TAC "l: Label" THEN 
          ASM_REWRITE_TAC[]                               %apply ind. hp.% 
          ;
          STRIP_TAC THEN IMP_RES_TAC LESS_OR_EQ THENL  
          [IMP_RES_TAC LESS_SUC_LESS_EQ THEN EXISTS_TAC "j: num" THEN 
           EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[] 
           ;
           ASSUME_TAC (REWRITE_RULE [ASSUME "j = SUC m"; 
                                     ASSUME "PREF_ACT(f(SUC m)) = label L"]   
           (ASSUME "PREF_ACT((f: num -> CCS) j) = label(COMPL l)")) THEN 
           IMP_RES_TAC Action_One_One THEN
           CHECK_ASSUME_TAC 
           (REWRITE_RULE [ASSUME "L = COMPL l"; COMPL_COMPL; 
                          ASSUME "L': Label = l"]
            (ASSUME "~(L' = COMPL L)")) ]]]]]);; 

let SYNC_TRANS_THM = save_thm(`SYNC_TRANS_THM`, EQ_IMP_LR SYNC_TRANS_THM_EQ);;
 
% --------------------------------------------------------------------------- %
% ALL_SYNC_TRANS_THM_EQ:                                                (948) %
% |- !n m f f' u E.                                                           %
%     TRANS(ALL_SYNC f n f' m)u E =                                           %
%     (?k k' l.                                                               %
%       k <= n /\ k' <= m /\                                                  % 
%       (PREF_ACT(f k) = label l) /\ (PREF_ACT(f' k') = label(COMPL l)) /\    %
%       (u = tau) /\ (E = par(PREF_PROC(f k))(PREF_PROC(f' k'))))             % 
% --------------------------------------------------------------------------- % 
let ALL_SYNC_TRANS_THM_EQ =
     prove_thm
      (`ALL_SYNC_TRANS_THM_EQ`,
       "!n m f f' u E.
         TRANS (ALL_SYNC f n f' m) u E =
         (?k k' l. 
           k <= n /\ k' <= m /\
           (PREF_ACT(f k) = label l) /\ 
           (PREF_ACT(f' k') = label (COMPL l)) /\ 
           (u = tau) /\ (E = par(PREF_PROC(f k))(PREF_PROC(f' k'))))", 
       INDUCT_TAC THENL
       [REPEAT GEN_TAC THEN 
        REWRITE_TAC [LESS_EQ_0; ALL_SYNC_BASE; SYNC_TRANS_THM_EQ] THEN 
        EQ_TAC THENL 
        [STRIP_TAC THEN EXISTS_TAC "0" THEN EXISTS_TAC "j: num" THEN  
         EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[]
         ; 
         STRIP_TAC THEN 
         ASSUME_TAC (REWRITE_RULE [ASSUME "k = 0"] 
               (ASSUME "PREF_ACT((f: num -> CCS) k) = label l")) THEN  
         ASSUME_TAC (REWRITE_RULE [ASSUME "k = 0"]
               (ASSUME "E = par(PREF_PROC((f: num -> CCS) k))
                               (PREF_PROC((f': num -> CCS) k'))")) THEN 
         EXISTS_TAC "k': num" THEN EXISTS_TAC "l: Label" THEN   
         ASM_REWRITE_TAC[] ]     
        ; 
%inductive case% 
        REPEAT GEN_TAC THEN REWRITE_TAC [ALL_SYNC_INDUCT; TRANS_SUM_EQ] THEN
        EQ_TAC THENL
        [STRIP_TAC THENL
         [STRIP_ASSUME_TAC                                    %apply ind. hp%
          (MATCH_MP
           (EQ_IMP_LR 
            (ASSUME "!m f f' u E.
                      TRANS(ALL_SYNC f n f' m)u E =
                      (?k k' l.
                        k <= n /\ k' <= m /\ 
                        (PREF_ACT(f k) = label l) /\
                        (PREF_ACT(f' k') = label(COMPL l)) /\
                        (u = tau) /\
                        (E = par(PREF_PROC(f k))(PREF_PROC(f' k'))))"))
            (ASSUME "TRANS(ALL_SYNC f n f' m)u E")) THEN   
          IMP_RES_TAC LESS_EQ_LESS_EQ_SUC THEN 
          EXISTS_TAC "k: num" THEN EXISTS_TAC "k': num" THEN 
          EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[] 
          ;
          IMP_RES_TAC SYNC_TRANS_THM THEN EXISTS_TAC "SUC n" THEN
          EXISTS_TAC "j: num" THEN EXISTS_TAC "l: Label" THEN 
          ASM_REWRITE_TAC [LESS_EQ_REFL] ]
         ;
         STRIP_TAC THEN
         IMP_RES_TAC (SPECL ["k: num"; "SUC n"] LESS_OR_EQ) THENL
         [DISJ1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] THEN
          IMP_RES_TAC LESS_SUC_LESS_EQ THEN EXISTS_TAC "k: num" THEN
          EXISTS_TAC "k': num" THEN EXISTS_TAC "l: Label" THEN 
          ASM_REWRITE_TAC[]
          ;
          DISJ2_TAC THEN ASM_REWRITE_TAC [SYNC_TRANS_THM_EQ] THEN
          ASSUME_TAC (REWRITE_RULE [ASSUME "k = SUC n"]
                (ASSUME "PREF_ACT((f: num -> CCS) k) = label l")) THEN 
          ASSUME_TAC (REWRITE_RULE [ASSUME "k = SUC n"]
                (ASSUME "E = par(PREF_PROC((f: num -> CCS) k))
                                (PREF_PROC((f': num -> CCS) k'))")) THEN
          EXISTS_TAC "k': num" THEN EXISTS_TAC "l: Label" THEN 
          ASM_REWRITE_TAC[] ]]]);;      

let ALL_SYNC_TRANS_THM = 
     save_thm(`ALL_SYNC_TRANS_THM`, EQ_IMP_LR ALL_SYNC_TRANS_THM_EQ);;

% --------------------------------------------------------------------------- %
% The expansion law for strong equivalence.                            (2330) %
% --------------------------------------------------------------------------- %
let STRONG_PAR_LAW = 
     prove_thm 
      (`STRONG_PAR_LAW`, 
       "!f n f' m.
         (!i. i <= n ==> Is_Prefix(f i)) /\ (!j. j <= m ==> Is_Prefix(f' j)) ==>
         STRONG_EQUIV
         (par (SIGMA f n) (SIGMA f' m))
         (sum
          (sum 
           (SIGMA (\i. prefix (PREF_ACT(f i))
                              (par (PREF_PROC(f i)) (SIGMA f' m))) n)
           (SIGMA (\j. prefix (PREF_ACT(f' j))
                              (par (SIGMA f n) (PREF_PROC(f' j)))) m))
          (ALL_SYNC f n f' m))", 
       REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN   
       EXISTS_TAC
       "\x y. 
        (x = y) \/ 
        (?f1 n1 f2 m2. 
         (!i. i <= n1 ==> Is_Prefix(f1 i)) /\ 
         (!j. j <= m2 ==> Is_Prefix(f2 j)) /\ 
         (x = par(SIGMA f1 n1)(SIGMA f2 m2)) /\  
         (y = sum
              (sum
               (SIGMA (\i. prefix(PREF_ACT(f1 i))
                                 (par(PREF_PROC(f1 i))(SIGMA f2 m2))) n1)
               (SIGMA (\j. prefix(PREF_ACT(f2 j))  
                                 (par(SIGMA f1 n1)(PREF_PROC(f2 j)))) m2))
              (ALL_SYNC f1 n1 f2 m2)))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "f: num -> CCS" THEN 
        EXISTS_TAC "n: num" THEN EXISTS_TAC "f': num -> CCS" THEN 
        EXISTS_TAC "m: num" THEN ASM_REWRITE_TAC[] 
        ;
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E: CCS = E'"]
                            (ASSUME "TRANS E u E1")) THEN
         EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[]
         ;
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]
         ;
         EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] THEN
         ASSUME_TAC 
         (REWRITE_RULE [ASSUME "E = par(SIGMA f1 n1)(SIGMA f2 m2)"] 
                 (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [SUM1_TAC THEN SUM1_TAC THEN
          PURE_ONCE_REWRITE_TAC [SIGMA_TRANS_THM_EQ] THEN BETA_TAC THEN 
          IMP_RES_TAC SIGMA_TRANS_THM THEN EXISTS_TAC "k: num" THEN  
          STRIP_ASSUME_TAC
          (REWRITE_RULE [Is_Prefix]
           (MATCH_MP (ASSUME "!i. i <= n1 ==> Is_Prefix(f1 i)") 
            (ASSUME "k <= n1"))) THEN 
          ASSUME_TAC
          (REWRITE_RULE [ASSUME "(f1: num -> CCS)k = prefix u' E''"]
           (ASSUME "TRANS ((f1: num -> CCS)k)u E1'")) THEN
          IMP_RES_TAC TRANS_PREFIX THEN  
          ASM_REWRITE_TAC [PREF_ACT; PREF_PROC; PREFIX]
          ; 
          SUM1_TAC THEN SUM2_TAC THEN 
          PURE_ONCE_REWRITE_TAC [SIGMA_TRANS_THM_EQ] THEN BETA_TAC THEN 
          IMP_RES_TAC SIGMA_TRANS_THM THEN EXISTS_TAC "k: num" THEN  
          STRIP_ASSUME_TAC
          (REWRITE_RULE [Is_Prefix]
           (MATCH_MP (ASSUME "!j. j <= m2 ==> Is_Prefix(f2 j)")
            (ASSUME "k <= m2"))) THEN
          ASSUME_TAC
          (REWRITE_RULE [ASSUME "(f2: num -> CCS)k = prefix u' E''"]
           (ASSUME "TRANS ((f2: num -> CCS)k)u E1'")) THEN
          IMP_RES_TAC TRANS_PREFIX THEN 
          ASM_REWRITE_TAC [PREF_ACT; PREF_PROC; PREFIX]
          ; 
          SUM2_TAC THEN ASM_REWRITE_TAC [ALL_SYNC_TRANS_THM_EQ] THEN  
          IMP_RES_TAC SIGMA_TRANS_THM THEN 
          STRIP_ASSUME_TAC
          (REWRITE_RULE [Is_Prefix]
           (MATCH_MP (ASSUME "!j. j <= m2 ==> Is_Prefix(f2 j)")
            (ASSUME "k <= m2"))) THEN 
          STRIP_ASSUME_TAC
          (REWRITE_RULE [Is_Prefix]
           (MATCH_MP (ASSUME "!i. i <= n1 ==> Is_Prefix(f1 i)")
            (ASSUME "k' <= n1"))) THEN
          ASSUME_TAC
          (REWRITE_RULE [ASSUME "(f2: num -> CCS)k = prefix u' E''"]
           (ASSUME "TRANS ((f2: num -> CCS)k)(label(COMPL l))E2")) THEN
          ASSUME_TAC
          (REWRITE_RULE [ASSUME "(f1: num -> CCS)k' = prefix u'' E'''"]
           (ASSUME "TRANS ((f1: num -> CCS)k')(label l)E1'")) THEN
          IMP_RES_TAC TRANS_PREFIX THEN 
          EXISTS_TAC "k': num" THEN EXISTS_TAC "k: num" THEN 
          EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC [PREF_ACT; PREF_PROC] ]  
         ;  
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] THEN
         ASSUME_TAC 
         (REWRITE_RULE
          [ASSUME "E' =
                   sum
                   (sum
                    (SIGMA 
                     (\i. prefix(PREF_ACT(f1 i))
                                (par(PREF_PROC(f1 i))(SIGMA f2 m2))) n1)  
                    (SIGMA
                     (\j. prefix(PREF_ACT(f2 j))
                                (par(SIGMA f1 n1)(PREF_PROC(f2 j)))) m2)) 
                   (ALL_SYNC f1 n1 f2 m2)"] 
         (ASSUME "TRANS E' u E2")) THEN
         IMP_RES_TAC TRANS_SUM THENL
         [IMP_RES_TAC 
          (SPECL ["SIGMA 
                   (\i. prefix(PREF_ACT(f1 i))
                              (par(PREF_PROC(f1 i))(SIGMA f2 m2))) n1"; 
                  "SIGMA 
                   (\j. prefix(PREF_ACT(f2 j))
                              (par(SIGMA f1 n1)(PREF_PROC(f2 j)))) m2"; 
                  "u: Action"; 
                  "E2: CCS"] TRANS_SUM) THENL             % 2 subgoals %  
          [IMP_RES_TAC SIGMA_TRANS_THM THEN 
           ASSUME_TAC
           (BETA_RULE
            (ASSUME "TRANS 
                     ((\i: num.
                        prefix(PREF_ACT(f1 i))
                              (par(PREF_PROC(f1 i))(SIGMA f2 m2))) k) u E2")) 
           THEN IMP_RES_TAC TRANS_PREFIX THEN 
           STRIP_ASSUME_TAC
           (REWRITE_RULE [Is_Prefix]
            (MATCH_MP (ASSUME "!i. i <= n1 ==> Is_Prefix(f1 i)") 
             (ASSUME "k <= n1"))) THEN
           ASM_REWRITE_TAC[] THEN PAR1_TAC THEN 
           REWRITE_TAC [SIGMA_TRANS_THM_EQ] THEN EXISTS_TAC "k: num" THEN   
           ASM_REWRITE_TAC [PREF_ACT; PREF_PROC; PREFIX] 
           ; 
           IMP_RES_TAC SIGMA_TRANS_THM THEN
           ASSUME_TAC
           (BETA_RULE
            (ASSUME "TRANS  
                     ((\j: num.
                        prefix(PREF_ACT(f2 j))
                              (par(SIGMA f1 n1)(PREF_PROC(f2 j)))) k) u E2"))  
           THEN IMP_RES_TAC TRANS_PREFIX THEN 
           STRIP_ASSUME_TAC
           (REWRITE_RULE [Is_Prefix]
            (MATCH_MP (ASSUME "!j. j <= m2 ==> Is_Prefix(f2 j)") 
             (ASSUME "k <= m2"))) THEN 
           ASM_REWRITE_TAC[] THEN PAR2_TAC THEN  
           REWRITE_TAC [SIGMA_TRANS_THM_EQ] THEN EXISTS_TAC "k: num" THEN
           ASM_REWRITE_TAC [PREF_ACT; PREF_PROC; PREFIX] ]
          ; 
          IMP_RES_TAC ALL_SYNC_TRANS_THM THEN ASM_REWRITE_TAC[] THEN  
          PAR3_TAC THEN EXISTS_TAC "l: Label" THEN  
          REWRITE_TAC [SIGMA_TRANS_THM_EQ] THEN 
          CONJ_TAC THENL 
          [EXISTS_TAC "k: num" THEN 
           STRIP_ASSUME_TAC
           (REWRITE_RULE [Is_Prefix]
            (MATCH_MP (ASSUME "!i. i <= n1 ==> Is_Prefix(f1 i)")
             (ASSUME "k <= n1"))) THEN
           ASSUME_TAC
           (REWRITE_RULE [ASSUME "(f1: num -> CCS)k = prefix u' E''"; PREF_ACT]
            (ASSUME "PREF_ACT((f1: num -> CCS) k) = label l")) THEN 
           ASM_REWRITE_TAC [PREF_PROC; PREFIX]  
           ;     
           EXISTS_TAC "k': num" THEN 
           STRIP_ASSUME_TAC
           (REWRITE_RULE [Is_Prefix]
            (MATCH_MP (ASSUME "!j. j <= m2 ==> Is_Prefix(f2 j)")
             (ASSUME "k' <= m2"))) THEN
           ASSUME_TAC
           (REWRITE_RULE [ASSUME "(f2: num -> CCS)k' = prefix u' E''"; PREF_ACT]
            (ASSUME "PREF_ACT((f2: num -> CCS) k') = label(COMPL l)")) THEN  
           ASM_REWRITE_TAC [PREF_PROC; PREFIX] ] ]]]);;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

