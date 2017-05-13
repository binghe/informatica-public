% =========================================================================== %
% FILE          : rec_strong_laws.ml                                          %
% DESCRIPTION   : Laws for the recursion operator and strong equivalence      %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : March 1992                                                  %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `rec_strong_laws`;;

% --------------------------------------------------------------------------- %
% The unfolding law R1 for strong equivalence:                          (290) %
% STRONG_UNFOLDING: |- !X E. STRONG_EQUIV (rec X E) (CCS_Subst E (rec X E) X) %
% --------------------------------------------------------------------------- %
let STRONG_UNFOLDING =
     prove_thm
      (`STRONG_UNFOLDING`,
       "!X E. STRONG_EQUIV (rec X E) (CCS_Subst E (rec X E) X)", 
       REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN 
       EXISTS_TAC
       "\x y. (x = y) \/ 
              (?Y E'. (x = rec Y E') /\ (y = CCS_Subst E' (rec Y E') Y))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN
        EXISTS_TAC "X: string" THEN EXISTS_TAC "E: CCS" THEN REWRITE_TAC[]
        ;
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL 
        [EXISTS_TAC "E1: CCS" THEN
         REWRITE_TAC [REWRITE_RULE [ASSUME "E: CCS = E'"]
                             (ASSUME "TRANS E u E1")] 
         ;
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]
         ;
         EXISTS_TAC "E1: CCS" THEN 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E = rec Y E''"] 
                            (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_REC THEN ASM_REWRITE_TAC[] 
         ; 
         EXISTS_TAC "E2: CCS" THEN  
         ASM_REWRITE_TAC 
         [REWRITE_RULE [ASSUME "E' = CCS_Subst E''(rec Y E'')Y"]  
                 (ASSUME "TRANS E' u E2"); TRANS_REC_EQ] ]]);;

% --------------------------------------------------------------------------- %
% Prove the theorem STRONG_PREF_REC_EQUIV:                             (1104) %
%  |- !u s v.                                                                 % 
%      STRONG_EQUIV                                                           % 
%      (prefix u(rec s(prefix v(prefix u(var s)))))                           % 
%      (rec s(prefix u(prefix v(var s))))                                     % 
% --------------------------------------------------------------------------- %
let STRONG_PREF_REC_EQUIV = 
     prove_thm 
      (`STRONG_PREF_REC_EQUIV`, 
       "!u s v.
         STRONG_EQUIV  
         (prefix u (rec s (prefix v (prefix u (var s))))) 
         (rec s (prefix u (prefix v (var s))))",     
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC 
       "\x y. 
        (?u' v' s'.  
          (x = prefix u'(rec s'(prefix v'(prefix u'(var s'))))) /\ 
          (y = rec s'(prefix u'(prefix v'(var s')))) \/ 
          (x = rec s'(prefix v'(prefix u'(var s')))) /\ 
          (y = prefix v'(rec s'(prefix u'(prefix v'(var s'))))))" THEN
       CONJ_TAC THENL 
       [BETA_TAC THEN EXISTS_TAC "u: Action" THEN 
        EXISTS_TAC "v: Action" THEN EXISTS_TAC "s: string" THEN REWRITE_TAC[] 
        ; 
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE 
               [ASSUME "E = prefix u'(rec s'(prefix v'(prefix u'(var s'))))"]
                                 (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_PREFIX THEN
         EXISTS_TAC "prefix v'(rec s'(prefix u'(prefix v'(var s'))))" THEN 
         CONJ_TAC THENL 
         [ASM_REWRITE_TAC[] THEN REC_TAC THEN REWRITE_TAC [CCS_Subst; PREFIX] 
          ; 
          EXISTS_TAC "u': Action" THEN EXISTS_TAC "v': Action" THEN 
          EXISTS_TAC "s': string" THEN ASM_REWRITE_TAC[] ] 
         ; 
         ASSUME_TAC (REWRITE_RULE 
                     [ASSUME "E' = rec s'(prefix u'(prefix v'(var s')))"; 
                      TRANS_REC_EQ; CCS_Subst] 
                            (ASSUME "TRANS E' u E2")) THEN 
         IMP_RES_TAC TRANS_PREFIX THEN
         EXISTS_TAC "rec s'(prefix v'(prefix u(var s')))" THEN  
         CONJ_TAC THENL 
         [ASM_REWRITE_TAC [PREFIX] 
          ; 
          EXISTS_TAC "u: Action" THEN EXISTS_TAC "v': Action" THEN 
          EXISTS_TAC "s': string" THEN 
          ASM_REWRITE_TAC
          [REWRITE_RULE [ASSUME "u': Action = u"]  
           (ASSUME "E2 = prefix v'(rec s'(prefix u'(prefix v'(var s'))))")] ]
         ; 
         ASSUME_TAC (REWRITE_RULE
                     [ASSUME "E = rec s'(prefix v'(prefix u'(var s')))"; 
                      TRANS_REC_EQ; CCS_Subst] 
                            (ASSUME "TRANS E u E1")) THEN 
         IMP_RES_TAC TRANS_PREFIX THEN
         EXISTS_TAC "rec s'(prefix u'(prefix v'(var s')))" THEN 
         CONJ_TAC THENL 
         [ASM_REWRITE_TAC [PREFIX]  
          ; 
          EXISTS_TAC "u': Action" THEN EXISTS_TAC "v': Action" THEN
          EXISTS_TAC "s': string" THEN ASM_REWRITE_TAC[] ]   
         ; 
         ASSUME_TAC (REWRITE_RULE
             [ASSUME "E' = prefix v'(rec s'(prefix u'(prefix v'(var s'))))"] 
                                 (ASSUME "TRANS E' u E2")) THEN 
         IMP_RES_TAC TRANS_PREFIX THEN 
         EXISTS_TAC "prefix u'(rec s'(prefix v'(prefix u'(var s'))))" THEN 
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN REC_TAC THEN REWRITE_TAC [CCS_Subst; PREFIX]
          ; 
          EXISTS_TAC "u': Action" THEN EXISTS_TAC "v': Action" THEN
          EXISTS_TAC "s': string" THEN ASM_REWRITE_TAC[] ] ]]);;   

% --------------------------------------------------------------------------- %
% Prove the theorem STRONG_REC_ACT2:                                   (1353) %
%  |- !s u.                                                                   %
%      STRONG_EQUIV                                                           %
%      (rec s(prefix u(prefix u(var s))))                                     %
%      (rec s(prefix u(var s)))                                               %
% --------------------------------------------------------------------------- %
let STRONG_REC_ACT2 =
     prove_thm
      (`STRONG_REC_ACT2`,
       "!s u.
         STRONG_EQUIV
         (rec s (prefix u (prefix u (var s))))
         (rec s (prefix u (var s)))",
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y.
        (?s' u'.
          (x = rec s'(prefix u'(prefix u'(var s')))) /\
          (y = rec s'(prefix u'(var s'))) \/
          (x = prefix u'(rec s'(prefix u'(prefix u'(var s'))))) /\ 
          (y = rec s'(prefix u'(var s'))))" THEN 
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "s: string" THEN 
        EXISTS_TAC "u: Action" THEN REWRITE_TAC[] 
        ;
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE
                     [ASSUME "E = rec s'(prefix u'(prefix u'(var s')))"; 
                      TRANS_REC_EQ; CCS_Subst]
                         (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E': CCS" THEN 
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN REC_TAC THEN REWRITE_TAC [CCS_Subst; PREFIX]
          ;
          EXISTS_TAC "s': string" THEN EXISTS_TAC "u': Action" THEN 
          ASM_REWRITE_TAC[] ]
         ;
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = rec s'(prefix u'(var s'))";
                                   TRANS_REC_EQ; CCS_Subst]
                            (ASSUME "TRANS E' u E2")) THEN
         IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "prefix u' E" THEN 
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN REC_TAC THEN REWRITE_TAC [CCS_Subst; PREFIX] 
          ;
          EXISTS_TAC "s': string" THEN EXISTS_TAC "u': Action" THEN 
          ASM_REWRITE_TAC[] ]
         ;
         ASSUME_TAC (REWRITE_RULE
               [ASSUME "E = prefix u'(rec s'(prefix u'(prefix u'(var s'))))"]
                                 (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E': CCS" THEN 
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN REC_TAC THEN REWRITE_TAC [CCS_Subst; PREFIX]
          ;
          EXISTS_TAC "s': string" THEN EXISTS_TAC "u': Action" THEN 
          ASM_REWRITE_TAC[] ] 
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = rec s'(prefix u'(var s'))";
                                   TRANS_REC_EQ; CCS_Subst] 
                            (ASSUME "TRANS E' u E2")) THEN 
         IMP_RES_TAC TRANS_PREFIX THEN 
         EXISTS_TAC "rec s'(prefix u'(prefix u'(var s')))" THEN  
         CONJ_TAC THENL
         [ASM_REWRITE_TAC [PREFIX]  
          ;
          EXISTS_TAC "s': string" THEN EXISTS_TAC "u': Action" THEN
          ASM_REWRITE_TAC[] ] ]]);;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

 
