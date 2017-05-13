% =========================================================================== %
% FILE          : restr_strong_laws.ml                                        %
% DESCRIPTION   : Basic laws of strong equivalence for the restriction        %
%                 operator                                                    %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 3 March 1992                                                %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `restr_strong_laws`;;        

% --------------------------------------------------------------------------- %
% Prove STRONG_RESTR_NIL: |- !L. STRONG_EQUIV(restr nil L)nil           (149) %
% --------------------------------------------------------------------------- %
let STRONG_RESTR_NIL =
     prove_thm
      (`STRONG_RESTR_NIL`,
       "!L. STRONG_EQUIV (restr nil L) nil",
       GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC "\x y. (?L'. (x = restr nil L') /\ (y = nil))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "L: (Label)set" THEN REWRITE_TAC[]   
        ; 
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN     
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E = restr nil L'"]
                            (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC RESTR_NIL_NO_TRANS 
         ;
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = nil"]
                            (ASSUME "TRANS E' u E2")) THEN
         IMP_RES_TAC NIL_NO_TRANS] ]);;

% --------------------------------------------------------------------------- %
% Prove STRONG_RESTR_SUM:                                               (809) %
%  |- !E E' L. STRONG_EQUIV(restr(sum E E')L)(sum(restr E L)(restr E' L))     %
% --------------------------------------------------------------------------- %
let STRONG_RESTR_SUM =
     prove_thm
      (`STRONG_RESTR_SUM`,
       "!E E' L. 
         STRONG_EQUIV (restr (sum E E') L) (sum (restr E L) (restr E' L))",  
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [PROPERTY_STAR] THEN
       REPEAT STRIP_TAC THENL
       [EXISTS_TAC "E1: CCS" THEN REWRITE_TAC [STRONG_EQUIV_REFL] THEN 
        IMP_RES_TAC TRANS_RESTR THENL 
        [IMP_RES_TAC TRANS_SUM THENL 
         [ASM_REWRITE_TAC[] THEN SUM1_TAC THEN RESTR_TAC THEN 
          REWRITE_TAC [REWRITE_RULE [ASSUME "u = tau"] 
                       (ASSUME "TRANS E u E''")] 
          ; 
          ASM_REWRITE_TAC[] THEN SUM2_TAC THEN RESTR_TAC THEN
          REWRITE_TAC [REWRITE_RULE [ASSUME "u = tau"] 
                       (ASSUME "TRANS E' u E''")] ] 
         ; 
         IMP_RES_TAC TRANS_SUM THENL 
         [ASM_REWRITE_TAC[] THEN SUM1_TAC THEN RESTR_TAC THEN 
          EXISTS_TAC "l: Label" THEN 
          ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "u = label l"] 
                           (ASSUME "TRANS E u E''")] 
          ; 
          ASM_REWRITE_TAC[] THEN SUM2_TAC THEN RESTR_TAC THEN 
          EXISTS_TAC "l: Label" THEN 
          ASM_REWRITE_TAC [REWRITE_RULE [ASSUME "u = label l"]
                           (ASSUME "TRANS E' u E''")] ] ] 
        ; 
        EXISTS_TAC "E2: CCS" THEN REWRITE_TAC [STRONG_EQUIV_REFL] THEN       
        IMP_RES_TAC TRANS_SUM THENL 
        [IMP_RES_TAC TRANS_RESTR THENL 
         [ASM_REWRITE_TAC[] THEN RESTR_TAC THEN REWRITE_TAC[] THEN SUM1_TAC THEN
          REWRITE_TAC [REWRITE_RULE [ASSUME "u = tau"] 
                       (ASSUME "TRANS E u E''")] 
          ; 
          ASM_REWRITE_TAC[] THEN RESTR_TAC THEN EXISTS_TAC "l: Label" THEN 
          ASM_REWRITE_TAC[] THEN SUM1_TAC THEN 
          REWRITE_TAC [REWRITE_RULE [ASSUME "u = label l"] 
                       (ASSUME "TRANS E u E''")] ] 
         ; 
         IMP_RES_TAC TRANS_RESTR THENL 
         [ASM_REWRITE_TAC[] THEN RESTR_TAC THEN REWRITE_TAC[] THEN SUM2_TAC THEN
          REWRITE_TAC [REWRITE_RULE [ASSUME "u = tau"]
                       (ASSUME "TRANS E' u E''")] 
          ; 
          ASM_REWRITE_TAC[] THEN RESTR_TAC THEN EXISTS_TAC "l: Label" THEN 
          ASM_REWRITE_TAC[] THEN SUM2_TAC THEN  
          REWRITE_TAC [REWRITE_RULE [ASSUME "u = label l"]
                       (ASSUME "TRANS E' u E''")] ] ]]);; 
 
% --------------------------------------------------------------------------- %
% Prove STRONG_RESTR_PREFIX_TAU:                                        (647) % 
%  |- !E L. STRONG_EQUIV(restr(prefix tau E)L)(prefix tau(restr E L))         %
% --------------------------------------------------------------------------- %
let STRONG_RESTR_PREFIX_TAU =
     prove_thm
      (`STRONG_RESTR_PREFIX_TAU`,
       "!E L.
         STRONG_EQUIV (restr (prefix tau E) L) (prefix tau (restr E L))",
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y. (x = y) \/ (?E' L'. (x = restr (prefix tau E') L') /\
                                  (y = prefix tau (restr E' L')))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "E: CCS" THEN
        EXISTS_TAC "L: (Label)set" THEN REWRITE_TAC[] 
        ;  
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN  
        REPEAT STRIP_TAC THENL
        [EXISTS_TAC "E1: CCS" THEN 
         REWRITE_TAC [REWRITE_RULE [ASSUME "E: CCS = E'"]
                             (ASSUME "TRANS E u E1")] 
         ; 
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
         ;  
         ASSUME_TAC (REWRITE_RULE [ASSUME "E = restr(prefix tau E'')L'"]
                            (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_RESTR THENL
         [IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E1: CCS" THEN    
          ASM_REWRITE_TAC [PREFIX] 
          ;
          IMP_RES_TAC TRANS_PREFIX THEN 
          CHECK_ASSUME_TAC 
          (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct] 
           (ASSUME "u = label l")) ] 
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = prefix tau(restr E'' L')"] 
                            (ASSUME "TRANS E' u E2")) THEN 
         IMP_RES_TAC TRANS_PREFIX THEN EXISTS_TAC "E2: CCS" THEN  
         ASM_REWRITE_TAC[] THEN RESTR_TAC THEN REWRITE_TAC [PREFIX] ]]);;

% --------------------------------------------------------------------------- %
% Prove STRONG_RESTR_PR_LAB_NIL:                                        (378) %
%  |- !l L.                                                                   %
%      l IN L \/ (COMPL l) IN L ==>                                           %
%      (!E. STRONG_EQUIV(restr(prefix(label l)E)L)nil)                        %
% --------------------------------------------------------------------------- %
let STRONG_RESTR_PR_LAB_NIL =
     prove_thm
      (`STRONG_RESTR_PR_LAB_NIL`,
       "!l L. 
         (l IN L) \/ ((COMPL l) IN L) ==>
         (!E. STRONG_EQUIV (restr (prefix (label l) E) L) nil)",
       REPEAT GEN_TAC THEN 
       DISCH_TAC THEN GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN 
       EXISTS_TAC "\x y. 
                    (?l' L' E'. ((l' IN L') \/ ((COMPL l') IN L')) /\ 
                                 (x = restr (prefix (label l') E') L') /\ 
                                 (y = nil))" THEN 
       CONJ_TAC THENL 
       [BETA_TAC THEN EXISTS_TAC "l: Label" THEN 
        EXISTS_TAC "L: (Label)set" THEN EXISTS_TAC "E: CCS" THEN 
        ASM_REWRITE_TAC[] 
        ; 
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN 
        REPEAT STRIP_TAC THENL 
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E = restr(prefix(label l')E'')L'"] 
                            (ASSUME "TRANS E u E1")) THEN  
         IMP_RES_TAC RESTR_LABEL_NO_TRANS 
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = nil"] 
                            (ASSUME "TRANS E' u E2")) THEN 
         IMP_RES_TAC NIL_NO_TRANS 
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E = restr(prefix(label l')E'')L'"]
                            (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC RESTR_LABEL_NO_TRANS 
         ; 
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = nil"]
                            (ASSUME "TRANS E' u E2")) THEN
         IMP_RES_TAC NIL_NO_TRANS ] ]);;   
 
% --------------------------------------------------------------------------- %
% Prove STRONG_RESTR_PREFIX_LABEL:                                      (643) %
%  |- !l L.                                                                   %
%      ~l IN L /\ ~(COMPL l) IN L ==>                                         %
%      (!E.                                                                   %
%        STRONG_EQUIV(restr(prefix(label l)E)L)(prefix(label l)(restr E L)))  %
% --------------------------------------------------------------------------- %
let STRONG_RESTR_PREFIX_LABEL =
     prove_thm
      (`STRONG_RESTR_PREFIX_LABEL`,
       "!l L. 
         (~l IN L /\ ~(COMPL l) IN L) ==>
         (!E. STRONG_EQUIV (restr (prefix (label l) E) L)
                           (prefix (label l) (restr E L)))",
       REPEAT STRIP_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC 
       "\x y. (x = y) \/
              (?l' L' E'. (~l' IN L') /\ (~(COMPL l') IN L') /\ 
                          (x = restr (prefix (label l') E') L') /\
                          (y = prefix (label l') (restr E' L')))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "l: Label" THEN 
        EXISTS_TAC "L: (Label)set" THEN EXISTS_TAC "E: CCS" THEN 
        ASM_REWRITE_TAC[]   
        ;
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN     
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E: CCS = E'"]
                            (ASSUME "TRANS E u E1")) THEN 
         EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] 
         ; 
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
         ;  
         EXISTS_TAC "E1: CCS" THEN REWRITE_TAC[] THEN    
         ASSUME_TAC (REWRITE_RULE [ASSUME "E = restr(prefix(label l')E'')L'"]
                            (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_RESTR THENL 
         [IMP_RES_TAC TRANS_PREFIX THEN    
          CHECK_ASSUME_TAC 
          (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct] 
           (ASSUME "u = label l'")) 
          ; 
          IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC [PREFIX] ] 
         ;  
         EXISTS_TAC "E2: CCS" THEN REWRITE_TAC[] THEN   
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = prefix(label l')(restr E'' L')"]
                            (ASSUME "TRANS E' u E2")) THEN
         IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC[] THEN RESTR_TAC THEN
         EXISTS_TAC "l': Label" THEN ASM_REWRITE_TAC [PREFIX] ]]);;    

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;    
 
