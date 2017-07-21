% =========================================================================== %
% FILE          : par_strong_laws.ml                                          %
% DESCRIPTION   : Basic laws of strong equivalence for the parallel operator  %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 4 March 1992                                                %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `par_strong_laws`;;

% --------------------------------------------------------------------------- %
% Prove STRONG_PAR_IDENT_R: |- !E. STRONG_EQUIV(par E nil)E             (250) %
% --------------------------------------------------------------------------- %
let STRONG_PAR_IDENT_R = 
     prove_thm
      (`STRONG_PAR_IDENT_R`, 
       "!E. STRONG_EQUIV (par E nil) E", 
       GEN_TAC THEN PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN 
       EXISTS_TAC "\x y. (?E'. (x = par E' nil) /\ (y = E'))" THEN 
       CONJ_TAC THENL 
       [BETA_TAC THEN EXISTS_TAC "E: CCS" THEN REWRITE_TAC[] 
        ; 
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN 
        REPEAT STRIP_TAC THENL   
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E = par E'' nil"]
                            (ASSUME "TRANS E u E1")) THEN    
         IMP_RES_TAC TRANS_PAR_P_NIL THEN EXISTS_TAC "E''': CCS" THEN 
         ASM_REWRITE_TAC[] THEN EXISTS_TAC "E''': CCS" THEN ASM_REWRITE_TAC[] 
         ;   
         EXISTS_TAC "par E2 nil" THEN CONJ_TAC THENL 
         [PURE_ONCE_ASM_REWRITE_TAC[] THEN PAR1_TAC THEN  
          ASSUME_TAC (REWRITE_RULE [ASSUME "E': CCS = E''"] 
                             (ASSUME "TRANS E' u E2")) THEN       
          PURE_ONCE_ASM_REWRITE_TAC[] ; 
          EXISTS_TAC "E2: CCS" THEN REWRITE_TAC[] ]]]);;  

% --------------------------------------------------------------------------- %
% Prove STRONG_PAR_COMM: |- !E E'. STRONG_EQUIV(par E E')(par E' E)     (663) %
% --------------------------------------------------------------------------- %
let STRONG_PAR_COMM =
     prove_thm
      (`STRONG_PAR_COMM`,
       "!E E'. STRONG_EQUIV (par E E') (par E' E)",
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN 
       EXISTS_TAC "\x y. (?E1 E2. (x = par E1 E2) /\ (y = par E2 E1))" THEN 
       CONJ_TAC THENL  
       [BETA_TAC THEN EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E': CCS" THEN 
        REWRITE_TAC[] 
        ; 
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN 
        REPEAT STRIP_TAC THENL 
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E = par E1 E2"]
                            (ASSUME "TRANS E u E1'")) THEN
         IMP_RES_TAC TRANS_PAR THENL  
         [EXISTS_TAC "par E2 E1''" THEN ASM_REWRITE_TAC[] THEN 
          CONJ_TAC THENL
          [PAR2_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;  
           EXISTS_TAC "E1'': CCS" THEN EXISTS_TAC "E2: CCS" THEN
           REWRITE_TAC[] ] 
          ; 
          EXISTS_TAC "par E1'' E1" THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
          [PAR1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
           EXISTS_TAC "E1: CCS" THEN EXISTS_TAC "E1'': CCS" THEN
           REWRITE_TAC[] ] 
          ; 
          EXISTS_TAC "par E2' E1''" THEN ASM_REWRITE_TAC[] THEN 
          CONJ_TAC THENL
          [PAR3_TAC THEN EXISTS_TAC "COMPL l" THEN
           ASM_REWRITE_TAC [COMPL_COMPL] ;   
           EXISTS_TAC "E1'': CCS" THEN EXISTS_TAC "E2': CCS" THEN
           REWRITE_TAC[] ] ]   
         ;  
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = par E2 E1"]
                            (ASSUME "TRANS E' u E2'")) THEN   
         IMP_RES_TAC TRANS_PAR THENL 
         [EXISTS_TAC "par E1 E1'" THEN ASM_REWRITE_TAC[] THEN 
          CONJ_TAC THENL
          [PAR2_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ; 
           EXISTS_TAC "E1: CCS" THEN EXISTS_TAC "E1': CCS" THEN 
           REWRITE_TAC[] ] 
          ;  
          EXISTS_TAC "par E1' E2" THEN ASM_REWRITE_TAC[] THEN 
          CONJ_TAC THENL
          [PAR1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
           EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E2: CCS" THEN
           REWRITE_TAC[] ] 
          ; 
          EXISTS_TAC "par E2'' E1'" THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
          [PAR3_TAC THEN EXISTS_TAC "COMPL l" THEN
           ASM_REWRITE_TAC [COMPL_COMPL] ;  
           EXISTS_TAC "E2'': CCS" THEN EXISTS_TAC "E1': CCS" THEN
           REWRITE_TAC[] ]]]]);;

% --------------------------------------------------------------------------- %
% Prove STRONG_PAR_IDENT_L: |- !E. STRONG_EQUIV(par nil E)E                   %
% --------------------------------------------------------------------------- %
let STRONG_PAR_IDENT_L =
     save_thm
      (`STRONG_PAR_IDENT_L`,
       GEN_ALL
       (S_TRANS (SPECL ["nil"; "E: CCS"] STRONG_PAR_COMM) 
                (SPEC "E: CCS" STRONG_PAR_IDENT_R)));; 

% --------------------------------------------------------------------------- %
% Prove STRONG_PAR_ASSOC:                                              (2022) %
%  |- !E E' E''. STRONG_EQUIV(par(par E E')E'')(par E(par E' E''))            %
% --------------------------------------------------------------------------- %
let STRONG_PAR_ASSOC =
     prove_thm
      (`STRONG_PAR_ASSOC`,
       "!E E' E''. STRONG_EQUIV (par (par E E') E'') (par E (par E' E''))",   
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC 
       "\x y. (?E1 E2 E3. 
               (x = par (par E1 E2) E3) /\ (y = par E1 (par E2 E3)))" THEN   
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E': CCS" THEN 
        EXISTS_TAC "E'': CCS" THEN REWRITE_TAC[]  
        ;
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E = par(par E1 E2)E3"]
                            (ASSUME "TRANS E u E1'")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [STRIP_ASSUME_TAC
          (MATCH_MP TRANS_PAR (ASSUME "TRANS(par E1 E2)u E1''")) THENL
          [EXISTS_TAC "par E1'''(par E2 E3)" THEN ASM_REWRITE_TAC[] THEN 
           CONJ_TAC THENL
           [PAR1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2: CCS" THEN 
            EXISTS_TAC "E3: CCS" THEN ASM_REWRITE_TAC[] ]
           ;
           EXISTS_TAC "par E1(par E1''' E3)" THEN ASM_REWRITE_TAC[] THEN 
           CONJ_TAC THENL
           [PAR2_TAC THEN PAR1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1: CCS" THEN EXISTS_TAC "E1''': CCS" THEN
            EXISTS_TAC "E3: CCS" THEN ASM_REWRITE_TAC[] ]
           ;
           EXISTS_TAC "par E1'''(par E2' E3)" THEN ASM_REWRITE_TAC[] THEN
           CONJ_TAC THENL
           [PAR3_TAC THEN EXISTS_TAC "l: Label" THEN
            ASM_REWRITE_TAC[] THEN PAR1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2': CCS" THEN
            EXISTS_TAC "E3: CCS" THEN ASM_REWRITE_TAC[] ] ]
          ;
          EXISTS_TAC "par E1(par E2 E1'')" THEN
          CONJ_TAC THENL
          [PURE_ONCE_ASM_REWRITE_TAC[] THEN PAR2_TAC THEN PAR2_TAC THEN
           PURE_ONCE_ASM_REWRITE_TAC[] ;
           EXISTS_TAC "E1: CCS" THEN EXISTS_TAC "E2: CCS" THEN 
           EXISTS_TAC "E1'': CCS" THEN ASM_REWRITE_TAC[] ]
          ;
          STRIP_ASSUME_TAC
          (MATCH_MP TRANS_PAR (ASSUME "TRANS(par E1 E2)(label l)E1''")) THENL
          [EXISTS_TAC "par E1'''(par E2 E2')" THEN ASM_REWRITE_TAC[] THEN
           CONJ_TAC THENL
           [PAR3_TAC THEN EXISTS_TAC "l: Label" THEN
            ASM_REWRITE_TAC[] THEN PAR2_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1''': CCS" THEN EXISTS_TAC "E2: CCS" THEN 
            EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[] ]
           ;
           EXISTS_TAC "par E1(par E1''' E2')" THEN ASM_REWRITE_TAC[] THEN
           CONJ_TAC THENL
           [PAR2_TAC THEN PAR3_TAC THEN EXISTS_TAC "l: Label" THEN
            ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1: CCS" THEN EXISTS_TAC "E1''': CCS" THEN 
            EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[] ]
           ;
           IMP_RES_TAC Action_Distinct_label ] ] 
         ;
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = par E1(par E2 E3)"] 
                            (ASSUME "TRANS E' u E2'")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [EXISTS_TAC "par(par E1' E2)E3" THEN ASM_REWRITE_TAC[] THEN 
          CONJ_TAC THENL
          [PAR1_TAC THEN PAR1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
           EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E2: CCS" THEN 
           EXISTS_TAC "E3: CCS" THEN ASM_REWRITE_TAC[] ]
          ;
          STRIP_ASSUME_TAC
          (MATCH_MP TRANS_PAR (ASSUME "TRANS(par E2 E3)u E1'")) THENL
          [EXISTS_TAC "par(par E1 E1'')E3" THEN ASM_REWRITE_TAC[] THEN
           CONJ_TAC THENL
           [PAR1_TAC THEN PAR2_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1: CCS" THEN EXISTS_TAC "E1'': CCS" THEN 
            EXISTS_TAC "E3: CCS" THEN ASM_REWRITE_TAC[] ]
           ;
           EXISTS_TAC "par(par E1 E2)E1''" THEN ASM_REWRITE_TAC[] THEN
           CONJ_TAC THENL
           [PAR2_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1: CCS" THEN EXISTS_TAC "E2: CCS" THEN
            EXISTS_TAC "E1'': CCS" THEN ASM_REWRITE_TAC[] ]
           ;
           EXISTS_TAC "par(par E1 E1'')E2''" THEN ASM_REWRITE_TAC[] THEN
           CONJ_TAC THENL
           [PAR3_TAC THEN EXISTS_TAC "l: Label" THEN ASM_REWRITE_TAC[] THEN
            PAR2_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1: CCS" THEN EXISTS_TAC "E1'': CCS" THEN 
            EXISTS_TAC "E2'': CCS" THEN ASM_REWRITE_TAC[] ] ]
          ;
          STRIP_ASSUME_TAC
          (MATCH_MP TRANS_PAR
           (ASSUME "TRANS(par E2 E3)(label(COMPL l))E2''")) THENL 
          [EXISTS_TAC "par(par E1' E1'')E3" THEN ASM_REWRITE_TAC[] THEN 
           CONJ_TAC THENL
           [PAR1_TAC THEN PAR3_TAC THEN EXISTS_TAC "l: Label" THEN
            ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E1'': CCS" THEN 
            EXISTS_TAC "E3: CCS" THEN ASM_REWRITE_TAC[] ]
           ;
           EXISTS_TAC "par(par E1' E2)E1''" THEN ASM_REWRITE_TAC[] THEN 
           CONJ_TAC THENL
           [PAR3_TAC THEN EXISTS_TAC "l: Label" THEN
            ASM_REWRITE_TAC[] THEN PAR1_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[] ;
            EXISTS_TAC "E1': CCS" THEN EXISTS_TAC "E2: CCS" THEN 
            EXISTS_TAC "E1'': CCS" THEN ASM_REWRITE_TAC[] ]
           ;
           IMP_RES_TAC Action_Distinct_label ] ]]]);;

% --------------------------------------------------------------------------- %
% Prove STRONG_PAR_PREF_TAU:                                            (711) %
%  |- !u E E'.                                                                %
%      STRONG_EQUIV(par(prefix u E)(prefix tau E'))                           %
%                  (sum(prefix u(par E(prefix tau E')))                       %
%                      (prefix tau(par(prefix u E)E')))                       %
% --------------------------------------------------------------------------- %
let STRONG_PAR_PREF_TAU = 
     prove_thm
      (`STRONG_PAR_PREF_TAU`,
       "!u E E'. 
         STRONG_EQUIV 
         (par (prefix u E) (prefix tau E'))
         (sum (prefix u (par E (prefix tau E')))
              (prefix tau (par (prefix u E) E')))", 
       REPEAT GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y. (x = y) \/ 
              (?u' E1 E2. (x = par (prefix u' E1) (prefix tau E2)) /\
                          (y = sum (prefix u' (par E1 (prefix tau E2)))
                                   (prefix tau (par (prefix u' E1) E2))))" THEN 
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "u: Action" THEN 
        EXISTS_TAC "E: CCS" THEN EXISTS_TAC "E': CCS" THEN REWRITE_TAC[]   
        ; 
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN 
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E: CCS = E'"] 
                            (ASSUME "TRANS E u E1")) THEN 
         EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[] 
         ;   
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
         ;  
         EXISTS_TAC "E1': CCS" THEN ASM_REWRITE_TAC[] THEN   
         ASSUME_TAC (REWRITE_RULE
                     [ASSUME "E = par(prefix u' E1)(prefix tau E2)"]
                            (ASSUME "TRANS E u E1'")) THEN
         IMP_RES_TAC TRANS_PAR THENL 
         [IMP_RES_TAC TRANS_PREFIX THEN SUM1_TAC THEN ASM_REWRITE_TAC [PREFIX]
          ;
          IMP_RES_TAC TRANS_PREFIX THEN SUM2_TAC THEN ASM_REWRITE_TAC [PREFIX]
          ;  
          IMP_RES_TAC TRANS_PREFIX THEN IMP_RES_TAC Action_Distinct_label ]
         ; 
         EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[] THEN   
         ASSUME_TAC (REWRITE_RULE 
                     [ASSUME "E' = sum(prefix u'(par E1(prefix tau E2)))
                                      (prefix tau(par(prefix u' E1)E2))"]  
                            (ASSUME "TRANS E' u E2'")) THEN 
         IMP_RES_TAC TRANS_SUM THENL    
         [IMP_RES_TAC TRANS_PREFIX THEN PURE_ONCE_ASM_REWRITE_TAC[] THEN  
          PAR1_TAC THEN PREFIX_TAC 
          ; 
          IMP_RES_TAC TRANS_PREFIX THEN PURE_ONCE_ASM_REWRITE_TAC[] THEN 
          PAR2_TAC THEN PREFIX_TAC ]]]);;  

% --------------------------------------------------------------------------- %
% Prove STRONG_PAR_TAU_PREF:                                                  %
%  |- !E u E'.                                                                %
%      STRONG_EQUIV                                                           %
%      (par(prefix tau E)(prefix u E'))                                       %
%      (sum(prefix tau(par E(prefix u E')))(prefix u(par(prefix tau E)E')))   %
% --------------------------------------------------------------------------- %
let STRONG_PAR_TAU_PREF =
     save_thm
      (`STRONG_PAR_TAU_PREF`,
       GEN_ALL
       (S_TRANS 
        (S_TRANS 
          (S_TRANS 
            (SPECL ["prefix tau E"; "prefix u E'"] STRONG_PAR_COMM) 
            (SPECL ["u: Action"; "E': CCS"; "E: CCS"] STRONG_PAR_PREF_TAU))
          (SPECL ["prefix u(par E'(prefix tau E))"; 
                  "prefix tau(par(prefix u E')E)"] STRONG_SUM_COMM)) 
        (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM  
         (CONJ (SPEC "tau" 
                (MATCH_MP STRONG_EQUIV_SUBST_PREFIX
                 (SPECL ["prefix u E'"; "E: CCS"] STRONG_PAR_COMM))) 
               (SPEC "u: Action" 
                (MATCH_MP STRONG_EQUIV_SUBST_PREFIX  
                 (SPECL ["E': CCS"; "prefix tau E"] STRONG_PAR_COMM)))))));;
     
% --------------------------------------------------------------------------- %
% Prove STRONG_PAR_TAU_TAU:                                                   %
%  |- !E E'.                                                                  %
%      STRONG_EQUIV                                                           %
%      (par(prefix tau E)(prefix tau E'))                                     %
%      (sum(prefix tau(par E(prefix tau E')))(prefix tau(par(prefix tau E)E')))%
% --------------------------------------------------------------------------- %
let STRONG_PAR_TAU_TAU = 
     save_thm(`STRONG_PAR_TAU_TAU`, SPEC "tau" STRONG_PAR_PREF_TAU);;
 
% --------------------------------------------------------------------------- %
% Prove STRONG_PAR_PREF_NO_SYNCR:                                       (919) %
%  |- !l l'.                                                                  %
%      ~(l = COMPL l') ==>                                                    %
%      (!E E'.                                                                %
%        STRONG_EQUIV                                                         % 
%        (par(prefix(label l)E)(prefix(label l')E'))                          %
%        (sum(prefix(label l)(par E(prefix(label l')E')))                     %
%            (prefix(label l')(par(prefix(label l)E)E'))))                    %
% --------------------------------------------------------------------------- %
let STRONG_PAR_PREF_NO_SYNCR = 
     prove_thm 
      (`STRONG_PAR_PREF_NO_SYNCR`, 
       "!l l'. 
         ~(l = COMPL l') ==>
         (!E E'.     
           STRONG_EQUIV 
           (par (prefix (label l) E) (prefix (label l') E')) 
           (sum (prefix (label l) (par E (prefix (label l') E'))) 
                (prefix (label l') (par (prefix (label l) E) E'))))", 
       REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y. (x = y) \/
              (?l1 l2 E1 E2. ~(l1 = COMPL l2) /\  
               (x = par (prefix (label l1) E1) (prefix (label l2) E2)) /\
               (y = sum (prefix (label l1) (par E1 (prefix (label l2) E2))) 
                        (prefix (label l2) (par (prefix (label l1) E1) E2))))" 
       THEN CONJ_TAC THENL      
       [BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "l: Label" THEN 
        EXISTS_TAC "l': Label" THEN EXISTS_TAC "E: CCS" THEN 
        EXISTS_TAC "E': CCS" THEN ASM_REWRITE_TAC[] 
        ;  
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN     
        REPEAT STRIP_TAC THENL                                
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E: CCS = E'"] 
                            (ASSUME "TRANS E u E1")) THEN 
         EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[]    
         ;  
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[] 
         ;  
         EXISTS_TAC "E1': CCS" THEN ASM_REWRITE_TAC[] THEN   
         ASSUME_TAC (REWRITE_RULE
                     [ASSUME "E = par(prefix(label l1)E1)(prefix(label l2)E2)"]
                            (ASSUME "TRANS E u E1'")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [SUM1_TAC THEN IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC [PREFIX]
          ;
          SUM2_TAC THEN IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC [PREFIX]
          ;
          IMP_RES_TAC TRANS_PAR_NO_SYNCR THEN 
          ASSUME_TAC (REWRITE_RULE [ASSUME "u = tau"] 
                      (ASSUME "TRANS(par(prefix(label l1)E1)
                                        (prefix(label l2)E2))u E1'")) THEN 
          RES_TAC ]  
         ;  
         EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[] THEN  
         ASSUME_TAC (REWRITE_RULE
               [ASSUME "E' = sum 
                             (prefix(label l1)(par E1(prefix(label l2)E2))) 
                             (prefix(label l2)(par(prefix(label l1)E1)E2))"] 
                     (ASSUME "TRANS E' u E2'")) THEN   
         IMP_RES_TAC TRANS_SUM THEN 
         IMP_RES_TAC TRANS_PREFIX THEN PURE_ONCE_ASM_REWRITE_TAC[] THENL
         [PAR1_TAC ; PAR2_TAC] THEN PREFIX_TAC ]]);;

% --------------------------------------------------------------------------- %
% Prove STRONG_PAR_PREF_SYNCR:                                         (1274) %
%  |- !l l'.                                                                  %
%      (l = COMPL l') ==>                                                     %
%      (!E E'.                                                                %
%        STRONG_EQUIV                                                         %
%        (par(prefix(label l)E)(prefix(label l')E'))                          %
%        (sum                                                                 % 
%         (sum                                                                % 
%          (prefix(label l)(par E(prefix(label l')E')))                       % 
%          (prefix(label l')(par(prefix(label l)E)E')))                       % 
%         (prefix tau(par E E'))))                                            % 
% --------------------------------------------------------------------------- %
let STRONG_PAR_PREF_SYNCR =
     prove_thm
      (`STRONG_PAR_PREF_SYNCR`,
       "!l l'. 
         (l = COMPL l') ==>         
         (!E E'.
           STRONG_EQUIV 
           (par (prefix (label l) E) (prefix (label l') E'))
           (sum
            (sum (prefix (label l) (par E (prefix (label l') E')))
                 (prefix (label l') (par (prefix (label l) E) E')))
            (prefix tau (par E E'))))",    
       REPEAT STRIP_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC
       "\x y. (x = y) \/
              (?l1 l2 E1 E2. 
               (l1 = COMPL l2) /\    
               (x = par (prefix (label l1) E1) (prefix (label l2) E2)) /\
               (y = sum
                    (sum (prefix (label l1) (par E1 (prefix (label l2) E2)))
                         (prefix (label l2) (par (prefix (label l1) E1) E2)))
                    (prefix tau (par E1 E2))))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "l: Label" THEN 
        EXISTS_TAC "l': Label" THEN EXISTS_TAC "E: CCS" THEN     
        EXISTS_TAC "E': CCS" THEN ASM_REWRITE_TAC[]   
        ;
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN BETA_TAC THEN     
        REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E: CCS = E'"] 
                            (ASSUME "TRANS E u E1")) THEN 
         EXISTS_TAC "E1: CCS" THEN ASM_REWRITE_TAC[]       
         ; 
         EXISTS_TAC "E2: CCS" THEN ASM_REWRITE_TAC[]   
         ;   
         EXISTS_TAC "E1': CCS" THEN ASM_REWRITE_TAC[] THEN   
         ASSUME_TAC (REWRITE_RULE
                     [ASSUME "E = par(prefix(label l1)E1)(prefix(label l2)E2)"]
                            (ASSUME "TRANS E u E1'")) THEN
         IMP_RES_TAC TRANS_PAR THENL
         [SUM1_TAC THEN SUM1_TAC ; SUM1_TAC THEN SUM2_TAC ; SUM2_TAC] THEN
         IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC [PREFIX]
         ;
         EXISTS_TAC "E2': CCS" THEN ASM_REWRITE_TAC[] THEN   
         ASSUME_TAC (REWRITE_RULE
      	   [ASSUME "E' = sum(sum
                             (prefix(label l1)(par E1(prefix(label l2)E2)))
                             (prefix(label l2)(par(prefix(label l1)E1)E2)))
                            (prefix tau(par E1 E2))"]
                     (ASSUME "TRANS E' u E2'")) THEN
         IMP_RES_TAC TRANS_SUM THENL
         [IMP_RES_TAC TRANS_SUM THENL
          [IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC[] THEN
           PAR1_TAC THEN PREFIX_TAC
           ;
           IMP_RES_TAC TRANS_PREFIX THEN
           CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct] 
                             (ASSUME "u = label l1")) 
           ;
           IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC[] THEN
           PAR2_TAC THEN PREFIX_TAC
           ;
           IMP_RES_TAC TRANS_PREFIX THEN
           CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct]
                             (ASSUME "u = label l2")) ] 
          ;
          IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC[] THEN PAR3_TAC THEN
          EXISTS_TAC "COMPL l2" THEN REWRITE_TAC [COMPL_COMPL; PREFIX] ]]]);;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

