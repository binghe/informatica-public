% =========================================================================== %
% FILE          : relab_strong_laws.ml                                        %
% DESCRIPTION   : Basic axioms of strong equivalence for the relabelling      %
%                 operator                                                    %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 3 March 1992                                                %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `relab_strong_laws`;;

% --------------------------------------------------------------------------- %
% Prove STRONG_RELAB_NIL: |- !rf. STRONG_EQUIV(relab nil rf)nil         (149) %
% --------------------------------------------------------------------------- %
let STRONG_RELAB_NIL =
     prove_thm
      (`STRONG_RELAB_NIL`,
       "!rf. STRONG_EQUIV (relab nil rf) nil",
       GEN_TAC THEN 
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC "\x y. (?rf'. (x = relab nil rf') /\ (y = nil))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN EXISTS_TAC "rf: Relabelling" THEN REWRITE_TAC[] 
        ;   
        PURE_ONCE_REWRITE_TAC [STRONG_BISIM] THEN
        BETA_TAC THEN REPEAT STRIP_TAC THENL
        [ASSUME_TAC (REWRITE_RULE [ASSUME "E = relab nil rf'"]
                            (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC RELAB_NIL_NO_TRANS 
         ;
         ASSUME_TAC (REWRITE_RULE [ASSUME "E' = nil"]
                            (ASSUME "TRANS E' u E2")) THEN
         IMP_RES_TAC NIL_NO_TRANS ] ]);;

% --------------------------------------------------------------------------- %
% Prove STRONG_RELAB_SUM:                                               (388) %
%  |- !E E' rf. STRONG_EQUIV(relab(sum E E')rf)(sum(relab E rf)(relab E' rf)) % 
% --------------------------------------------------------------------------- %
let STRONG_RELAB_SUM =
     prove_thm
      (`STRONG_RELAB_SUM`,
       "!E E' rf. 
         STRONG_EQUIV (relab (sum E E') rf) (sum (relab E rf) (relab E' rf))",  
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [PROPERTY_STAR] THEN
       REPEAT STRIP_TAC THENL
       [EXISTS_TAC "E1: CCS" THEN REWRITE_TAC [STRONG_EQUIV_REFL] THEN 
        IMP_RES_TAC TRANS_RELAB THEN IMP_RES_TAC TRANS_SUM THEN 
        ASM_REWRITE_TAC[] THENL [SUM1_TAC ; SUM2_TAC] THEN 
        RELAB_TAC THEN ASM_REWRITE_TAC[]
        ;  
        EXISTS_TAC "E2: CCS" THEN REWRITE_TAC [STRONG_EQUIV_REFL] THEN
        IMP_RES_TAC TRANS_SUM THEN IMP_RES_TAC TRANS_RELAB THEN  
        ASM_REWRITE_TAC[] THEN RELAB_TAC THENL 
        [SUM1_TAC ; SUM2_TAC] THEN ASM_REWRITE_TAC[] ]);;  
 
% --------------------------------------------------------------------------- %
% Prove STRONG_RELAB_PREFIX:                                            (423) %
%  |- !u E labl.                                                              %
%      STRONG_EQUIV (relab(prefix u E)(RELAB labl))                           %
%                   (prefix(relabel(Apply_Relab labl)u)(relab E(RELAB labl))) %
% --------------------------------------------------------------------------- %
let STRONG_RELAB_PREFIX =
     prove_thm
      (`STRONG_RELAB_PREFIX`,
       "!u E labl.
         STRONG_EQUIV (relab (prefix u E) (RELAB labl))
                      (prefix (relabel(Apply_Relab labl) u)
                              (relab E (RELAB labl)))",
       REPEAT GEN_TAC THEN
       PURE_ONCE_REWRITE_TAC [STRONG_EQUIV] THEN
       EXISTS_TAC 
       "\x y. (x = y) \/ (?u' E'. (x = relab (prefix u' E') (RELAB labl)) /\  
                                  (y = prefix (relabel(Apply_Relab labl) u')
                                              (relab E' (RELAB labl))))" THEN
       CONJ_TAC THENL
       [BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "u: Action" THEN
        EXISTS_TAC "E: CCS" THEN REWRITE_TAC[] 
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
         ASSUME_TAC(REWRITE_RULE [ASSUME "E = relab(prefix u' E'')(RELAB labl)"]
                           (ASSUME "TRANS E u E1")) THEN
         IMP_RES_TAC TRANS_RELAB THEN IMP_RES_TAC TRANS_PREFIX THEN 
         IMP_RES_TAC RELAB_LABL THEN ASM_REWRITE_TAC [PREFIX] 
         ;
         EXISTS_TAC "E2: CCS" THEN REWRITE_TAC[] THEN   
         ASSUME_TAC (REWRITE_RULE
                     [ASSUME "E' = prefix(relabel(Apply_Relab labl)u')
                                         (relab E''(RELAB labl))"]
                            (ASSUME "TRANS E' u E2")) THEN
         IMP_RES_TAC TRANS_PREFIX THEN
         ASM_REWRITE_TAC[] THEN RELAB_TAC THEN PREFIX_TAC ]]);;

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;

