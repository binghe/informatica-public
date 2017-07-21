% =========================================================================== %
% FILE          : vending.ml                                                  %
% DESCRIPTION   : Proof of some modal properties of a simple vending machine  %
%                 (Stirling,1989)                                             %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 20 January 1992                                             %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Create the new theory.                                                      %
% --------------------------------------------------------------------------- %
new_theory `vending`;;

% --------------------------------------------------------------------------- %
% Specification of a simple vending machine.                                  %
%      V = 2p.big.collect.V + 1p.little.collect.V                             %
% --------------------------------------------------------------------------- % 
let V =
  new_definition
     (`V`,
      "V = rec `X`
           (sum (prefix (label(name `2p`))
                  (prefix (label(name `big`))
                    (prefix (label(name `collect`)) (var `X`))))
                (prefix (label(name `1p`))
                  (prefix (label(name `little`))
                    (prefix (label(name `collect`)) (var `X`)))))");;

% --------------------------------------------------------------------------- %
% The steps to unfold a rec term in one tactic.                               %
% --------------------------------------------------------------------------- %
let REC_EXP_TAC pdef_thm =
     REC_TAC THEN REWRITE_TAC [CCS_Subst; SYM pdef_thm];;
  
% --------------------------------------------------------------------------- %
% Prove that V can accept `2p`, i.e. V satifies <2p> tt.                (215) %
% --------------------------------------------------------------------------- % 
g "SAT V (dmd {label(name `2p`)} tt)";; 

e (REWRITE_TAC [CAPC_ACT_THM; V] THEN EXISTS_TAC "label(name `2p`)" THEN 
   EXISTS_TAC "prefix (label(name `big`))
                (prefix (label(name `collect`)) V)" THEN
   REWRITE_TAC [IN_SING] THEN REC_EXP_TAC V THEN SUM1_TAC THEN PREFIX_TAC);;  
 
% --------------------------------------------------------------------------- %
% Prove that a button cannot yet depressed (before money is deposited), i.e.  %
%  V satifies [{big,little}] ff.                                        (537) %
% --------------------------------------------------------------------------- %
g "SAT V (box {label(name `big`),label(name `little`)} ff)";; 

e (REWRITE_TAC [V; INAB_ACT_THM] THEN
   REWRITE_TAC [TRANS_REC_EQ; CCS_Subst; SYM V] THEN  
   REPEAT STRIP_TAC THEN IMP_RES_TAC TRANS_SUM THENL       
   [MODAL_TAC "u = label(name `2p`)" 
              "u IN {label(name `big`),label(name `little`)}" 
    ;  
    MODAL_TAC "u = label(name `1p`)" 
              "u IN {label(name `big`),label(name `little`)}" ]);;  
   
% --------------------------------------------------------------------------- %
% Prove that, after 2p is deposited, the little button cannot be depressed    %
% whereas the big one can, i.e. (necessity of `big')                          %
%  V satifies [{2p}] ([{little}] ff /\ <{big}> tt).                     (604) %
% --------------------------------------------------------------------------- %
let Fm1 = 
    new_definition 
       (`Fm1`, 
        "Fm1 = box {label(name `2p`)} 
                   (conj (box {label(name `little`)} ff) 
                         (dmd {label(name `big`)} tt))");;
 
g "SAT V Fm1";;

e (PURE_ONCE_REWRITE_TAC [V; Fm1] THEN
   SAT_box_TAC THEN REWRITE_TAC [TRANS_REC_EQ; CCS_Subst; SYM V] THEN    
   REPEAT STRIP_TAC THEN IMP_RES_TAC TRANS_SUM THENL
   [IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC[] THEN 
    SAT_conj_TAC THENL 
    [PURE_ONCE_REWRITE_TAC [INAB_ACT_THM] THEN REPEAT STRIP_TAC THEN 
     MODAL_TAC "u' = label(name `big`)" "u' IN {label(name `little`)}"   
     ; 
     PURE_ONCE_REWRITE_TAC [CAPC_ACT_THM] THEN 
     EXISTS_TAC "label(name `big`)" THEN 
     EXISTS_TAC "prefix (label(name `collect`)) V" THEN 
     REWRITE_TAC [IN_SING] THEN PREFIX_TAC ] 
    ; 
    MODAL_TAC "u = label(name `1p`)" "u IN {label(name `2p`)}" ]);; 
  
% --------------------------------------------------------------------------- %
% Prove that, after a coin is entrusted, no other coin (2p or 1p) may be      %
% deposited, i.e. V satifies [{1p,2p}] [{1p,2p}] ff.                    (719) %
% --------------------------------------------------------------------------- %
let Fm2 =
    new_definition
       (`Fm2`,
        "Fm2 = box {label(name `1p`), label(name `2p`)}
                   (box {label(name `1p`), label(name `2p`)} ff)");; 

g "SAT V Fm2";;

e (PURE_ONCE_REWRITE_TAC [V; Fm2] THEN
   SAT_box_TAC THEN REWRITE_TAC [TRANS_REC_EQ; CCS_Subst; SYM V] THEN
   REPEAT STRIP_TAC THEN IMP_RES_TAC TRANS_SUM THENL
   [IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC[] THEN 
    PURE_ONCE_REWRITE_TAC [INAB_ACT_THM] THEN REPEAT STRIP_TAC THEN   
    MODAL_TAC "u' = label(name `big`)" 
              "u' IN {label(name `1p`),label(name `2p`)}" 
    ;
    IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC[] THEN   
    PURE_ONCE_REWRITE_TAC [INAB_ACT_THM] THEN REPEAT STRIP_TAC THEN
    MODAL_TAC "u' = label(name `little`)" 
              "u' IN {label(name `1p`),label(name `2p`)}" ]);; 

% --------------------------------------------------------------------------- %
% Prove that, after a coin is deposited and then a button is depressed, a     %
% chocolate can be collected, i.e.                                            %
%  V satifies [{1p,2p}] [{big,little}] <{collect}> tt.                  (671) %
% --------------------------------------------------------------------------- %
let Fm3 =
    new_definition
       (`Fm3`,
        "Fm3 = box {label(name `1p`), label(name `2p`)}
                   (box {label(name `big`), label(name `little`)} 
                         (dmd {label(name `collect`)} tt))");;

g "SAT V Fm3";;

% Qui MODAL_TAC non puo' essere applicata, necessita una versione piu' 
  raffinata, piu' generale % 

e (PURE_ONCE_REWRITE_TAC [V; Fm3] THEN
   SAT_box_TAC THEN REWRITE_TAC [TRANS_REC_EQ; CCS_Subst; SYM V] THEN
   REPEAT STRIP_TAC THEN IMP_RES_TAC TRANS_SUM THEN 
   IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC[] THEN 
   SAT_box_TAC THEN REPEAT STRIP_TAC THEN
   IMP_RES_TAC TRANS_PREFIX THEN ASM_REWRITE_TAC[] THEN 
   PURE_ONCE_REWRITE_TAC [CAPC_ACT_THM] THEN 
   EXISTS_TAC "label(name `collect`)" THEN EXISTS_TAC "V: CCS" THEN 
   REWRITE_TAC [IN_SING] THEN PREFIX_TAC);;  

% --------------------------------------------------------------------------- %
% Prove that, after a 1p coin is deposited, another 1p coin cannot be         %
% deposited, i.e. V does not satisfy <{1p}> <{1p}> tt.                  (606) %
% --------------------------------------------------------------------------- %
g "~SAT V (dmd {label(name `1p`)} (dmd {label(name `1p`)} tt))";; 
 
e (PURE_ONCE_REWRITE_TAC [V] THEN PURE_ONCE_REWRITE_TAC [SAT_dmd] THEN    
   REWRITE_TAC [TRANS_REC_EQ; CCS_Subst; SYM V] THEN 
   REPEAT STRIP_TAC THEN IMP_RES_TAC TRANS_SUM THENL
   [MODAL_TAC "u = label(name `2p`)" "u IN {label(name `1p`)}" 
    ; 
    IMP_RES_TAC TRANS_PREFIX THEN
    ASSUME_TAC (ONCE_REWRITE_RULE 
               [ASSUME "E' = prefix(label(name `little`))
                                   (prefix(label(name `collect`))V)"] 
                    (ASSUME "SAT E'(dmd{label(name `1p`)}tt)")) THEN 
    IMP_RES_TAC (fst (EQ_IMP_RULE (SPEC_ALL SAT_dmd))) THEN 
    MODAL_TAC "u' = label(name `little`)" "u' IN {label(name `1p`)}" ]);;  

% --------------------------------------------------------------------------- %
% Prove that, after a 2p coin is deposited, V must perform `big`, i.e.        %
%  V satisfes [{2p}] (<{Action}> tt /\ [{Action - big}] ff).            (716) %
% --------------------------------------------------------------------------- %
g "SAT V (box {label(name `2p`)} (nec (label(name `big`))))";;

e (SAT_box_TAC THEN REWRITE_TAC [V; NEC_ACT_THM] THEN
   REWRITE_TAC [TRANS_REC_EQ; CCS_Subst; SYM V] THEN
   REPEAT STRIP_TAC THENL 
   [IMP_RES_TAC TRANS_SUM THENL 
    [IMP_RES_TAC TRANS_PREFIX THEN 
     EXISTS_TAC "prefix(label(name `collect`))V" THEN 
     ASM_REWRITE_TAC[] THEN PREFIX_TAC ; 
     MODAL_TAC "u = label(name `1p`)" "u IN {label(name `2p`)}" ] 
    ; 
    IMP_RES_TAC TRANS_SUM THENL 
    [IMP_RES_TAC TRANS_PREFIX THEN 
     ASSUME_TAC
     (REWRITE_RULE [ASSUME "E' = prefix(label(name `big`))
                                       (prefix(label(name `collect`))V)"]
      (ASSUME "TRANS E' u' E''")) THEN
     IMP_RES_TAC TRANS_PREFIX THEN RES_TAC ;
     MODAL_TAC "u = label(name `1p`)" "u IN {label(name `2p`)}" ]]);; 

% --------------------------------------------------------------------------- %
% Close the theory.                                                           %
% --------------------------------------------------------------------------- %
close_theory();;
 
