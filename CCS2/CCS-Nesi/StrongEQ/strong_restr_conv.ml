% =========================================================================== %
% FILE          : strong_restr_conv.ml                                        %
% DESCRIPTION   : Conversions for the restriction operator and                %
%                 strong equivalence                                          %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 21 February 1992                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Conversion for the application of the laws for the restriction operator.    % 
% --------------------------------------------------------------------------- %
let STRONG_RESTR_ELIM_CONV tm =
   is_restr tm =>
    let P,L = args_restr tm in 
    (is_nil P) => SPEC L STRONG_RESTR_NIL |
    (is_sum P) =>
     let P1,P2 = args_sum P in SPECL [P1; P2; L] STRONG_RESTR_SUM |  
    (is_prefix P) =>
     let (u,P') = args_prefix P in 
     (is_tau u) => SPECL [P'; L] STRONG_RESTR_PREFIX_TAU |
      let l = arg_action u in 
      let thm = Label_IN_CONV l L in  
      (rconcl thm = "T") => 
       SPEC P' (MP (SPECL [l; L] STRONG_RESTR_PR_LAB_NIL) 
                   (DISJ1 (EQT_ELIM thm) "COMPL ^l IN ^L")) | 
       let thmc = REW_RHS_RULE [COMPL] (REFL "COMPL ^l") in  
       let thm' = Label_IN_CONV (rconcl thmc) L in  
       (rconcl thm' = "T") => 
        SPEC P' (MP (ONCE_REWRITE_RULE [COMPL] 
                     (SPECL [l; L] STRONG_RESTR_PR_LAB_NIL))  
                    (DISJ2 "^l IN ^L" (EQT_ELIM thm'))) | 
        SPEC P' (MP (ONCE_REWRITE_RULE [COMPL] 
                     (SPECL [l; L] STRONG_RESTR_PREFIX_LABEL))  
                    (CONJ (EQF_ELIM thm) (EQF_ELIM thm'))) |  
      failwith `STRONG_RESTR_ELIM_CONV` |
    failwith `STRONG_RESTR_ELIM_CONV`;; 


