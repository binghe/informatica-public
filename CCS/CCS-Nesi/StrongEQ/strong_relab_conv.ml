% =========================================================================== %
% FILE          : strong_relab_conv.ml                                        %
% DESCRIPTION   : Conversions for the relabelling operator and                %
%                 strong equivalence                                          %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 22 February 1992                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Conversion for the application of the laws for the relabelling operator.    %
% --------------------------------------------------------------------------- %
let STRONG_RELAB_ELIM_CONV tm =
   is_relab tm => 
    let P,rf = args_relab tm in 
    (is_nil P) => SPEC rf STRONG_RELAB_NIL |
    (is_sum P) =>
     let P1,P2 = args_sum P in SPECL [P1; P2; rf] STRONG_RELAB_SUM |
    (is_prefix P) =>
     let u,P' = args_prefix P
     and labl = arg_relabelling rf in 
     let thm_act = REW_RHS_RULE [relabel; Apply_Relab; Label_Distinct;
                                 Label_Distinct'; Label_One_One;
                                 COMPL; COMPL_COMPL] 
                   (REFL "relabel(Apply_Relab ^labl) ^u") in  
     let thm_act' = RELAB_EVAL_CONV (rconcl thm_act) in  
      ONCE_REWRITE_RULE [TRANS thm_act thm_act'] 
      (SPECL [u; P'; labl] STRONG_RELAB_PREFIX) | 
    failwith `STRONG_RELAB_ELIM_CONV` | 
   failwith `STRONG_RELAB_ELIM_CONV`;; 


