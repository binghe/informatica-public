% =========================================================================== %
% FILE          : obscongr_conv_tac.ml                                        %
% DESCRIPTION   : Conversions and tactics for applying the laws for           % 
%                 observation congruence                                      %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Define the conversions for the application of the laws for OBS_CONGR        %
% (through the conversions for strong equivalence).                           %
% --------------------------------------------------------------------------- %
let STRONG_TO_OBSCONGR_CONV (c: conv) tm =
   MATCH_MP STRONG_IMP_OBS_CONGR (c tm);; 

let [OC_SUM_IDEMP_CONV; OC_SUM_NIL_CONV; 
     OC_RELAB_ELIM_CONV; OC_RESTR_ELIM_CONV;  
     OC_PAR_ELIM_CONV; OC_EXP_THM_CONV; OC_REC_UNF_CONV] =  

map STRONG_TO_OBSCONGR_CONV 
    [STRONG_SUM_IDEMP_CONV; STRONG_SUM_NIL_CONV; STRONG_RELAB_ELIM_CONV; 
     STRONG_RESTR_ELIM_CONV; STRONG_PAR_ELIM_CONV; STRONG_EXP_THM_CONV; 
     STRONG_REC_UNF_CONV];; 

% --------------------------------------------------------------------------- %
% Define the tactics for the application of the laws for OBS_CONGR            %
% --------------------------------------------------------------------------- %
let [OC_SUM_IDEMP_TAC; OC_SUM_NIL_TAC; OC_RELAB_ELIM_TAC; OC_RESTR_ELIM_TAC;  
     OC_PAR_ELIM_TAC; OC_REC_UNF_TAC; OC_TAU1_TAC] = 

map (OC_LHS_CONV_TAC o OC_DEPTH_CONV) 
    [OC_SUM_IDEMP_CONV; OC_SUM_NIL_CONV; 
     OC_RELAB_ELIM_CONV; OC_RESTR_ELIM_CONV; 
     OC_PAR_ELIM_CONV; OC_REC_UNF_CONV; OC_TAU1_CONV];;  
 
let OC_RHS_RELAB_ELIM_TAC = 
     (OC_RHS_CONV_TAC o OC_DEPTH_CONV) OC_RELAB_ELIM_CONV;; 

% idem for the other operators %

% --------------------------------------------------------------------------- %
% Tactic for applying the expansion theorem                                   %
% (parallel and restriction operators).                                       %
% --------------------------------------------------------------------------- % 
let OC_EXP_THM_TAC = OC_LHS_CONV_TAC OC_EXP_THM_CONV;;

% let TAU1_TAC = OC_CONV_TAC (OC_DEPTH_CONV TAU1_CONV);; % 


