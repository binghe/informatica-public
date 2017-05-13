% =========================================================================== %
% FILE          : strong_tac.ml                                               %
% DESCRIPTION   : Tactics for applying the laws for strong equivalence        %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Tactics for the application of the laws for STRONG_EQUIV on the left-hand   %
% side of a strong equivalence.                                               %
% --------------------------------------------------------------------------- %
let [STRONG_SUM_IDEMP_TAC; 
     STRONG_SUM_NIL_TAC; 
     STRONG_RELAB_ELIM_TAC; 
     STRONG_RESTR_ELIM_TAC; 
     STRONG_PAR_ELIM_TAC; 
     STRONG_REC_UNF_TAC] = map (S_LHS_CONV_TAC o S_DEPTH_CONV)  
                                [STRONG_SUM_IDEMP_CONV; 
                                 STRONG_SUM_NIL_CONV; 
                                 STRONG_RELAB_ELIM_CONV; 
                                 STRONG_RESTR_ELIM_CONV; 
                                 STRONG_PAR_ELIM_CONV; 
                                 STRONG_REC_UNF_CONV];; 

% --------------------------------------------------------------------------- %
% Tactic for applying the expansion theorem.                                  %
% --------------------------------------------------------------------------- % 
let STRONG_EXP_THM_TAC = S_LHS_CONV_TAC STRONG_EXP_THM_CONV;;


