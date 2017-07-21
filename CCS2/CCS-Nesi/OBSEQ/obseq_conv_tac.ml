% =========================================================================== %
% FILE          : obseq_conv_tac.ml                                           %
% DESCRIPTION   : Conversions and tactics for applying the laws for           % 
%                 observation equivalence through strong equivalence          %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Define the conversions and tactics for the application of the laws for      %
% OBS_EQUIV (through the conversions and tactics for strong equivalence).     %
% --------------------------------------------------------------------------- %
let STRONG_TO_OBSEQUIV_CONV (c: conv) tm =
   MATCH_MP STRONG_IMP_OBS_EQUIV (c tm);;

let [OE_SUM_IDEMP_CONV; OE_SUM_NIL_CONV; OE_RELAB_ELIM_CONV;  
     OE_RESTR_ELIM_CONV; OE_PAR_ELIM_CONV; OE_EXP_THM_CONV; 
     OE_REC_UNF_CONV] =  

map STRONG_TO_OBSEQUIV_CONV 
    [STRONG_SUM_IDEMP_CONV; STRONG_SUM_NIL_CONV; STRONG_RELAB_ELIM_CONV;  
     STRONG_RESTR_ELIM_CONV; STRONG_PAR_ELIM_CONV; STRONG_EXP_THM_CONV;  
     STRONG_REC_UNF_CONV];; 

let [OE_SUM_IDEMP_TAC; OE_SUM_NIL_TAC; OE_RELAB_ELIM_TAC;  
     OE_RESTR_ELIM_TAC; OE_PAR_ELIM_TAC; OE_REC_UNF_TAC] = 

map OE_LHS_CONV_TAC  
    [STRONG_SUM_IDEMP_CONV; STRONG_SUM_NIL_CONV; STRONG_RELAB_ELIM_CONV; 
     STRONG_RESTR_ELIM_CONV; STRONG_PAR_ELIM_CONV; STRONG_REC_UNF_CONV];;  

let OE_RHS_RELAB_ELIM_TAC = OE_RHS_CONV_TAC STRONG_RELAB_ELIM_CONV;; 

% idem for the other operators %

% --------------------------------------------------------------------------- %
% Tactic for applying the expansion theorem                                   %
% (parallel and restriction operators).                                       %
% --------------------------------------------------------------------------- % 
let OE_EXP_THM_TAC: tactic (asl,w) =
   let (op,t1,t2) = args_equiv w in
   (op = "OBS_EQUIV") =>
    let thm = MATCH_MP STRONG_IMP_OBS_EQUIV (STRONG_EXP_THM_CONV t1) in 
    let (t1',t') = args_thm thm in                           % t1' = t1 %
    (t' = t2) =>
     ([], \[]. OE_TRANS thm (SPEC t' OBS_EQUIV_REFL)) |
     ([asl,"OBS_EQUIV ^t' ^t2"], \[thm']. OE_TRANS thm thm') |
   failwith `the goal is not an OBS_EQUIV relation`;;

