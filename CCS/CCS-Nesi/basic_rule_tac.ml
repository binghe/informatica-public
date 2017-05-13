% =========================================================================== %
% FILE          : basic_rule_tac.ml                                           %
% DESCRIPTION   : Basic rules and tactics for particular forms of rewriting   %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 21 February 1992                                            %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Rule for rewriting only the right-hand side on an equation once.            %
% --------------------------------------------------------------------------- %
let ONCE_REW_RHS_RULE = GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [];;

% --------------------------------------------------------------------------- %
% Rule for rewriting only the right-hand side on an equation (pure version).  %
% --------------------------------------------------------------------------- %
let PURE_REW_RHS_RULE = GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) [];;

% --------------------------------------------------------------------------- %
% Rule for rewriting only the right-hand side on an equation                  % 
% (basic rewrites included).                                                  %
% --------------------------------------------------------------------------- %
let REW_RHS_RULE = 
       GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) basic_rewrites;;   

% --------------------------------------------------------------------------- %
% Tactic for rewriting only the right-hand side on an equation once.          %
% --------------------------------------------------------------------------- %
let ONCE_REW_RHS_TAC = GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [];;

% --------------------------------------------------------------------------- %
% Tactic for rewriting only the right-hand side on an equation.               %
% --------------------------------------------------------------------------- %
let REW_RHS_TAC = GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) basic_rewrites;;
 
% --------------------------------------------------------------------------- %
% Rule for rewriting only the left-hand side on an equation once.             %
% --------------------------------------------------------------------------- %
let ONCE_REW_LHS_RULE = GEN_REWRITE_RULE (RATOR_CONV o ONCE_DEPTH_CONV) [];;

% --------------------------------------------------------------------------- %
% Rule for rewriting only the left-hand side on an equation (pure version).   %
% --------------------------------------------------------------------------- %
let PURE_REW_LHS_RULE = GEN_REWRITE_RULE (RATOR_CONV o TOP_DEPTH_CONV) [];;

% --------------------------------------------------------------------------- %
% Rule for rewriting only the left-hand side on an equation                   %
% (basic rewrites included).                                                  %
% --------------------------------------------------------------------------- %
let REW_LHS_RULE =
       GEN_REWRITE_RULE (RATOR_CONV o TOP_DEPTH_CONV) basic_rewrites;;

% --------------------------------------------------------------------------- %
% Tactic for rewriting only the left-hand side on an equation once.           %
% --------------------------------------------------------------------------- %
let ONCE_REW_LHS_TAC = GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [];;

% --------------------------------------------------------------------------- %
% Tactic for rewriting only the left-hand side on an equation.                %
% --------------------------------------------------------------------------- %
let REW_LHS_TAC = GEN_REWRITE_TAC (RATOR_CONV o TOP_DEPTH_CONV) basic_rewrites;;

% --------------------------------------------------------------------------- %
% Rule for rewriting only the left-hand side of an equation once with the     % 
% assumptions.                                                                %
% --------------------------------------------------------------------------- %
let ONCE_ASM_REW_LHS_RULE thl th =
        ONCE_REW_LHS_RULE ((map ASSUME (hyp th)) @ thl) th;;

% --------------------------------------------------------------------------- %
% Tactic for rewriting only the left-hand side of an equation once with the   %
% assumptions.                                                                %
% --------------------------------------------------------------------------- %
let ONCE_ASM_REW_LHS_TAC thl =
        ASSUM_LIST (\asl. ONCE_REW_LHS_TAC (asl @ thl));;

% --------------------------------------------------------------------------- %
% Conversion to swap two universally quantified variables.                    %
% --------------------------------------------------------------------------- %
let SWAP_FORALL_CONV tm =
  let v1,v2,bod = (I # dest_forall) (dest_forall tm) in
  let tl1 = [v1;v2] and tl2 = [v2;v1] in
  let th1 = GENL tl2 (SPECL tl1 (ASSUME tm)) in
  let th2 = GENL tl1 (SPECL tl2 (ASSUME (concl th1))) in
  IMP_ANTISYM_RULE (DISCH_ALL th1) (DISCH_ALL th2);;

% --------------------------------------------------------------------------- %
% The rule EQ_IMP_LR returns the implication from left to right of a given    %
% equational theorem.                                                         %
% --------------------------------------------------------------------------- %
let EQ_IMP_LR thm = GEN_ALL (fst (EQ_IMP_RULE (SPEC_ALL thm)));;

% --------------------------------------------------------------------------- %
% The rule EQ_IMP_RL returns the implication from right to left of a given    %
% equational theorem.                                                         %
% --------------------------------------------------------------------------- %
let EQ_IMP_RL thm = GEN_ALL (snd (EQ_IMP_RULE (SPEC_ALL thm)));;

% --------------------------------------------------------------------------- %
% Functions to get the left and right hand side of the equational conclusion  %
% of a theorem.                                                               %
% --------------------------------------------------------------------------- %
let lconcl = fst o dest_eq o concl o SPEC_ALL 
and rconcl = snd o dest_eq o concl o SPEC_ALL ;;


