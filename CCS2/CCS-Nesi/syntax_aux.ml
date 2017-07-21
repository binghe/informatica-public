% =========================================================================== %
% FILE          : syntax_aux.ml                                               %
% DESCRIPTION   : Auxiliary ML functions for dealing with CCS syntax          %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 30 May 1991                                                 %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Define the destructors related to the constructors of the type Label.       %
% --------------------------------------------------------------------------- %
let args_label l = 
    let op,s = dest_comb l in  
    (op = "name") or (op = "coname") => (op,s) 
    | failwith `term not a CCS label`;;
  
let arg_name l =
    let op,s = dest_comb l in 
    (op = "name") => s | failwith `term not a CCS name`;;

let arg_coname l =
    let op,s = dest_comb  l in 
    (op = "coname") => s | failwith `term not a CCS co-name`;;

% --------------------------------------------------------------------------- %
% Define the destructors related to the constructors of the type Action.      %
% --------------------------------------------------------------------------- %
let arg_action u =
    let op,l = dest_comb u in 
    (op = "label") => l | failwith `term not a CCS action(label)`;;

% --------------------------------------------------------------------------- %
% Define the destructor related to the operator COMPL.                        %
% --------------------------------------------------------------------------- %
let arg_compl l =
    let op,x = dest_comb l in
    (op = "COMPL") => x | failwith `term not complement of a CCS label`;;

% --------------------------------------------------------------------------- %
% Define the destructor related to the type Relabelling.                      %
% --------------------------------------------------------------------------- %
let arg_relabelling rf = 
    let op,strl = dest_comb rf in  
    (op = "RELAB") => strl | failwith `term not a CCS relabelling`;;  

% --------------------------------------------------------------------------- %
% Define the destructors related to the constructors of the type CCS.         %
% --------------------------------------------------------------------------- %
let arg_ccs_var tm =
    let op,X = dest_comb tm in 
    (op = "var") => X | failwith `term not a CCS variable`;;

let args_prefix tm =
    let (op,[u;P]) = strip_comb tm in 
    (op = "prefix") => (u,P) | failwith `term not CCS prefix`;; 

let args_sum tm =
    let (op,[P1;P2]) = strip_comb tm in 
    (op = "sum") => (P1,P2) | failwith `term not CCS summation`;; 

let args_par tm =
    let (op,[P1;P2]) = strip_comb tm in 
    (op = "par") => (P1,P2) | failwith `term not CCS parallel`;;

let args_restr tm =
    let (op,[P;lset]) = strip_comb tm in 
    (op = "restr") => (P,lset) | failwith `term not CCS restriction`;; 

let args_relab tm =
    let (op,[P;f]) = strip_comb tm in 
    (op = "relab") => (P,f) | failwith `term not CCS relabelling`;; 

let args_rec tm =
    let (op,[X;E]) = strip_comb tm in 
    (op = "rec") => (X,E) | failwith `term not CCS recursion`;;

% --------------------------------------------------------------------------- %
% Define predicates related to the destructors above.                         %
% --------------------------------------------------------------------------- %
let is_name = can arg_name;;
let is_coname = can arg_coname;;
let is_label = can arg_action;;
let is_tau u = (u = "tau");;
let is_compl = can arg_compl;;

let is_nil tm = (tm = "nil");;
let is_ccs_var = can arg_ccs_var;;
let is_prefix = can args_prefix;;
let is_sum = can args_sum;;
let is_par = can args_par;;
let is_restr = can args_restr;;
let is_relab = can args_relab;;
let is_rec = can args_rec;;

% --------------------------------------------------------------------------- %
% Define construction of CCS terms.                                           %
% --------------------------------------------------------------------------- %
let mk_name s = "name ^s";;
let mk_coname s = "coname ^s";;
let mk_label l = "label ^l";;
let mk_ccs_var X = "var ^X";;
let mk_prefix (u,P) = "prefix ^u ^P";;
let mk_sum (P1,P2) = "sum ^P1 ^P2";;
let mk_par (P1,P2) = "par ^P1 ^P2";;
let mk_restr (P,lset) = "restr ^P ^lset";;
let mk_relab (P,f) = "relab ^P ^f";;
let mk_rec (X,E) = "rec ^X ^E";;

% --------------------------------------------------------------------------- %
% Define flattening of a CCS summation.                                       %
% --------------------------------------------------------------------------- %
letrec flat_sum tm =
   not(is_sum tm) => [tm] |
   let (t1, t2) = args_sum tm in (flat_sum t1) @ (flat_sum t2);;

% --------------------------------------------------------------------------- %
% Conversion that implements a decision procedure for equality of labels.     %
% --------------------------------------------------------------------------- %
let Label_EQ_CONV lab_eq =
    let (l1,l2) = dest_eq lab_eq in 
    let (op1,s1) = args_label l1
    and (op2,s2) = args_label l2 in 
    (op1 = op2) =>
     let thm = string_EQ_CONV "^s1 = ^s2" in 
     (op1 = "name") =>
      TRANS (SPECL [s1; s2] (CONJUNCT1 Label_One_One)) thm | 
      TRANS (SPECL [s1; s2] (CONJUNCT2 Label_One_One)) thm | 
     (op1 = "name") & (op2 = "coname") =>                    % not(op1 = op2) %
      SPECL [s1; s2] Label_Not_Eq |         %(op1 = "coname") & (op2 = "name")% 
      SPECL [s1; s2] Label_Not_Eq' ;;

% --------------------------------------------------------------------------- %
% Conversion that proves/disproves membership of a label to a set of labels.  %
% --------------------------------------------------------------------------- %
let Label_IN_CONV l L = IN_CONV Label_EQ_CONV "^l IN ^L";;

% --------------------------------------------------------------------------- %
% Conversion that implements a decision procedure for equality of actions.    %
% --------------------------------------------------------------------------- %
let Action_EQ_CONV act_eq = 
    let (u1,u2) = dest_eq act_eq in  
    (is_tau u1 & is_tau u2) => EQT_INTRO (REFL u1) |    
    (is_tau u1 & is_label u2) => 
     EQF_INTRO (SPEC (arg_action u2) Action_Distinct) | 
    (is_label u1 & is_tau u2) =>  
     EQF_INTRO (SPEC (arg_action u1) Action_Distinct_label) | 
    let l1 = arg_action u1                      % u1,u2 are both labels %  
    and l2 = arg_action u2 in  
    let (op1,s1) = args_label l1 
    and (op2,s2) = args_label l2 
    and thm = Label_EQ_CONV "^l1 = ^l2" in  
    (op1 = op2) =>
     (op1 = "name") =>
      TRANS (SPECL ["name ^s1"; "name ^s2"] Action_One_One) thm |
      TRANS (SPECL ["coname ^s1"; "coname ^s2"] Action_One_One) thm |
     (op1 = "name") & (op2 = "coname") =>                    % not(op1 = op2) %
      TRANS (SPECL ["name ^s1"; "coname ^s2"] Action_One_One)
            (SPECL [s1; s2] Label_Not_Eq) |
                                            %(op1 = "coname") & (op2 = "name")%
      TRANS (SPECL ["coname ^s1"; "name ^s2"] Action_One_One)
            (SPECL [s1; s2] Label_Not_Eq') ;;

% --------------------------------------------------------------------------- %
% Conversion that proves/disproves membership of an action to a set of actions.%
% --------------------------------------------------------------------------- %
let Action_IN_CONV u A = IN_CONV Action_EQ_CONV "^u IN ^A";;

% --------------------------------------------------------------------------- %
% Conversion for evaluating a relabelling function fc (in conditional form).  %
% --------------------------------------------------------------------------- %
letrec RELAB_EVAL_CONV fc =
   let c = snd(dest_comb fc) in
   is_cond c =>
    let (b,l,r) = dest_cond c in
    let s1,s2 = dest_eq b in
    let thm = string_EQ_CONV "^s1 = ^s2" in
    let thm' = REW_RHS_RULE [thm] (REFL fc) in
     TRANS thm' (RELAB_EVAL_CONV (rconcl thm')) |
    REFL fc;;


