% =========================================================================== %
% FILE          : aux_fun.ml                                                  %
% DESCRIPTION   : Auxiliary functions for rewriting with the CCS behavioural  %
%                 equivalences                                                %
%                                                                             % 
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Define args_thm as a function that, given a theorem |- f t1 t2, returns     %
% (t1,t2).                                                                    %
% --------------------------------------------------------------------------- %
let args_thm thm =
   let (f,[t1;t2]) = strip_comb (concl thm) in (t1,t2);;

let lhs_tm = \thm. (fst o args_thm) thm
and rhs_tm = \thm. (snd o args_thm) thm;;

% --------------------------------------------------------------------------- %
% Define args_equiv as a function that, given a term "p t1 t2", returns       %
% (p,t1,t2).                                                                  %
% --------------------------------------------------------------------------- %
let args_equiv tm =
   let (p,[t1;t2]) = strip_comb tm in (p,t1,t2);; 

% --------------------------------------------------------------------------- %
% Auxiliary functions (on lists and terms) to find repeated occurrences of a  %
% summand to be then deleted by applying the idempotence law for summation.   %
% --------------------------------------------------------------------------- %
letrec elim h l =
   (null l) => l |
    (h = (hd l)) => (tl l) | (hd l).(elim h (tl l));;

let ladd x l = (null l) => [x] | [mk_sum(x, hd l)];;

letrec FIND_SMD before mark after exp =
   (exp = mark) => (before, after) |
    is_sum exp =>
     let a,b = args_sum exp
     in
      (b = mark) => ([a], after) |
                    (FIND_SMD before mark (ladd b after) a) |
   failwith `FIND_SMD`;;

% --------------------------------------------------------------------------- %
% Define the predecessor of a SUC term, and the number of elements in a list. %
% --------------------------------------------------------------------------- %
% predefined ??? %

let pre tm = let (suc,n) = dest_comb tm in (suc = "SUC") => n | fail;;

letrec n_elems l = (null (tl l)) => "0" | "SUC ^(n_elems (tl l))";;

% --------------------------------------------------------------------------- %
% Given a list of terms, the function build_sum builds a CCS term which is    %
% the summation of the terms in the list (associating to the right).          %
% --------------------------------------------------------------------------- %
letrec build_sum tauL =
    null tauL => "nil" |
    null (tl tauL) => (hd tauL) |
     mk_sum (hd tauL, build_sum (tl tauL));;

% --------------------------------------------------------------------------- %
% Given a list of summands sumL and an instance ARBtm of the term ARB': CCS,  %
% the function sum_to_fun sumL ARBtm n returns a function which associates    %
% each summand to its index, starting from index n.                           %
% --------------------------------------------------------------------------- %
letrec sum_to_fun sumL ARBtm n =
    (null sumL) => ARBtm | 
    "(x = ^n) => ^(hd sumL) | ^(sum_to_fun (tl sumL) ARBtm "SUC ^n")";;

