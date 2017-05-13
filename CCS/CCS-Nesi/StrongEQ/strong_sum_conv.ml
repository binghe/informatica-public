% =========================================================================== %
% FILE          : strong_sum_conv.ml                                          %
% DESCRIPTION   : Conversions for the summation operator and                  % 
%                 strong equivalence                                          %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : 3 December 1991                                             %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Associate the summands in a term to the left.                               %
% --------------------------------------------------------------------------- %
letrec STRONG_SUM_ASSOC_CONV tm =
   let a,b = args_sum tm in
   is_sum b =>
    let b1,b2 = args_sum b in
    let thm = SPECL [a; b1; b2] STRONG_SUM_ASSOC_L in
    let thm' = STRONG_SUM_ASSOC_CONV (rhs_tm thm) in
     S_TRANS thm thm' |
   is_sum a =>
    let thm'' = STRONG_SUM_ASSOC_CONV a in
     SPEC b (MATCH_MP STRONG_EQUIV_SUBST_SUM_R thm'') |
     SPEC tm STRONG_EQUIV_REFL;;

% --------------------------------------------------------------------------- %
% Conversion for the application of STRONG_SUM_IDENT(_L/R).                   %
% --------------------------------------------------------------------------- % 
let STRONG_SUM_NIL_CONV tm =  
   is_sum tm =>
    let t1, t2 = args_sum tm in 
    is_nil t1 => SPEC t2 STRONG_SUM_IDENT_L |
    is_nil t2 => SPEC t1 STRONG_SUM_IDENT_R |
    failwith `STRONG_SUM_NIL_CONV` |
   failwith `STRONG_SUM_NIL_CONV`;;

% --------------------------------------------------------------------------- %
% Find repeated occurrences of a summand to be then deleted by applying       % 
% STRONG_SUM_IDEMP.                                                           %
% --------------------------------------------------------------------------- %
letrec STRONG_FIND_IDEMP tm l =
   let h.t = l in 
   (null t) => failwith `term not a CCS summation` |
    let tm' = fst(args_sum tm) in 
    (mem h t) =>
     let (l1,l2) = FIND_SMD [] h [] tm' in 
     (null l2) =>
      ((null l1) => SPEC h STRONG_SUM_IDEMP |
       let y = hd l1 in 
        S_TRANS (SPECL [y; h; h] STRONG_SUM_ASSOC_R) 
                (SPEC y (MP (SPECL [mk_sum(h,h); h] STRONG_EQUIV_SUBST_SUM_R)
                            (SPEC h STRONG_SUM_IDEMP)))) | 
       let thm1 = 
       (null l1) =>
        S_TRANS (S_SYM (STRONG_SUM_ASSOC_CONV (mk_sum(mk_sum(h, hd l2), h))))
                (SPECL [h; hd l2] STRONG_SUM_MID_IDEMP) |      
        S_TRANS 
        (S_SYM 
         (STRONG_SUM_ASSOC_CONV (mk_sum(mk_sum(mk_sum(hd l1,h),hd l2),h)))) 
        (SPECL [hd l1; h; hd l2] STRONG_LEFT_SUM_MID_IDEMP) in  
         S_TRANS thm1 (STRONG_SUM_ASSOC_CONV (snd (args_thm thm1))) |
     let thm' = STRONG_FIND_IDEMP tm' t in  
      SPEC h (MATCH_MP STRONG_EQUIV_SUBST_SUM_R thm');;      

% --------------------------------------------------------------------------- %
% Conversion for the application of STRONG_SUM_IDEMP.                         %
% --------------------------------------------------------------------------- % 
let STRONG_SUM_IDEMP_CONV tm =
   is_sum tm =>
    let thm = STRONG_SUM_ASSOC_CONV tm in 
    let t1 = rhs_tm thm in 
    let thm' = STRONG_FIND_IDEMP t1 (rev (flat_sum t1)) in  
     S_TRANS thm thm' |    
   failwith `STRONG_SUM_IDEMP_CONV`;;


