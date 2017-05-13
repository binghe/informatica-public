% =========================================================================== %
% FILE          : strong_par_conv.ml                                          %
% DESCRIPTION   : Conversions for the parallel operator and strong equivalence%
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : May 1993                                                    %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% |- !t1 t2. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2)                   %
% --------------------------------------------------------------------------- %
let CCS_COND_CLAUSES = INST_TYPE [": CCS",": *"] COND_CLAUSES;;  
 
% --------------------------------------------------------------------------- %
% Conversion to evaluate conditionals involving numbers.                      %
% --------------------------------------------------------------------------- %
letrec COND_EVAL_CONV c =
   is_cond c =>
    let (b,l,r) = dest_cond c in 
    let thm1 = num_EQ_CONV b
    and thm2 = ISPECL [l;r] CCS_COND_CLAUSES in 
    (rconcl thm1) = "T" =>
     SUBS [SYM thm1] (CONJUNCT1 thm2) |
     TRANS (SUBS [SYM thm1] (CONJUNCT2 thm2)) (COND_EVAL_CONV r) |
    REFL c;;

let BETA_COND_CONV = BETA_CONV THENC COND_EVAL_CONV;;

% --------------------------------------------------------------------------- %
% Conversion that checks that, for all k <= n, the agents given by the        %
% function f are prefixed agents.                                             %
% --------------------------------------------------------------------------- %
let IS_PREFIX_CHECK k n f =
     PROVE
      ("!^k. ^k <= ^n ==> Is_Prefix(^f ^k)",
       GEN_TAC THEN REWRITE_TAC [LESS_OR_EQ; LESS_THM; NOT_LESS_0] THEN 
       BETA_TAC THEN STRIP_TAC THEN
       ASM_REWRITE_TAC [INV_SUC_EQ; NOT_SUC; SUC_NOT; PREF_IS_PREFIX]);;  

% --------------------------------------------------------------------------- %
% Conversion for deleting nil subterms by means of the identity laws for the  %
% parallel operator.                                                          %
% --------------------------------------------------------------------------- %
let STRONG_PAR_NIL_CONV tm =
   is_par tm =>
    let P,Q = args_par tm in
    is_nil P => SPEC Q STRONG_PAR_IDENT_L |
    is_nil Q => SPEC P STRONG_PAR_IDENT_R |
    failwith `STRONG_PAR_NIL_CONV` | 
   failwith `STRONG_PAR_NIL_CONV`;; 

% --------------------------------------------------------------------------- %
% Conversion for deleting nil subterms by means of the identity laws for the  %
% parallel and summation operators.                                           %
% --------------------------------------------------------------------------- %
let STRONG_NIL_SUM_PAR_CONV tm =
   is_par tm =>
    let P,Q = args_par tm in 
    is_nil P => SPEC Q STRONG_PAR_IDENT_L |
    is_nil Q => SPEC P STRONG_PAR_IDENT_R |
    failwith `STRONG_NIL_SUM_PAR_CONV` |
   is_sum tm =>
    let P,Q = args_sum tm in 
    is_nil P => SPEC Q STRONG_SUM_IDENT_L |
    is_nil Q => SPEC P STRONG_SUM_IDENT_R |
    failwith `STRONG_NIL_SUM_PAR_CONV` |
   failwith `STRONG_NIL_SUM_PAR_CONV`;;

% --------------------------------------------------------------------------- %
% Conversion for extracting the prefixed action and the prefixed process by   %
% applying PREF_ACT and PREF_PROC, respectively.                              %
% --------------------------------------------------------------------------- %
let PREFIX_EXTRACT tm =
   let (opr, opd) = dest_comb tm in 
   let (act, proc) = args_prefix opd in 
   (opr = "PREF_ACT") => SPECL [act; proc] PREF_ACT |  
   (opr = "PREF_PROC") => SPECL [act; proc] PREF_PROC | 
   failwith `PREFIX_EXTRACT`;;

% --------------------------------------------------------------------------- %
% Conversion for simplifying a summation term.                                %
% --------------------------------------------------------------------------- %
let SIMPLIFY_CONV =
    (DEPTH_CONV BETA_COND_CONV) THENC (DEPTH_CONV PREFIX_EXTRACT);;

% --------------------------------------------------------------------------- %
% Conversion to compute the synchronizing summands.                           %
% --------------------------------------------------------------------------- %
let ALL_SYNC_CONV f n1 f' n2 = 
   let c1 = REWRITE_CONV [ALL_SYNC] "ALL_SYNC ^f ^n1 ^f' ^n2" in  
   let c2 = TRANS c1 (SIMPLIFY_CONV (rconcl c1)) in 
   let c3 = TRANS c2 (REWRITE_CONV [SYNC] (rconcl c2)) in
   let c4 = TRANS c3 (SIMPLIFY_CONV (rconcl c3)) in 
   let c5 = TRANS c4 (REWRITE_CONV [LABEL; COMPL; Action_Distinct_label;   
                                    Label_Not_Eq; Label_Not_Eq'; Label_One_One] 
                      (rconcl c4)) in 
    TRANS c5 (REW_RHS_RULE [] (DEPTH_CONV string_EQ_CONV (rconcl c5)));; 

% --------------------------------------------------------------------------- %
% Conversion for the application of the law for the parallel operator in the  %
% general case of at least one summation agent in parallel.                   %
% --------------------------------------------------------------------------- %
let STRONG_PAR_SUM_CONV tm =
   let comp_fun tm =  
    let thm = REW_RHS_RULE [SIGMA] ((DEPTH_CONV BETA_CONV) tm) in
    let thm' = REW_RHS_RULE [INV_SUC_EQ; NOT_SUC; SUC_NOT;
                             PREF_ACT; PREF_PROC]
               ((DEPTH_CONV BETA_CONV) (rconcl thm)) in TRANS thm thm' 
   and ls1,ls2 = (flat_sum # flat_sum) (args_par tm) 
   and P1,P2 = args_par tm in 
   let ARBtm = inst [] [": CCS",": *"] "ARB: *" in   
   let f = "\x: num. ^(sum_to_fun ls1 ARBtm "0")"
   and f' = "\x: num. ^(sum_to_fun ls2 ARBtm "0")"
   and [n1; n2] = map n_elems [ls1; ls2] in 
   let [thm1;thm2] = 
       map (\t. REWRITE_RULE [INV_SUC_EQ; NOT_SUC; SUC_ID]
                (BETA_RULE (REWRITE_CONV [SIGMA] t)))  
           ["SIGMA ^f ^n1"; "SIGMA ^f' ^n2"] 
   and thmp1 = IS_PREFIX_CHECK "i: num" n1 f 
   and thmp2 = IS_PREFIX_CHECK "j: num" n2 f' 
   and [thmc1; thmc2] =
        map comp_fun 
        ["SIGMA (\i. prefix(PREF_ACT(^f i))
                           (par(PREF_PROC(^f i))(SIGMA ^f' ^n2))) ^n1"; 
         "SIGMA (\j. prefix(PREF_ACT(^f' j))
                           (par(SIGMA ^f ^n1)(PREF_PROC(^f' j)))) ^n2"] 
   and thm_sync = ALL_SYNC_CONV f n1 f' n2 in  
   let thmt =
       REWRITE_RULE [thmc1; thmc2; thm_sync] 
       (MATCH_MP (SPECL [f; n1; f'; n2] STRONG_PAR_LAW)
        (CONJ thmp1 thmp2)) in 
   is_prefix P1 => 
    let thma' = S_SUBST (STRONG_SUM_ASSOC_CONV P2) "par ^P1 ^P2" in 
     S_TRANS thma' (REW_LHS_RULE [thm1; thm2] thmt) | 
   is_prefix P2 => 
    let thma' = S_SUBST (STRONG_SUM_ASSOC_CONV P1) "par ^P1 ^P2" in 
     S_TRANS thma' (REW_LHS_RULE [thm1; thm2] thmt) |  
   let thma = S_SUBST (STRONG_SUM_ASSOC_CONV P1) "par ^P1 ^P2" in 
   let thma' = S_TRANS thma 
               (S_SUBST (STRONG_SUM_ASSOC_CONV P2) (rhs_tm thma)) in 
    S_TRANS thma' (REW_LHS_RULE [thm1; thm2] thmt);; 

% --------------------------------------------------------------------------- %
% Conversion for the application of the laws for the parallel operator in the % 
% particular case of two prefixed agents in parallel.                         %
% --------------------------------------------------------------------------- %
let STRONG_PAR_PREFIX_CONV (u,P) (v,Q) =   
   is_tau u & is_tau v => SPECL [P; Q] STRONG_PAR_TAU_TAU |  
   is_tau u => SPECL [P; v; Q] STRONG_PAR_TAU_PREF |  
   is_tau v => SPECL [u; P; Q] STRONG_PAR_PREF_TAU |  
    let [l1; l2] = map arg_action [u; v] in  
    let thmc = REW_RHS_RULE [COMPL] (REFL "^l1 = COMPL ^l2") in  
    (rconcl thmc = "T") =>                %synchronization between l1 and l2% 
     SPECL [P; Q]                      
     (MP (SPECL [l1; l2] STRONG_PAR_PREF_SYNCR)  
         (EQT_ELIM thmc)) |            %no synchronization between l1 and l2% 
     let thm_lab = TRANS thmc (Label_EQ_CONV (rconcl thmc)) in  
     SPECL [P; Q] 
     (MP (SPECL [l1; l2] STRONG_PAR_PREF_NO_SYNCR)  
         (EQF_ELIM thm_lab));;   

% --------------------------------------------------------------------------- %
% Conversion for the application of the laws for the parallel operator.       %
% --------------------------------------------------------------------------- %
let STRONG_PAR_ELIM_CONV tm =
   is_par tm =>
    let P1,P2 = args_par tm in 
    (is_prefix P1 & is_prefix P2) =>
     let thm = STRONG_PAR_PREFIX_CONV (args_prefix P1) (args_prefix P2) in  
      S_TRANS thm 
      (S_DEPTH_CONV STRONG_NIL_SUM_PAR_CONV (rhs_tm thm)) | 
    (is_sum P1 & is_prefix P2) or (is_prefix P1 & is_sum P2) or 
    (is_sum P1 & is_sum P2) =>  
     let thm = STRONG_PAR_SUM_CONV tm in  
      S_TRANS thm 
      (S_DEPTH_CONV STRONG_NIL_SUM_PAR_CONV (rhs_tm thm)) |
    failwith `STRONG_PAR_ELIM_CONV` |
   failwith `STRONG_PAR_ELIM_CONV`;;

% --------------------------------------------------------------------------- %
% Conversion for applying the expansion theorem (parallel and restriction     %
% operators).                                                                 %
% --------------------------------------------------------------------------- %
let STRONG_EXP_THM_CONV =
    (S_DEPTH_CONV STRONG_PAR_ELIM_CONV) S_THENC
    (S_TOP_DEPTH_CONV STRONG_RESTR_ELIM_CONV) S_THENC
    (S_DEPTH_CONV STRONG_SUM_NIL_CONV);;

