% =========================================================================== %
% FILE          : runM.ml                                                     %
% DESCRIPTION   : Conversion for computing the transitions of a pure CCS agent%
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : June 1994                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Function for applying a list of tactics to a list of subgoals.              %
% --------------------------------------------------------------------------- %
letrec list_apply_tac (f: * -> tactic) (actl : * list) : tactic list =
   (null actl) => [] | f (hd actl) . list_apply_tac f (tl actl);;

% --------------------------------------------------------------------------- %
% Conversion for executing the operational semantics.                         %
% --------------------------------------------------------------------------- %
letrec runM tm = 
   let list2_pair [x;y] = (x,y)
   and f = (\c. map (snd o dest_eq) (conjuncts c)) in

   is_nil tm => NIL_NO_TRANS | 

   is_prefix tm => 
    let u,P = args_prefix tm in SPECL [u; P] TRANS_PREFIX_EQ |  

   is_sum tm => 
    let P1,P2 = args_sum tm in 
    let thm1 = runM P1 
    and thm2 = runM P2 in 
     REWRITE_RULE [thm1; thm2] (SPECL [P1; P2] TRANS_SUM_EQ) | 

   is_restr tm => 
    letrec extr_acts actl L =
       (null actl) => [] |
        let act = hd actl in
        is_tau act => act . extr_acts (tl actl) L |
        let l = arg_action act in
        let thml = Label_IN_CONV l L in
        (rconcl thml = "T") => extr_acts (tl actl) L |
        let thmlc = Label_IN_CONV 
                    (rconcl(REWRITE_CONV [COMPL] "COMPL ^l")) L in
        (rconcl thmlc = "T") => extr_acts (tl actl) L |
        act . extr_acts (tl actl) L in 
 
    let P,L = args_restr tm in 
    let thm = runM P in 
    (rconcl thm = "F") => 
     prove 
     ("!u E. TRANS ^tm u E = F", 
      REPEAT GEN_TAC THEN EQ_TAC THENL 
      [DISCH_TAC THEN IMP_RES_TAC TRANS_RESTR THEN 
       IMP_RES_TAC thm 
       ; REWRITE_TAC[] ]) |  
    let dl = disjuncts(rconcl thm) in 
    let actl = map (snd o dest_eq o hd o conjuncts) dl in   
    let actl_not = extr_acts actl L in 
    (null actl_not) => 
     prove 
     ("!u E. TRANS ^tm u E = F", 
      REPEAT GEN_TAC THEN EQ_TAC THENL   
      [STRIP_TAC THEN IMP_RES_TAC TRANS_RESTR THENL 
       [IMP_RES_TAC thm THENL  
        list_apply_tac   
        (\a. CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct]
                               (ASSUME "u = ^a"))) actl
        ; 
        IMP_RES_TAC thm THENL  
        list_apply_tac 
        (\a. 
          ASSUME_TAC (REWRITE_RULE [ASSUME "u = label l"; Action_One_One] 
                      (ASSUME "u = ^a")) THEN
          CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME "l = ^(arg_action a)";
                         Label_IN_CONV (arg_action a) L]   
           (ASSUME "~l IN ^L")) THEN 
          CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME "l = ^(arg_action a)"; COMPL;
                         Label_IN_CONV 
                         (rconcl(REWRITE_CONV [COMPL] "COMPL ^(arg_action a)")) 
                         L]
           (ASSUME "~(COMPL l) IN ^L"))) actl ] 
       ;
       REWRITE_TAC[] ]) | 
% actl_not is not empty => the list of pairs lp is not empty as well % 
    letrec build_disj lp L = 
       let u,p = hd lp in 
       (null (tl lp)) => mk_conj("u = ^u", "E = ^(mk_restr(p,L))") |  
       mk_disj(mk_conj("u = ^u", "E = ^(mk_restr(p,L))"),
               build_disj (tl lp) L) in     
    let lp = map (list2_pair o f) 
             (filter (\c. mem(snd(dest_eq(hd(conjuncts c)))) actl_not) dl) in 
    let dsjt = build_disj lp L in 
    prove 
    ("!u E. TRANS ^tm u E = ^dsjt", 
     REPEAT GEN_TAC THEN EQ_TAC THENL 
     [DISCH_TAC THEN IMP_RES_TAC TRANS_RESTR THENL 
      [IMP_RES_TAC thm THENL 
       list_apply_tac
       (\a. CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME "u = tau"; Action_Distinct]
                                     (ASSUME "u = ^a")) THEN 
            ASM_REWRITE_TAC[]) actl 
       ; 
       IMP_RES_TAC thm THENL
       list_apply_tac
       (\a. 
         ASSUME_TAC (REWRITE_RULE [ASSUME "u = label l"; Action_One_One] 
                     (ASSUME "u = ^a")) THEN
         CHECK_ASSUME_TAC
         (REWRITE_RULE [ASSUME "l = ^(arg_action a)";
                        Label_IN_CONV (arg_action a) L]  
                 (ASSUME "~l IN ^L")) THEN
         CHECK_ASSUME_TAC
         (REWRITE_RULE [ASSUME "l = ^(arg_action a)"; COMPL;
                        Label_IN_CONV 
                        (rconcl(REWRITE_CONV [COMPL] "COMPL ^(arg_action a)"))
                        L]
                 (ASSUME "~(COMPL l) IN ^L")) THEN 
         ASM_REWRITE_TAC[]) actl ] 
      ;
      STRIP_TAC THENL  
      list_apply_tac
      (\(a,P). 
        REWRITE_TAC [ASSUME "u = ^a"; 
                     ASSUME "E = restr ^P ^L"] THEN  
        RESTR_TAC THEN EXISTS_TAC (arg_action a) THEN 
        ASM_REWRITE_TAC [thm; Label_IN_CONV (arg_action a) L; COMPL;  
                         Label_IN_CONV 
                         (rconcl(REWRITE_CONV [COMPL] "COMPL ^(arg_action a)")) 
                         L]) lp ]) | 

%    is_relab tm => 
    let P,rf = args_relab tm in 
    let thm = runM P in 
    (rconcl thm = "F") =>
     prove
     ("!u E. TRANS ^tm u E = F",
      REPEAT GEN_TAC THEN EQ_TAC THENL
      [DISCH_TAC THEN IMP_RES_TAC TRANS_RELAB THEN
       IMP_RES_TAC thm 
       ; REWRITE_TAC[] ]) | % 
% ~(rconcl thm = "F") implies  dl is not empty %
%     letrec relab_act actl labl =
        (null actl) => []  | 
         let act = hd actl in 
         let thm_act = 
             REW_RHS_RULE [relabel; Apply_Relab; Label_Distinct;
                           Label_Distinct'; Label_One_One; COMPL; COMPL_COMPL]
             (REFL "relabel(Apply_Relab ^labl) ^act") in
         let thm_act' = RELAB_EVAL_CONV (rconcl thm_act) in
          TRANS thm_act thm_act'. relab_act (tl actl) labl in 
     letrec build_disj_relab rlp rf =
        let u,p = hd rlp in
        (null (tl rlp)) =>
         mk_conj("u = ^u", "E = ^(mk_relab(p,rf))") | 
         mk_disj(mk_conj("u = ^u", "E = ^(mk_relab(p,rf))"), 
                 build_disj_relab (tl rlp) rf) in 

     let dl = disjuncts(rconcl thm) in                     
     let actl = map (snd o dest_eq o hd o conjuncts) dl  
     and labl = arg_relabelling rf in 
     let thml = relab_act actl labl in 
     let rlp = combine (map rconcl thml, map (snd o list2_pair o f) dl) in 
     let disjt = build_disj_relab rlp rf in
     prove
     ("!u E. TRANS ^tm u E = ^disjt", 
      REPEAT GEN_TAC THEN EQ_TAC THENL
      [DISCH_TAC THEN IMP_RES_TAC TRANS_RELAB THEN IMP_RES_TAC thm THENL 
       list_apply_tac
       (\(a,thm_act). 
         REWRITE_TAC  
         [REWRITE_RULE [ASSUME "u' = ^a"; thm_act]  
                        (REWRITE_RULE [SYM(MATCH_MP RELAB_LABL 
                                          (ASSUME "RELAB ^labl = RELAB labl"))]
          (ASSUME "u = relabel(Apply_Relab labl)u'"))] THEN 
         ASM_REWRITE_TAC[]) (combine (actl,thml))    
       ;
       STRIP_TAC THENL 
       list_apply_tac 
       (\(a,P),thm_act.
         REWRITE_TAC [ONCE_REWRITE_RULE [SYM thm_act] 
                             (ASSUME "u = ^a");
                      ASSUME "E = relab ^P ^rf"] THEN
         RELAB_TAC THEN REWRITE_TAC [thm]) (combine (rlp,thml)) ]) |  
%    
   is_par tm => 
    letrec build_disj1 dl P =
       let u,p = hd dl in
       (null (tl dl)) => mk_conj("u = ^u", "E = ^(mk_par(p,P))") |
        mk_disj(mk_conj("u = ^u", "E = ^(mk_par(p,P))"),
                build_disj1 (tl dl) P)
    and build_disj2 dl P =
       let u,p = hd dl in
       (null (tl dl)) => mk_conj("u = ^u", "E = ^(mk_par(P,p))") |
        mk_disj(mk_conj("u = ^u", "E = ^(mk_par(P,p))"),
                build_disj2 (tl dl) P) 
    and build_disj_tau p syncl =
       (null syncl) => "F" |
       let _,p' = hd syncl in
       mk_disj(mk_conj("u = tau", "E = ^(mk_par(p,p'))"),
               build_disj_tau p (tl syncl)) 
    and act_sync dl1 dl2 =
       (null dl1) => [] |
        let (act,p) = hd dl1 in
        let syncl = filter (\(a,p). a = rconcl(REWRITE_CONV [COMPL_ACT; COMPL] 
                                               "COMPL_ACT ^act")) dl2 in
        (null syncl) => act_sync (tl dl1) dl2 |
                        act . act_sync (tl dl1) dl2 in
    letrec build_sync dl1 dl2 =
       let (act,p) = hd dl1 in
       let syncl =
           filter (\(a,p).
                     a = rconcl(REWRITE_CONV [COMPL_ACT; COMPL]
                                "COMPL_ACT ^act")) dl2 in
       (null (tl dl1)) =>
        build_disj_tau p syncl |
        mk_disj(build_disj_tau p syncl, build_sync (tl dl1) dl2) in

    let P1,P2 = args_par tm in 
    let thm1 = runM P1 
    and thm2 = runM P2 in 
    (rconcl thm1 = "F") & (rconcl thm2 = "F") => 
     prove
     ("!u E. TRANS ^tm u E = F", 
      REPEAT GEN_TAC THEN EQ_TAC THENL
      [DISCH_TAC THEN IMP_RES_TAC TRANS_PAR THENL
       [IMP_RES_TAC thm1 ; IMP_RES_TAC thm2 ; IMP_RES_TAC thm1 ] ;  
       REWRITE_TAC[] ]) |       
    (rconcl thm1 = "F") => 
     let dl2 = map (list2_pair o f) (disjuncts (rconcl thm2)) in 
     let actl2 = map fst dl2 
     and disj_nosync = build_disj2 dl2 P1 in  
     prove 
     ("!u E. TRANS ^tm u E = ^disj_nosync",  
      REPEAT GEN_TAC THEN EQ_TAC THENL
      [DISCH_TAC THEN IMP_RES_TAC TRANS_PAR THENL
       [IMP_RES_TAC thm1 ;  
        IMP_RES_TAC thm2 THEN ASM_REWRITE_TAC[] ; 
        IMP_RES_TAC thm1 ]
       ;
       STRIP_TAC THENL 
       (list_apply_tac
       (\a. ASM_REWRITE_TAC[] THEN PAR2_TAC THEN
            REWRITE_TAC [GEN_ALL thm2]) actl2) ]) | 
    (rconcl thm2 = "F") => 
     let dl1 = map (list2_pair o f) (disjuncts (rconcl thm1)) in 
     let actl1 = map fst dl1 
     and disj_nosync = build_disj1 dl1 P2 in 
     prove
     ("!u E. TRANS ^tm u E = ^disj_nosync",
      REPEAT GEN_TAC THEN EQ_TAC THENL
      [DISCH_TAC THEN IMP_RES_TAC TRANS_PAR THENL
       [IMP_RES_TAC thm1 THEN ASM_REWRITE_TAC[] ; 
        IMP_RES_TAC thm2 ;
        IMP_RES_TAC thm2 ]
       ;
       STRIP_TAC THENL
       (list_apply_tac
       (\a. ASM_REWRITE_TAC[] THEN PAR1_TAC THEN
            REWRITE_TAC [GEN_ALL thm1]) actl1) ]) | 
% ~(rconcl thm1 = "F") and ~(rconcl thm2 = "F") => dl1 and dl2 are not empty %
    let [dl1;dl2] = 
        map ((map (list2_pair o f)) o disjuncts o rconcl) [thm1;thm2] in
    let [actl1;actl2] = map (map fst) [dl1;dl2] 
    and disj_nosync = mk_disj(build_disj1 dl1 P2, build_disj2 dl2 P1) 
    and disj_sync = rconcl(REWRITE_CONV [] (build_sync dl1 dl2)) in 
    (disj_sync = "F") => 
    prove 
    ("!u E. TRANS ^tm u E = ^disj_nosync",
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN IMP_RES_TAC TRANS_PAR THENL
      [IMP_RES_TAC thm1 THEN ASM_REWRITE_TAC[] ;  
       IMP_RES_TAC thm2 THEN ASM_REWRITE_TAC[] ;  
       IMP_RES_TAC thm1 THEN IMP_RES_TAC thm2 THENL
       (list_apply_tac
       (\a.  
        (let eq = REWRITE_RULE  
        [REWRITE_RULE [Action_One_One] (ASSUME "label l = ^(hd actl1)"); COMPL] 
         (ASSUME "label(COMPL l) = ^a") in 
       CHECK_ASSUME_TAC 
       (REWRITE_RULE [eq] (Action_EQ_CONV (concl eq))))) actl2) ]   
      ; 
      STRIP_TAC THENL  % as many as the number of the summands %  
      (list_apply_tac
       (\a. ASM_REWRITE_TAC[] THEN PAR1_TAC THEN 
            REWRITE_TAC [GEN_ALL thm1]) actl1) @ 
      (list_apply_tac
       (\a. ASM_REWRITE_TAC[] THEN PAR2_TAC THEN 
            REWRITE_TAC [GEN_ALL thm2]) actl2) @  
      (list_apply_tac 
       (\a. ASM_REWRITE_TAC[] THEN PAR3_TAC THEN 
            EXISTS_TAC (arg_action a) THEN 
            REWRITE_TAC [COMPL; GEN_ALL thm1; GEN_ALL thm2]) 
         (act_sync dl1 dl2)) ]) |    
    prove
    ("!u E. TRANS ^tm u E = ^(mk_disj(disj_nosync,disj_sync))",
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN IMP_RES_TAC TRANS_PAR THENL
      [IMP_RES_TAC thm1 THEN ASM_REWRITE_TAC[] ;
       IMP_RES_TAC thm2 THEN ASM_REWRITE_TAC[] ;
       IMP_RES_TAC thm1 THEN IMP_RES_TAC thm2 THEN ASM_REWRITE_TAC[] ]
      ;
      STRIP_TAC THENL  % as many as the number of the summands %
      (list_apply_tac
       (\a. ASM_REWRITE_TAC[] THEN PAR1_TAC THEN
            REWRITE_TAC [GEN_ALL thm1]) actl1) @
      (list_apply_tac
       (\a. ASM_REWRITE_TAC[] THEN PAR2_TAC THEN
            REWRITE_TAC [GEN_ALL thm2]) actl2) @
      (list_apply_tac
       (\a. ASM_REWRITE_TAC[] THEN PAR3_TAC THEN
            EXISTS_TAC (arg_action a) THEN
            REWRITE_TAC [COMPL; GEN_ALL thm1; GEN_ALL thm2])
         (act_sync dl1 dl2)) ]) |

   is_rec tm =>
    let X,P = args_rec tm in
    let thmS = REWRITE_CONV [CCS_Subst] "CCS_Subst ^P ^tm ^X" in
    let thm = runM (rconcl thmS) in
    GEN_ALL (REWRITE_CONV [TRANS_REC_EQ; thmS; thm] "TRANS ^tm u E") |
% no need to distinguish on (rconcl thm) %
  
   failwith `runM`;; 
  
  
