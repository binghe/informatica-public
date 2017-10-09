(* -*- mode: lisp; coding: utf-8 -*- *) (* Emacs hangs in SML mode *)
(* ========================================================================== *)
(*                                                                            *)
(*     A formalized general Graph Theory for HOL4, version 1.0                *)
(*       (based on Reinhard Diestel's "Graph Theory" book)                    *)
(*                                                                            *)
(* ========================================================================== *)

(*
 * Copyright 2017  University of Bologna, Italy (Author: Chun Tian)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 * THIS CODE IS PROVIDED *AS IS* BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, EITHER EXPRESS OR IMPLIED, INCLUDING WITHOUT LIMITATION ANY IMPLIED
 * WARRANTIES OR CONDITIONS OF TITLE, FITNESS FOR A PARTICULAR PURPOSE,
 * MERCHANTABLITY OR NON-INFRINGEMENT.
 * See the Apache 2 License for the specific language governing permissions and
 * limitations under the License.
 *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory realTheory pred_setTheory pathTheory relationTheory
     oneTheory pairTheory;

(******************************************************************************)
(*									      *)
(*      Backward compatibility and utility tactic/tacticals (2017/07/16)      *)
(*									      *)
(******************************************************************************)

local
    val PAT_X_ASSUM = PAT_ASSUM;
    val qpat_x_assum = Q.PAT_ASSUM;
    open Tactical
in
    (* Backward compatibility with Kananaskis 11 *)
    val PAT_X_ASSUM = PAT_X_ASSUM;
    val qpat_x_assum = qpat_x_assum;
end;

(** Q.GENL generalises in wrong order #428, fixed on June 27, 2017 *)
fun Q_GENL qs th = List.foldr (fn (q, th) => Q.GEN q th) th qs;

(* Tacticals for better expressivity *)
fun fix  ts = MAP_EVERY Q.X_GEN_TAC ts;		(* from HOL Light *)
fun set  ts = MAP_EVERY Q.ABBREV_TAC ts;	(* from HOL mizar mode *)
fun take ts = MAP_EVERY Q.EXISTS_TAC ts;	(* from HOL mizar mode *)
val op // = op REPEAT				(* from Matita *)
val Know = Q_TAC KNOW_TAC;			(* from util_prob *)
val Suff = Q_TAC SUFF_TAC;			(* from util_prob *)
fun K_TAC _ = ALL_TAC;				(* from util_prob *)
val KILL_TAC = POP_ASSUM_LIST K_TAC;		(* from util_prob *)
fun wrap a = [a];

fun PRINT_TAC s gl =				(* from cardinalTheory *)
  (print ("** " ^ s ^ "\n"); ALL_TAC gl);

fun COUNT_TAC tac g =				(* from Konrad Slind *)
   let val res as (sg, _) = tac g
       val _ = print ("subgoals: " ^ Int.toString (List.length sg) ^ "\n")
   in res end;

val _ = new_theory "Graph";

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*   1. The Basics                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* type variables: 'a: type of vertices, 'b: type of labels *)
val _ = type_abbrev ("edge", ``:'a set # 'b # 'a set``);
(* val _ = disable_tyabbrev_printing "edge"; *)

(* the representation type for all graphs *)
val _ = type_abbrev ("REP_graph", ``:'a set # (('a, 'b) edge) set``);

(* essential accessors of REP_graph *)
val REP_vertices_def = Define `REP_vertices ((V, E) :('a, 'b) REP_graph) = V`;
val REP_edges_def    = Define `REP_edges    ((V, E) :('a, 'b) REP_graph) = E`;

val REP_graph = store_thm ("REP_graph",
  ``!g :('a, 'b) REP_graph. (REP_vertices g, REP_edges g) = g``,
    STRIP_TAC
 >> MP_TAC (Q.ISPEC `(g :('a, 'b) REP_graph)` pair_CASES)
 >> RW_TAC std_ss [REP_vertices_def, REP_edges_def]);

val label_def = Define `label ((ins, lab, outs) :('a, 'b) edge) = lab`;

(** init = initials *)
val inits_def = Define `inits ((ins, lab, outs) :('a, 'b) edge) = ins`;

(** ter = terminals *)
val ters_def  = Define `ters  ((ins, lab, outs) :('a, 'b) edge) = outs`;

val edge_thm = store_thm (
   "edge_thm", ``!e :('a, 'b) edge. (inits e, label e, ters e) = e``,
    STRIP_TAC
 >> MP_TAC (Q.ISPEC `(e :('a, 'b) edge)` pair_CASES)
 >> STRIP_TAC
 >> Q.UNDISCH_TAC `e = (q, r)`
 >> MP_TAC (Q.ISPEC `(r :'b # 'a set)` pair_CASES)
 >> REPEAT STRIP_TAC
 >> RW_TAC std_ss [label_def, inits_def, ters_def]);

(* An edge e is said to be directed from init (e) to ter (e) in graphs, in this case
   we expect (CARD (ters e) = 1) so that the only vertex can be chosen.
 *)
val init_def = Define `init e = CHOICE (inits e)`;
val  ter_def = Define ` ter e = CHOICE (ters e)`;

(* ends (e) is for undirected edges in hypergraphs or multigraphs, in latter case
   we expect (CARD (ters e) = 1) /\ (CARD (ends e) = 1 or 2). ends (e) can also be
   used to get the ends set for directed graphs. (in this case the direction is not
   concerned for related definiton or theorem) *)
val ends_def  = Define `ends e = (inits e) UNION (ters e)`;

(* transformers of different types of edges used in some definitions *)
val labeled_directed_def = Define `
    labeled_directed (e :('a, 'b) edge) = (init e, label e, ter e)`;

val unlabeled_directed_def = Define `
    unlabeled_directed (e :('a, 'b) edge) = (init e, ter e)`;

val labeled_undirected_def = Define `
    labeled_undirected (e :('a, 'b) edge) = (label e, ends e)`;

val unlabeled_undirected_def = Define `
    unlabeled_undirected (e :('a, 'b) edge) = ends e`;

(* For the most general concept of (hyper)graph, the only requirement is that,
   the ends of all edges must be in the vertex set, nothing else. *)
val hypergraph_def = Define
   `hypergraph ((V, E) :('a, 'b) REP_graph) = !e. e IN E ==> (ends e) SUBSET V`;

val REP_empty_graph_def = Define `(REP_empty_graph :('a, 'b) REP_graph) = ({}, {})`;

val REP_empty_graph_is_graph = store_thm ("REP_empty_graph_is_graph",
  ``hypergraph REP_empty_graph``,
    REWRITE_TAC [REP_empty_graph_def, hypergraph_def]
 >> PROVE_TAC [NOT_IN_EMPTY]);

val EXISTS_graph = store_thm ("EXISTS_graph", ``?g. hypergraph g``,
    EXISTS_TAC ``REP_empty_graph``
 >> REWRITE_TAC [REP_empty_graph_is_graph]);

val graph_TY_DEF = new_type_definition ("graph", EXISTS_graph);

val graph_ISO_DEF = define_new_type_bijections
		      { ABS  = "ABS_graph",
			REP  = "REP_graph",
			name = "graph_ISO_DEF",
			tyax =  graph_TY_DEF };
(*
graph_ABS_REP =
   |-  a. ABS_graph (REP_graph a) = a:
   thm
graph_REP_ABS =
   |-  r. hypergraph r = (REP_graph (ABS_graph r) = r):
   thm
 *)
val [graph_ABS_REP, graph_REP_ABS] =
    map save_thm
        (combine (["graph_ABS_REP", "graph_REP_ABS"], CONJ_LIST 2 graph_ISO_DEF));

(*
ABS_graph_one_one =
   |- !r r'. hypergraph r  ==>
	     hypergraph r' ==>
	     ((ABS_graph r = ABS_graph r') <=> (r = r'))

ABS_graph_onto =
   |- !a. ?r. (a = ABS_graph r) /\ hypergraph r

REP_graph_one_one =
   |- !a a'. (REP_graph a = REP_graph a') <=> (a = a')

REP_graph_onto =
   |- !r. hypergraph r <=> (!a. r = REP_graph a)
 *)
val [ABS_graph_one_one, ABS_graph_onto,
     REP_graph_one_one, REP_graph_onto] =
    map save_thm
        (combine (["ABS_graph_one_one", "ABS_graph_onto",
                   "REP_graph_one_one", "REP_graph_onto"],
                  map (fn f => f graph_ISO_DEF)
                      [prove_abs_fn_one_one, prove_abs_fn_onto,
                       prove_rep_fn_one_one, prove_rep_fn_onto]));

val REP_graph_thm = store_thm ("REP_graph_thm", ``!G. hypergraph (REP_graph G)``,
    GEN_TAC
 >> REWRITE_TAC [REP_graph_onto]
 >> Q.EXISTS_TAC `G`
 >> REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*   1.1 Graphs                                                               *)
(*                                                                            *)
(******************************************************************************)

val graph_vertices_def = Define `
    graph_vertices G = REP_vertices (REP_graph G)`;
val _ = overload_on ("vertices", ``graph_vertices``);

val graph_edges_def = Define `
    graph_edges G = REP_edges (REP_graph G)`;
val _ = overload_on ("edges", ``graph_edges``);

(* self-loop is forbidden for graphs *)
val is_graph_def = Define `
    is_graph G = !e. e IN (edges G) ==> (CARD (ends e) = 2)`;

val labeled_directed_edges_def = Define `
    labeled_directed_edges G = IMAGE labeled_directed (edges G)`;

val unlabeled_directed_edges_def = Define `
    unlabeled_directed_edges G = IMAGE unlabeled_directed (edges G)`;

val labeled_undirected_edges_def = Define `
    labeled_undirected_edges G = IMAGE labeled_undirected (edges G)`;

val unlabeled_undirected_edges_def = Define `
    unlabeled_undirected_edges G = IMAGE unlabeled_undirected (edges G)`;

hide "labels"; (* from pathTheory *)
val graph_labels_def = Define `graph_labels G = IMAGE label (edges G)`;
val _ = overload_on ("labels", ``graph_labels``);
val _ = overload_on ("labels", ``path$labels``);

val empty_graph_def = Define `empty_graph = ABS_graph REP_empty_graph`;

val empty_graph_is_graph = store_thm (
   "empty_graph_is_graph",
  ``is_graph empty_graph``,
    REWRITE_TAC [is_graph_def, empty_graph_def, graph_edges_def]
 >> `(REP_graph (ABS_graph REP_empty_graph)) = REP_empty_graph`
	by PROVE_TAC [REP_empty_graph_is_graph, graph_REP_ABS]
 >> ASM_REWRITE_TAC [REP_empty_graph_def, REP_edges_def, NOT_IN_EMPTY]);

val empty_def = Define `empty G = (G = empty_graph)`;

val order_def = Define `order G = CARD (vertices G)`;

val empty_graph_order = store_thm (
   "empty_graph_order", ``order empty_graph = 0``,
    REWRITE_TAC [order_def, graph_vertices_def, empty_graph_def]
 >> `(REP_graph (ABS_graph REP_empty_graph)) = REP_empty_graph`
	by PROVE_TAC [REP_empty_graph_is_graph, graph_REP_ABS]
 >> ASM_REWRITE_TAC [CARD_DEF, REP_vertices_def, REP_empty_graph_def]);

val trivial_def = Define `
    trivial G = (order G = 0) \/ (order G = 1)`;

val empty_graph_is_trivial = store_thm ("empty_graph_is_trivial",
  ``trivial empty_graph``,
    REWRITE_TAC [trivial_def, empty_graph_order]);

val incident_def = Define `incident v e = v IN (ends e)`;

val adjacent_vertices_def = Define `
    adjacent_vertices (G :('a, 'b) graph) (x :'a) (y :'a) =
	?e. e IN (edges G) /\ (incident x e) /\ (incident y e)`;

val adjacent_edges_def = Define `
    adjacent_edges (G :('a, 'b) graph) (x :('a, 'b) edge) (y :('a, 'b) edge) =
	~(x = y) /\ ?(v :'a). (incident v x) /\ (incident v y)`;

val independent_vertices_def = Define `
    independent_vertices G x y = ~(x = y) /\ ~(adjacent_vertices G x y)`;

val independent_edges_def = Define `
    independent_edges G x y = ~(x = y) /\ ~(adjacent_edges G x y)`;

val general_homomorphism_def = Define `
    general_homomorphism psi phi (G :('a, 'b) graph) (G' :('c, 'd) graph) =
        !ins lab outs. (ins, lab, outs) IN (edges G) ==>
	  (IMAGE phi ins, psi lab, IMAGE phi outs) IN (edges G')`;

val homomorphism_def = Define `homomorphism = general_homomorphism I`;

val INV_DEF = Define `INV f = (\y. @x. y = f x)`;

val general_isomorphism_def = Define `
    general_isomorphism psi phi (G :('a, 'b) graph) (G' :('c, 'd) graph) =
        BIJ psi (labels G) (labels G') /\
	BIJ phi (vertices G) (vertices G') /\
	general_homomorphism psi phi G G' /\
	general_homomorphism (INV psi) (INV phi) G' G`;

val isomorphism_def = Define `isomorphism = general_isomorphism I`;

val union_def = Define `
    union G G' = ABS_graph ((vertices G) UNION (vertices G'),
			    (edges G) UNION (edges G'))`;

val inter_def = Define `
    inter G G' = ABS_graph ((vertices G) INTER (vertices G'),
			    (edges G) INTER (edges G'))`;

val disjoint_def = Define `
    disjoint G G' = (inter G G' = empty_graph)`;

val subgraph_def = Define (* G' is a subgraph of G *) `
    subgraph G' G = (vertices G') SUBSET (vertices G) /\ (edges G') SUBSET (edges G)`;

val supergraph_def = Define (* G is a supergraph of G' *) `
    supergraph G G' = subgraph G' G`;

(* G' is subgraph of G and G' contains all the edges xy IN E with x,y IN V', then G' is
   an induced subgraph of G. *)
val induced_subgraph_def = Define `
    induced_subgraph G' G = subgraph G' G /\
	!e. e IN (edges G) /\ (ends e) SUBSET (vertices G') ==> e IN (edges G')`;

(* (continued) we say that V' induces or spans G' in G, and write G' =: G[V'] *)
val induces_def = Define `
    induces G V' = ABS_graph (V', { e | e IN (edges G) /\ (ends e) SUBSET V'})`;

(* If H is a subgraph of G, not necessary induced, we abbreviate G[V(H)] to G[H] *)
val spans_def = Define `
    spans G H = induces G (vertices H)`;

(* Finally, G' SUBSET G is a spanning subgraph of G if V' spans all of G. i.e. if V' = V *)
val spanning_subgraph_def = Define `
    spanning_subgraph G' G = subgraph G' G /\ (vertices G' = vertices G)`;

val removes_def = Define `
    removes G U = ABS_graph ((vertices G) DIFF U,
			     {e | e IN (edges G) /\ !v. incident v e ==> ~(v IN U)})`;

(* edge_maximal is meaningful for unlabeled graphs only, we also assume undirected here *)
val edge_maximal_def = Define `
    edge_maximal (G :('a, 'b) graph) =
    ~(!G' :('a, 'b) graph. (vertices G = vertices G') /\
	(unlabeled_undirected_edges G) PSUBSET (unlabeled_undirected_edges G'))`;

(******************************************************************************)
(*                                                                            *)
(*   1.2 The degree of a vertex                                               *)
(*                                                                            *)
(******************************************************************************)

val degree_def = Define `
    degree (v:'a) (G:('a, 'b) graph) = CARD {e | e IN (edges G) /\ incident v e}`;

val minimal_degree_def = Define `
    minimal_degree (G:('a, 'b) graph) = MIN_SET (IMAGE (\v. degree v G) (vertices G))`;

val maximal_degree_def = Define `
    maximal_degree (G:('a, 'b) graph) = MAX_SET (IMAGE (\v. degree v G) (vertices G))`;

val average_degree_def = Define `
    average_degree (G:('a, 'b) graph) =
	real_of_num (SUM_IMAGE (\v. degree v G) (vertices G)) / real_of_num (order G)`;

(******************************************************************************)
(*                                                                            *)
(*   1.3 Paths and cycles                                                     *)
(*                                                                            *)
(******************************************************************************)

val distinct_path_def = Define `
    distinct_path p = !m n. m IN PL p /\ n IN PL p /\ ~(m = n) ==> ~((el m p) = (el n p))`;

(* NOTE: in Diestel's book, a path is a subgraph of the graph containing it. But here we want
   to benefit from the existing pathTheory in HOL, so we treat "path" as a different type. *)

val path_def = Define `
    path (p :('a, 'b) path) (G :('a, 'b) graph) =
	~(is_stopped p) /\ (distinct_path p) /\ okpath (\x r y. ({x}, r, {y}) IN (edges G)) p`;

val path_vertices_def = Define `
    path_vertices p = IMAGE (\n. el n p) (PL p)`;
val _ = overload_on ("vertices", ``path_vertices``);

val path_edges_def = Define `
    path_edges p = { (ins, lab, outs) |
		     (okpath (\x r y. (lab = r) /\ (ins = {x}) /\ (outs = {y})) p) }`;
val _ = overload_on ("edges", ``path_edges``);

val path_as_graph_def = Define `path_as_graph p = ABS_graph (path_vertices p, path_edges p)`;

val xy_path_def = Define `
    xy_path G x y p = path p G /\ (x = (first p)) /\ (y = (last p))`;

val xy_connected_def = Define `
    xy_connected G x y = !p. xy_path G x y p`;

val AB_path_def = Define `
    AB_path G A B p = path p G /\
		      ((vertices p) INTER A = {first p}) /\
		      ((vertices p) INTER B = {last p}) `;

val distinct_cycle_def = Define `
    distinct_cycle p = (first p = last p) /\ distinct_path (tail p)`;

val cycle_def = Define `
    cycle (p :('a, 'b) path) (G :('a, 'b) graph) =
	(distinct_cycle p) /\ okpath (\x r y. (x, r, y) IN (labeled_directed_edges G)) p`;

val has_cycles_def = Define `has_cycles G = ?c. cycle c G`;

val girth_def = Define `
    girth G = MIN_SET { THE (length c) | cycle c G }`;

val circumference_def = Define `
    circumference G = MAX_SET { THE (length c) | cycle c G }`;

val chord_def = Define `
    chord G c e = e IN (edges G) /\ (ends e) SUBSET (path_vertices c) /\ ~(e IN (path_edges c))`;

val distance_def = Define `
    distance G x y = MIN_SET { THE (length p) | xy_path G x y p }`;

val diameter_def = Define `
    diameter G = MAX_SET { THE (length p) | !x y. x IN (vertices G) /\ y IN (vertices G)
						/\ xy_path G x y p }`;

val greatest_distance_from_others = Define `
    greatest_distance_from_others G v = MAX_SET { THE (length p) | path p G /\ (v = last p) }`;

val central_def = Define `
    central G v = v IN (vertices G) /\
		  !x. x IN (vertices G) /\ ~(x = v) ==>
			greatest_distance_from_others G v <= greatest_distance_from_others G x`;

val radius_def = Define `
    radius G = greatest_distance_from_others G (@v. central G v)`;

(******************************************************************************)
(*                                                                            *)
(*   1.4 Connectivity                                                         *)
(*                                                                            *)
(******************************************************************************)

val connected_def = Define `
    connected G = ~(empty G) /\
		  !x y. x IN (vertices G) /\ y IN (vertices G) ==> xy_connected G x y`;

val component_def = Define `
    component G' G = induced_subgraph G' G /\ connected G' /\
		     ~(?G''. ~(G' = G'') /\ subgraph G' G'' /\ connected G'')`;

(******************************************************************************)
(*                                                                            *)
(*   1.5 Trees and forests                                                   *)
(*                                                                            *)
(******************************************************************************)

val forest_def = Define `
    forest G = ~(has_cycles G)`;

val tree_def = Define `
    tree G = forest G /\ connected G`;

val rooted_tree_def = Define `
    rooted_tree (r,t) = r IN (vertices t) /\ tree t`;

(******************************************************************************)
(*                                                                            *)
(*   1.6 Bipartite graphs                                                     *)
(*                                                                            *)
(******************************************************************************)

(* use partitions of sets from pred_set *)


(******************************************************************************)
(*                                                                            *)
(*   1.7 Contraction and minors                                               *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(*   1.10 Other notions of graphs                                             *)
(*                                                                            *)
(******************************************************************************)

(* In multigraphs, every edge has either one or two vertices (its ends). Thus
   multigraphs too can have loops and multiple edges (with different labels if
   they share the same ends). In our framework, we require that, for each edge e
   either inits(e) or ters(e) must contain exactly one element, and when they're
   the same, the resulting ends(e) is still singleton. *)
val multigraph_def = Define `
    multigraph (G :('a, 'b) graph) =
	!e. e IN (edges G) ==> SING (inits e) /\ SING (ters e)`;

val multigraph_ends = store_thm (
   "multigraph_ends",
  ``multigraph (G :('a, 'b) graph) ==>
        !e. e IN (edges G) ==> (CARD (ends e) = 1) \/ (CARD (ends e) = 2)``,
    REWRITE_TAC [multigraph_def]
 >> rpt STRIP_TAC
 >> RES_TAC
 >> REWRITE_TAC [ends_def]
 >> FULL_SIMP_TAC std_ss [SING_DEF]
 >> `(CARD (inits e) = 1) /\ (CARD (ters e) = 1)` by PROVE_TAC [CARD_SING]
 >> `FINITE (inits e) /\ FINITE (ters e)` by PROVE_TAC [FINITE_SING]
 >> REV_FULL_SIMP_TAC std_ss []
 >> `CARD ({x} UNION {x'}) = CARD {x} + CARD {x'} - CARD ({x} INTER {x'})`
        by PROVE_TAC [CARD_UNION_EQN]
 >> ASM_REWRITE_TAC []
 >> SIMP_TAC arith_ss []
 >> Cases_on `x = x'` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISJ1_TAC \\
      ASM_REWRITE_TAC [] \\
      REWRITE_TAC [INTER_IDEMPOT, CARD_SING] \\
      SIMP_TAC arith_ss [],
      (* goal 2 (of 2) *)
      DISJ2_TAC \\
      Know `DISJOINT {x} {x'}` >- ( REWRITE_TAC [DISJOINT_ALT, IN_SING] >> PROVE_TAC [] ) \\
      REWRITE_TAC [DISJOINT_DEF] \\
      DISCH_TAC >> ASM_REWRITE_TAC [] \\
      SIMP_TAC arith_ss [CARD_EMPTY] ]);

val _ = export_theory ();
val _ = html_theory "Graph";

(* last updated: Oct 9, 2017 *)
