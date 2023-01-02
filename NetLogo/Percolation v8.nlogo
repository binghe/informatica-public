;;;; A percolation thresholds demo in NetLogo - Course project for Complex Systems
;;;; Chun Tian <chun.tian@studio.unibo.it>, Numero di matricola: 0000735539
;;;; Scuola di Scienze, Università di Bologna

extensions [ nw array ]

; we have two different kinf of link breeds, one directed and one undirected, just
; to show what the different networks look like with directed vs. undirected links
directed-link-breed [ dirlinks dirlink ]
undirected-link-breed [ unlinks unlink ]

turtles-own [ occupied pointer ]

globals [
  ;; original global variables from NW demo
  highlighted-node                ; used for the "highlight mode" buttons to keep track of the currently highlighted node
  highlight-bicomponents-on       ; indicates that highlight-bicomponents mode is active
  stop-highlight-bicomponents     ; indicates that highlight-bicomponents mode needs to stop
  highlight-maximal-cliques-on    ; indicates highlight-maximal-cliques mode is active
  stop-highlight-maximal-cliques  ; indicates highlight-maximal-cliques mode needs to stop

  ;; below is new global variables related to "Percolation"
  pc1                             ; percolation threshold (p_c), computed from giant threshold
  pc2                             ; percolation threshold (p_c), computed from max relabeling
  random-list
  random-array
  pc-index
  fraction
  relabeling-array                ; array for holding the relabeling data in one percolation run
  giant-size-array                ; array for holding the giant size data in one percolation run
  relabeling-data                 ; array for holding the relabeling data in all percolation runs
  giant-size-data                 ; array for holding the giant size data in all percolation runs
  giant-threshold                 ; giant component threshold (N^2/3 of sites)
  relabeling
  max-relabeling
  giant-size
  giant-index
  number-of-sites-or-bonds
]

to clear
  clear-all
  set-current-plot "Percolation"
  set-default-shape turtles "circle"
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Percolation threshold computation for any graph
;;
;; author: Chun Tian (binghe) <chun.tian@studio.unibo.it>
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to percolation-setup
  clear-all-plots
  ifelse percolation-type? = "bond"
    [ set number-of-sites-or-bonds count links ]
    [ set number-of-sites-or-bonds count turtles ]
  ask turtles [ set color grey
                set label ""
                set occupied 0 ]
  ask links   [ set color grey ]
  set random-list []
  ifelse percolation-type? = "bond"
    [ ask links [ set random-list lput self random-list ] ]
    [ ask turtles [ set random-list lput self random-list ] ]
  set fraction 0
  set relabeling 0
  set max-relabeling 0
  set giant-size 0
  set giant-index 0
  set pc1 0
  set pc2 0
  set giant-threshold (count turtles)^(2 / 3)
  set random-list shuffle random-list
  set random-array array:from-list random-list
  set relabeling-array (array:from-list n-values number-of-sites-or-bonds [0])
  set giant-size-array (array:from-list n-values number-of-sites-or-bonds [0])
  set pc-index 0
  reset-ticks
end

to percolation-full
  set relabeling-data (array:from-list n-values percolation-runs [0])
  set giant-size-data (array:from-list n-values percolation-runs [0])
  let run-index 0
  repeat percolation-runs
  [ percolation-setup
    percolation
    array:set relabeling-data run-index relabeling-array
    array:set giant-size-data run-index giant-size-array
    set run-index (run-index + 1)
  ]
  percolation-compute
end

to percolation-compute
  clear-all-plots
  set relabeling-array (array:from-list n-values number-of-sites-or-bonds [0])
  set giant-size-array (array:from-list n-values number-of-sites-or-bonds [0])
  set max-relabeling 0
  set giant-index 0

  ;; begin LOOP
  set pc-index 0
  repeat number-of-sites-or-bonds
  [ let run-index 0
    let r 0
    let g 0
    repeat percolation-runs
    [ set r (r + array:item (array:item relabeling-data run-index) pc-index)
      set g (g + array:item (array:item giant-size-data run-index) pc-index)
      set run-index (run-index + 1) ]
    set fraction pc-index / number-of-sites-or-bonds
    set relabeling r / percolation-runs * 20
    set giant-size g / percolation-runs
    array:set relabeling-array pc-index relabeling
    array:set giant-size-array pc-index giant-size
    percolation-test
    set pc-index (pc-index + 1)
    tick ]
end

to percolation-test
  ;; 1. test giant-threshold, then compute pc1 (once once)
  if giant-index = 0 and giant-size > giant-threshold
  [ set giant-index pc-index
    set pc1 giant-index / number-of-sites-or-bonds
  ]
  ;; 2. test max-relabeling, then compute pc2 (keep updating)
  if relabeling > max-relabeling
  [ set max-relabeling relabeling
    set pc2 pc-index / number-of-sites-or-bonds
  ]
end

to percolation
  percolation-setup
  ifelse percolation-type? = "bond"
  [ repeat number-of-sites-or-bonds
    [ while [any? turtles with [ occupied = 0 ]]
      [ percolation-step ] ] ]
  [ repeat number-of-sites-or-bonds
    [ percolation-step ] ]
end

to percolation-step
  if pc-index >= number-of-sites-or-bonds [ stop ]
  set relabeling 0
  ifelse percolation-type? = "bond"
    [ bond-percolation-step ]
    [ site-percolation-step ]
  array:set relabeling-array pc-index relabeling
  array:set giant-size-array pc-index giant-size
  set pc-index (pc-index + 1)
  set fraction pc-index / number-of-sites-or-bonds
  percolation-test
  tick
end

to bond-percolation-step
  let a-link array:item random-array pc-index
  ;; reset everything if percolation-type? is changed
  if not is-link? a-link
  [ percolation-setup
    stop ]

  ask a-link
  [
    set color red
    let r1 end1
    ifelse ([occupied] of r1) = 0
      [ ask r1 [ set color red
                 set occupied 1
                 set pointer 1 ] ]
      [ set r1 find-root r1 ]
    let r2 end2
    ifelse ([occupied] of r2) = 0
      [ ask r2 [ set color red
                 set occupied 1
                 set pointer 1 ] ]
      [ set r2 find-root r2 ]
    if r1 != r2 [ set r1 (union-nodes r1 r2) ]
  ]
end

to site-percolation-step
  let a-node array:item random-array pc-index
  ; reset everything if percolation-type? is changed
  if not is-turtle? a-node
  [ percolation-setup
    stop ]
  let local-relabeling 0
  ask a-node
  [ set occupied 1
    set pointer 1 ; cluster size
    set color red
    set label pointer
    let r1 self
    ;; bug with giant-size here !!!
    ask my-links
    [ ask other-end
      [ if occupied = 1
        [ let r2 find-root self
          if r2 != r1
          [ set r1 (union-nodes r1 r2)
            set local-relabeling (local-relabeling + relabeling) ]]]]]
  set relabeling local-relabeling
end

to-report union-nodes [r1 r2]
  let s1 [pointer] of r1
  let s2 [pointer] of r2
  let s s1 + s2
  ifelse s1 < s2
    [ ask r2 [ set pointer s
               set label pointer ]
      ask r1 [ set pointer r2 ]
      set r1 r2
      set relabeling s1 ]
    [ ask r1 [ set pointer s
               set label pointer ]
      ask r2 [ set pointer r1 ]
      set relabeling s2 ]
  if s > giant-size [ set giant-size s ]
  report r1
end

to-report find-root [node]
  let root [pointer] of node
  ifelse (is-number? root)
    [ report node ]
    [ ask node [ set pointer find-root root ]
      report [pointer] of node ]
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2D lattices and cayley tree generator
;;
;; author: Chun Tian (binghe) <chun.tian@studio.unibo.it>
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; a list of supported 2d lattices: (all the 11 Archimedean lattices)
;;
;; "3.3.3.3.3.3 (triangular)"
;; "3.3.3.3.6 (maple leaf)"
;; "3.3.3.4.4"
;; "3.3.4.3.4 (puzzle)"
;; "3.4.6.4 (ruby)"
;; "3.6.3.6 (Kagomé)"
;; "3.12.12"
;; "4.4.4.4 (grid)"
;; "4.6.12 (cross)"
;; "4.8.8"
;; "6.6.6 (honeycomb)"

to lattice-2d
  if lattice-2d-type? = "3.3.3.3.3.3 (triangular)" [ generate-triangular ]
  if lattice-2d-type? = "3.3.3.3.6 (maple leaf)" [ generate-3-3-3-3-6 ]
  if lattice-2d-type? = "3.3.3.4.4" [ generate-3-3-3-4-4 ]
  if lattice-2d-type? = "3.3.4.3.4 (puzzle)" [ generate-3-3-4-3-4 ]
  if lattice-2d-type? = "3.4.6.4 (ruby)" [ generate-3-4-6-4 ]
  if lattice-2d-type? = "3.6.3.6 (Kagomé)" [ generate-3-6-3-6 ]
  if lattice-2d-type? = "3.12.12" [ generate-3-12-12 ]
  if lattice-2d-type? = "4.4.4.4 (grid)" [ generate-4-4-4-4 ] ; old-lattice-2d
  if lattice-2d-type? = "4.6.12 (cross)" [ generate-4-6-12 ]
  if lattice-2d-type? = "4.8.8" [ generate-4-8-8 ]
  if lattice-2d-type? = "6.6.6 (honeycomb)" [ generate-6-6-6 ]
  layout-once ; again
end

to generate-4-4-4-4 ; grid
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      line-up nodes n r c
      line-left nodes n r c
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-6-6-6
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      if r mod 2 = 1 and c mod 2 = 0
        [ line-up nodes n r c ]
      if r mod 2 = 0 and c mod 2 = 1
        [ line-up nodes n r c ]
      line-left nodes n r c
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-4-8-8
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      if r mod 2 = 1 and (c mod 4 = 0 or c mod 4 = 1)
        [ line-up nodes n r c ]
      if r mod 2 = 0 and (c mod 4 = 2 or c mod 4 = 3)
        [ line-up nodes n r c ]
      line-left nodes n r c
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-4-6-12
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      if (r mod 6 = 1 or r mod 6 = 3 or r mod 6 = 5) and
         (c mod 4 = 0 or c mod 4 = 3)
        [ line-up nodes n r c ]
      if (r mod 6 = 2 or r mod 6 = 4 or r mod 6 = 0) and
         (c mod 4 = 1 or c mod 4 = 2)
        [ line-up nodes n r c ]
      if (r mod 6 = 0 or r mod 6 = 5) and (c mod 4 != 0)
        [ line-left nodes n r c ]
      if (r mod 6 = 1 or r mod 6 = 4) and (c mod 4 = 0 or c mod 4 = 2)
        [ line-left nodes n r c ]
      if (r mod 6 = 2 or r mod 6 = 3) and
         (c mod 4 = 0 or c mod 4 = 1 or c mod 4 = 3)
        [ line-left nodes n r c ]
      if (r mod 6 = 0 or r mod 6 = 1) and c mod 4 = 0
        [ line-right-down nodes n r c ]
      if (r mod 6 = 3 or r mod 6 = 4) and c mod 4 = 2
        [ line-right-down nodes n r c ]
      if (r mod 6 = 4 or r mod 6 = 5) and c mod 4 = 0
        [ line-right-up nodes n r c]
      if (r mod 6 = 1 or r mod 6 = 2) and c mod 4 = 2
        [ line-right-up nodes n r c]
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-3-12-12
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      if r mod 6 = 0 or r mod 6 = 3
        [ line-left nodes n r c ]
      if (c mod 4 = 0 and
          (r mod 6 = 1 or r mod 6 = 2 or r mod 6 = 3)) or
         (c mod 4 = 2 and
          (r mod 6 = 4 or r mod 6 = 5 or r mod 6 = 0))
        [ line-up nodes n r c ]
      if (c mod 4 = 0 and r mod 6 = 1) or
         (c mod 4 = 2 and r mod 6 = 4)
        [ line-left-up nodes n r c ]
      if (c mod 4 = 0 and r mod 6 = 2) or
         (c mod 4 = 2 and r mod 6 = 6)
        [ line-left-down nodes n r c ]
      if (r mod 6 = 1 or r mod 6 = 2) and
         (c mod 4 = 1 or c mod 4 = 2 or c mod 4 = 3)
        [ remove-node nodes r c ]
      if (r mod 6 = 4 or r mod 6 = 5) and
         (c mod 4 = 0 or c mod 4 = 1 or c mod 4 = 3)
        [ remove-node nodes r c ]
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-3-6-3-6
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      if not (r mod 2 = 1)
      [ line-left nodes n r c ]
      if not (c mod 2 = 0)
      [ line-up nodes n r c ]
      if r mod 2 = 1 and c mod 2 = 1
      [ line-left-down nodes n r c
        line-right-up nodes n r c ]
      if r mod 2 = 1 and c mod 2 = 0
      [ remove-node nodes r c ]
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-3-4-6-4
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      if not ((r mod 3 = 1) or
              (c mod 2 = 1))
      [ line-left nodes n r c ]
      line-up nodes n r c
      if r mod 3 = 0 or r mod 3 = 1
      [ line-right-down nodes n r c ]
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-3-3-4-3-4
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      line-left nodes n r c
      line-up nodes n r c
      if r mod 2 = 1 and c mod 2 = 0
      [ line-right-up nodes n r c ]
      if r mod 2 = 1 and c mod 2 = 1
      [ line-right-down nodes n r c ]
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-3-3-3-4-4
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      line-left nodes n r c
      line-up nodes n r c
      if r mod 4 = 0
      [ line-right-up nodes n r c ]
      if r mod 4 = 1
      [ line-right-down nodes n r c ]
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-3-3-3-3-6
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      ;; connect with left node with exceptions
      if not ((r mod 3 = 1 and c mod 6 = 1) or
              (r mod 3 = 2 and c mod 6 = 3) or
              (r mod 3 = 0 and c mod 6 = 5))
        [ line-left nodes n r c ]
      ;; always connect with up node
      line-up nodes n r c
      ;; other links
      if r mod 3 = 1
      [ if c mod 6 = 1
        [ line-right-up nodes n r c
          line-right-down nodes n r c ]
        if c mod 6 = 2 or c mod 6 = 3
        [ line-right-up nodes n r c ]
        if c mod 6 = 4 or c mod 6 = 5
        [ line-left-down nodes n r c ]
        if c != 0 and c mod 6 = 0
        [ line-left-up nodes n r c
          line-left-down nodes n r c ] ]
      if r mod 3 = 2
      [ if c mod 6 = 1 or c mod 6 = 2 or c mod 6 = 0
        [ line-left-down nodes n r c ]
        if c mod 6 = 3
        [ line-right-down nodes n r c ] ]
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to generate-triangular
  let nodes generate-nodes
  let r 0
  repeat nb-rows
  [ let c 0
    repeat nb-cols
    [ let n (array:item (array:item nodes r) c)
      line-left nodes n r c
      line-up nodes n r c
      if r mod 2 = 1
      [ line-right-up nodes n r c
        line-right-down nodes n r c ]
      set c (c + 1) ]
    set r (r + 1) ]
  layout-once
end

to line-to [nodes n r c]
  if wrap or (r >= 0 and r < nb-rows and c >= 0 and c < nb-cols)
  [ if wrap
    [ set r r mod nb-rows
      set c c mod nb-cols ]
    let m (array:item (array:item nodes r) c)
    ask n [ create-link-with m ] ]
end

to line-right-up [nodes n r c]
  line-to nodes n (r - 1) (c + 1)
end

to line-right-down [nodes n r c]
  line-to nodes n (r + 1) (c + 1)
end

to line-left-up [nodes n r c]
  line-to nodes n (r - 1) (c - 1)
end

to line-left-down [nodes n r c]
  line-to nodes n (r + 1) (c - 1)
end

to line-left [nodes n r c]
  line-to nodes n r (c - 1)
end

to line-up [nodes n r c]
  line-to nodes n (r - 1) c
end

to remove-node [nodes r c]
  let n (array:item (array:item nodes r) c)
  ask n [ die ]
end

to-report generate-nodes
  let nodes []
  repeat nb-rows
  [ let a-row []
    crt nb-cols [ set a-row lput self a-row ]
    set nodes lput (array:from-list a-row) nodes ]
  report array:from-list nodes
end

to cayley-tree
  let front-nodes [] ; a queue for width-first node creation
  crt 1 [ set front-nodes lput self front-nodes ]
  let all-nodes []   ; a pool for un-allocated nodes
  crt (nb-nodes - 1) [ set all-nodes lput self all-nodes ]

  while [not empty? front-nodes]
  [ let a first front-nodes
    set front-nodes but-first front-nodes
    repeat coord-num
    [ if not empty? all-nodes
      [ let front first all-nodes
        set all-nodes but-first all-nodes
        ask front [
          ifelse links-to-use = "undirected"
            [ create-link-with a ]
            [ create-link-from a ]
          set front-nodes lput self front-nodes ] ] ] ]
  layout-once
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Below is the original NW demo code
;;
;; Copyright 2012 Uri Wilensky.
;; See Info tab for full copyright and license.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reports the link set corresponding to the value of the links-to-use combo box
to-report get-links-to-use
  report ifelse-value (links-to-use = "directed")
    [ dirlinks ]
    [ unlinks ]
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Layouts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to redo-layout [ forever? ]
  if layout = "radial" and count turtles > 1 [
    layout-radial turtles links ( max-one-of turtles [ count my-links + count my-out-links + count my-in-links ] )
  ]
  if layout = "spring" [
    let factor sqrt count turtles
    if factor = 0 [ set factor 1 ]
    repeat ifelse-value forever? [ 1 ] [ 50 ] [
      ; layout-spring turtles links (1 / factor) (14 / factor) (1.5 / factor)
      layout-spring turtles links 1 1 1
      display
      if not forever? [ wait 0.005 ]
    ]
  ]
  if layout = "circle" [
    layout-circle sort turtles max-pxcor * 0.9
  ]
  if layout = "tutte" [
    layout-circle sort turtles max-pxcor * 0.9
    repeat 10 [
      layout-tutte max-n-of (count turtles * 0.5) turtles [ count my-links ] links 12
    ]
  ]
end

to layout-once
  redo-layout false
end

to spring-forever
  set layout "spring"
  redo-layout true
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Clusterers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Colorizes each node according to which component it is part of
to weak-component
  nw:set-context turtles get-links-to-use
  color-clusters nw:weak-component-clusters
end

;; Allows the user to mouse over and highlight all bicomponents
to highlight-bicomponents

  if stop-highlight-bicomponents = true [
    ; we're asked to stop - do so
    set stop-highlight-bicomponents false
    set highlight-bicomponents-on false
    stop
  ]
  set highlight-bicomponents-on true ; we're on!
  if highlight-maximal-cliques-on = true [
    ; if the other guy is on, he needs to stop
    set stop-highlight-maximal-cliques true
  ]

  if mouse-inside? [
    nw:set-context turtles get-links-to-use
    highlight-clusters nw:bicomponent-clusters
  ]
  display
end

;; Allows the user to mouse over and highlight all maximal cliques
to highlight-maximal-cliques
  if (links-to-use != "undirected") [
    user-message "Maximal cliques only work with undirected links."
    stop
  ]
  if stop-highlight-maximal-cliques = true [
    ; we're asked to stop - do so
    set stop-highlight-maximal-cliques false
    set highlight-maximal-cliques-on false
    stop
  ]
  set highlight-maximal-cliques-on true ; we're on!
  if highlight-bicomponents-on = true [
    ; if the other guy is on, he needs to stop
    set stop-highlight-bicomponents true
  ]

  if mouse-inside? [
    nw:set-context turtles unlinks
    highlight-clusters nw:maximal-cliques
  ]
  display
end

;; Colorizes the biggest maximal clique in the graph, or a random one if there is more than one
to find-biggest-cliques
  if (links-to-use != "undirected") [
    user-message "Maximal cliques only work with undirected links."
    stop
  ]
  nw:set-context turtles unlinks
  color-clusters nw:biggest-maximal-cliques
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Highlighting and coloring of clusters
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Allows the user to mouse over different nodes and
;; highlight all the clusters that this node is a part of
to highlight-clusters [ clusters ]
  ;; get the node with neighbors that is closest to the mouse
  let node min-one-of turtles [ distancexy mouse-xcor mouse-ycor ]
  if node != nobody and node != highlighted-node [
    set highlighted-node node
    ;; find all clusters the node is in and assign them different colors
    color-clusters filter [ [?1] -> member? node ?1 ] clusters
    ;; highlight target node
    ask node [ set color white ]
  ]
end

to color-clusters [ clusters ]
  ;; reset all colors
  ask turtles [ set color gray - 3 ]
  ask links [ set color gray - 3 ]
  let n length clusters
  let colors ifelse-value (n <= 12)
    [ n-of n remove gray remove white base-colors ] ;; choose base colors other than white and gray
    [ n-values n [ approximate-hsb (random 255) 255 (100 + random 100) ] ] ; too many colors - pick random ones

    ;; loop through the clusters and colors zipped together
    (foreach clusters colors [ [?1 ?2] ->
      let cluster ?1
      let cluster-color ?2
      ask cluster [ ;; for each node in the cluster
        ;; give the node the color of its cluster
        set color cluster-color
        ;; colorize the links from the node to other nodes in the same cluster
        ;; link color is slightly darker...
        ask my-unlinks [ if member? other-end cluster [ set color cluster-color - 1 ] ]
        ask my-in-dirlinks [ if member? other-end cluster [ set color cluster-color - 1 ] ]
        ask my-out-dirlinks [ if member? other-end cluster [ set color cluster-color - 1 ] ]
      ]
    ])
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Centrality Measures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to betweenness
  centrality [ [] -> nw:betweenness-centrality ]
end

to eigenvector
  centrality [ [] -> nw:eigenvector-centrality ]
end

to closeness
  centrality [ [] -> nw:closeness-centrality ]
end

;; Takes a centrality measure as a reporter task, runs it for all nodes
;; and set labels, sizes and colors of turtles to illustrate result
to centrality [ measure ]
  nw:set-context turtles get-links-to-use
  ask turtles [
    let res (runresult measure) ;; run the task for the turtle
    ifelse is-number? res [
      set label precision res 2
      set size res ;; this will be normalized later
    ]
    [ ;; if the result is not a number, it is because eigenvector returned false (in the case of disconnected graphs
      set label res
      set size 1
    ]
  ]
  normalize-sizes-and-colors
end

;; We want the size of the turtles to reflect their centrality, but different measures
;; give different ranges of size, so we normalize the sizes according to the formula
;; below. We then use the normalized sizes to pick an appropriate color.
to normalize-sizes-and-colors
  if count turtles > 0 [
    let sizes sort [ size ] of turtles ;; initial sizes in increasing order
    let delta last sizes - first sizes ;; difference between biggest and smallest
    ifelse delta = 0 [ ;; if they are all the same size
      ask turtles [ set size 1 ]
    ]
    [ ;; remap the size to a range between 0.5 and 2.5
      ask turtles [ set size ((size - first sizes) / delta) * 2 + 0.5 ]
    ]
    ask turtles [ set color scale-color red size 0 5 ] ; using a higher range max not to get too white...
  ]
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generators
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to generate [ generator-task ]
  ; we have a general "generate" procedure that basically just takes a task
  ; parameter and run it, but takes care of calling layout and update stuff
  set-default-shape turtles "circle"
  run generator-task
  layout-once
  update-plots
end

to preferential-attachment
  generate [ [] ->  nw:generate-preferential-attachment turtles get-links-to-use nb-nodes 1 ]
end

to ring
  generate [ [] ->  nw:generate-ring turtles get-links-to-use nb-nodes ]
end

to star
  generate [ [] ->  nw:generate-star turtles get-links-to-use nb-nodes ]
end

to wheel
  ifelse (links-to-use = "directed") [
    ifelse spokes-direction = "inward" [
      generate [ [] ->  nw:generate-wheel-inward turtles get-links-to-use nb-nodes ]
    ]
    [ ; if it's not inward, it's outward
      generate [ [] ->  nw:generate-wheel-outward turtles get-links-to-use nb-nodes ]
    ]
  ]
  [ ; for an undirected network, we don't care about spokes
    generate [ [] ->  nw:generate-wheel turtles get-links-to-use nb-nodes ]
  ]
end

to old-lattice-2d
  generate [ [] ->  nw:generate-lattice-2d turtles get-links-to-use nb-rows nb-cols wrap ]
end

to small-world
  generate [ [] ->  nw:generate-small-world turtles get-links-to-use nb-rows nb-cols clustering-exponent wrap ]
end

to generate-random
  generate [ [] ->  nw:generate-random turtles get-links-to-use nb-nodes connexion-prob ]
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Saving and loading of network files
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to save-matrix
  nw:set-context turtles get-links-to-use
  nw:save-matrix "matrix.txt"
end

to load-matrix
  generate [ [] ->  nw:load-matrix "matrix.txt" turtles get-links-to-use ]
end

to save-graphml
  nw:set-context turtles get-links-to-use
  nw:save-graphml "demo.graphml"
end

to load-graphml
  nw:set-context turtles get-links-to-use
  nw:load-graphml "demo.graphml"
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reporters for monitors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to-report mean-path-length
  report nw:mean-path-length
end
@#$#@#$#@
GRAPHICS-WINDOW
570
10
1111
552
-1
-1
8.2
1
10
1
1
1
0
0
0
1
-32
32
-32
32
0
0
1
ticks
30.0

BUTTON
450
90
560
123
NIL
betweenness
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

TEXTBOX
245
65
395
83
Clusterers & Cliques
12
0.0
1

SLIDER
10
90
225
123
nb-nodes
nb-nodes
0
1000
200.0
1
1
NIL
HORIZONTAL

TEXTBOX
450
65
600
83
Centrality
12
0.0
1

BUTTON
10
10
120
55
NIL
clear
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
10
130
225
163
preferential attachment
preferential-attachment
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
105
450
225
485
lattice 2D
lattice-2d
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
120
360
225
393
nb-rows
nb-rows
4
50
16.0
1
1
NIL
HORIZONTAL

SLIDER
10
360
115
393
nb-cols
nb-cols
4
50
16.0
1
1
NIL
HORIZONTAL

SWITCH
150
490
240
523
wrap
wrap
1
1
-1000

TEXTBOX
15
65
165
83
Generators
12
0.0
1

BUTTON
450
125
560
158
NIL
eigenvector
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
10
250
75
283
random
generate-random
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
80
250
225
283
connexion-prob
connexion-prob
0
1
0.2
0.01
1
NIL
HORIZONTAL

BUTTON
10
325
225
358
small world
small-world
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
10
290
225
323
clustering-exponent
clustering-exponent
0
10
5.0
0.1
1
NIL
HORIZONTAL

BUTTON
450
160
560
193
NIL
closeness
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
245
90
425
123
weak component clusters
weak-component
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

CHOOSER
125
10
225
55
links-to-use
links-to-use
"undirected" "directed"
0

PLOT
245
355
560
520
Percolation
Fraction of occupied sites/bonds
Giant size (red)
0.0
1.0
0.0
10.0
true
false
"" ""
PENS
"pen-0" 1.0 0 -2674135 true "" "plotxy fraction giant-size"
"pen-1" 1.0 0 -13345367 true "" "plotxy fraction relabeling"
"pen-2" 1.0 0 -7500403 true "" "plotxy fraction max-relabeling"

BUTTON
245
275
330
308
save matrix
save-matrix
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
245
310
330
343
load matrix
load-matrix
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
360
530
445
575
NIL
count turtles
17
1
11

MONITOR
280
530
355
575
NIL
count links
17
1
11

BUTTON
245
210
425
243
biggest maximal cliques
find-biggest-cliques
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
10
165
115
198
NIL
ring
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
10
200
75
245
NIL
wheel
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
120
165
225
198
NIL
star
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
450
530
560
575
Mean path length
mean-path-length
3
1
11

CHOOSER
355
10
447
55
layout
layout
"spring" "circle" "radial" "tutte"
0

BUTTON
245
10
347
55
layout
layout-once
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
455
10
560
55
spring
spring-forever
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
245
130
425
163
highlight bicomponents
highlight-bicomponents
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
245
170
425
203
highlight maximal cliques
highlight-maximal-cliques
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

CHOOSER
80
200
225
245
spokes-direction
spokes-direction
"inward" "outward"
1

TEXTBOX
245
255
395
273
Files
12
0.0
1

BUTTON
335
275
425
308
save GraphML
save-graphml
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
335
310
425
343
load GraphML
load-graphml
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

CHOOSER
10
530
120
575
percolation-type?
percolation-type?
"site" "bond"
0

BUTTON
450
235
560
268
NIL
percolation
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
125
530
195
575
NIL
pc1
17
1
11

BUTTON
440
310
560
343
NIL
percolation-step
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
440
275
560
308
NIL
percolation-setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
200
530
270
575
NIL
pc2
17
1
11

SLIDER
10
490
145
523
percolation-runs
percolation-runs
1
100
20.0
1
1
NIL
HORIZONTAL

BUTTON
450
200
560
233
NIL
percolation-full
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

CHOOSER
105
400
225
445
lattice-2d-type?
lattice-2d-type?
"3.3.3.3.3.3 (triangular)" "3.3.3.3.6 (maple leaf)" "3.3.3.4.4" "3.3.4.3.4 (puzzle)" "3.4.6.4 (ruby)" "3.6.3.6 (Kagomé)" "3.12.12" "4.4.4.4 (grid)" "4.6.12 (cross)" "4.8.8" "6.6.6 (honeycomb)"
5

BUTTON
10
450
100
485
cayley tree
cayley-tree
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
10
410
102
443
coord-num
coord-num
2
6
3.0
1
1
NIL
HORIZONTAL

@#$#@#$#@
## WHAT IS IT?

This model computes site/bond percolation thresholds for various types of graphs. 

## HOW IT WORKS

It is not a model _of_ anything per se, but rather a collection of tools that allow you the generate various kind of networks, lay them out on screen, and get information about them.

## HOW TO USE IT

The first thing to think about is if you want to use directed or undirected links. The **links-to-use** chooser will allow you to specify that: all the generators will use the kind of links specfied in the chooser. You can generate different networks with different kinds of links without clearing everything in between.

As an aside, also note that the value of the **links-to-use** chooser is used by the different clusterers and measures as well. Be careful to use the right value for the network you are interested in! For example, if you ask for betweenness centrality with "directed links" selected in the chooser, but the network on the screen is undirected, the betweenness centrality values will all be zero, because the algorithm only takes directed links into account!

On the right of the **links-to-use** chooser, is another one called **layout**. NetLogo currently offers four different kinds of layouts (this is not new in the extension - they were all available before): [circle](http://ccl.northwestern.edu/netlogo/docs/dictionary.html#layout-circle), [radial](http://ccl.northwestern.edu/netlogo/docs/dictionary.html#layout-radial), [spring](http://ccl.northwestern.edu/netlogo/docs/dictionary.html#layout-spring) and [tutte](http://ccl.northwestern.edu/netlogo/docs/dictionary.html#layout-tutte). The chosen layout will be applied automatically when generating new networks, but you can also apply yourself by clicking the **layout** button. One special case is the "spring" layout, which works better when applied multiple times (or even continuously). To make it easy to do that, we have a **spring** forever button. When you click this button, it will automatically choose "spring" layout and apply it as long as the button is pressed.

Now that you know what kind of links you want, and how you want it to look, it's time to generate a network!

### Generators

The first thing that you will see in the **Generators** section of the model is a slider labeled **nb-nodes**. As you might have guessed, this will allow you to specify the number of nodes you want to have in your network. The first five generator buttons (**preferential attachment**, **ring**, **star**, **wheel**, and **random**) will take the value of that slider into account.

Note that at any time, you can press the **clear** button to erase everything and start over.

Here is a description of each of them:

#### preferential attachment

Generates a new network using the [Barabási–Albert](http://en.wikipedia.org/wiki/Barab%C3%A1si%E2%80%93Albert_model) algorithm. This network will have the property of being "scale free": the distribution of degrees (i.e. the number of links for each turtle) should follow a power law.

Turtles are added, one by one, each forming one link to a previously added turtle, until _nb-nodes_ is reached. The more links a turtle already has, the greater the probability that new turtles form links with it when they are added.

#### ring

Generates a [ring network](http://en.wikipedia.org/wiki/Ring_network) of **nb-nodes** turtles, in which each turtle is connected to exactly two other turtles.

#### star

Generates a [star network](http://en.wikipedia.org/wiki/Star_graph) in which there is one central turtle and every other turtle is connected only to this central node. The number of turtles can be as low as one, but it won't look much like a star.

#### wheel

Generates a [wheel network](http://en.wikipedia.org/wiki/Wheel_graph), which is basically a [ring network](http://en.wikipedia.org/wiki/Ring_network) with an additional "central" turtle that is connected to every other turtle. The number of nodes must be at least four.

On the right side of the **wheel** button, you will see a chooser allowing you the select either "inward" or "outward". This will allow to specify if the "spokes" of the wheel point toward the central turtle (inward) or away from it (outward). This is, of course, meaningful only in the case of a directed network.

#### random

Generates a new random network of _nb-nodes_ turtles in which each one has a  connection probability (between 0 and 1) of being connected to each other turtles (this is specified through the **connection-prob** slider). The algorithm uses the [Erdős–Rényi model](http://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93R%C3%A9nyi_model).

#### lattice 2D

Generates a new 2D [lattice network](http://en.wikipedia.org/wiki/Lattice_graph) (basically, a grid) of **nb-rows** rows and **nb-cols** columns. The grid will wrap around itsef if the **wrap** switch is set to on.

#### small world

Generates a new [small-world network](http://en.wikipedia.org/wiki/Small-world_network) using the [Kleinberg Model](http://en.wikipedia.org/wiki/Small_world_routing#The_Kleinberg_Model). 

The generator uses the same sliders and switch as the lattice 2D generator, namely, **nb-rows**, **nb-cols** and **wrap**. The algorithm proceeds by generating a lattice of the given number of rows and columns (the lattice will wrap around itself if **wrap** is on). The "small world effect" is created by adding additional links between the nodes in the lattice. The higher the **clustering-exponent**, the more the algorithm will favor already close-by nodes when adding new links. A clustering exponent of `2.0` is typically used.

### Clusters and cliques

Now that you have generated one or more networks, there are things that you might want to know about them.

#### weak component clusters

This button will assign a different color to all the "weakly" [connected components](http://en.wikipedia.org/wiki/Connected_component_%28graph_theory%29) in the current network. A weakly connected component is simply a group of nodes where there is a path from each node to every other node. A "strongly" connected component would be one where there is a _directed_ path from each node to every other. The extension does not support the identification of strongly connected components at the moment.

#### highlight bicomponents

Clicking on this button will put you in a mode where you use your mouse to highlight the different [bicomponent clusters](http://en.wikipedia.org/wiki/Biconnected_component) in the current network. A bicomponent (also known as a maximal biconnected subgraph) is a part of a network that cannot be disconnected by removing only one node (i.e. you need to remove at least two to disconnect it).

Note that one turtle can be a member of more than one bicomponent at once. If it is the case, all the bicomponents that the target turtle is part of will be highlighted when you move your mouse pointer near it, but they will be of different color.

#### highlight maximal cliques

The general usage for this is the same as for the **highlight bicomponents** mode. Note you should not try to use both highlight modes at the same time.

A [clique](http://en.wikipedia.org/wiki/Clique_%28graph_theory%29) is a subset of a network in which every node has a direct link to every other node. A maximal clique is a clique that is not, itself, contained in a bigger clique.

#### biggest maximal cliques

This simply highlights the biggests of all the maximal cliques in the networks. If there are multiple cliques that are equally big (as is often the case), it will highlight them with different colors.

### Centrality measures

Besides all the clusterers and the clique finder, you can also calculate some centrality measures on your networks. All the centrality measures will label the nodes will the result of the calculation and adjust their size and color to reflect that result.

#### betweenness

To calculate the [betweenness centrality](http://en.wikipedia.org/wiki/Betweenness_centrality) of a turtle, you take every other possible pairs of turtles and, for each pair, you calculate the proportion of shortest paths between members of the pair that passes through the current turtle. The betweeness centrality of a turtle is the sum of these.

#### eigenvector

The [Eigenvector centrality](http://en.wikipedia.org/wiki/Centrality#Eigenvector_centrality) of a node can be thought of as the proportion of its time that an agent forever "walking" at random on the network would spend on this node. In practice, turtles that are connected to a lot of other turtles that are themselves well-connected (and so) get a higher Eigenvector centrality score.

Eigenvector centrality is only defined for connected networks, and will report `false` for disconnected graphs.

#### closeness

The [closeness centrality](http://en.wikipedia.org/wiki/Centrality#Closeness_centrality) of a turtle is defined as the inverse of the sum of it's distances to all other turtles.

Note that this primitive reports the _intra-component_ closeness of a turtle, that is, it takes into account only the distances to the turtles that are part of the same [component](http://en.wikipedia.org/wiki/Connected_component_%28graph_theory%29) as the current turtle, since distance to turtles in other components is undefined. The closeness centrality of an isolated turtle is defined to be zero.


### Files

#### Load / Save Matrix

Finally, you can save and load your networks. This can be done through the use of simple text files containing an [adjacency matrix](http://en.wikipedia.org/wiki/Adjacency_matrix).

The model currently always save the network to your NetLogo directory in a file called `matrix.txt` when you click the **save** button. When you click the **load** button, it reads from the same location and creates a new network from the file.

#### Load / Save GraphML

You can also save and load GraphML files. Please see the [extension's documentation](https://github.com/NetLogo/NW-Extension#save-graphml) for more detail on handling GraphML files. The demo simply saves the current network to (and can load from) the file `demo.graphml` in your default directory.


## THINGS TO NOTICE

- When you generate preferential attachment networks, notice the distribution of node degrees in the histogram. What does it look like? What happens if you generate a network with more nodes, or multiple preferential attachment networks?

- When you generate a small world network, what is the **mean path length** value that you can see on the monitor? How does it compare the a random network with the same number of nodes?

## THINGS TO TRY

- In general, different layouts work best for different kind of graphs. Can you try every combination of graph/layout? Which layout do you prefer for each kind of graph? Why?

- Try the spring layout with a lattice 2D network, with **wrap** set to off. How does it look? Now try it with **wrap** set to on. Can you explain the difference?

- Generate a small world network with a low clustering exponent (e.g., 0.1). What is the size of the biggest maximal clique? Now try it with a big exponent (e.g. 10.0). What is the size? Try it multiple times. Do you see a pattern? What if you crank up the number of rows and columns?

## EXTENDING THE MODEL

The current version of the demo does not take link weights into account. You can add a "weight" variable to each link breed. Can you add a button assigning random weights to the links? Can you make it so that link thickness reflects the "weight" of the link? Look at the extensions documentation for primitive that take weights into account. Can you integrate those in the demo?

## NETLOGO FEATURES

Well, this model obviously shows the network extension primitives.

But aside from that, notice the interesting use it makes of tasks for the centrality buttons. We have only one `centrality` procedure in the code that does all the hard work, and the other procedures call it with a `measure` reporter task as a parameter, that the `centrality` primitive then runs with `runresult`. This removes a lot of code duplication.

Another nice tidbit is how the `foreach` command is used in the `color-clusters` primitive. Notice how it loops over both the `clusters` list and the `colors` and then uses `?1` and `?2` to access members of each pair of cluster/color.

## RELATED MODELS

A couple of models already in the model library, namely the "Giant Component" model and the "Small World" model could be build much more easily by using the primitives in the network extension. Such versions of these two models are included in the "demo" folder of the extension, but trying to make the modifications yourself would be an excellent exercice.

## CREDITS AND REFERENCES

Copyright 2015 Chun Tian <chun.tian@studio.unibo.it>.
Copyright 2012 Uri Wilensky.

![CC BY-NC-SA 3.0](http://i.creativecommons.org/l/by-nc-sa/3.0/88x31.png)

This work is licensed under the Creative Commons Attribution-NonCommercial-ShareAlike 3.0 License.  To view a copy of this license, visit http://creativecommons.org/licenses/by-nc-sa/3.0/ or send a letter to Creative Commons, 559 Nathan Abbott Way, Stanford, California 94305, USA.

Commercial licenses are also available. To inquire about commercial licenses, please contact Uri Wilensky at uri@northwestern.edu.
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
0
Rectangle -7500403 true true 151 225 180 285
Rectangle -7500403 true true 47 225 75 285
Rectangle -7500403 true true 15 75 210 225
Circle -7500403 true true 135 75 150
Circle -16777216 true false 165 76 116

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -7500403 true true 135 285 195 285 270 90 30 90 105 285
Polygon -7500403 true true 270 90 225 15 180 90
Polygon -7500403 true true 30 90 75 15 120 90
Circle -1 true false 183 138 24
Circle -1 true false 93 138 24

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.2.2
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
1
@#$#@#$#@
