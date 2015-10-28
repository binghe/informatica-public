include "basics/types.ma".

inductive nat : Type[0] ≝ 
| O: nat
| S: nat → nat.

let rec add n m ≝ 
match n with
[ O ⇒ m
| S a ⇒ S (add a m)
].

lemma add_0: ∀a. add a O = a.
#a elim a
normalize // qed.

lemma add_S : ∀a,b. add a (S b) = S (add a b).
#a #b elim a normalize //
qed. 

theorem add_comm : ∀a,b. add a b = add b a.
#a elim a normalize
// qed.

definition twice ≝ λn.add n n.

theorem ex_half: ∀n.∃m. n = twice m ∨ n = S (twice m).
#n elim n normalize
  [ @(ex_intro … O) %1 //
  | #x * #m * #eqx
    [ @(ex_intro … m) /2/ | @(ex_intro … (S m)) normalize /2/ ]
  ]
qed. 

(* here is the new definition of div2 *)
let rec div2 n ≝
  match n with
  [ O ⇒ O
  | S x ⇒
    match x with
    [ O ⇒ O
    | S y ⇒ S (div2 y)
    ]
   ].

lemma twice_deduction: ∀n. twice (S n) = (S (S (twice n))).
normalize // qed.

lemma div2_deduction: ∀n. div2 (S (S n)) = S (div2 n).
normalize // qed.

lemma div2_and_twice_deduction: ∀n. div2 (twice (S n)) = S (div2 (twice n)).
#n >twice_deduction in match (twice (S n)); // qed.

lemma div2_ok_for_even_n: ∀n. ∀m. n = twice m → n = twice (div2 n).
#n #m #H >H elim m
[ normalize //
| #x #M >M >div2_and_twice_deduction //
] qed.

lemma div2_ok_for_odd_n: ∀n. ∀m. n = S (twice m) → n = S (twice (div2 n)).
#n #m #H >H elim m
[ normalize //
| #x >twice_deduction #M >M >div2_deduction //
] qed.

(*
lemma div2_almost_ok: ∀n.n = twice (div2 n) ∨ n = S (twice (div2 n)).

proof: according to "ex_half" ∃m. n = twice m ∨ n = S (twice m).

cases:
1) if n = twice m, use "div2_ok_for_even_n", n = twice (div2 n).
2) if n = S (twice m), use "div2_ok_for_odd_n", n = S (twice (div2 n)).
therefore: n = twice (div2 n) ∨ n = S (twice (div2 n)). QED.

But how to use the existential lemma "ex_half" here?!

theorem div2_ok: ∀n,q. div2 n = q → n = (twice q) ∨ n = S (twice q).
*)