signature LambekTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val Arrow_def : thm
    val Form_TY_DEF : thm
    val Form_case_def : thm
    val Form_size_def : thm
    val LP_Sequent_def : thm
    val LP_def : thm
    val L_Sequent_def : thm
    val L_def : thm
    val NLP_Sequent_def : thm
    val NLP_def : thm
    val NL_Sequent_def : thm
    val NL_def : thm
    val Term_TY_DEF : thm
    val Term_case_def : thm
    val Term_size_def : thm
    val add_extension_def : thm
    val arrow_L_def : thm
    val arrow_def : thm
    val deltaTranslation_def : thm
    val extends_def : thm
    val gentzenSequent_def : thm
    val implements_def : thm
    val natDed_def : thm
    val p_arrow_def : thm
    val replaceCommaDot1_def : thm
    val replaceCommaDot_def : thm
    val replace_def : thm

  (*  Theorems  *)
    val Arrow_NLP : thm
    val Backslash_antimono_left : thm
    val Backslash_mono_right : thm
    val CutRuleSimpl : thm
    val DotElimGeneralized : thm
    val DotRightBackslash' : thm
    val DotRightSlash' : thm
    val Dot_mono : thm
    val Dot_mono_left : thm
    val Dot_mono_right : thm
    val Form_11 : thm
    val Form_Axiom : thm
    val Form_case_cong : thm
    val Form_distinct : thm
    val Form_induction : thm
    val Form_nchotomy : thm
    val LP_extends_L : thm
    val LP_extends_NLP : thm
    val LP_implements_LP_Sequent : thm
    val L_Intro_lr : thm
    val L_Intro_rl : thm
    val L_LP : thm
    val L_a : thm
    val L_b : thm
    val L_b' : thm
    val L_backslash_antimono_l : thm
    val L_backslash_mono_r : thm
    val L_c : thm
    val L_c' : thm
    val L_cases : thm
    val L_d : thm
    val L_d' : thm
    val L_dot_mono_l : thm
    val L_dot_mono_r : thm
    val L_e : thm
    val L_f : thm
    val L_g : thm
    val L_h : thm
    val L_i : thm
    val L_implements_L_Sequent : thm
    val L_ind : thm
    val L_j : thm
    val L_k : thm
    val L_k' : thm
    val L_l : thm
    val L_l' : thm
    val L_m : thm
    val L_n : thm
    val L_rules : thm
    val L_slash_antimono_r : thm
    val L_slash_mono_l : thm
    val L_strongind : thm
    val LeftBackslashSimpl : thm
    val LeftDotGeneralized : thm
    val LeftDotSimpl : thm
    val LeftSlashSimpl : thm
    val LextensionSimpl : thm
    val LextensionSimpl' : thm
    val LextensionSimplDot : thm
    val LextensionSimplDot' : thm
    val NLP_Intro : thm
    val NLP_LP : thm
    val NLP_cases : thm
    val NLP_implements_NLP_Sequent : thm
    val NLP_ind : thm
    val NLP_rules : thm
    val NLP_strongind : thm
    val NLPextensionSimpl : thm
    val NLPextensionSimplDot : thm
    val NL_X : thm
    val NL_implements_NL_Sequent : thm
    val NatAxiomGen : thm
    val RightSlashDot : thm
    val SeqAxiomGen : thm
    val Slash_antimono_right : thm
    val Slash_mono_left : thm
    val TermToForm : thm
    val Term_11 : thm
    val Term_Axiom : thm
    val Term_case_cong : thm
    val Term_distinct : thm
    val Term_induction : thm
    val Term_nchotomy : thm
    val X_arrow : thm
    val add_extend_l : thm
    val add_extend_r : thm
    val antitonicity : thm
    val antitonicity' : thm
    val application : thm
    val application' : thm
    val arrow_Arrow : thm
    val arrow_plus : thm
    val beta : thm
    val beta' : thm
    val coApplication : thm
    val coApplication' : thm
    val comp : thm
    val datatype_Form : thm
    val datatype_Term : thm
    val extends_trans : thm
    val gamma : thm
    val gamma' : thm
    val gentzenSequent_cases : thm
    val gentzenSequent_ind : thm
    val gentzenSequent_rules : thm
    val gentzenSequent_strongind : thm
    val isotonicity : thm
    val isotonicity' : thm
    val lifting : thm
    val lifting' : thm
    val mainGeach : thm
    val mainGeach' : thm
    val mono_X : thm
    val monotonicity : thm
    val natDed_cases : thm
    val natDed_ind : thm
    val natDed_rules : thm
    val natDed_strongind : thm
    val noReplace : thm
    val no_extend : thm
    val one : thm
    val p_arrow_cases : thm
    val p_arrow_ind : thm
    val p_arrow_rules : thm
    val p_arrow_strongind : thm
    val replaceCommaDot1_cases : thm
    val replaceCommaDot1_ind : thm
    val replaceCommaDot1_rules : thm
    val replaceCommaDot1_strongind : thm
    val replaceCommaDot_ind : thm
    val replaceMono : thm
    val replaceMonoLeft : thm
    val replaceMonoRight : thm
    val replaceOneComma : thm
    val replaceOneComma' : thm
    val replaceTransitive : thm
    val replaceTransitive' : thm
    val replaceTranslation : thm
    val replace_cases : thm
    val replace_ind : thm
    val replace_rules : thm
    val replace_strongind : thm
    val secondaryGeach : thm
    val secondaryGeach' : thm

  val Lambek_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "Lambek"

   [patternMatches] Parent theory of "Lambek"

   [Arrow_def]  Definition

      |- ∀X. Arrow X = add_extension arrow X

   [Form_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'Form' .
                  (∀a0'.
                     (∃a.
                        a0' =
                        (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC 0) ARB
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'Form' a0 ∧ 'Form' a1) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC (SUC 0)) ARB
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'Form' a0 ∧ 'Form' a1) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC (SUC (SUC 0))) ARB
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'Form' a0 ∧ 'Form' a1) ⇒
                     'Form' a0') ⇒
                  'Form' a0') rep

   [Form_case_def]  Definition

      |- (∀a f f1 f2 f3. Form_CASE (At a) f f1 f2 f3 = f a) ∧
         (∀a0 a1 f f1 f2 f3. Form_CASE (a0 / a1) f f1 f2 f3 = f1 a0 a1) ∧
         (∀a0 a1 f f1 f2 f3. Form_CASE (a0 \ a1) f f1 f2 f3 = f2 a0 a1) ∧
         ∀a0 a1 f f1 f2 f3. Form_CASE (a0 . a1) f f1 f2 f3 = f3 a0 a1

   [Form_size_def]  Definition

      |- (∀f a. Form_size f (At a) = 1 + f a) ∧
         (∀f a0 a1.
            Form_size f (a0 / a1) =
            1 + (Form_size f a0 + Form_size f a1)) ∧
         (∀f a0 a1.
            Form_size f (a0 \ a1) =
            1 + (Form_size f a0 + Form_size f a1)) ∧
         ∀f a0 a1.
           Form_size f (a0 . a1) = 1 + (Form_size f a0 + Form_size f a1)

   [LP_Sequent_def]  Definition

      |- LP_Sequent = add_extension NLP_Sequent L_Sequent

   [LP_def]  Definition

      |- LP = add_extension NLP L

   [L_Sequent_def]  Definition

      |- ∀A B. L_Sequent A B ⇔ L (deltaTranslation A) (deltaTranslation B)

   [L_def]  Definition

      |- L =
         (λa0 a1.
            ∀L'.
              (∀a0 a1.
                 (∃A B C. (a0 = A . (B . C)) ∧ (a1 = (A . B) . C)) ∨
                 (∃A B C. (a0 = (A . B) . C) ∧ (a1 = A . (B . C))) ⇒
                 L' a0 a1) ⇒
              L' a0 a1)

   [NLP_Sequent_def]  Definition

      |- ∀A B.
           NLP_Sequent A B ⇔ NLP (deltaTranslation A) (deltaTranslation B)

   [NLP_def]  Definition

      |- NLP =
         (λa0 a1.
            ∀NLP'.
              (∀a0 a1. (∃A B. (a0 = A . B) ∧ (a1 = B . A)) ⇒ NLP' a0 a1) ⇒
              NLP' a0 a1)

   [NL_Sequent_def]  Definition

      |- ∀A B.
           NL_Sequent A B ⇔ NL (deltaTranslation A) (deltaTranslation B)

   [NL_def]  Definition

      |- NL = ∅ᵣ

   [Term_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'Term' .
                  (∀a0'.
                     (∃a.
                        a0' =
                        (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC 0) ARB
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'Term' a0 ∧ 'Term' a1) ⇒
                     'Term' a0') ⇒
                  'Term' a0') rep

   [Term_case_def]  Definition

      |- (∀a f f1. Term_CASE (OneForm a) f f1 = f a) ∧
         ∀a0 a1 f f1. Term_CASE (a0, a1) f f1 = f1 a0 a1

   [Term_size_def]  Definition

      |- (∀f a. Term_size f (OneForm a) = 1 + Form_size f a) ∧
         ∀f a0 a1.
           Term_size f (a0, a1) = 1 + (Term_size f a0 + Term_size f a1)

   [add_extension_def]  Definition

      |- ∀E1 E2. add_extension E1 E2 = E1 ∪ᵣ E2

   [arrow_L_def]  Definition

      |- arrow_L = Arrow L

   [arrow_def]  Definition

      |- arrow = p_arrow^*

   [deltaTranslation_def]  Definition

      |- (∀f. deltaTranslation (OneForm f) = f) ∧
         ∀t1 t2.
           deltaTranslation (t1, t2) =
           deltaTranslation t1 . deltaTranslation t2

   [extends_def]  Definition

      |- ∀X X'. extends X X' ⇔ X ⊆ᵣ X'

   [gentzenSequent_def]  Definition

      |- gentzenSequent =
         (λa0 a1 a2.
            ∀gentzenSequent'.
              (∀a0 a1 a2.
                 (a1 = OneForm a2) ∨
                 (∃A B.
                    (a2 = A / B) ∧ gentzenSequent' a0 (a1, OneForm B) A) ∨
                 (∃A B.
                    (a2 = B \ A) ∧ gentzenSequent' a0 (OneForm B, a1) A) ∨
                 (∃Gamma Delta A B.
                    (a1 = (Gamma, Delta)) ∧ (a2 = A . B) ∧
                    gentzenSequent' a0 Gamma A ∧
                    gentzenSequent' a0 Delta B) ∨
                 (∃Gamma Delta A B.
                    replace Gamma a1 (OneForm A) (OneForm (A / B), Delta) ∧
                    gentzenSequent' a0 Delta B ∧
                    gentzenSequent' a0 Gamma a2) ∨
                 (∃Gamma Delta A B.
                    replace Gamma a1 (OneForm A) (Delta, OneForm (B \ A)) ∧
                    gentzenSequent' a0 Delta B ∧
                    gentzenSequent' a0 Gamma a2) ∨
                 (∃Gamma A B.
                    replace Gamma a1 (OneForm A, OneForm B)
                      (OneForm (A . B)) ∧ gentzenSequent' a0 Gamma a2) ∨
                 (∃Delta Gamma A.
                    replace Gamma a1 (OneForm A) Delta ∧
                    gentzenSequent' a0 Delta A ∧
                    gentzenSequent' a0 Gamma a2) ∨
                 (∃N Gamma T1 T2.
                    N T1 T2 ∧ replace Gamma a1 T1 T2 ∧
                    gentzenSequent' a0 Gamma a2) ⇒
                 gentzenSequent' a0 a1 a2) ⇒
              gentzenSequent' a0 a1 a2)

   [implements_def]  Definition

      |- ∀X E.
           implements X E ⇔
           ∀A B. E A B ⇔ X (deltaTranslation A) (deltaTranslation B)

   [natDed_def]  Definition

      |- natDed =
         (λa0 a1 a2.
            ∀natDed'.
              (∀a0 a1 a2.
                 (a1 = OneForm a2) ∨
                 (∃A B. (a2 = A / B) ∧ natDed' a0 (a1, OneForm B) A) ∨
                 (∃A B. (a2 = B \ A) ∧ natDed' a0 (OneForm B, a1) A) ∨
                 (∃Gamma Delta A B.
                    (a1 = (Gamma, Delta)) ∧ (a2 = A . B) ∧
                    natDed' a0 Gamma A ∧ natDed' a0 Delta B) ∨
                 (∃Gamma Delta B.
                    (a1 = (Gamma, Delta)) ∧ natDed' a0 Gamma (a2 / B) ∧
                    natDed' a0 Delta B) ∨
                 (∃Gamma Delta B.
                    (a1 = (Gamma, Delta)) ∧ natDed' a0 Gamma B ∧
                    natDed' a0 Delta (B \ a2)) ∨
                 (∃Gamma Delta A B.
                    replace Gamma a1 (OneForm A, OneForm B) Delta ∧
                    natDed' a0 Delta (A . B) ∧ natDed' a0 Gamma a2) ∨
                 (∃N Gamma T1 T2.
                    N T1 T2 ∧ replace Gamma a1 T1 T2 ∧
                    natDed' a0 Gamma a2) ⇒
                 natDed' a0 a1 a2) ⇒
              natDed' a0 a1 a2)

   [p_arrow_def]  Definition

      |- p_arrow =
         (λa0 a1.
            ∀p_arrow'.
              (∀a0 a1.
                 (∃B C. (a1 = C / B) ∧ p_arrow' (a0 . B) C) ∨
                 (∃A B. (a0 = A . B) ∧ p_arrow' A (a1 / B)) ∨
                 (∃A C. (a1 = A \ C) ∧ p_arrow' (A . a0) C) ∨
                 (∃A B. (a0 = A . B) ∧ p_arrow' B (A \ a1)) ∨
                 (∃X. X a0 a1) ⇒
                 p_arrow' a0 a1) ⇒
              p_arrow' a0 a1)

   [replaceCommaDot1_def]  Definition

      |- replaceCommaDot1 =
         (λa0 a1.
            ∀replaceCommaDot1'.
              (∀a0 a1.
                 (∃A B.
                    replace a0 a1 (OneForm A, OneForm B)
                      (OneForm (A . B))) ⇒
                 replaceCommaDot1' a0 a1) ⇒
              replaceCommaDot1' a0 a1)

   [replaceCommaDot_def]  Definition

      |- replaceCommaDot = replaceCommaDot1^*

   [replace_def]  Definition

      |- replace =
         (λa0 a1 a2 a3.
            ∀replace'.
              (∀a0 a1 a2 a3.
                 (a2 = a0) ∧ (a3 = a1) ∨
                 (∃Gamma1 Gamma2 Delta.
                    (a0 = (Gamma1, Delta)) ∧ (a1 = (Gamma2, Delta)) ∧
                    replace' Gamma1 Gamma2 a2 a3) ∨
                 (∃Gamma1 Gamma2 Delta.
                    (a0 = (Delta, Gamma1)) ∧ (a1 = (Delta, Gamma2)) ∧
                    replace' Gamma1 Gamma2 a2 a3) ⇒
                 replace' a0 a1 a2 a3) ⇒
              replace' a0 a1 a2 a3)

   [Arrow_NLP]  Theorem

      |- ∀A B. Arrow NLP (A . B) (B . A)

   [Backslash_antimono_left]  Theorem

      |- ∀A C A'. A → A' ⇒ A' \ C → A \ C

   [Backslash_mono_right]  Theorem

      |- ∀A C C'. C' → C ⇒ A \ C' → A \ C

   [CutRuleSimpl]  Theorem

      |- ∀Gamma A C E.
           gentzenSequent E Gamma A ∧ gentzenSequent E (OneForm A) C ⇒
           gentzenSequent E Gamma C

   [DotElimGeneralized]  Theorem

      |- ∀E T1 T2 C. replaceCommaDot T1 T2 ∧ natDed E T1 C ⇒ natDed E T2 C

   [DotRightBackslash']  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm B) (A \ C) ⇒
           gentzenSequent E (OneForm (A . B)) C

   [DotRightSlash']  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm A) (C / B) ⇒
           gentzenSequent E (OneForm (A . B)) C

   [Dot_mono]  Theorem

      |- ∀A B C D. A → C ∧ B → D ⇒ (A . B) → (C . D)

   [Dot_mono_left]  Theorem

      |- ∀A B A'. A' → A ⇒ (A' . B) → (A . B)

   [Dot_mono_right]  Theorem

      |- ∀A B B'. B' → B ⇒ (A . B') → (A . B)

   [Form_11]  Theorem

      |- (∀a a'. (At a = At a') ⇔ (a = a')) ∧
         (∀a0 a1 a0' a1'.
            (a0 / a1 = a0' / a1') ⇔ (a0 = a0') ∧ (a1 = a1')) ∧
         (∀a0 a1 a0' a1'.
            (a0 \ a1 = a0' \ a1') ⇔ (a0 = a0') ∧ (a1 = a1')) ∧
         ∀a0 a1 a0' a1'. (a0 . a1 = a0' . a1') ⇔ (a0 = a0') ∧ (a1 = a1')

   [Form_Axiom]  Theorem

      |- ∀f0 f1 f2 f3.
           ∃fn.
             (∀a. fn (At a) = f0 a) ∧
             (∀a0 a1. fn (a0 / a1) = f1 a0 a1 (fn a0) (fn a1)) ∧
             (∀a0 a1. fn (a0 \ a1) = f2 a0 a1 (fn a0) (fn a1)) ∧
             ∀a0 a1. fn (a0 . a1) = f3 a0 a1 (fn a0) (fn a1)

   [Form_case_cong]  Theorem

      |- ∀M M' f f1 f2 f3.
           (M = M') ∧ (∀a. (M' = At a) ⇒ (f a = f' a)) ∧
           (∀a0 a1. (M' = a0 / a1) ⇒ (f1 a0 a1 = f1' a0 a1)) ∧
           (∀a0 a1. (M' = a0 \ a1) ⇒ (f2 a0 a1 = f2' a0 a1)) ∧
           (∀a0 a1. (M' = a0 . a1) ⇒ (f3 a0 a1 = f3' a0 a1)) ⇒
           (Form_CASE M f f1 f2 f3 = Form_CASE M' f' f1' f2' f3')

   [Form_distinct]  Theorem

      |- (∀a1 a0 a. At a ≠ a0 / a1) ∧ (∀a1 a0 a. At a ≠ a0 \ a1) ∧
         (∀a1 a0 a. At a ≠ (a0 . a1)) ∧
         (∀a1' a1 a0' a0. a0 / a1 ≠ a0' \ a1') ∧
         (∀a1' a1 a0' a0. a0 / a1 ≠ (a0' . a1')) ∧
         ∀a1' a1 a0' a0. a0 \ a1 ≠ (a0' . a1')

   [Form_induction]  Theorem

      |- ∀P.
           (∀a. P (At a)) ∧ (∀F' F0. P F' ∧ P F0 ⇒ P (F' / F0)) ∧
           (∀F' F0. P F' ∧ P F0 ⇒ P (F' \ F0)) ∧
           (∀F' F0. P F' ∧ P F0 ⇒ P (F' . F0)) ⇒
           ∀F'. P F'

   [Form_nchotomy]  Theorem

      |- ∀F'F'.
           (∃a. F'F' = At a) ∨ (∃F' F0. F'F' = F' / F0) ∨
           (∃F' F0. F'F' = F' \ F0) ∨ ∃F' F0. F'F' = F' . F0

   [LP_extends_L]  Theorem

      |- ∀E. extends LP_Sequent E ⇒ extends L_Sequent E

   [LP_extends_NLP]  Theorem

      |- ∀E. extends LP_Sequent E ⇒ extends NLP_Sequent E

   [LP_implements_LP_Sequent]  Theorem

      |- implements LP LP_Sequent

   [L_Intro_lr]  Theorem

      |- ∀A B C. L_Sequent (A, (B, C)) ((A, B), C)

   [L_Intro_rl]  Theorem

      |- ∀A B C. L_Sequent ((A, B), C) (A, (B, C))

   [L_LP]  Theorem

      |- extends L LP

   [L_a]  Theorem

      |- ∀x. x →ˡ x

   [L_b]  Theorem

      |- ∀x y z. ((x . y) . z) →ˡ (x . (y . z))

   [L_b']  Theorem

      |- ∀x y z. (x . (y . z)) →ˡ ((x . y) . z)

   [L_backslash_antimono_l]  Theorem

      |- ∀A C A'. A →ˡ A' ⇒ A' \ C →ˡ A \ C

   [L_backslash_mono_r]  Theorem

      |- ∀A C C'. C →ˡ C' ⇒ A \ C →ˡ A \ C'

   [L_c]  Theorem

      |- ∀x y z. (x . y) →ˡ z ⇒ x →ˡ z / y

   [L_c']  Theorem

      |- ∀x y z. (x . y) →ˡ z ⇒ y →ˡ x \ z

   [L_cases]  Theorem

      |- ∀a0 a1.
           L a0 a1 ⇔
           (∃A B C. (a0 = A . (B . C)) ∧ (a1 = (A . B) . C)) ∨
           ∃A B C. (a0 = (A . B) . C) ∧ (a1 = A . (B . C))

   [L_d]  Theorem

      |- ∀x y z. x →ˡ z / y ⇒ (x . y) →ˡ z

   [L_d']  Theorem

      |- ∀x y z. y →ˡ x \ z ⇒ (x . y) →ˡ z

   [L_dot_mono_l]  Theorem

      |- ∀A B A'. A →ˡ A' ⇒ (A . B) →ˡ (A' . B)

   [L_dot_mono_r]  Theorem

      |- ∀A B B'. B →ˡ B' ⇒ (A . B) →ˡ (A . B')

   [L_e]  Theorem

      |- ∀x y z. x →ˡ y ∧ y →ˡ z ⇒ x →ˡ z

   [L_f]  Theorem

      |- ∀x y. x →ˡ (x . y) / y

   [L_g]  Theorem

      |- ∀y z. (z / y . y) →ˡ z

   [L_h]  Theorem

      |- ∀y z. y →ˡ (z / y) \ z

   [L_i]  Theorem

      |- ∀x y z. (z / y . y / x) →ˡ z / x

   [L_implements_L_Sequent]  Theorem

      |- implements L L_Sequent

   [L_ind]  Theorem

      |- ∀L'.
           (∀A B C. L' (A . (B . C)) ((A . B) . C)) ∧
           (∀A B C. L' ((A . B) . C) (A . (B . C))) ⇒
           ∀a0 a1. L a0 a1 ⇒ L' a0 a1

   [L_j]  Theorem

      |- ∀x y z. z / y →ˡ z / x / (y / x)

   [L_k]  Theorem

      |- ∀x y z. x \ y / z →ˡ x \ (y / z)

   [L_k']  Theorem

      |- ∀x y z. x \ (y / z) →ˡ x \ y / z

   [L_l]  Theorem

      |- ∀x y z. x / y / z →ˡ x / (z . y)

   [L_l']  Theorem

      |- ∀x y z. x / (z . y) →ˡ x / y / z

   [L_m]  Theorem

      |- ∀x x' y y'. x →ˡ x' ∧ y →ˡ y' ⇒ (x . y) →ˡ (x' . y')

   [L_n]  Theorem

      |- ∀x x' y y'. x →ˡ x' ∧ y →ˡ y' ⇒ x / y' →ˡ x' / y

   [L_rules]  Theorem

      |- (∀A B C. L (A . (B . C)) ((A . B) . C)) ∧
         ∀A B C. L ((A . B) . C) (A . (B . C))

   [L_slash_antimono_r]  Theorem

      |- ∀C B B'. B →ˡ B' ⇒ C / B' →ˡ C / B

   [L_slash_mono_l]  Theorem

      |- ∀C B C'. C →ˡ C' ⇒ C / B →ˡ C' / B

   [L_strongind]  Theorem

      |- ∀L'.
           (∀A B C. L' (A . (B . C)) ((A . B) . C)) ∧
           (∀A B C. L' ((A . B) . C) (A . (B . C))) ⇒
           ∀a0 a1. L a0 a1 ⇒ L' a0 a1

   [LeftBackslashSimpl]  Theorem

      |- ∀Gamma A B C E.
           gentzenSequent E Gamma B ∧ gentzenSequent E (OneForm A) C ⇒
           gentzenSequent E (Gamma, OneForm (B \ A)) C

   [LeftDotGeneralized]  Theorem

      |- ∀T1 T2 C E.
           replaceCommaDot T1 T2 ∧ gentzenSequent E T1 C ⇒
           gentzenSequent E T2 C

   [LeftDotSimpl]  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm A, OneForm B) C ⇒
           gentzenSequent E (OneForm (A . B)) C

   [LeftSlashSimpl]  Theorem

      |- ∀Gamma A B C E.
           gentzenSequent E Gamma B ∧ gentzenSequent E (OneForm A) C ⇒
           gentzenSequent E (OneForm (A / B), Gamma) C

   [LextensionSimpl]  Theorem

      |- ∀T1 T2 T3 C E.
           extends L_Sequent E ∧ gentzenSequent E (T1, (T2, T3)) C ⇒
           gentzenSequent E ((T1, T2), T3) C

   [LextensionSimpl']  Theorem

      |- ∀T1 T2 T3 C E.
           extends L_Sequent E ∧ gentzenSequent E ((T1, T2), T3) C ⇒
           gentzenSequent E (T1, (T2, T3)) C

   [LextensionSimplDot]  Theorem

      |- ∀A B C D E.
           extends L_Sequent E ∧
           gentzenSequent E (OneForm (A . (B . C))) D ⇒
           gentzenSequent E (OneForm ((A . B) . C)) D

   [LextensionSimplDot']  Theorem

      |- ∀A B C D E.
           extends L_Sequent E ∧
           gentzenSequent E (OneForm ((A . B) . C)) D ⇒
           gentzenSequent E (OneForm (A . (B . C))) D

   [NLP_Intro]  Theorem

      |- ∀A B. NLP_Sequent (A, B) (B, A)

   [NLP_LP]  Theorem

      |- extends NLP LP

   [NLP_cases]  Theorem

      |- ∀a0 a1. NLP a0 a1 ⇔ ∃A B. (a0 = A . B) ∧ (a1 = B . A)

   [NLP_implements_NLP_Sequent]  Theorem

      |- implements NLP NLP_Sequent

   [NLP_ind]  Theorem

      |- ∀NLP'.
           (∀A B. NLP' (A . B) (B . A)) ⇒ ∀a0 a1. NLP a0 a1 ⇒ NLP' a0 a1

   [NLP_rules]  Theorem

      |- ∀A B. NLP (A . B) (B . A)

   [NLP_strongind]  Theorem

      |- ∀NLP'.
           (∀A B. NLP' (A . B) (B . A)) ⇒ ∀a0 a1. NLP a0 a1 ⇒ NLP' a0 a1

   [NLPextensionSimpl]  Theorem

      |- ∀T1 T2 C E.
           extends NLP_Sequent E ∧ gentzenSequent E (T1, T2) C ⇒
           gentzenSequent E (T2, T1) C

   [NLPextensionSimplDot]  Theorem

      |- ∀A B C E.
           extends NLP_Sequent E ∧ gentzenSequent E (OneForm (A . B)) C ⇒
           gentzenSequent E (OneForm (B . A)) C

   [NL_X]  Theorem

      |- ∀X. extends NL X

   [NL_implements_NL_Sequent]  Theorem

      |- implements NL NL_Sequent

   [NatAxiomGen]  Theorem

      |- ∀Gamma E. natDed E Gamma (deltaTranslation Gamma)

   [RightSlashDot]  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm (A . C)) B ⇒
           gentzenSequent E (OneForm A) (B / C)

   [SeqAxiomGen]  Theorem

      |- ∀Gamma E. gentzenSequent E Gamma (deltaTranslation Gamma)

   [Slash_antimono_right]  Theorem

      |- ∀C B B'. B' → B ⇒ C / B → C / B'

   [Slash_mono_left]  Theorem

      |- ∀C B C'. C' → C ⇒ C' / B → C / B

   [TermToForm]  Theorem

      |- ∀Gamma C E.
           gentzenSequent E Gamma C ⇒
           gentzenSequent E (OneForm (deltaTranslation Gamma)) C

   [Term_11]  Theorem

      |- (∀a a'. (OneForm a = OneForm a') ⇔ (a = a')) ∧
         ∀a0 a1 a0' a1'. ((a0, a1) = (a0', a1')) ⇔ (a0 = a0') ∧ (a1 = a1')

   [Term_Axiom]  Theorem

      |- ∀f0 f1.
           ∃fn.
             (∀a. fn (OneForm a) = f0 a) ∧
             ∀a0 a1. fn (a0, a1) = f1 a0 a1 (fn a0) (fn a1)

   [Term_case_cong]  Theorem

      |- ∀M M' f f1.
           (M = M') ∧ (∀a. (M' = OneForm a) ⇒ (f a = f' a)) ∧
           (∀a0 a1. (M' = (a0, a1)) ⇒ (f1 a0 a1 = f1' a0 a1)) ⇒
           (Term_CASE M f f1 = Term_CASE M' f' f1')

   [Term_distinct]  Theorem

      |- ∀a1 a0 a. OneForm a ≠ (a0, a1)

   [Term_induction]  Theorem

      |- ∀P.
           (∀F'. P (OneForm F')) ∧ (∀T' T0. P T' ∧ P T0 ⇒ P (T', T0)) ⇒
           ∀T'. P T'

   [Term_nchotomy]  Theorem

      |- ∀T'T'. (∃F'. T'T' = OneForm F') ∨ ∃T' T0. T'T' = (T', T0)

   [X_arrow]  Theorem

      |- ∀X A B. X A B ⇒ Arrow X A B

   [add_extend_l]  Theorem

      |- ∀X X'. extends X (add_extension X X')

   [add_extend_r]  Theorem

      |- ∀X X'. extends X' (add_extension X X')

   [antitonicity]  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm A) B ⇒
           gentzenSequent E (OneForm (C / B)) (C / A)

   [antitonicity']  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm A) B ⇒
           gentzenSequent E (OneForm (B \ C)) (A \ C)

   [application]  Theorem

      |- ∀A B E. gentzenSequent E (OneForm (A / B . B)) A

   [application']  Theorem

      |- ∀A B E. gentzenSequent E (OneForm (B . B \ A)) A

   [arrow_Arrow]  Theorem

      |- ∀X A B. A → B ⇒ Arrow X A B

   [arrow_plus]  Theorem

      |- ∀X A B. X A B ⇒ A → B

   [beta]  Theorem

      |- ∀A B C. (A . B) → C ⇒ A → C / B

   [beta']  Theorem

      |- ∀A B C. A → C / B ⇒ (A . B) → C

   [coApplication]  Theorem

      |- ∀A B E. gentzenSequent E (OneForm A) ((A . B) / B)

   [coApplication']  Theorem

      |- ∀A B E. gentzenSequent E (OneForm A) (B \ (B . A))

   [comp]  Theorem

      |- ∀A B C. A → B ∧ B → C ⇒ A → C

   [datatype_Form]  Theorem

      |- DATATYPE (Form At Slash Backslash Dot)

   [datatype_Term]  Theorem

      |- DATATYPE (Term OneForm Comma)

   [extends_trans]  Theorem

      |- transitive extends

   [gamma]  Theorem

      |- ∀A B C. (A . B) → C ⇒ B → A \ C

   [gamma']  Theorem

      |- ∀A B C. B → A \ C ⇒ (A . B) → C

   [gentzenSequent_cases]  Theorem

      |- ∀a0 a1 a2.
           gentzenSequent a0 a1 a2 ⇔
           (a1 = OneForm a2) ∨
           (∃A B. (a2 = A / B) ∧ gentzenSequent a0 (a1, OneForm B) A) ∨
           (∃A B. (a2 = B \ A) ∧ gentzenSequent a0 (OneForm B, a1) A) ∨
           (∃Gamma Delta A B.
              (a1 = (Gamma, Delta)) ∧ (a2 = A . B) ∧
              gentzenSequent a0 Gamma A ∧ gentzenSequent a0 Delta B) ∨
           (∃Gamma Delta A B.
              replace Gamma a1 (OneForm A) (OneForm (A / B), Delta) ∧
              gentzenSequent a0 Delta B ∧ gentzenSequent a0 Gamma a2) ∨
           (∃Gamma Delta A B.
              replace Gamma a1 (OneForm A) (Delta, OneForm (B \ A)) ∧
              gentzenSequent a0 Delta B ∧ gentzenSequent a0 Gamma a2) ∨
           (∃Gamma A B.
              replace Gamma a1 (OneForm A, OneForm B) (OneForm (A . B)) ∧
              gentzenSequent a0 Gamma a2) ∨
           (∃Delta Gamma A.
              replace Gamma a1 (OneForm A) Delta ∧
              gentzenSequent a0 Delta A ∧ gentzenSequent a0 Gamma a2) ∨
           ∃N Gamma T1 T2.
             N T1 T2 ∧ replace Gamma a1 T1 T2 ∧ gentzenSequent a0 Gamma a2

   [gentzenSequent_ind]  Theorem

      |- ∀gentzenSequent'.
           (∀A E. gentzenSequent' E (OneForm A) A) ∧
           (∀Gamma A B E.
              gentzenSequent' E (Gamma, OneForm B) A ⇒
              gentzenSequent' E Gamma (A / B)) ∧
           (∀Gamma A B E.
              gentzenSequent' E (OneForm B, Gamma) A ⇒
              gentzenSequent' E Gamma (B \ A)) ∧
           (∀Gamma Delta A B E.
              gentzenSequent' E Gamma A ∧ gentzenSequent' E Delta B ⇒
              gentzenSequent' E (Gamma, Delta) (A . B)) ∧
           (∀Gamma Gamma' Delta A B C E.
              replace Gamma Gamma' (OneForm A) (OneForm (A / B), Delta) ∧
              gentzenSequent' E Delta B ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀Gamma Gamma' Delta A B C E.
              replace Gamma Gamma' (OneForm A) (Delta, OneForm (B \ A)) ∧
              gentzenSequent' E Delta B ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀Gamma Gamma' A B C E.
              replace Gamma Gamma' (OneForm A, OneForm B)
                (OneForm (A . B)) ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀Delta Gamma Gamma' A C E.
              replace Gamma Gamma' (OneForm A) Delta ∧
              gentzenSequent' E Delta A ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀N Gamma Gamma' T1 T2 C E.
              N T1 T2 ∧ replace Gamma Gamma' T1 T2 ∧
              gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ⇒
           ∀a0 a1 a2. gentzenSequent a0 a1 a2 ⇒ gentzenSequent' a0 a1 a2

   [gentzenSequent_rules]  Theorem

      |- (∀A E. gentzenSequent E (OneForm A) A) ∧
         (∀Gamma A B E.
            gentzenSequent E (Gamma, OneForm B) A ⇒
            gentzenSequent E Gamma (A / B)) ∧
         (∀Gamma A B E.
            gentzenSequent E (OneForm B, Gamma) A ⇒
            gentzenSequent E Gamma (B \ A)) ∧
         (∀Gamma Delta A B E.
            gentzenSequent E Gamma A ∧ gentzenSequent E Delta B ⇒
            gentzenSequent E (Gamma, Delta) (A . B)) ∧
         (∀Gamma Gamma' Delta A B C E.
            replace Gamma Gamma' (OneForm A) (OneForm (A / B), Delta) ∧
            gentzenSequent E Delta B ∧ gentzenSequent E Gamma C ⇒
            gentzenSequent E Gamma' C) ∧
         (∀Gamma Gamma' Delta A B C E.
            replace Gamma Gamma' (OneForm A) (Delta, OneForm (B \ A)) ∧
            gentzenSequent E Delta B ∧ gentzenSequent E Gamma C ⇒
            gentzenSequent E Gamma' C) ∧
         (∀Gamma Gamma' A B C E.
            replace Gamma Gamma' (OneForm A, OneForm B) (OneForm (A . B)) ∧
            gentzenSequent E Gamma C ⇒
            gentzenSequent E Gamma' C) ∧
         (∀Delta Gamma Gamma' A C E.
            replace Gamma Gamma' (OneForm A) Delta ∧
            gentzenSequent E Delta A ∧ gentzenSequent E Gamma C ⇒
            gentzenSequent E Gamma' C) ∧
         ∀N Gamma Gamma' T1 T2 C E.
           N T1 T2 ∧ replace Gamma Gamma' T1 T2 ∧
           gentzenSequent E Gamma C ⇒
           gentzenSequent E Gamma' C

   [gentzenSequent_strongind]  Theorem

      |- ∀gentzenSequent'.
           (∀A E. gentzenSequent' E (OneForm A) A) ∧
           (∀Gamma A B E.
              gentzenSequent E (Gamma, OneForm B) A ∧
              gentzenSequent' E (Gamma, OneForm B) A ⇒
              gentzenSequent' E Gamma (A / B)) ∧
           (∀Gamma A B E.
              gentzenSequent E (OneForm B, Gamma) A ∧
              gentzenSequent' E (OneForm B, Gamma) A ⇒
              gentzenSequent' E Gamma (B \ A)) ∧
           (∀Gamma Delta A B E.
              gentzenSequent E Gamma A ∧ gentzenSequent' E Gamma A ∧
              gentzenSequent E Delta B ∧ gentzenSequent' E Delta B ⇒
              gentzenSequent' E (Gamma, Delta) (A . B)) ∧
           (∀Gamma Gamma' Delta A B C E.
              replace Gamma Gamma' (OneForm A) (OneForm (A / B), Delta) ∧
              gentzenSequent E Delta B ∧ gentzenSequent' E Delta B ∧
              gentzenSequent E Gamma C ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀Gamma Gamma' Delta A B C E.
              replace Gamma Gamma' (OneForm A) (Delta, OneForm (B \ A)) ∧
              gentzenSequent E Delta B ∧ gentzenSequent' E Delta B ∧
              gentzenSequent E Gamma C ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀Gamma Gamma' A B C E.
              replace Gamma Gamma' (OneForm A, OneForm B)
                (OneForm (A . B)) ∧ gentzenSequent E Gamma C ∧
              gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀Delta Gamma Gamma' A C E.
              replace Gamma Gamma' (OneForm A) Delta ∧
              gentzenSequent E Delta A ∧ gentzenSequent' E Delta A ∧
              gentzenSequent E Gamma C ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀N Gamma Gamma' T1 T2 C E.
              N T1 T2 ∧ replace Gamma Gamma' T1 T2 ∧
              gentzenSequent E Gamma C ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ⇒
           ∀a0 a1 a2. gentzenSequent a0 a1 a2 ⇒ gentzenSequent' a0 a1 a2

   [isotonicity]  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm A) B ⇒
           gentzenSequent E (OneForm (A / C)) (B / C)

   [isotonicity']  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm A) B ⇒
           gentzenSequent E (OneForm (C \ A)) (C \ B)

   [lifting]  Theorem

      |- ∀A B C E. gentzenSequent E (OneForm A) (B / A \ B)

   [lifting']  Theorem

      |- ∀A B C E. gentzenSequent E (OneForm A) ((B / A) \ B)

   [mainGeach]  Theorem

      |- ∀A B C E.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (A / B)) (A / C / (B / C))

   [mainGeach']  Theorem

      |- ∀A B C E.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (B \ A)) ((C \ B) \ C \ A)

   [mono_X]  Theorem

      |- ∀X X'. extends X X' ⇒ ∀A B. Arrow X A B ⇒ Arrow X' A B

   [monotonicity]  Theorem

      |- ∀A B C D E.
           gentzenSequent E (OneForm A) B ∧
           gentzenSequent E (OneForm C) D ⇒
           gentzenSequent E (OneForm (A . C)) (B . D)

   [natDed_cases]  Theorem

      |- ∀a0 a1 a2.
           natDed a0 a1 a2 ⇔
           (a1 = OneForm a2) ∨
           (∃A B. (a2 = A / B) ∧ natDed a0 (a1, OneForm B) A) ∨
           (∃A B. (a2 = B \ A) ∧ natDed a0 (OneForm B, a1) A) ∨
           (∃Gamma Delta A B.
              (a1 = (Gamma, Delta)) ∧ (a2 = A . B) ∧ natDed a0 Gamma A ∧
              natDed a0 Delta B) ∨
           (∃Gamma Delta B.
              (a1 = (Gamma, Delta)) ∧ natDed a0 Gamma (a2 / B) ∧
              natDed a0 Delta B) ∨
           (∃Gamma Delta B.
              (a1 = (Gamma, Delta)) ∧ natDed a0 Gamma B ∧
              natDed a0 Delta (B \ a2)) ∨
           (∃Gamma Delta A B.
              replace Gamma a1 (OneForm A, OneForm B) Delta ∧
              natDed a0 Delta (A . B) ∧ natDed a0 Gamma a2) ∨
           ∃N Gamma T1 T2.
             N T1 T2 ∧ replace Gamma a1 T1 T2 ∧ natDed a0 Gamma a2

   [natDed_ind]  Theorem

      |- ∀natDed'.
           (∀A E. natDed' E (OneForm A) A) ∧
           (∀Gamma A B E.
              natDed' E (Gamma, OneForm B) A ⇒ natDed' E Gamma (A / B)) ∧
           (∀Gamma A B E.
              natDed' E (OneForm B, Gamma) A ⇒ natDed' E Gamma (B \ A)) ∧
           (∀Gamma Delta A B E.
              natDed' E Gamma A ∧ natDed' E Delta B ⇒
              natDed' E (Gamma, Delta) (A . B)) ∧
           (∀Gamma Delta A B E.
              natDed' E Gamma (A / B) ∧ natDed' E Delta B ⇒
              natDed' E (Gamma, Delta) A) ∧
           (∀Gamma Delta A B E.
              natDed' E Gamma B ∧ natDed' E Delta (B \ A) ⇒
              natDed' E (Gamma, Delta) A) ∧
           (∀Gamma Gamma' Delta A B C E.
              replace Gamma Gamma' (OneForm A, OneForm B) Delta ∧
              natDed' E Delta (A . B) ∧ natDed' E Gamma C ⇒
              natDed' E Gamma' C) ∧
           (∀N Gamma Gamma' T1 T2 C E.
              N T1 T2 ∧ replace Gamma Gamma' T1 T2 ∧ natDed' E Gamma C ⇒
              natDed' E Gamma' C) ⇒
           ∀a0 a1 a2. natDed a0 a1 a2 ⇒ natDed' a0 a1 a2

   [natDed_rules]  Theorem

      |- (∀A E. natDed E (OneForm A) A) ∧
         (∀Gamma A B E.
            natDed E (Gamma, OneForm B) A ⇒ natDed E Gamma (A / B)) ∧
         (∀Gamma A B E.
            natDed E (OneForm B, Gamma) A ⇒ natDed E Gamma (B \ A)) ∧
         (∀Gamma Delta A B E.
            natDed E Gamma A ∧ natDed E Delta B ⇒
            natDed E (Gamma, Delta) (A . B)) ∧
         (∀Gamma Delta A B E.
            natDed E Gamma (A / B) ∧ natDed E Delta B ⇒
            natDed E (Gamma, Delta) A) ∧
         (∀Gamma Delta A B E.
            natDed E Gamma B ∧ natDed E Delta (B \ A) ⇒
            natDed E (Gamma, Delta) A) ∧
         (∀Gamma Gamma' Delta A B C E.
            replace Gamma Gamma' (OneForm A, OneForm B) Delta ∧
            natDed E Delta (A . B) ∧ natDed E Gamma C ⇒
            natDed E Gamma' C) ∧
         ∀N Gamma Gamma' T1 T2 C E.
           N T1 T2 ∧ replace Gamma Gamma' T1 T2 ∧ natDed E Gamma C ⇒
           natDed E Gamma' C

   [natDed_strongind]  Theorem

      |- ∀natDed'.
           (∀A E. natDed' E (OneForm A) A) ∧
           (∀Gamma A B E.
              natDed E (Gamma, OneForm B) A ∧
              natDed' E (Gamma, OneForm B) A ⇒
              natDed' E Gamma (A / B)) ∧
           (∀Gamma A B E.
              natDed E (OneForm B, Gamma) A ∧
              natDed' E (OneForm B, Gamma) A ⇒
              natDed' E Gamma (B \ A)) ∧
           (∀Gamma Delta A B E.
              natDed E Gamma A ∧ natDed' E Gamma A ∧ natDed E Delta B ∧
              natDed' E Delta B ⇒
              natDed' E (Gamma, Delta) (A . B)) ∧
           (∀Gamma Delta A B E.
              natDed E Gamma (A / B) ∧ natDed' E Gamma (A / B) ∧
              natDed E Delta B ∧ natDed' E Delta B ⇒
              natDed' E (Gamma, Delta) A) ∧
           (∀Gamma Delta A B E.
              natDed E Gamma B ∧ natDed' E Gamma B ∧
              natDed E Delta (B \ A) ∧ natDed' E Delta (B \ A) ⇒
              natDed' E (Gamma, Delta) A) ∧
           (∀Gamma Gamma' Delta A B C E.
              replace Gamma Gamma' (OneForm A, OneForm B) Delta ∧
              natDed E Delta (A . B) ∧ natDed' E Delta (A . B) ∧
              natDed E Gamma C ∧ natDed' E Gamma C ⇒
              natDed' E Gamma' C) ∧
           (∀N Gamma Gamma' T1 T2 C E.
              N T1 T2 ∧ replace Gamma Gamma' T1 T2 ∧ natDed E Gamma C ∧
              natDed' E Gamma C ⇒
              natDed' E Gamma' C) ⇒
           ∀a0 a1 a2. natDed a0 a1 a2 ⇒ natDed' a0 a1 a2

   [noReplace]  Theorem

      |- ∀T. replaceCommaDot T T

   [no_extend]  Theorem

      |- ∀X. extends X X

   [one]  Theorem

      |- ∀A. A → A

   [p_arrow_cases]  Theorem

      |- ∀a0 a1.
           p_arrow a0 a1 ⇔
           (∃B C. (a1 = C / B) ∧ p_arrow (a0 . B) C) ∨
           (∃A B. (a0 = A . B) ∧ p_arrow A (a1 / B)) ∨
           (∃A C. (a1 = A \ C) ∧ p_arrow (A . a0) C) ∨
           (∃A B. (a0 = A . B) ∧ p_arrow B (A \ a1)) ∨ ∃X. X a0 a1

   [p_arrow_ind]  Theorem

      |- ∀p_arrow'.
           (∀A B C. p_arrow' (A . B) C ⇒ p_arrow' A (C / B)) ∧
           (∀A B C. p_arrow' A (C / B) ⇒ p_arrow' (A . B) C) ∧
           (∀A B C. p_arrow' (A . B) C ⇒ p_arrow' B (A \ C)) ∧
           (∀A B C. p_arrow' B (A \ C) ⇒ p_arrow' (A . B) C) ∧
           (∀X A B. X A B ⇒ p_arrow' A B) ⇒
           ∀a0 a1. p_arrow a0 a1 ⇒ p_arrow' a0 a1

   [p_arrow_rules]  Theorem

      |- (∀A B C. p_arrow (A . B) C ⇒ p_arrow A (C / B)) ∧
         (∀A B C. p_arrow A (C / B) ⇒ p_arrow (A . B) C) ∧
         (∀A B C. p_arrow (A . B) C ⇒ p_arrow B (A \ C)) ∧
         (∀A B C. p_arrow B (A \ C) ⇒ p_arrow (A . B) C) ∧
         ∀X A B. X A B ⇒ p_arrow A B

   [p_arrow_strongind]  Theorem

      |- ∀p_arrow'.
           (∀A B C.
              p_arrow (A . B) C ∧ p_arrow' (A . B) C ⇒
              p_arrow' A (C / B)) ∧
           (∀A B C.
              p_arrow A (C / B) ∧ p_arrow' A (C / B) ⇒
              p_arrow' (A . B) C) ∧
           (∀A B C.
              p_arrow (A . B) C ∧ p_arrow' (A . B) C ⇒
              p_arrow' B (A \ C)) ∧
           (∀A B C.
              p_arrow B (A \ C) ∧ p_arrow' B (A \ C) ⇒
              p_arrow' (A . B) C) ∧ (∀X A B. X A B ⇒ p_arrow' A B) ⇒
           ∀a0 a1. p_arrow a0 a1 ⇒ p_arrow' a0 a1

   [replaceCommaDot1_cases]  Theorem

      |- ∀a0 a1.
           replaceCommaDot1 a0 a1 ⇔
           ∃A B. replace a0 a1 (OneForm A, OneForm B) (OneForm (A . B))

   [replaceCommaDot1_ind]  Theorem

      |- ∀replaceCommaDot1'.
           (∀T1 T2 A B.
              replace T1 T2 (OneForm A, OneForm B) (OneForm (A . B)) ⇒
              replaceCommaDot1' T1 T2) ⇒
           ∀a0 a1. replaceCommaDot1 a0 a1 ⇒ replaceCommaDot1' a0 a1

   [replaceCommaDot1_rules]  Theorem

      |- ∀T1 T2 A B.
           replace T1 T2 (OneForm A, OneForm B) (OneForm (A . B)) ⇒
           replaceCommaDot1 T1 T2

   [replaceCommaDot1_strongind]  Theorem

      |- ∀replaceCommaDot1'.
           (∀T1 T2 A B.
              replace T1 T2 (OneForm A, OneForm B) (OneForm (A . B)) ⇒
              replaceCommaDot1' T1 T2) ⇒
           ∀a0 a1. replaceCommaDot1 a0 a1 ⇒ replaceCommaDot1' a0 a1

   [replaceCommaDot_ind]  Theorem

      |- ∀P.
           (∀x. P x x) ∧
           (∀x y z A B.
              replace x y (OneForm A, OneForm B) (OneForm (A . B)) ∧
              P y z ⇒
              P x z) ⇒
           ∀x y. replaceCommaDot x y ⇒ P x y

   [replaceMono]  Theorem

      |- ∀T1 T2 T3 T4.
           replaceCommaDot T1 T2 ∧ replaceCommaDot T3 T4 ⇒
           replaceCommaDot (T1, T3) (T2, T4)

   [replaceMonoLeft]  Theorem

      |- ∀T3 T1 T2.
           replaceCommaDot T1 T2 ⇒ replaceCommaDot (T3, T1) (T3, T2)

   [replaceMonoRight]  Theorem

      |- ∀T3 T1 T2.
           replaceCommaDot T1 T2 ⇒ replaceCommaDot (T1, T3) (T2, T3)

   [replaceOneComma]  Theorem

      |- ∀T1 T2 T3 A B.
           replaceCommaDot T1 T2 ∧
           replace T2 T3 (OneForm A, OneForm B) (OneForm (A . B)) ⇒
           replaceCommaDot T1 T3

   [replaceOneComma']  Theorem

      |- ∀T1 T2 T3 A B.
           replace T1 T2 (OneForm A, OneForm B) (OneForm (A . B)) ∧
           replaceCommaDot T2 T3 ⇒
           replaceCommaDot T1 T3

   [replaceTransitive]  Theorem

      |- transitive replaceCommaDot

   [replaceTransitive']  Theorem

      |- ∀T1 T2 T3.
           replaceCommaDot T1 T2 ∧ replaceCommaDot T2 T3 ⇒
           replaceCommaDot T1 T3

   [replaceTranslation]  Theorem

      |- ∀T. replaceCommaDot T (OneForm (deltaTranslation T))

   [replace_cases]  Theorem

      |- ∀a0 a1 a2 a3.
           replace a0 a1 a2 a3 ⇔
           (a2 = a0) ∧ (a3 = a1) ∨
           (∃Gamma1 Gamma2 Delta.
              (a0 = (Gamma1, Delta)) ∧ (a1 = (Gamma2, Delta)) ∧
              replace Gamma1 Gamma2 a2 a3) ∨
           ∃Gamma1 Gamma2 Delta.
             (a0 = (Delta, Gamma1)) ∧ (a1 = (Delta, Gamma2)) ∧
             replace Gamma1 Gamma2 a2 a3

   [replace_ind]  Theorem

      |- ∀replace'.
           (∀F1 F2. replace' F1 F2 F1 F2) ∧
           (∀Gamma1 Gamma2 Delta F1 F2.
              replace' Gamma1 Gamma2 F1 F2 ⇒
              replace' (Gamma1, Delta) (Gamma2, Delta) F1 F2) ∧
           (∀Gamma1 Gamma2 Delta F1 F2.
              replace' Gamma1 Gamma2 F1 F2 ⇒
              replace' (Delta, Gamma1) (Delta, Gamma2) F1 F2) ⇒
           ∀a0 a1 a2 a3. replace a0 a1 a2 a3 ⇒ replace' a0 a1 a2 a3

   [replace_rules]  Theorem

      |- (∀F1 F2. replace F1 F2 F1 F2) ∧
         (∀Gamma1 Gamma2 Delta F1 F2.
            replace Gamma1 Gamma2 F1 F2 ⇒
            replace (Gamma1, Delta) (Gamma2, Delta) F1 F2) ∧
         ∀Gamma1 Gamma2 Delta F1 F2.
           replace Gamma1 Gamma2 F1 F2 ⇒
           replace (Delta, Gamma1) (Delta, Gamma2) F1 F2

   [replace_strongind]  Theorem

      |- ∀replace'.
           (∀F1 F2. replace' F1 F2 F1 F2) ∧
           (∀Gamma1 Gamma2 Delta F1 F2.
              replace Gamma1 Gamma2 F1 F2 ∧ replace' Gamma1 Gamma2 F1 F2 ⇒
              replace' (Gamma1, Delta) (Gamma2, Delta) F1 F2) ∧
           (∀Gamma1 Gamma2 Delta F1 F2.
              replace Gamma1 Gamma2 F1 F2 ∧ replace' Gamma1 Gamma2 F1 F2 ⇒
              replace' (Delta, Gamma1) (Delta, Gamma2) F1 F2) ⇒
           ∀a0 a1 a2 a3. replace a0 a1 a2 a3 ⇒ replace' a0 a1 a2 a3

   [secondaryGeach]  Theorem

      |- ∀A B C E.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (B / C)) ((A / B) \ (A / C))

   [secondaryGeach']  Theorem

      |- ∀A B C E.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (C \ B)) (C \ A / B \ A)


*)
end
