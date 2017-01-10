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
    val arrow_def : thm
    val deltaTranslation_def : thm
    val extends_def : thm
    val gentzenSequent_def : thm
    val implements_def : thm
    val natDed_def : thm
    val replaceCommaDot1_def : thm
    val replaceCommaDot_def : thm
    val replace_def : thm

  (*  Theorems  *)
    val Arrow_cases : thm
    val Arrow_ind : thm
    val Arrow_rules : thm
    val Arrow_strongind : thm
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
    val RightBackslashDot : thm
    val RightSlashDot : thm
    val SeqAxiomGen : thm
    val Slash_antimono_right : thm
    val Slash_mono_left : thm
    val TermToForm : thm
    val TermToFormDed : thm
    val Term_11 : thm
    val Term_Axiom : thm
    val Term_case_cong : thm
    val Term_distinct : thm
    val Term_induction : thm
    val Term_nchotomy : thm
    val add_extend_l : thm
    val add_extend_r : thm
    val antitonicity : thm
    val antitonicity' : thm
    val application : thm
    val application' : thm
    val coApplication : thm
    val coApplication' : thm
    val composition : thm
    val composition' : thm
    val currying : thm
    val currying' : thm
    val datatype_Form : thm
    val datatype_Term : thm
    val decurrying : thm
    val decurrying' : thm
    val exchange : thm
    val exchange' : thm
    val extends_trans : thm
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
    val mixedComposition : thm
    val mixedComposition' : thm
    val mono_E : thm
    val mono_X : thm
    val monotonicity : thm
    val natDed_cases : thm
    val natDed_ind : thm
    val natDed_rules : thm
    val natDed_strongind : thm
    val noReplace : thm
    val no_extend : thm
    val permutation : thm
    val postposing : thm
    val preposing : thm
    val replaceCommaDot1_cases : thm
    val replaceCommaDot1_ind : thm
    val replaceCommaDot1_rules : thm
    val replaceCommaDot1_strongind : thm
    val replaceCommaDot_ind : thm
    val replaceCommaDot_rule : thm
    val replaceMono : thm
    val replaceMonoLeft : thm
    val replaceMonoRight : thm
    val replaceNatDed : thm
    val replaceOneComma : thm
    val replaceOneComma' : thm
    val replaceTransitive : thm
    val replaceTransitive' : thm
    val replaceTranslation : thm
    val replace_cases : thm
    val replace_ind : thm
    val replace_rules : thm
    val replace_strongind : thm
    val restructuring : thm
    val restructuring' : thm
    val secondaryGeach : thm
    val secondaryGeach' : thm

  val Lambek_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "Lambek"

   [patternMatches] Parent theory of "Lambek"

   [Arrow_def]  Definition

      |- Arrow =
         (λa0 a1 a2.
            ∀Arrow'.
              (∀a0 a1 a2.
                 (a2 = a1) ∨ (∃B C. (a2 = C / B) ∧ Arrow' a0 (a1 . B) C) ∨
                 (∃A B. (a1 = A . B) ∧ Arrow' a0 A (a2 / B)) ∨
                 (∃A C. (a2 = A \ C) ∧ Arrow' a0 (A . a1) C) ∨
                 (∃A B. (a1 = A . B) ∧ Arrow' a0 B (A \ a2)) ∨
                 (∃B. Arrow' a0 a1 B ∧ Arrow' a0 B a2) ∨ a0 a1 a2 ⇒
                 Arrow' a0 a1 a2) ⇒
              Arrow' a0 a1 a2)

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

   [arrow_def]  Definition

      |- arrow = Arrow L

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
                 (∃Gamma Delta Delta'.
                    replace Gamma a1 Delta Delta' ∧ a0 Delta Delta' ∧
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
                 (∃Gamma Delta Delta'.
                    replace Gamma a1 Delta Delta' ∧ a0 Delta Delta' ∧
                    natDed' a0 Gamma a2) ⇒
                 natDed' a0 a1 a2) ⇒
              natDed' a0 a1 a2)

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

   [Arrow_cases]  Theorem

      |- ∀a0 a1 a2.
           Arrow a0 a1 a2 ⇔
           (a2 = a1) ∨ (∃B C. (a2 = C / B) ∧ Arrow a0 (a1 . B) C) ∨
           (∃A B. (a1 = A . B) ∧ Arrow a0 A (a2 / B)) ∨
           (∃A C. (a2 = A \ C) ∧ Arrow a0 (A . a1) C) ∨
           (∃A B. (a1 = A . B) ∧ Arrow a0 B (A \ a2)) ∨
           (∃B. Arrow a0 a1 B ∧ Arrow a0 B a2) ∨ a0 a1 a2

   [Arrow_ind]  Theorem

      |- ∀Arrow'.
           (∀X A. Arrow' X A A) ∧
           (∀X A B C. Arrow' X (A . B) C ⇒ Arrow' X A (C / B)) ∧
           (∀X A B C. Arrow' X A (C / B) ⇒ Arrow' X (A . B) C) ∧
           (∀X A B C. Arrow' X (A . B) C ⇒ Arrow' X B (A \ C)) ∧
           (∀X A B C. Arrow' X B (A \ C) ⇒ Arrow' X (A . B) C) ∧
           (∀X A B C. Arrow' X A B ∧ Arrow' X B C ⇒ Arrow' X A C) ∧
           (∀X A B. X A B ⇒ Arrow' X A B) ⇒
           ∀a0 a1 a2. Arrow a0 a1 a2 ⇒ Arrow' a0 a1 a2

   [Arrow_rules]  Theorem

      |- (∀X A. Arrow X A A) ∧
         (∀X A B C. Arrow X (A . B) C ⇒ Arrow X A (C / B)) ∧
         (∀X A B C. Arrow X A (C / B) ⇒ Arrow X (A . B) C) ∧
         (∀X A B C. Arrow X (A . B) C ⇒ Arrow X B (A \ C)) ∧
         (∀X A B C. Arrow X B (A \ C) ⇒ Arrow X (A . B) C) ∧
         (∀X A B C. Arrow X A B ∧ Arrow X B C ⇒ Arrow X A C) ∧
         ∀X A B. X A B ⇒ Arrow X A B

   [Arrow_strongind]  Theorem

      |- ∀Arrow'.
           (∀X A. Arrow' X A A) ∧
           (∀X A B C.
              Arrow X (A . B) C ∧ Arrow' X (A . B) C ⇒
              Arrow' X A (C / B)) ∧
           (∀X A B C.
              Arrow X A (C / B) ∧ Arrow' X A (C / B) ⇒
              Arrow' X (A . B) C) ∧
           (∀X A B C.
              Arrow X (A . B) C ∧ Arrow' X (A . B) C ⇒
              Arrow' X B (A \ C)) ∧
           (∀X A B C.
              Arrow X B (A \ C) ∧ Arrow' X B (A \ C) ⇒
              Arrow' X (A . B) C) ∧
           (∀X A B C.
              Arrow X A B ∧ Arrow' X A B ∧ Arrow X B C ∧ Arrow' X B C ⇒
              Arrow' X A C) ∧ (∀X A B. X A B ⇒ Arrow' X A B) ⇒
           ∀a0 a1 a2. Arrow a0 a1 a2 ⇒ Arrow' a0 a1 a2

   [Backslash_antimono_left]  Theorem

      |- ∀X A C A'. Arrow X A A' ⇒ Arrow X (A' \ C) (A \ C)

   [Backslash_mono_right]  Theorem

      |- ∀X A C C'. Arrow X C' C ⇒ Arrow X (A \ C') (A \ C)

   [CutRuleSimpl]  Theorem

      |- ∀Gamma A C E.
           gentzenSequent E Gamma A ∧ gentzenSequent E (OneForm A) C ⇒
           gentzenSequent E Gamma C

   [DotElimGeneralized]  Theorem

      |- ∀E C Gamma Gamma'.
           replaceCommaDot Gamma Gamma' ⇒
           natDed E Gamma C ⇒
           natDed E Gamma' C

   [DotRightBackslash']  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm B) (A \ C) ⇒
           gentzenSequent E (OneForm (A . B)) C

   [DotRightSlash']  Theorem

      |- ∀A B C E.
           gentzenSequent E (OneForm A) (C / B) ⇒
           gentzenSequent E (OneForm (A . B)) C

   [Dot_mono]  Theorem

      |- ∀X A B C D. Arrow X A C ∧ Arrow X B D ⇒ Arrow X (A . B) (C . D)

   [Dot_mono_left]  Theorem

      |- ∀X A B A'. Arrow X A' A ⇒ Arrow X (A' . B) (A . B)

   [Dot_mono_right]  Theorem

      |- ∀X A B B'. Arrow X B' B ⇒ Arrow X (A . B') (A . B)

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

      |- ∀x. x → x

   [L_b]  Theorem

      |- ∀x y z. ((x . y) . z) → (x . (y . z))

   [L_b']  Theorem

      |- ∀x y z. (x . (y . z)) → ((x . y) . z)

   [L_backslash_antimono_l]  Theorem

      |- ∀A C A'. A → A' ⇒ A' \ C → A \ C

   [L_backslash_mono_r]  Theorem

      |- ∀A C C'. C → C' ⇒ A \ C → A \ C'

   [L_c]  Theorem

      |- ∀x y z. (x . y) → z ⇒ x → z / y

   [L_c']  Theorem

      |- ∀x y z. (x . y) → z ⇒ y → x \ z

   [L_cases]  Theorem

      |- ∀a0 a1.
           L a0 a1 ⇔
           (∃A B C. (a0 = A . (B . C)) ∧ (a1 = (A . B) . C)) ∨
           ∃A B C. (a0 = (A . B) . C) ∧ (a1 = A . (B . C))

   [L_d]  Theorem

      |- ∀x y z. x → z / y ⇒ (x . y) → z

   [L_d']  Theorem

      |- ∀x y z. y → x \ z ⇒ (x . y) → z

   [L_dot_mono_l]  Theorem

      |- ∀A B A'. A → A' ⇒ (A . B) → (A' . B)

   [L_dot_mono_r]  Theorem

      |- ∀A B B'. B → B' ⇒ (A . B) → (A . B')

   [L_e]  Theorem

      |- ∀x y z. x → y ∧ y → z ⇒ x → z

   [L_f]  Theorem

      |- ∀x y. x → (x . y) / y

   [L_g]  Theorem

      |- ∀y z. (z / y . y) → z

   [L_h]  Theorem

      |- ∀y z. y → (z / y) \ z

   [L_i]  Theorem

      |- ∀x y z. (z / y . y / x) → z / x

   [L_implements_L_Sequent]  Theorem

      |- implements L L_Sequent

   [L_ind]  Theorem

      |- ∀L'.
           (∀A B C. L' (A . (B . C)) ((A . B) . C)) ∧
           (∀A B C. L' ((A . B) . C) (A . (B . C))) ⇒
           ∀a0 a1. L a0 a1 ⇒ L' a0 a1

   [L_j]  Theorem

      |- ∀x y z. z / y → z / x / (y / x)

   [L_k]  Theorem

      |- ∀x y z. x \ y / z → x \ (y / z)

   [L_k']  Theorem

      |- ∀x y z. x \ (y / z) → x \ y / z

   [L_l]  Theorem

      |- ∀x y z. x / y / z → x / (z . y)

   [L_l']  Theorem

      |- ∀x y z. x / (z . y) → x / y / z

   [L_m]  Theorem

      |- ∀x x' y y'. x → x' ∧ y → y' ⇒ (x . y) → (x' . y')

   [L_n]  Theorem

      |- ∀x x' y y'. x → x' ∧ y → y' ⇒ x / y' → x' / y

   [L_rules]  Theorem

      |- (∀A B C. L (A . (B . C)) ((A . B) . C)) ∧
         ∀A B C. L ((A . B) . C) (A . (B . C))

   [L_slash_antimono_r]  Theorem

      |- ∀C B B'. B → B' ⇒ C / B' → C / B

   [L_slash_mono_l]  Theorem

      |- ∀C B C'. C → C' ⇒ C / B → C' / B

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

      |- ∀E C T1 T2.
           replaceCommaDot T1 T2 ⇒
           gentzenSequent E T1 C ⇒
           gentzenSequent E T2 C

   [LeftDotSimpl]  Theorem

      |- ∀E A B C.
           gentzenSequent E (OneForm A, OneForm B) C ⇒
           gentzenSequent E (OneForm (A . B)) C

   [LeftSlashSimpl]  Theorem

      |- ∀Gamma A B C E.
           gentzenSequent E Gamma B ∧ gentzenSequent E (OneForm A) C ⇒
           gentzenSequent E (OneForm (A / B), Gamma) C

   [LextensionSimpl]  Theorem

      |- ∀E T1 T2 T3 C.
           extends L_Sequent E ∧ gentzenSequent E (T1, (T2, T3)) C ⇒
           gentzenSequent E ((T1, T2), T3) C

   [LextensionSimpl']  Theorem

      |- ∀E T1 T2 T3 C.
           extends L_Sequent E ∧ gentzenSequent E ((T1, T2), T3) C ⇒
           gentzenSequent E (T1, (T2, T3)) C

   [LextensionSimplDot]  Theorem

      |- ∀E A B C D.
           extends L_Sequent E ∧
           gentzenSequent E (OneForm (A . (B . C))) D ⇒
           gentzenSequent E (OneForm ((A . B) . C)) D

   [LextensionSimplDot']  Theorem

      |- ∀E A B C D.
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

      |- ∀E T1 T2 C.
           extends NLP_Sequent E ∧ gentzenSequent E (T1, T2) C ⇒
           gentzenSequent E (T2, T1) C

   [NLPextensionSimplDot]  Theorem

      |- ∀E A B C.
           extends NLP_Sequent E ∧ gentzenSequent E (OneForm (A . B)) C ⇒
           gentzenSequent E (OneForm (B . A)) C

   [NL_X]  Theorem

      |- ∀X. extends NL X

   [NL_implements_NL_Sequent]  Theorem

      |- implements NL NL_Sequent

   [NatAxiomGen]  Theorem

      |- ∀E Gamma. natDed E Gamma (deltaTranslation Gamma)

   [RightBackslashDot]  Theorem

      |- ∀E A B C.
           gentzenSequent E (OneForm (B . A)) C ⇒
           gentzenSequent E (OneForm A) (B \ C)

   [RightSlashDot]  Theorem

      |- ∀E A B C.
           gentzenSequent E (OneForm (A . C)) B ⇒
           gentzenSequent E (OneForm A) (B / C)

   [SeqAxiomGen]  Theorem

      |- ∀E Gamma. gentzenSequent E Gamma (deltaTranslation Gamma)

   [Slash_antimono_right]  Theorem

      |- ∀X C B B'. Arrow X B' B ⇒ Arrow X (C / B) (C / B')

   [Slash_mono_left]  Theorem

      |- ∀X C B C'. Arrow X C' C ⇒ Arrow X (C' / B) (C / B)

   [TermToForm]  Theorem

      |- ∀Gamma C E.
           gentzenSequent E Gamma C ⇒
           gentzenSequent E (OneForm (deltaTranslation Gamma)) C

   [TermToFormDed]  Theorem

      |- ∀E Gamma C.
           natDed E Gamma C ⇒ natDed E (OneForm (deltaTranslation Gamma)) C

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

   [add_extend_l]  Theorem

      |- ∀X X'. extends X (add_extension X X')

   [add_extend_r]  Theorem

      |- ∀X X'. extends X' (add_extension X X')

   [antitonicity]  Theorem

      |- ∀E A B C.
           gentzenSequent E (OneForm A) B ⇒
           gentzenSequent E (OneForm (C / B)) (C / A)

   [antitonicity']  Theorem

      |- ∀E A B C.
           gentzenSequent E (OneForm A) B ⇒
           gentzenSequent E (OneForm (B \ C)) (A \ C)

   [application]  Theorem

      |- ∀E A B. gentzenSequent E (OneForm (A / B . B)) A

   [application']  Theorem

      |- ∀E A B. gentzenSequent E (OneForm (B . B \ A)) A

   [coApplication]  Theorem

      |- ∀E A B. gentzenSequent E (OneForm A) ((A . B) / B)

   [coApplication']  Theorem

      |- ∀E A B. gentzenSequent E (OneForm A) (B \ (B . A))

   [composition]  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (A / B . B / C)) (A / C)

   [composition']  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (C \ B . B \ A)) (C \ A)

   [currying]  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (A / (B . C))) (A / C / B)

   [currying']  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (A / C / B)) (A / (B . C))

   [datatype_Form]  Theorem

      |- DATATYPE (Form At Slash Backslash Dot)

   [datatype_Term]  Theorem

      |- DATATYPE (Term OneForm Comma)

   [decurrying]  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm ((A . B) \ C)) (B \ A \ C)

   [decurrying']  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (B \ A \ C)) ((A . B) \ C)

   [exchange]  Theorem

      |- ∀E A B.
           extends NLP_Sequent E ⇒
           gentzenSequent E (OneForm (A / B)) (B \ A)

   [exchange']  Theorem

      |- ∀E A B.
           extends NLP_Sequent E ⇒
           gentzenSequent E (OneForm (B \ A)) (A / B)

   [extends_trans]  Theorem

      |- transitive extends

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
           ∃Gamma Delta Delta'.
             replace Gamma a1 Delta Delta' ∧ a0 Delta Delta' ∧
             gentzenSequent a0 Gamma a2

   [gentzenSequent_ind]  Theorem

      |- ∀gentzenSequent'.
           (∀E A. gentzenSequent' E (OneForm A) A) ∧
           (∀E Gamma A B.
              gentzenSequent' E (Gamma, OneForm B) A ⇒
              gentzenSequent' E Gamma (A / B)) ∧
           (∀E Gamma A B.
              gentzenSequent' E (OneForm B, Gamma) A ⇒
              gentzenSequent' E Gamma (B \ A)) ∧
           (∀E Gamma Delta A B.
              gentzenSequent' E Gamma A ∧ gentzenSequent' E Delta B ⇒
              gentzenSequent' E (Gamma, Delta) (A . B)) ∧
           (∀E Gamma Gamma' Delta A B C.
              replace Gamma Gamma' (OneForm A) (OneForm (A / B), Delta) ∧
              gentzenSequent' E Delta B ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀E Gamma Gamma' Delta A B C.
              replace Gamma Gamma' (OneForm A) (Delta, OneForm (B \ A)) ∧
              gentzenSequent' E Delta B ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀E Gamma Gamma' A B C.
              replace Gamma Gamma' (OneForm A, OneForm B)
                (OneForm (A . B)) ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀E Delta Gamma Gamma' A C.
              replace Gamma Gamma' (OneForm A) Delta ∧
              gentzenSequent' E Delta A ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀E Gamma Gamma' Delta Delta' C.
              replace Gamma Gamma' Delta Delta' ∧ E Delta Delta' ∧
              gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ⇒
           ∀a0 a1 a2. gentzenSequent a0 a1 a2 ⇒ gentzenSequent' a0 a1 a2

   [gentzenSequent_rules]  Theorem

      |- (∀E A. gentzenSequent E (OneForm A) A) ∧
         (∀E Gamma A B.
            gentzenSequent E (Gamma, OneForm B) A ⇒
            gentzenSequent E Gamma (A / B)) ∧
         (∀E Gamma A B.
            gentzenSequent E (OneForm B, Gamma) A ⇒
            gentzenSequent E Gamma (B \ A)) ∧
         (∀E Gamma Delta A B.
            gentzenSequent E Gamma A ∧ gentzenSequent E Delta B ⇒
            gentzenSequent E (Gamma, Delta) (A . B)) ∧
         (∀E Gamma Gamma' Delta A B C.
            replace Gamma Gamma' (OneForm A) (OneForm (A / B), Delta) ∧
            gentzenSequent E Delta B ∧ gentzenSequent E Gamma C ⇒
            gentzenSequent E Gamma' C) ∧
         (∀E Gamma Gamma' Delta A B C.
            replace Gamma Gamma' (OneForm A) (Delta, OneForm (B \ A)) ∧
            gentzenSequent E Delta B ∧ gentzenSequent E Gamma C ⇒
            gentzenSequent E Gamma' C) ∧
         (∀E Gamma Gamma' A B C.
            replace Gamma Gamma' (OneForm A, OneForm B) (OneForm (A . B)) ∧
            gentzenSequent E Gamma C ⇒
            gentzenSequent E Gamma' C) ∧
         (∀E Delta Gamma Gamma' A C.
            replace Gamma Gamma' (OneForm A) Delta ∧
            gentzenSequent E Delta A ∧ gentzenSequent E Gamma C ⇒
            gentzenSequent E Gamma' C) ∧
         ∀E Gamma Gamma' Delta Delta' C.
           replace Gamma Gamma' Delta Delta' ∧ E Delta Delta' ∧
           gentzenSequent E Gamma C ⇒
           gentzenSequent E Gamma' C

   [gentzenSequent_strongind]  Theorem

      |- ∀gentzenSequent'.
           (∀E A. gentzenSequent' E (OneForm A) A) ∧
           (∀E Gamma A B.
              gentzenSequent E (Gamma, OneForm B) A ∧
              gentzenSequent' E (Gamma, OneForm B) A ⇒
              gentzenSequent' E Gamma (A / B)) ∧
           (∀E Gamma A B.
              gentzenSequent E (OneForm B, Gamma) A ∧
              gentzenSequent' E (OneForm B, Gamma) A ⇒
              gentzenSequent' E Gamma (B \ A)) ∧
           (∀E Gamma Delta A B.
              gentzenSequent E Gamma A ∧ gentzenSequent' E Gamma A ∧
              gentzenSequent E Delta B ∧ gentzenSequent' E Delta B ⇒
              gentzenSequent' E (Gamma, Delta) (A . B)) ∧
           (∀E Gamma Gamma' Delta A B C.
              replace Gamma Gamma' (OneForm A) (OneForm (A / B), Delta) ∧
              gentzenSequent E Delta B ∧ gentzenSequent' E Delta B ∧
              gentzenSequent E Gamma C ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀E Gamma Gamma' Delta A B C.
              replace Gamma Gamma' (OneForm A) (Delta, OneForm (B \ A)) ∧
              gentzenSequent E Delta B ∧ gentzenSequent' E Delta B ∧
              gentzenSequent E Gamma C ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀E Gamma Gamma' A B C.
              replace Gamma Gamma' (OneForm A, OneForm B)
                (OneForm (A . B)) ∧ gentzenSequent E Gamma C ∧
              gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀E Delta Gamma Gamma' A C.
              replace Gamma Gamma' (OneForm A) Delta ∧
              gentzenSequent E Delta A ∧ gentzenSequent' E Delta A ∧
              gentzenSequent E Gamma C ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ∧
           (∀E Gamma Gamma' Delta Delta' C.
              replace Gamma Gamma' Delta Delta' ∧ E Delta Delta' ∧
              gentzenSequent E Gamma C ∧ gentzenSequent' E Gamma C ⇒
              gentzenSequent' E Gamma' C) ⇒
           ∀a0 a1 a2. gentzenSequent a0 a1 a2 ⇒ gentzenSequent' a0 a1 a2

   [isotonicity]  Theorem

      |- ∀E A B C.
           gentzenSequent E (OneForm A) B ⇒
           gentzenSequent E (OneForm (A / C)) (B / C)

   [isotonicity']  Theorem

      |- ∀E A B C.
           gentzenSequent E (OneForm A) B ⇒
           gentzenSequent E (OneForm (C \ A)) (C \ B)

   [lifting]  Theorem

      |- ∀E A B C. gentzenSequent E (OneForm A) (B / A \ B)

   [lifting']  Theorem

      |- ∀E A B C. gentzenSequent E (OneForm A) ((B / A) \ B)

   [mainGeach]  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (A / B)) (A / C / (B / C))

   [mainGeach']  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (B \ A)) ((C \ B) \ C \ A)

   [mixedComposition]  Theorem

      |- ∀E A B C.
           extends LP_Sequent E ⇒
           gentzenSequent E (OneForm (A / B . C \ B)) (C \ A)

   [mixedComposition']  Theorem

      |- ∀E A B C.
           extends LP_Sequent E ⇒
           gentzenSequent E (OneForm (B / C . B \ A)) (A / C)

   [mono_E]  Theorem

      |- ∀E' E Gamma A.
           gentzenSequent E Gamma A ⇒
           extends E E' ⇒
           gentzenSequent E' Gamma A

   [mono_X]  Theorem

      |- ∀X' X A B. Arrow X A B ⇒ extends X X' ⇒ Arrow X' A B

   [monotonicity]  Theorem

      |- ∀E A B C D.
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
           ∃Gamma Delta Delta'.
             replace Gamma a1 Delta Delta' ∧ a0 Delta Delta' ∧
             natDed a0 Gamma a2

   [natDed_ind]  Theorem

      |- ∀natDed'.
           (∀E A. natDed' E (OneForm A) A) ∧
           (∀E Gamma A B.
              natDed' E (Gamma, OneForm B) A ⇒ natDed' E Gamma (A / B)) ∧
           (∀E Gamma A B.
              natDed' E (OneForm B, Gamma) A ⇒ natDed' E Gamma (B \ A)) ∧
           (∀E Gamma Delta A B.
              natDed' E Gamma A ∧ natDed' E Delta B ⇒
              natDed' E (Gamma, Delta) (A . B)) ∧
           (∀E Gamma Delta A B.
              natDed' E Gamma (A / B) ∧ natDed' E Delta B ⇒
              natDed' E (Gamma, Delta) A) ∧
           (∀E Gamma Delta A B.
              natDed' E Gamma B ∧ natDed' E Delta (B \ A) ⇒
              natDed' E (Gamma, Delta) A) ∧
           (∀E Gamma Gamma' Delta A B C.
              replace Gamma Gamma' (OneForm A, OneForm B) Delta ∧
              natDed' E Delta (A . B) ∧ natDed' E Gamma C ⇒
              natDed' E Gamma' C) ∧
           (∀E C Gamma Gamma' Delta Delta'.
              replace Gamma Gamma' Delta Delta' ∧ E Delta Delta' ∧
              natDed' E Gamma C ⇒
              natDed' E Gamma' C) ⇒
           ∀a0 a1 a2. natDed a0 a1 a2 ⇒ natDed' a0 a1 a2

   [natDed_rules]  Theorem

      |- (∀E A. natDed E (OneForm A) A) ∧
         (∀E Gamma A B.
            natDed E (Gamma, OneForm B) A ⇒ natDed E Gamma (A / B)) ∧
         (∀E Gamma A B.
            natDed E (OneForm B, Gamma) A ⇒ natDed E Gamma (B \ A)) ∧
         (∀E Gamma Delta A B.
            natDed E Gamma A ∧ natDed E Delta B ⇒
            natDed E (Gamma, Delta) (A . B)) ∧
         (∀E Gamma Delta A B.
            natDed E Gamma (A / B) ∧ natDed E Delta B ⇒
            natDed E (Gamma, Delta) A) ∧
         (∀E Gamma Delta A B.
            natDed E Gamma B ∧ natDed E Delta (B \ A) ⇒
            natDed E (Gamma, Delta) A) ∧
         (∀E Gamma Gamma' Delta A B C.
            replace Gamma Gamma' (OneForm A, OneForm B) Delta ∧
            natDed E Delta (A . B) ∧ natDed E Gamma C ⇒
            natDed E Gamma' C) ∧
         ∀E C Gamma Gamma' Delta Delta'.
           replace Gamma Gamma' Delta Delta' ∧ E Delta Delta' ∧
           natDed E Gamma C ⇒
           natDed E Gamma' C

   [natDed_strongind]  Theorem

      |- ∀natDed'.
           (∀E A. natDed' E (OneForm A) A) ∧
           (∀E Gamma A B.
              natDed E (Gamma, OneForm B) A ∧
              natDed' E (Gamma, OneForm B) A ⇒
              natDed' E Gamma (A / B)) ∧
           (∀E Gamma A B.
              natDed E (OneForm B, Gamma) A ∧
              natDed' E (OneForm B, Gamma) A ⇒
              natDed' E Gamma (B \ A)) ∧
           (∀E Gamma Delta A B.
              natDed E Gamma A ∧ natDed' E Gamma A ∧ natDed E Delta B ∧
              natDed' E Delta B ⇒
              natDed' E (Gamma, Delta) (A . B)) ∧
           (∀E Gamma Delta A B.
              natDed E Gamma (A / B) ∧ natDed' E Gamma (A / B) ∧
              natDed E Delta B ∧ natDed' E Delta B ⇒
              natDed' E (Gamma, Delta) A) ∧
           (∀E Gamma Delta A B.
              natDed E Gamma B ∧ natDed' E Gamma B ∧
              natDed E Delta (B \ A) ∧ natDed' E Delta (B \ A) ⇒
              natDed' E (Gamma, Delta) A) ∧
           (∀E Gamma Gamma' Delta A B C.
              replace Gamma Gamma' (OneForm A, OneForm B) Delta ∧
              natDed E Delta (A . B) ∧ natDed' E Delta (A . B) ∧
              natDed E Gamma C ∧ natDed' E Gamma C ⇒
              natDed' E Gamma' C) ∧
           (∀E C Gamma Gamma' Delta Delta'.
              replace Gamma Gamma' Delta Delta' ∧ E Delta Delta' ∧
              natDed E Gamma C ∧ natDed' E Gamma C ⇒
              natDed' E Gamma' C) ⇒
           ∀a0 a1 a2. natDed a0 a1 a2 ⇒ natDed' a0 a1 a2

   [noReplace]  Theorem

      |- ∀T. replaceCommaDot T T

   [no_extend]  Theorem

      |- ∀X. extends X X

   [permutation]  Theorem

      |- ∀E A B C.
           extends NLP_Sequent E ⇒
           gentzenSequent E (OneForm A) (B \ C) ⇒
           gentzenSequent E (OneForm B) (A \ C)

   [postposing]  Theorem

      |- ∀E A B.
           extends NLP_Sequent E ⇒
           gentzenSequent E (OneForm A) ((A \ B) \ B)

   [preposing]  Theorem

      |- ∀E A B.
           extends NLP_Sequent E ⇒
           gentzenSequent E (OneForm A) (B / (B / A))

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

   [replaceCommaDot_rule]  Theorem

      |- ∀T1 T2 A B.
           replace T1 T2 (OneForm A, OneForm B) (OneForm (A . B)) ⇒
           replaceCommaDot T1 T2

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

   [replaceNatDed]  Theorem

      |- ∀E Gamma Gamma' Delta Delta'.
           replace Gamma Gamma' Delta Delta' ⇒
           natDed E Delta' (deltaTranslation Delta) ⇒
           natDed E Gamma' (deltaTranslation Gamma)

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

   [restructuring]  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (A \ B / C)) (A \ (B / C))

   [restructuring']  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (A \ (B / C))) (A \ B / C)

   [secondaryGeach]  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (B / C)) ((A / B) \ (A / C))

   [secondaryGeach']  Theorem

      |- ∀E A B C.
           extends L_Sequent E ⇒
           gentzenSequent E (OneForm (C \ B)) (C \ A / B \ A)


*)
end
