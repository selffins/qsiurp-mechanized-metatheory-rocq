From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Export Sorting.PermutSetoid.
From Stdlib Require Export Sorting.PermutEq.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Export Permutation.
Require Export LL.SequentCalculi.
Require Export LL.SequentCalculiBasicTheory.
Require Export LL.Multisets.
Require Export LL.StrongInduction.
Require Export LL.FLLMetaTheory.

#[local] Hint Resolve Nat.le_max_r : core .
#[local] Hint Resolve Nat.le_max_l : core .

(** * Linear logic (LL)
      - Girard's original linear logic system.
      - Following the presentation laid out in the Encyclopedia of Proof Systems)
      - Exchange behaves implicitly (no low-level shifting of elements), but is an explicit rule in the system.
      - Contexts are multisets - we use the multiset library from the paper "coq-ll".
      - This file was is a modification taken from the Linear Logic formalization in Coq: https://github.com/brunofx86/LL.
 *)

Module PL.

  Inductive LForm :=
  | PosA   : nat -> LForm
  | NegA   : nat -> LForm
  | Zero   : LForm
  | One    : LForm
  | Bot    : LForm
  | Top    : LForm
  | Tensor : LForm -> LForm -> LForm
  | With   : LForm -> LForm -> LForm
  | Oplus  : LForm -> LForm -> LForm
  | Par    : LForm -> LForm -> LForm
  | Ofc    : LForm -> LForm
  | YNot   : LForm -> LForm.

  (** * Some infrastructure for multisets

  - Refer to the documentation for coq-ll. In short, we need that formulas have decidable equality.
  - These are defined in a module [F_dec], which is passed to the multiset module.

   *)

  Theorem LForm_dec_eq : forall F G : LForm, {F = G} + {F <> G}.
    Admitted.

  Module F_dec <: Eqset_dec_pol.

    Definition A := LForm.
    Definition eqA_dec := LForm_dec_eq.
    Fixpoint isPositive (n:nat) :=
      match n with
      | 0%nat => false
      | 1%nat => true
      | S (S n) => isPositive n
      end.

  End F_dec.

  Declare Module MSFormulas : MultisetList F_dec.

  Export MSFormulas.

  (** *** Negation *)

  Fixpoint negation (A : LForm) : LForm :=
    match A with
    | PosA v => NegA v
    | NegA v => PosA v
    | Ofc A => YNot (negation A)
    | YNot A => Ofc (negation A)
    | Tensor A B => Par (negation A) (negation B)
    | Par A B => Tensor (negation A) (negation B)
    | Oplus A B => With (negation A) (negation B)
    | With A B => Oplus (negation A) (negation B)
    | One => Bot
    | Bot => One
    | Zero => Top
    | Top => Zero
    end.

  Theorem negation_involutive : forall A, negation (negation A) = A.
  Proof.
    intros.
    induction A;auto;
      (repeat(simpl; rewrite IHA1; rewrite IHA2; auto));
      (repeat simpl; rewrite IHA;auto).
  Qed.

    (** *** Questions

        Some rules require that the context contains only [YNot] formulas.
        TBD: equivalence proof between the proposition form and the fixpoint form.

     *)

  Definition is_YNot (A : LForm) : Prop :=
      match A with
      | YNot _ => True
      | _ => False
      end.

  Definition Questions (G : list LForm) := forall A, In A G -> is_YNot A.

  Fixpoint questions (G : list LForm) : bool :=
    match G with
    | nil => true
    | cons A G' => match A with
                   | YNot _ => questions G'
                   | _ => false
                   end
    end.

  Lemma questions_Questions :
    forall G, questions G = true <-> Questions G.
  Proof.
    Admitted.

  (**  *** Inductive Definition for rules *)

  Reserved Notation " '|-' G " (at level 80).
  Inductive rules : list LForm -> Prop :=
  (* |- G, A, Negation A *)
  | rules_id : forall G A,
      G =mul= [A; negation A] ->
      |- G
  (* |- G, A -> |- D, Negation A -> |- G, D *)
  | rules_cut : forall G D A G_A D_neg_A G_D,
      G_A =mul= A :: G -> D_neg_A =mul= negation A :: D -> G_D =mul= G ++ D ->
      |- G_A ->
      |- D_neg_A ->
      |- G_D
  (* |- G, A -> |- D, B -> |- G, D, (Tensor A B) *)
  | rules_tensor : forall G_A D_B G_D_Tensor_A_B G D A B,
      G_A =mul= A :: G -> D_B =mul= B :: D -> G_D_Tensor_A_B =mul= (Tensor A B) :: G ++ D ->
      |- G_A ->
      |- D_B ->
      |- G_D_Tensor_A_B
  (* |- G, A, B -> |- G, Par A B *)
  | rules_par : forall G_A_B G_Par_A_B G A B,
      G_A_B =mul= A :: B :: G -> G_Par_A_B =mul= (Par A B) :: G ->
      |- G_A_B ->
      |- G_Par_A_B
  (* |- One *)
  | rules_one : forall G,
      G =mul= [One] ->
      |- G
  (*  |- G -> |- G, Bot *)
  | rules_bot : forall G G_bot,
      G_bot =mul= Bot :: G ->
      |- G ->
      |- G_bot
  (* |- G, Top *)
  | rules_top : forall G G_Top,
      G_Top =mul= Top :: G ->
      |- G_Top
  (* |- G, A -> |- G, Oplus A B *)
  | rules_oplus_1 : forall G_A G_Oplus_A_B G A B,
      G_A =mul= A :: G -> G_Oplus_A_B =mul= Oplus A B :: G ->
      |- G_A ->
      |- G_Oplus_A_B
  (* |- G, B -> |- G, Oplus A B *)
  | rules_oplus_2 : forall G_B G_Oplus_A_B G A B,
      G_B =mul= B :: G -> G_Oplus_A_B =mul= Oplus A B :: G ->
      |- G_B ->
      |- G_Oplus_A_B
  (* |- G, A -> |- G, B  -> |- G, With A B *)
  | rules_with : forall G_A G_B G_With_A_B G A B,
      G_A =mul= A :: G -> G_B =mul= B :: G -> G_With_A_B =mul= (With A B) :: G ->
      |- G_A ->
      |- G_B ->
      |- G_With_A_B
  (* |- G, A -> |- G, YNot A *)
  | rules_ynot_conv : forall G_A G_YNot_A G A,
      G_A =mul= A :: G -> G_YNot_A =mul= (YNot A) :: G ->
      |- G_A ->
      |- G_YNot_A
  (*  |- Questions G, A -> |- G, YNot A *)
  | rules_ofc : forall G_A G_Ofc_A G A,
      G_A =mul= A :: G -> G_Ofc_A =mul= Ofc A :: G ->
      Questions G ->
      |- G_A ->
      |- G_Ofc_A
  (*  |- G, YNot A, YNot A -> |- G, YNot A *)
  | rules_ynot_contract : forall G_YNot_A G_YNot_A_YNot_A G A,
      G_YNot_A =mul= (YNot A) :: G -> G_YNot_A_YNot_A =mul= (YNot A) :: (YNot A) :: G ->
      |- G_YNot_A_YNot_A ->
      |- G_YNot_A
  (*  |- G -> |- G, YNot A *)
  | rules_ynot_weak : forall G_YNot_A G A,
      G_YNot_A =mul= (YNot A) :: G ->
      |- G ->
      |- G_YNot_A
  where " '|-' G " := (rules G).

  (** *** Linear implication

    Also known as lollipop.

   *)

  Definition Impl (A B : LForm) : LForm := Par (negation A) B.

  (** * Examples

  - TBD: derivation examples + metatheorems

   *)

  (** ** Metatheorems
      - TBD: cut admissibility, identity expansion, exchange, etc.

   *)

  (** *** Exchange
      - TBD: proof
   *)

  Theorem exchange_admissibility :
    forall G D,
      G =mul= D ->
      |- G ->
      |- D.
  Proof.
    Admitted.

  (** ** Derivation examples *)

  (** *** Derivation 1:

      The written proof is from [https://www.cs.uoregon.edu/research/summerschool/summer25/_lectures/Kesner_Lesson1.pdf, slide 30].

      There are some mildly interesting things to note:

      - We need to [apply] the rules with explicit arguments - to know which formula and context(s) are being manipulated.
      - We use [eapply] because there are multiset conditions / preludes for the rules, which [auto] can handle. Often, [eapply] can figure out the formula being manipulated.
      - The order of the context can sometimes be rearranged just by applying these tactics.
      - [Questions A] is a proposition stating that all formulas in [A] are of the form [YNot _]. We switch to the fixpoint version [questions] via [questions_Questions], which can be simplified/evaluated.
      - The theorem is stated this way (without using any multiset condiitions). This means we will have [ax : |- A :: [negation A]], and we wouldn't be able to apply [ax] directly on [|- [negation A] :: A]. So this requires exchange admissibility.
      - Or you can use a statement with multiset conditions.
      - Negation is meta in that it is not part of the syntax. It is a fixpoint.  So when we use a rule like [rules_cut], which requires that the cut formulas on both subtrees are negations of each other, the negation does not come automatically evaluated. Hence we called [simpl] and [apply negation_involutive].

   *)

  Example A__not_Ynot_A__not_Ynot_C :
    forall A C,
      |- A :: [negation A] ->
      |- A :: (YNot (negation A)) :: [YNot (negation C)].
  Proof.
    intros A C ax.
    eapply rules_ynot_weak with (A := negation C). auto.
    eapply rules_ynot_contract with (G := [A]) (A := negation A);auto.
    eapply rules_cut with (A := Tensor (negation A) (Ofc A));auto.
    - eapply rules_tensor with (G := [A]) (D := [YNot (negation A)]) (A := negation A) (B := Ofc A);auto.
      eapply rules_ofc;auto.
      -- apply questions_Questions. reflexivity.
      -- eapply rules_ynot_conv;auto.
    - simpl. rewrite negation_involutive.
      eapply rules_par;auto.
      -- eapply rules_ynot_conv;auto. eapply rules_ynot_weak;auto.
         eapply exchange_admissibility. auto.
         apply ax.
  Qed.

End PL.
