(* NOTE:  This file was taken from the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL. *)

(* Add LoadPath "../" . *)
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

  Definition is_YNot (A : LForm) : Prop :=
      match A with
      | YNot _ => True
      | _ => False
      end.

  Definition Questions (G : list LForm) := forall A, In A G -> is_YNot A.

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

  Definition Impl (A B : LForm) : LForm := Par (negation A) B.

  Theorem negation_involutive : forall A, negation (negation A) = A.
  Proof.
    intros.
    induction A;auto;
      (repeat(simpl; rewrite IHA1; rewrite IHA2; auto));
      (repeat simpl; rewrite IHA;auto).
  Qed.

End PL.
