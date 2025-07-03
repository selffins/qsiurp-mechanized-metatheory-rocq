From Stdlib Require Export Permutation.
From Stdlib Require Export List.
From OLlibs Require Import Permutation_solve. (* by Olivier Laurent on Github *)
Export List.ListNotations.
Set Implicit Arguments.
Set Printing Parentheses.

(** * Onesided MLL

  - Multiplicative linear logic, unilateral sequent presentation
  - Explicit exchange
  - Contexts are lists
  - From Kesner OPLSS '25
  - The duality between par and tens makes it clear that a unilateral sequent presentation is simpler: we simply take anything from the left hand side of the and move it to the right hand side and negate it. See: [twosided-mll-lists.v]

 *)

Module Onesided_MLL_lists.

  (** * Syntax
      Formulas and negation
   *)

  Section Formula.

    Definition var := nat.

    Inductive formula :=
    | PosA   : var -> formula
    | NegA   : var -> formula
    | Tensor : formula -> formula -> formula
    | Par    : formula -> formula -> formula.

    Fixpoint negation (A : formula) : formula :=
      match A with
      | PosA v => NegA v
      | NegA v => PosA v
      | Tensor A B => Par (negation A) (negation B)
      | Par A B => Tensor (negation A) (negation B)
      end.

    Theorem negation_involutive :
      forall A, negation (negation A) = A.
    Proof.
      intros.
      induction A.
      -  reflexivity.
      - reflexivity.
      - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
      - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
    Qed.

    Definition ctx := list formula.

  End Formula.

  (** * Inference rules *)

  Section Rules.

    Reserved Notation " '|-' D " (at level 80).
    Inductive onesided_mll : ctx -> Prop :=
    | rules_ax : forall A, |- [negation A] ++ [A]
    | rules_cut : forall G D A,
        |- G ++ [A] ->
        |- D ++ [negation A] ->
        |- G ++ D
    | rules_perm : forall G D A B,
        |- G ++ [A] ++ [B] ++ D ->
        |- G ++ [B] ++ [A] ++ D
    | rules_par : forall G A B,
        |- G ++ [A] ++ [B] ->
        |- G ++ [Par A B]
    | rules_tensor : forall G D A B,
        |- G ++ [A] ->
        |- D ++ [B] ->
        |- G ++ D ++ [Tensor A B]
    where " '|-' D " := (onesided_mll D).

  End Rules.

  Section Examples.

    (** * Examples *)

    (** *** Derivation 1

      Here we use explicit exchange and properties of append in order to manipulate the contexts
      into fitting the proper shape needed by the inference rules.

     *)

    Example a1_par_a2_a3_par_a4_1 : forall A1 A2 A3 A4,
        onesided_mll [A1 ; A2 ; A3 ; A4] -> onesided_mll [Par A1 A2; Par A3 A4].
    Proof.
      intros A1 A2 A3 A4.
      intros.
      (** rewriting in order to apply rules_par the first time*)
      replace [Par A1 A2; Par A3 A4] with ([Par A1 A2] ++ [Par A3 A4]).
      2 : reflexivity.
      apply rules_par.
      (** rewriting in order to apply rules_par the second time*)
      rewrite <- app_nil_l.
      apply rules_perm.
      rewrite app_nil_l.
      rewrite <- app_nil_r.
      rewrite <- app_assoc.
      apply rules_perm.
      rewrite app_nil_r.
      rewrite app_assoc.
      apply rules_par.
      (** rewriting in order to get |- [A3; A4; A1; A2] into |- [A1; A2; A3; A4] *)
      rewrite <- app_assoc.
      apply rules_perm with (A := A1).
      rewrite <- app_nil_l.
      apply rules_perm with (A := A1).
      rewrite app_nil_l.
      rewrite app_assoc.
      rewrite <- app_nil_r.
      rewrite <- app_assoc.
      apply rules_perm with (A := A2).
      rewrite app_nil_r.
      rewrite <- app_assoc.
      apply rules_perm with (A := A2).
      simpl.
      apply H.
    Qed.

  End Examples.

End Onesided_MLL_lists.
