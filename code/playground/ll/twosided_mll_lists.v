From Stdlib Require Export Permutation.
From Stdlib Require Export List.
From OLlibs Require Import Permutation_solve. (* by Olivier Laurent on Github *)
Export List.ListNotations.
Set Implicit Arguments.
Set Printing Parentheses.

(** * Twosided MLL

  - Multiplicative linear logic, twosided sequent presentation
  - Explicit exchange
  - Contexts are lists
  - The duality between par and tens makes it clear that a unilateral sequent presentation is simpler: we simply take anything from the left hand side of the and move it to the right   hand side and negate it. See: [onesided-mll-lists.v].
  - Following Kesner's presentation from OPLSS '25.

 *)

Module Twosided_MLL_lists.

  (** * Syntax *)

  Section Formula.
    Definition var := nat.

    Inductive formula :=
    | PosA   : var -> formula
    | NegA   : var -> formula
    | Tensor : formula -> formula -> formula
    | Par    : formula -> formula -> formula.

    (** ** Negation

       Note that negation is a fixpoint and not syntactic.

     *)

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
  End Formula.

  (** * Inference rules *)

  Section Rules.
    Definition ctx := list formula.

    Reserved Notation " G '|-' D " (at level 80).
    Inductive dyadic_mll : ctx -> ctx -> Prop :=
    | rules_ax : forall A, [A] |- [A]
    | rules_cut : forall G G' D D' A,
        G |- D ++ [A] ->
        G' ++ [A] |- D' ->
        G ++ G' |- D ++ D'
    | rules_perm_l : forall G G' D A B,
        G ++ [A] ++ [B] ++ G' |- D ->
        G ++ [B] ++ [A] ++ G' |- D
    | rules_perm_r : forall G D D' A B,
        G |- D ++ [A] ++ [B] ++ D' ->
        G |- D ++ [B] ++ [A] ++ D'
    | rules_par_l : forall G G' D D' A B,
        G ++ [A] |- D ->
        G' ++ [B] |- D' ->
        G ++ G' ++ [Par A B] |- D ++ D'
    | rules_par_r : forall G A B D D',
        G |- [A] ++ [B] ++ D' ->
        G |- [Par A B] ++ D
    | rules_tens_l : forall G A B D,
        G ++ [A] ++ [B] |- D ->
        G ++ [Tensor A B] |- D
    | rules_tens_r : forall G G' D D' A B,
        G |- D ++ [A] -> G' |- D' ++ [B] ->
        G ++ G' |- [Tensor A B] ++ D ++ D'
    where " G '|-' D " := (dyadic_mll G D).
  End Rules.

  (** * Examples

      - TODO: example derivations and metatheorem proofs

   *)

  Section Examples.

  End Examples.

End Twosided_MLL_lists.
