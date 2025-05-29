From Stdlib Require Export Permutation.
From OLlibs Require Import Permutation_solve. (* Olivier Laurent on Github *)
From Stdlib Require Export List.
Export List.ListNotations.
Set Implicit Arguments.
Set Printing Parentheses.

(* LJ lists *)
Module LJ_lists.

  (** Atomic propositions *)
  Section Var.

    Parameter var: Set.

  End Var.

  (** Formulas *)
  Section Formula.

    Inductive formula :=
    | Bot  : formula
    | Atom : var -> formula
    | Not  : formula -> formula
    | Conj  : formula -> formula -> formula
    | Disj   : formula -> formula -> formula
    | Impl : formula -> formula -> formula.

  End Formula.

  (** Inference rules *)
  Section InferenceRules.
    Definition ctx := list formula.

    Reserved Notation " A '|-' B " (at level 80).
    Inductive rules : ctx -> formula -> Prop :=
    | rules_id     : forall G_A A,
                         Permutation G_A [Atom A] ->
                         G_A |- Atom A
    | rules_cut    : forall G D_A D A B,
                         Permutation D_A (A :: D) ->
                         G |- A ->
                         D_A |- B ->
                         G ++ D |- B
    | rules_w_l    : forall G_A G A B,
                         Permutation G_A (A :: G) ->
                         G |- B ->
                         G_A |- B
    | rules_w_r    : forall G A,
                         G |- Bot ->
                         G |- A
    | rules_c_l    : forall G_A_A G_A G A B,
                         Permutation G_A_A (A :: A :: G) -> Permutation G_A (A :: G) ->
                         G_A_A |- B ->
                         G_A |- B
    | rules_neg_l  : forall G_not_A G A,
                         Permutation G_not_A (Not A :: G) ->
                         G |- A ->
                         G_not_A |- Bot
    | rules_neg_r  : forall G_A G A,
                         Permutation G_A (A :: G) ->
                         G_A |- Bot ->
                         G |- Not A
    | rules_conj_l  : forall G_A_B G_conj_A_B G A B C,
                         Permutation G_A_B (A :: B :: G) -> Permutation G_conj_A_B ((Conj A B) :: G) ->
                         G_A_B |- C ->
                         G_conj_A_B |- C
    | rules_conj_r  : forall G A B,
                         G |- A ->
                         G |- B ->
                         G |- Conj A B
    | rules_disj_l   : forall G_A G_B G_disj_A_B G A B C,
                         Permutation G_A (A :: G) -> Permutation G_B (B :: G) -> Permutation G_disj_A_B ((Disj A B) :: G) ->
                         G_A |- C ->
                         G_B |- C ->
                         G_disj_A_B |- C
    | rules_disj_r_1 : forall G A B,
                         G |- A ->
                         G |- Disj A B
    | rules_disj_r_2 : forall G A B,
                         G |- B ->
                         G |- Disj A B
    | rules_impl_l : forall D_B G_D_impl_A_B G D A B C,
                         Permutation D_B (B :: D) -> Permutation G_D_impl_A_B ((Impl A B) :: G ++ D) ->
                         G |- A ->
                         D_B |- C ->
                         G_D_impl_A_B |- C
    | rules_impl_r : forall G_A G A B,
                         Permutation G_A (A :: G) ->
                         G_A |- B ->
                         G |- Impl A B
    where " A '|-' B " := (rules A B).

    Theorem init : forall G A, (Atom A) :: G |- Atom A.
      intros.
      induction G as [| X G'].
      - apply rules_id. auto.
      - eapply rules_w_l with (A := X) (G := (Atom A) :: G').
        -- Permutation_solve.
        -- apply IHG'.
    Qed.

    Lemma w_ctx : forall G G_copy C, Permutation G G_copy -> G |- C -> G ++ G_copy |- C.
    Proof.
      intros. generalize dependent G_copy.
      induction G as [| X G'];intros;subst.
      - apply Permutation_nil in H. subst. auto.
      - Admitted.

    (* Example proofs *)
    Example double_negation : forall A, [Atom A] |- Not (Not (Atom A)).
      intros.
      apply rules_neg_r with (G_A := [Atom A; Not (Atom A)]).
      - Permutation_solve.
      - apply rules_neg_l with (G := [Atom A]) (A := (Atom A)).
        -- Permutation_solve.
        -- apply rules_id. auto.
    Qed.

    Example non_contradiction : forall A, [] |- Not (Conj (Atom A) (Not (Atom A))).
      intros.
      apply rules_neg_r with (G_A := [Conj (Atom A) (Not (Atom A))]). auto.
      apply rules_conj_l with (G_A_B := [Atom A ; Not (Atom A)]) (G := []) (A := Atom A) (B := Not (Atom A)).
      Permutation_solve. Permutation_solve.
      apply rules_neg_l with (G := [Atom A]) (A := Atom A).
      Permutation_solve. apply rules_id. Permutation_solve.
    Qed.

    Example cut_base_1 : forall A D G, [A] |- A -> G ++ [A] |- D -> G ++ [A] |- D.
      intros.
      apply H0.
    Qed.

    Example cut_base_2 : forall A G, G |- A -> [A] |- A -> G |- A.
      intros.
      apply H.
    Qed.

    Example cut_and : forall G G' G'' A1 A2 C, G |- A1 -> G' |- A2 -> G'' ++ [A1] |- C -> G ++ G' ++ G'' |- C.
      intros. Admitted.

  End InferenceRules.

End LJ_lists_permlib.
