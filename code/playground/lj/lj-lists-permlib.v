From Stdlib Require Export Permutation.
From OLlibs Require Import Permutation_solve. (* Olivier Laurent on Github *)
From Stdlib Require Export List.
Export List.ListNotations.
Set Implicit Arguments.
Set Printing Parentheses.

(* LJ lists with permutation from coq library *)
Module LJ_lists_permlib.

  (** Atomic propositions *)
  Section Var.

    Parameter var: Set.

  End Var.

  (** Formulas *)
  Section Formula.

    Inductive formula :=
    | Bot : formula
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
    | rules_bot_l : forall G_Bot G C, Permutation G_Bot (Bot :: G) -> G_Bot |- C
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

    (* Some metatheorems *)
    Theorem Init : forall G_Atom_A G A, Permutation G_Atom_A ((Atom A) :: G) -> G_Atom_A |- Atom A.
      intros. generalize dependent G_Atom_A.
      induction G as [| X G'];intros;subst.
      - apply rules_id. auto.
      - eapply rules_w_l with (A := X) (G := (Atom A) :: G'). Permutation_solve.
        eapply IHG'. auto.
    Qed.

    Theorem Identity : forall GG G A, Permutation GG (A :: G) -> GG |- A.
    Proof.
      intros. generalize dependent GG. generalize G.
      induction A;intros;subst.
      (* Bot *)
      - apply rules_bot_l with (G := G0). apply H.
      (* Atom *)
      - eapply Init. apply H.
      (* Not / Neg *)
      - apply rules_neg_r with (G_A := A :: GG). auto.
        apply rules_neg_l with (G := A :: G0) (G_not_A := A :: GG) (A := A). Permutation_solve. (* wow :D *)
        apply IHA with (G := G0). auto.
      (* Conj *)
      - apply rules_conj_l with (G_A_B := A1 :: A2 :: G0) (G := G0) (A := A1) (B := A2). auto. apply H.
        apply rules_conj_r.
        -- apply IHA1 with (G := A2 :: G0) (GG := A1 :: A2 :: G0). Permutation_solve.
        -- apply IHA2 with (G := A1 :: G0) (GG := A1 :: A2 :: G0). Permutation_solve.
      (* Disj *)
      - apply rules_disj_l with (G_A := A1 :: G0) (G_B := A2 :: G0) (G := G0) (A := A1) (B := A2). auto. auto. auto.
        -- apply rules_disj_r_1. apply IHA1 with (G := G0). auto.
        -- apply rules_disj_r_2. apply IHA2 with (G := G0). auto.
      (* Impl *)
      - apply rules_impl_r with (G_A := A1 ::GG). auto.
        apply rules_impl_l with (D := nil) (D_B := A2 :: nil) (G_D_impl_A_B := A1 :: GG) (G := A1 :: G0) (A := A1) (B := A2) (C := A2).
        auto. Permutation_solve.
        -- apply IHA1 with (G := G0). auto.
        -- apply IHA2 with (G := []). auto.
    Qed.

    Theorem Exchange : forall G D C, Permutation G D -> G |- C -> D |- C.
    Proof.
      intros. generalize dependent D.
      induction H0;intros;subst.
      (* rules_id / Atom*)
      - apply Permutation_sym in H. apply Permutation_length_1_inv in H.
        rewrite H in H0. apply Permutation_length_1_inv in H0.
        rewrite H0. apply rules_id. auto.
      (* rules_cut *)
      Admitted.


  End InferenceRules.

End LJ_lists_permlib.
