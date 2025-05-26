From Stdlib Require Export Permutation.
From Stdlib Require Export List.
From OLlibs Require Import Permutation_solve. (* Olivier Laurent on Github *)
Export List.ListNotations.
Set Implicit Arguments.
Set Printing Parentheses.


(* LL lists. Girard one-sided system *)
Module LL_lists.

  (** Atomic propositions *)
  Section Formula.
  Definition var := nat.

  (** Formulas *)

    Inductive formula :=
    | PosA   : var -> formula
    | NegA   : var -> formula
    | Zero   : formula
    | One    : formula
    | Bot    : formula
    | Top    : formula
    | Tensor : formula -> formula -> formula
    | With   : formula -> formula -> formula
    | OPlus  : formula -> formula -> formula
    | Par    : formula -> formula -> formula
    | Ofc    : formula -> formula
    | YNot   : formula -> formula.

    Fixpoint negation (A : formula) : formula :=
      match A with
      | PosA v => NegA v
      | NegA v => PosA v
      | Ofc A => YNot (negation A)
      | YNot A => Ofc (negation A)
      | Tensor A B => Par (negation A) (negation B)
      | Par A B => Tensor (negation A) (negation B)
      | OPlus A B => With (negation A) (negation B)
      | With A B => OPlus (negation A) (negation B)
      | One => Bot
      | Bot => One
      | Zero => Top
      | Top => Zero
      end.

  End Formula.

  (** Inference rules *)
  Section InferenceRules.
    Definition ctx := list formula.

    Lemma cons_app_singleton : forall T (G : list T) a, a :: G = [a] ++ G.
      intros. reflexivity.
    Qed.

    Definition is_YNot (A : formula) : Prop :=
      match A with
      | YNot _ => True
      | _ => False
      end.

    Definition Questions (G : ctx) := forall A, In A G -> is_YNot A.

    Reserved Notation " '|-' A " (at level 80).
    Inductive rules : ctx -> Prop :=
    | rules_id : forall A, |- [negation A] ++ [A]
    | rules_cut : forall G D A, |- G ++ [A] -> |- D ++ [negation A] -> |- G ++ D
    | rules_exchange : forall G D, Permutation G D -> |- G -> |- D
    | rules_tensor : forall G D A B, |- G ++ [A] -> |- D ++ [B] -> |- G ++ D ++ [Tensor A B]
    | rules_par : forall G A B, |- G ++ [A] ++ [B] -> |- G ++ [Par A B]
    | rules_one : |- [One]
    | rules_bot : forall G, |- G -> |- G ++ [Bot]
    | rules_top : forall G, |- G ++ [Top]
    | rules_oplus_1 : forall G A B, |- G ++ [A] -> |- G ++ [OPlus A B]
    | rules_oplus_2 : forall G A B, |- G ++ [B] -> |- G ++ [OPlus A B]
    | rules_with : forall G A B, |- G ++ [A] -> |- G ++ [B] -> |- G ++ [With A B]
    | rules_ynot_conv : forall G A, |- G ++ [A] -> |- G ++ [YNot A]
    | rules_ofc : forall G A, Questions G -> |- G ++ [A] -> |- G ++ [Ofc A]
    | rules_ynot_contract : forall G A, |- G ++ [YNot A] ++ [YNot A] -> |- G ++ [YNot A]
    | rules_ynot_weak : forall G A, |- G -> |- G ++ [YNot A]
    where " '|-' A " := (rules A).

    Definition Impl (A B : formula) : formula := Par (negation A) (B).

    Lemma ctx_nil_r : forall G, |- G <-> |- G ++ [].
    Proof.
      intros. split;intro.
      - rewrite app_nil_r. apply H.
      - rewrite app_nil_r in H. apply H.
    Qed.

    Lemma ctx_nil_l : forall G, |- G <-> |- [] ++ G.
    Proof.
      intros.
      split;intro;apply H.
    Qed.

    Example exchange_123_312: |- [PosA 1; PosA 2; PosA 3] -> |- [PosA 3 ; PosA 1 ; PosA 2].
    Proof.
      intros.
      apply rules_exchange with [PosA 1 ; PosA 2 ; PosA 3].
      - apply Permutation_sym.
        apply perm_trans with [PosA 1 ; PosA 3 ; PosA 2].
        -- apply perm_swap.
        -- apply perm_skip.
           apply perm_swap.
      - apply H.
    Qed.

    Example exchange_123_213: |- (PosA 1) :: ([PosA 2] ++ [PosA 3]) -> |- [PosA 3] ++ ((PosA 1) :: [PosA 2]).
    Proof.
      intros.
      apply rules_exchange with [PosA 1 ; PosA 2 ; PosA 3].
      - apply Permutation_sym.
        apply perm_trans with [PosA 1 ; PosA 3 ; PosA 2].
        -- apply perm_swap.
        -- apply perm_skip.
           apply perm_swap.
      - apply H.
    Qed.

    Example exchange_123_213_solver: |- (PosA 1) :: ([PosA 2] ++ [PosA 3]) -> |- [PosA 3] ++ ((PosA 1) :: [PosA 2]).
    Proof.
      intros.
      apply rules_exchange with [PosA 1 ; PosA 2 ; PosA 3].
      - Permutation_solve.
      - apply H.
    Qed.

    Example exchange_ABC_BAC_solver: forall A B C, |- A ++ B ++ C -> |- B ++ A ++ C.
    Proof.
      intros.
      apply rules_exchange with (A ++ B ++ C).
      - Permutation_solve.
      - apply H.
    Qed.

    Example impl_example : forall A B, |- [negation A ; B] -> |- [Impl A B].
    Proof.
      - unfold Impl. intros.
        apply ctx_nil_l.
        apply rules_par.
        simpl.
        rewrite cons_app_singleton.
        apply rules_cut with A.
        -- apply rules_id.
        -- apply rules_exchange with [negation A ; B]. apply perm_swap.
           apply H.
    Qed.

    Example tensor_example :
      forall A B,  |- [negation A ; negation B ; Tensor A B].
    Proof.
      intros.
      change ((negation A) :: [negation B ; Tensor A B]) with ([negation A] ++ [negation B] ++ [Tensor A B]).
      apply rules_tensor;
      apply rules_id.
    Qed.

    (* | rules_par : forall G A B, |- G ++ [A] ++ [B] -> |- G ++ [Par A B] *)
    Example par_example :
      forall A B, |- [negation A; OPlus A B].
    Proof.
      intros.
      rewrite cons_app_singleton.
      apply rules_oplus_1.
      apply rules_id.
    Qed.

    (* | rules_ofc : forall G A, Questions G -> |- G ++ [A] -> |- G ++ [Ofc A] *)
    Example ofc_example : forall A, Questions [YNot A] -> |- [YNot A] ++ [A] -> |- [YNot A] ++ [Ofc A].
    Proof.
      intros.
      apply rules_ofc.
      apply H.
      apply H0.
    Qed.

   Example negation_tensor : negation (negation (Tensor (PosA 0) (PosA 1))) = Tensor (PosA 0) (PosA 1).
   Proof.
     reflexivity.
   Qed.

   Theorem negation_involutive : forall A, negation (negation A) = A.
   Proof.
     intros.
     induction A.
     - reflexivity.
     - reflexivity.
     - reflexivity.
     - reflexivity.
     - reflexivity.
     - reflexivity.
     - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
     - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
     - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
     - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
     - simpl. rewrite IHA. reflexivity.
     - simpl. rewrite IHA. reflexivity.
   Qed.

  End InferenceRules.

End LL_lists.
