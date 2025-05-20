From Stdlib Require Export List.
Export List.ListNotations.
Set Implicit Arguments.
Set Printing Parentheses.

(* CS4 with lists *)
Module CS4_lists.

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
    | Box  : formula -> formula
    | Diamond : formula -> formula
    | And  : formula -> formula -> formula
    | Or   : formula -> formula -> formula
    | Impl : formula -> formula -> formula.

  End Formula.

  (** Inference rules *)
  Section InferenceRules.

    Definition ctx := list formula.

    Definition isBox (A : formula) : Prop :=
      match A with
      | Box _ => True
      | _ => False
      end.

    Definition Boxes (G : ctx) :=
      forall A, In A G -> isBox A.

    Reserved Notation " A '|-' B " (at level 80).
    Inductive rules : ctx -> formula -> Prop :=
    | rules_id : forall G A, G ++ [A] |- A
    | rules_cut : forall G D A B, G |- A -> D ++ [A] |- B -> G ++ D |- B
    | rules_bot_l : forall G A, G ++ [Bot] |- A
    | rules_or_l : forall G A B C, G ++ [A] |- C -> G ++ [B] |- C -> G ++ [Or A B] |- C
    | rules_or_r_1 : forall G A B, G |- A -> G |- Or A B
    | rules_or_r_2 : forall G A B, G |- B -> G |- Or A B
    | rules_impl_l : forall G A B C, G |- A -> G ++ [B] |- C -> G ++ [Impl A B] |- C
    | rules_impl_r : forall G A B, G ++ [A] |- B -> G |- Impl A B
    | rules_box_l : forall G A B, G ++ [A] |- B -> G ++ [Box A] |- B
    | rules_box_r : forall G A D, Boxes G -> G |- A -> G ++ D |- Box A
    | rules_diamond_l : forall G D A B, Boxes G -> G ++ [A] |- Diamond B -> D ++ G ++ [Diamond A] |- Diamond B
    | rules_diamond_r : forall G A, G |- A -> G |- Diamond A
    where " A '|-' B " := (rules A B).

    Lemma ctx_nil_r : forall G C, G |- C <-> G ++ [] |- C.
    Proof.
      intros. split;intro.
      - rewrite app_nil_r. apply H.
      - rewrite app_nil_r in H. apply H.
    Qed.

    Lemma ctx_nil_l : forall G C, G |- C <-> [] ++ G |- C.
    Proof.
      intros.
      split;intro;apply H.
    Qed.

    (** Examples *)
    (** This example is due to Bierman, de Paiva (2000) *)
    Example cut_boxes : forall G D A B, (Boxes G) -> (G |- A) -> D ++ [A] |- B -> G ++ D |- B.
    Proof.
      intros.
      apply rules_cut with (A := Box A).
      - apply ctx_nil_r. apply rules_box_r.
        -- apply H.
        -- apply H0.
      - apply rules_box_l. apply H1.
    Qed.

    Example cut_boxes_smaller :
      forall G D A B, (Boxes G) -> (G |- A) -> D ++ [A] |- B -> G ++ D |- B.
    Proof.
      intros.
      apply rules_cut with (A := A).
      - apply H0.
      - apply H1.
    Qed.

    Example cut_diamonds :
      forall G D A B, Boxes D -> G |- A -> D ++ [A] |- Diamond B -> G ++ D |- Diamond B.
    Proof.
      intros.
      apply rules_cut with (A := Diamond A).
      - apply rules_diamond_r. apply H0.
      - apply ctx_nil_l. apply rules_diamond_l.
        -- apply H.
        -- apply H1.
    Qed.

    Example cut_diamonds_smaller:
      forall G D A B, Boxes D -> G |- A -> D ++ [A] |- Diamond B -> G ++ D |- Diamond B.
    Proof.
      intros.
      apply rules_cut with (A := A).
      - apply H0.
      - apply H1.
    Qed.


  End InferenceRules.


End CS4_lists.
