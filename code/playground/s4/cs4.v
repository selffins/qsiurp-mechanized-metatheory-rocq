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

  End InferenceRules.

End CS4_lists.
