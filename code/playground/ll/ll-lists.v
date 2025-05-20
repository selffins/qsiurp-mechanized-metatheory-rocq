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





  End InferenceRules.

End LL_lists.
