(** * Atomic Propositions
Atomic propositions (no connectives), e.g. [A], are represented by the type [var].

 *)

Set Implicit Arguments.

(** ** Type for atomic propositions *)

Parameter var: Set.

(** * Formulas

Formulas in LJ are built from the following syntax:

F := Atom
   | ~ F
   | F /\ F
   | F \/ F
   | F -> F

*)

Inductive formula :=
  | Atom : var -> formula
  | Neg  : formula -> formula
  | And  : formula -> formula -> formula
  | Or   : formula -> formula -> formula
  | Impl : formula -> formula -> formula.

Notation "~ A" := (Neg A).
Notation "A /\ B" := (And A B).
Notation "A \/ B" := (Or A B).
Notation "A -> B" := (Impl A B).

(** * Inference Rules

   Not sure yet. We have to deal with the main thing: context representations. In the paper, they do multisets.
   So, [rules_id] might be written like [forall ctx form, ctx =mul= [form] -> ctx |-- form].

The following is clearly incomplete.

 *)

Reserved Notation "G '|--' F" (at level 80).

Inductive rules : list formula -> formula -> Prop :=
  | rules_id : forall G F,  [F] |-- F.
