From Stdlib Require Export Sets.Multiset.
From Stdlib Require Export List.
Export ListNotations.

Module lists_abella.

(** TODO: olist is a list of "o's" *)

Definition o := nat.

Inductive append : list o -> list o -> list o -> Prop :=
  | append_nil (L : list o): append [] L L
  | append_cons e J K L: append (e :: J) K (e :: L).

Inductive rev : list o -> list o -> Prop :=
| rev_nil : rev [] []
| rev_cons e J L (H : exists K, rev J K /\ append K (e :: []) L ) : rev J L.


End lists_abella.
