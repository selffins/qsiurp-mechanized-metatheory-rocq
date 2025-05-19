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
    | And  : formula -> formula -> formula
    | Or   : formula -> formula -> formula
    | Impl : formula -> formula -> formula.

  End Formula.

  (** Inference rules *)
  Section InferenceRules.
    Definition ctx := list formula.

    Reserved Notation " A '|-' B " (at level 80).
    Inductive rules : ctx -> formula -> Prop :=
    | rules_id     : forall A, [A] |- A
    | rules_cut    : forall G D A B, G |- A -> D ++ [A] |- B -> G ++ D |- B
    | rules_w_l    : forall G D B, G |- B -> G ++ D |- B      (* Weakening : contexts level *)
    | rules_w_r    : forall G A, G |- Bot -> G |- A
    | rules_e_l    : forall G D C, G ++ D |- C -> D ++ G |- C (* Exchange : contexts level *)
    | rules_c_l    : forall G A B, G ++ A ++ A |- B -> G ++ A |- B (* Contract : contexts level *)
    | rules_neg_l  : forall G A, G |- A -> G ++ [Not A] |- Bot
    | rules_neg_r  : forall G A, G ++ [A] |- Bot -> G |- Not A
    | rules_and_l  : forall G A B C, G ++ [A] ++ [B] |- C -> G ++ [And A B] |- C
    | rules_and_r  : forall G A B, G |- A -> G |- B -> G |- And A B
    | rules_or_l   : forall G A B C, G ++ [A] |- C -> G ++ [B] |- C -> G ++ [Or A B] |- C
    | rules_or_r_1 : forall G A B, G |- A -> G |- Or A B
    | rules_or_r_2 : forall G A B, G |- B -> G |- Or A B
    | rules_impl_l : forall G D A B C, G |- A -> D ++ [B] |- C -> G ++ D ++ [Impl A B] |- C
    | rules_impl_r : forall G A B, G ++ [A] |- B -> G |- Impl A B
    where " A '|-' B " := (rules A B).

    Lemma cons_app_singleton : forall T (G : list T) a, a :: G = [a] ++ G.
      intros. reflexivity.
    Qed.

    Theorem init : forall G A, G ++ [A] |- A.
      intros.
      induction G as [| X G'].
      - simpl. apply rules_id.
      - rewrite cons_app_singleton. rewrite <- app_assoc.
        apply rules_e_l. apply rules_w_l. apply IHG'.
    Qed.

    Theorem shift : forall X Y Z C, X ++ Y ++ Z |- C -> Z ++ X ++ Y |- C.
    Proof.
      intros.
      rewrite app_assoc.
      apply rules_e_l.
      rewrite app_assoc.
      apply rules_e_l.
      apply H.
    Qed.

    Lemma w_ctx : forall G C, G |- C -> G ++ G |- C.
    Proof.
      intros.
      apply rules_w_l with (D := G) in H. apply H.
    Qed.

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

    (* Example proofs *)
    Example double_negation : forall A, [A] |- Not (Not A).
      intros.
      apply rules_neg_r.
      apply rules_neg_l.
      apply rules_id.
    Qed.

    Example non_contradiction : forall A, [] |- Not (And A (Not A)).
      intros.
      apply rules_neg_r.
      apply rules_and_l.
      apply rules_neg_l.
      apply rules_id.
    Qed.

    Example cut_base_1 : forall A D G, [A] |- A -> G ++ [A] |- D -> G ++ [A] |- D.
      intros.
      apply H0.
    Qed.

    Example cut_base_2 : forall A G, G |- A -> [A] |- A -> G |- A.
      intros.
      apply H.
    Qed.

    Example cut_and : forall G G' G'' A1 A2 D, G |- A1 -> G' |- A2 -> G'' ++ [A1] |- D -> G ++ G' ++ G'' |- D.
      intros.
      apply rules_cut with A1.
      - apply H.
      - rewrite <- app_assoc. apply rules_cut with A2.
        -- apply H0.
        -- apply rules_w_l. apply H1.
    Qed.

    Search "app_nil".

    Example invertibility_and_r :
      forall G A B,  G |- And A B -> ((G ++ [A] ++ [B] |- A) /\ (G ++ [A] ++ [B] |- B)).
      intros.
      split.
      - rewrite app_assoc. apply rules_w_l. apply init.
      - rewrite app_assoc. apply init.
    Qed.

    Example invertibility_or_l :
      forall G A B C, G ++ [Or A B] |- C -> G ++ [A] |- C /\ G ++ [B] |- C.
      intros.
      split.
      { apply ctx_nil_l.
        apply rules_c_l.
        simpl.
        apply rules_cut with (A := Or A B).
        -- apply rules_or_r_1. apply init.
        -- rewrite <- app_assoc. apply shift. apply shift. rewrite app_assoc.
           apply rules_w_l. apply rules_e_l. apply H. }
      { apply ctx_nil_l.
        apply rules_c_l.
        simpl.
        apply rules_cut with (A := Or A B).
        -- apply rules_or_r_2. apply init.
        -- rewrite <- app_assoc. apply shift. apply shift. rewrite app_assoc.
           apply rules_w_l. apply rules_e_l. apply H. }
    Qed.

    Example invertibility_impl_r :
      forall G A B, G |- Impl A B -> G ++ [A] |- B.
    Proof.
      intros.
      apply rules_c_l.
      apply ctx_nil_l.
      apply rules_c_l.
      simpl.
      apply rules_cut with (A := Impl A B).
      - apply rules_w_l. apply H.
      - rewrite cons_app_singleton.
        assert ((G ++ ([A] ++ [A])) ++ [Impl A B] = (G ++ [A]) ++ ([A] ++ [Impl A B])). {
          rewrite app_assoc.
          rewrite app_assoc.
          reflexivity.
        }
        rewrite H0.
        apply rules_impl_l; apply init.
    Qed.

  End InferenceRules.

End LJ_lists.
