From Stdlib Require Export Permutation.
From Stdlib Require Export List.
From OLlibs Require Import Permutation_solve. (* by Olivier Laurent on Github *)
Export List.ListNotations.
Set Implicit Arguments.
Set Printing Parentheses.

(** * Onesided MELL

  - Multiplicative exponential linear logic, unilateral sequent presentation
  - MELL is MLL with exponentials, or LL without additive connectives (oplus and and).
  - Explicit exchange
  - Contexts are lists
  - Inspired from Kesner OPLSS '25
  - The duality between par and tens makes it clear that a unilateral sequent presentation is simpler: we simply take anything from the left hand side of the and move it to the right hand side and negate it. See: [twosided-mell-lists.v]

 *)

Module Onesided_MELL_lists.

  (** * Syntax
      Formulas and negation
   *)

  Section Formula.

    Definition var := nat.

    Inductive formula :=
    | PosA   : var -> formula
    | NegA   : var -> formula
    | Tensor : formula -> formula -> formula
    | Par    : formula -> formula -> formula
    | YNot   : formula -> formula
    | Ofc    : formula -> formula.

    Fixpoint negation (A : formula) : formula :=
      match A with
      | PosA v => NegA v
      | NegA v => PosA v
      | Tensor A B => Par (negation A) (negation B)
      | Par A B => Tensor (negation A) (negation B)
      | YNot A => Ofc (negation A)
      | Ofc A => YNot (negation A)
      end.

    Theorem negation_involutive :
      forall A, negation (negation A) = A.
    Proof.
      intros.
      induction A.
      - reflexivity.
      - reflexivity.
      - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
      - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
      - simpl. rewrite IHA. reflexivity.
      - simpl. rewrite IHA. reflexivity.
    Qed.

    (** *** Questions

        Some rules require that the context contains only [YNot] formulas.
        TBD: equivalence proof between the proposition form and the fixpoint boolean form.

     *)

  Definition is_YNot (A : formula) : Prop :=
    match A with
    | YNot _ => True
    | _ => False
    end.

  Definition Questions (G : list formula) := forall A, In A G -> is_YNot A.

  Fixpoint questions (G : list formula) : bool :=
    match G with
    | nil => true
    | cons A G' => match A with
                   | YNot _ => questions G'
                   | _ => false
                   end
    end.

  Lemma questions_Questions :
    forall G, questions G = true <-> Questions G.
  Proof.
    Admitted.

  Lemma Questions_cons_inv :
    forall a G, Questions (a :: G) -> (exists b, a = YNot b).
  Proof.
    Admitted.

  Lemma Questions_rest :
    forall a G, Questions (a :: G) -> Questions G.
  Proof.
    Admitted.

  Lemma Questions_app :
    forall G D, Questions G -> Questions D -> Questions (G ++ D).
  Proof.
    Admitted.

  Lemma Questions_perm :
    forall G D, Permutation G D -> Questions G -> Questions D.
  Proof.
    Admitted.

  (** * Context representation *)

    Definition ctx := list formula.

  End Formula.

  (** * Inference rules *)

  Section Rules.

    Reserved Notation " '|-' D " (at level 80).
    Inductive onesided_mell : ctx -> Prop :=
    | rules_ax : forall A,
        |- [negation A] ++ [A]
    | rules_cut : forall G D A,
        |- G ++ [A] ->
        |- D ++ [negation A] ->
        |- G ++ D
    | rules_perm : forall G D A B,
        |- G ++ [A] ++ [B] ++ D ->
        |- G ++ [B] ++ [A] ++ D
    | rules_par : forall G A B,
        |- G ++ [A] ++ [B] ->
        |- G ++ [Par A B]
    | rules_tensor : forall G D A B,
        |- G ++ [A] ->
        |- D ++ [B] ->
        |- G ++ D ++ [Tensor A B]
    | rules_weak : forall G A,
        |- G ->
        |- G ++ [YNot A]
    | rules_cont : forall G A,
        |- G ++ [YNot A] ++ [YNot A] ->
        |- G ++ [YNot A]
    | rules_ynot : forall G A,
        |- G ++ [A] ->
        |- G ++ [YNot A]
    | rules_ofc : forall q_G A,
        Questions q_G ->
        |- q_G ++ [A] ->
        |- q_G ++ [Ofc A]
    where " '|-' D " := (onesided_mell D).

  End Rules.

  Section Examples.

    Notation " '|-' D " := (onesided_mell D) (at level 80).
    (** * Examples *)

    (** *** Derivation 1

      Here we use explicit exchange and properties of append in order to manipulate the contexts into fitting the proper shape needed by the inference rules.

      This proof was from [onesided_mll_lists.v]. It works without any modification because MLL is a fragment of MELL.

     *)

    Example a1_par_a2_a3_par_a4_1 : forall A1 A2 A3 A4,
        |- [A1 ; A2 ; A3 ; A4] -> |- [Par A1 A2; Par A3 A4].
    Proof.
      intros A1 A2 A3 A4.
      intros.
      (** rewriting in order to apply rules_par the first time*)
      replace [Par A1 A2; Par A3 A4] with ([Par A1 A2] ++ [Par A3 A4]).
      2 : reflexivity.
      apply rules_par.
      (** rewriting in order to apply rules_par the second time*)
      rewrite <- app_nil_l.
      apply rules_perm.
      rewrite app_nil_l.
      rewrite <- app_nil_r.
      rewrite <- app_assoc.
      apply rules_perm.
      rewrite app_nil_r.
      rewrite app_assoc.
      apply rules_par.
      (** rewriting in order to get |- [A3; A4; A1; A2] into |- [A1; A2; A3; A4] *)
      rewrite <- app_assoc.
      apply rules_perm with (A := A1).
      rewrite <- app_nil_l.
      apply rules_perm with (A := A1).
      rewrite app_nil_l.
      rewrite app_assoc.
      rewrite <- app_nil_r.
      rewrite <- app_assoc.
      apply rules_perm with (A := A2).
      rewrite app_nil_r.
      rewrite <- app_assoc.
      apply rules_perm with (A := A2).
      simpl.
      apply H.
    Qed.

    (** * Exchange
        I'm not sure if I'm gonna prove exchange admissibility for now.
     *)
    Theorem Exchange :
      forall G D,
      Permutation G D ->
      |- G ->
      |- D.
    Proof.
      intros.
      induction H0;subst.
      - inversion H;subst.
        -- apply Permutation_length_1_inv in H3;subst. apply rules_ax.
        -- replace A with (negation (negation A)).
           replace (negation (negation (negation A))) with (negation A).
           --- apply rules_ax.
           --- rewrite negation_involutive. reflexivity.
           --- rewrite negation_involutive. reflexivity.
        --  simpl in H. simpl in H0.
      Admitted.

    (** * Context-level contraction *)

    Theorem Contract :
      forall G q_D,
        Questions q_D ->
        |- G ++ q_D ++ q_D ->
        |- G ++ q_D.
    Proof.
      intros.
      Admitted.


    (** * Context-level weakening *)

    Theorem Weak :
      forall G q_D,
        Questions q_D ->
        |- G ->
        |- G ++ q_D.
    Proof.
      intros.
      induction q_D.
      - rewrite app_nil_r. apply H0.
      - apply Exchange with (G := [a] ++ G ++ q_D).
        Permutation_solve. apply Questions_cons_inv in H as H1. destruct H1;subst.
        apply Exchange with (G := (G ++ q_D) ++ [YNot x]).
        Permutation_solve.
        apply rules_weak.
        apply IHq_D.
        apply Questions_rest in H.
        apply H.
    Qed.

    (** * Cut elimination *)

    (** ** Multiplicative cut elimination rules *)

    Lemma cut_ax_1 : forall G A,
        |- G ++ [A] ->
        |- [A] ++ [negation A] ->
        |- G ++ [A].
    Proof.
      intros.
      apply rules_cut with (A := A).
      apply H.
      apply H0.
    Qed.

    Lemma cut_ax_2 : forall G A,
      |- G ++ [A] ->
      |- [A] ++ [negation A] ->
      |- G ++ [A].
    Proof.
      intros.
      apply H.
    Qed.

    Lemma cut_mult_1 : forall G D P A B,
        |- G ++ [A] ++ [B] ->
        |- D ++ [negation A] ->
        |- P ++ [negation B] ->
        |- G ++ D ++ P.
    Proof.
      intros.
      apply rules_cut with (A := Par A B).
      - apply rules_par. apply H.
      - simpl.
        rewrite <- app_assoc.
        apply rules_tensor.
        -- apply H0.
        -- apply H1.
    Qed.

    Lemma cut_mult_2 : forall G D P A B,
        |- G ++ [A] ++ [B] ->
        |- D ++ [negation A] ->
        |- P ++ [negation B] ->
        |- G ++ D ++ P.
    Proof.
      intros.
      apply Exchange with (G := (G ++ P) ++ D).
      Permutation_solve.
      apply rules_cut with (A := A).
      - apply Exchange with (G := (G ++ [A]) ++ P).
        Permutation_solve.
        apply rules_cut with (A := B).
        rewrite <- app_assoc.
        -- apply H.
        -- apply H1.
      - apply H0.
    Qed.

    (** ** Exponential cut elimination rules *)
    Lemma cut_exp_1_b :
      forall q_G A D,
        Questions q_G ->
        |- D ->
        |- q_G ++ [negation A] ->
        |- D ++ q_G.
    Proof.
      intros.
      apply Weak.
      apply H.
      apply H0.
    Qed.

    Lemma cut_exp_1_a :
      forall q_G A D,
        Questions q_G ->
        |- D ->
        |- q_G ++ [negation A] ->
        |- D ++ q_G.
    Proof.
      intros.
      apply rules_cut with (A := YNot A).
      - apply rules_weak. apply H0.
      - simpl. apply rules_ofc.
        -- apply H.
        -- apply H1.
    Qed.

    Lemma cut_exp_2_a :
      forall q_G D A,
        Questions q_G ->
      |- D ++ [A] ->
      |- q_G ++ [negation A] ->
      |- D ++ q_G.
    Proof.
      intros.
      apply rules_cut with (A := YNot A).
      - apply rules_ynot. apply H0.
      - simpl. apply rules_ofc. apply H. apply H1.
    Qed.

    Lemma cut_exp_2_b :
      forall q_G D A,
        Questions q_G ->
      |- D ++ [A] ->
      |- q_G ++ [negation A] ->
      |- D ++ q_G.
    Proof.
      intros.
      apply rules_cut with (A := A).
      - apply H0.
      - apply H1.
    Qed.

    Lemma cut_exp_3_b :
      forall q_G D A,
        Questions q_G ->
      |- D ++ [A] ->
      |- q_G ++ [negation A] ->
      |- D ++ q_G.
    Proof.
      intros.
      apply rules_cut with (A := A).
      - apply H0.
      - apply H1.
    Qed.

    Lemma cut_exp_4_a :
      forall q_G D A,
        Questions q_G ->
        |- D ++ [YNot A] ++ [YNot A] ->
        |- q_G ++ [negation A] ->
        |- D ++ q_G.
    Proof.
      intros.
      apply rules_cut with (A := YNot A).
      - apply rules_cont. apply H0.
      - simpl. apply rules_ofc.  apply H.  apply H1.
    Qed.

    Lemma cut_exp_4_b :
      forall q_G D A,
        Questions q_G ->
        |- D ++ [YNot A] ++ [YNot A] ->
        |- q_G ++ [negation A] ->
        |- D ++ q_G.
    Proof.
      intros.
      apply Contract with (q_D := q_G).
      - apply H.
      - rewrite app_assoc. apply rules_cut with (A := YNot A).
        -- apply Exchange with (G := ((D ++ [YNot A]) ++ q_G)).
           Permutation_solve.
           apply rules_cut with (A := YNot A).
           rewrite <- app_assoc.
           --- apply H0.
           --- simpl. apply rules_ofc.
               ---- apply H.
               ---- apply H1.
        -- simpl. apply rules_ofc.
           --- apply H.
           --- apply H1.
    Qed.

    Lemma cut_exp_5_a :
      forall q_G B A q_D,
        Questions q_G -> Questions q_D ->
        |- q_G ++ [negation B] ++ [YNot A] ->
        |- q_D ++ [negation A] ->
        |- q_G ++ q_D ++ [Ofc (negation B)].
    Proof.
      intros.
      apply Exchange with (G := (q_G ++ [Ofc (negation B)]) ++ q_D). Permutation_solve.
      apply rules_cut with (A := YNot A).
      - apply Exchange with (G := ((q_G ++ [YNot A]) ++ [Ofc (negation B)])). Permutation_solve.
        apply rules_ofc. apply Questions_app. apply H. apply questions_Questions. reflexivity.
        -- apply Exchange with (G := (q_G ++ ([negation B] ++ [YNot A]))). Permutation_solve.
           apply H1.
      - simpl. apply rules_ofc.
        -- apply H0.
        -- apply H2.
    Qed.

  End Examples.

End Onesided_MELL_lists.
