From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Export Sorting.PermutSetoid.
From Stdlib Require Export Sorting.PermutEq.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Export Permutation.
Require Export LL.SequentCalculi.
Require Export LL.SequentCalculiBasicTheory.
Require Export LL.Multisets.
Require Export LL.StrongInduction.
Require Export LL.FLLMetaTheory.

#[local] Hint Resolve Nat.le_max_r : core .
#[local] Hint Resolve Nat.le_max_l : core .

(** * LJ

  - Sequent calculus version of NJ. Intuitionistic.
  - Introduced by Gentzen. We follow a "modernized" presentation.
  - Weakening, contraction are explicit.
  - Exchange is implicit and handled via multiset equality.
  - Contexts are multisets
  - This file is a modification taken from the Linear Logic formalization in Coq: https://github.com/brunofx86/LL.

 *)

Module PL.

  (** * Formulas *)

  Inductive LForm :Set :=
  | bot (* false *)
  | atom : nat -> LForm (* atomic propositions are named with a natural number *)
  | conj : LForm -> LForm -> LForm (* conjunction *)
  | disj : LForm -> LForm -> LForm (* disjunction *)
  | impl : LForm -> LForm -> LForm (* intuitionistic implication *)
  .

  (** * Some infrastructure for multisets

  - Refer to the documentation for coq-ll. In short, we need that formulas have decidable equality.
  - These are defined in a module [F_dec], which is passed to the multiset module.

   *)

  Theorem LForm_dec_eq : forall F G : LForm, {F = G} + {F <> G}.
    induction F;destruct G;try(right;discriminate);
      try(
          generalize(IHF1 G1);intro;
          generalize(IHF2 G2);intro;
          destruct H;destruct H0;subst;try(right;intro;inversion H;contradiction);auto).
    left;auto.
    generalize(eq_nat_decide n n0);intro Hn.
    destruct Hn.
    apply eq_nat_is_eq in e;subst;auto.
    right; intro;rewrite eq_nat_is_eq in n1.
    inversion H.
    contradiction.
  Qed.

  Module F_dec <: Eqset_dec_pol.
    Definition A := LForm.
    Definition eqA_dec := LForm_dec_eq.
    Fixpoint isPositive (n:nat) :=
      match n with
      | 0%nat => false
      | 1%nat => true
      | S (S n) => isPositive n
      end.
  End F_dec.

  Declare Module MSFormulas : MultisetList F_dec.
  Export MSFormulas.

(** * Inference rules *)

Reserved Notation " G '|-' C " (at level 80).
Inductive rules : list LForm -> LForm -> Prop :=
  | rules_init     : forall G_atom_A G A,
                            (G_atom_A =mul= atom A :: G)
                             -> G_atom_A |- atom A             (* G, atom a |- atom a *)
  | rules_bot_l    : forall G_bot G C,
                            (G_bot =mul= bot :: G)
                            -> G_bot |- C                      (* G, bot |- C *)
  | rules_conj_r   : forall G A B, G |- A -> G |- B -> G |- conj A B
  | rules_conj_l   : forall G_conj_A_B A B C G,
                            (G_conj_A_B =mul= (conj A B) :: G)
                            -> A :: B :: G |- C
                            -> G_conj_A_B |- C                 (* G, A, B |- C -> G, conj A B |- C *)
  | rules_disj_r_1 : forall G A B, G |- A -> G |- disj A B
  | rules_disj_r_2 : forall G A B, G |- B -> G |- disj A B
  | rules_disj_l   : forall G_disj_A_B G A B C,
                            (G_disj_A_B =mul= disj A B :: G)
                            -> A :: G |- C
                            -> B :: G |- C
                            -> G_disj_A_B |- C                 (* G, A |- C -> G, B |-  C -> G, disj A B |- C *)
  | rules_impl_r   : forall G A B, A :: G |- B -> G |- impl A B
  | rules_impl_l   : forall G_impl_A_B G A B C,
                            (G_impl_A_B =mul= impl A B :: G)
                            -> G_impl_A_B |- A
                            -> B :: G |- C
                            -> G_impl_A_B |- C
  | rules_weak     : forall G A G_A C,
                            (G_A =mul= A :: G)
                            -> G |- C
                            -> G_A |- C
  | rules_contract : forall G A G_A G_A_A C,
                            (G_A =mul= A :: G) -> (G_A_A =mul= A :: G_A)
                            -> G_A_A |- C
                            -> G_A |- C

where " G '|-' C " := (rules G C).

(** * Example derivations

    - TBD: more examples

 *)

(** *** An exchange example *)

Example Ex1: [(atom 3)] |- impl (conj (atom 1) (atom 2)) (conj (atom 2) (conj (atom 3) (atom 1))).
Proof.
  remember (atom 1) as A.
  remember (atom 2) as B.
  remember (atom 3) as C.
  eapply rules_impl_r;eauto.                   (* [C] |- impl (conj A B) (conj B (conj C A)) *)
  eapply rules_conj_l;eauto.                   (* [conj A B; C] |- conj B (conj C A) *)
  eapply rules_conj_r;eauto.                   (* [A; B; C] |- conj B (conj C A) *)
  rewrite HeqB;eapply rules_init;eauto.        (* [A; B; C] |- B *)
  eapply rules_conj_r;eauto.                   (* [A; B; C] |- conj C A *)
  rewrite HeqC;eapply rules_init;eauto.        (* [A; B; C] |- C *)
  rewrite HeqA;eapply rules_init;eauto.        (* [A; B; C] |- A *)
Qed.

(** * Metatheorems

    - TBD: cut

 *)

(** *** Exchange *)

Theorem Exchange : forall G D C, G =mul= D -> G |- C -> D |- C.
Proof.
    intros. generalize dependent D.

    induction H0;intros;subst.

    (* base case 1: init *)
    - rewrite H in H0.
      eapply rules_init;auto.

    (* base case 2: bot left *)
    -  rewrite H in H0.
       eapply rules_bot_l;auto.

    (* conjunction right *)
    (* two IH: for D |- A and D |- B *)
    -  apply rules_conj_r.
       -- apply IHrules1. apply H. (* IH: G =mul D+ -> D |- A*)
       -- apply IHrules2. apply H.

    (* conjunction left *)
    - eapply rules_conj_l.
      -- rewrite <- H1. apply H.
      -- apply H0.

    (* disjunction right 1 *)
    - apply rules_disj_r_1;auto.

    (* disjunction right 2 *)
    - apply rules_disj_r_2;auto.

    (* disjunction left *)
    - eapply rules_disj_l.
      -- rewrite <- H0. apply H.
      -- apply H0_.
      -- apply H0_0.

    (* implication right *)
    - apply rules_impl_r. apply IHrules;auto.
    (* implication left *)
    - eapply rules_impl_l.
      -- rewrite <- H0. apply H.
      -- apply IHrules1. apply H0.
      -- apply H0_0.
    (* weakening *)
    -  eapply rules_weak.
       -- apply meq_sym in H. apply meq_sym. eapply meq_trans.
          --- apply H.
          --- apply H1.
       -- apply H0.
    - eapply rules_contract.
      --  apply meq_sym in H. apply meq_sym. eapply meq_trans.
          --- apply H.
          --- apply H2.
      -- rewrite <- H2. apply H0.
      -- apply H1.
Qed.

(** *** Identity *)

Theorem Identity : forall GG G A, GG =mul= A :: G  -> GG |- A.
Proof.
  intros. generalize dependent GG. generalize dependent G.
  induction A;intros;subst.
  - eapply rules_bot_l. auto.
  - eapply rules_init. auto.
  - eapply rules_conj_r.
    -- eapply rules_conj_l.
       --- apply H.
       --- eapply rules_weak with (G_A := A1 :: A2 :: G) (G := A1 :: G) (A := A2).
           ---- auto.
           ---- apply IHA1 with (G := G) (GG := A1 :: G).
                ----- reflexivity.
    -- eapply rules_conj_l.
       --- apply H.
       --- eapply rules_weak with (G_A := A1 :: A2 :: G) (G := A2 :: G) (A := A1).
           ---- auto.
           ---- apply IHA2 with (G := G) (GG := A2 :: G).
                ----- reflexivity.
  - eapply rules_disj_l.
     -- apply H.
     -- apply rules_disj_r_1. apply IHA1 with (G := G). reflexivity.
     -- apply rules_disj_r_2. apply IHA2 with (G := G). reflexivity.
  - eapply rules_impl_r.
    eapply rules_impl_l with (G_impl_A_B := A1 :: GG) (G := A1 :: G) (A := A1) (B := A2) (C := A2).
    -- rewrite H. auto.
    -- apply IHA1 with (G := GG). auto.
    -- apply IHA2 with (G := A1 :: G). auto.
Qed.

(** *** Cut elimination *)

Theorem Cut : forall GG G A C, GG =mul= A :: G -> G |- A -> GG |- C -> G |- C.
Proof.
  intros. generalize dependent GG. generalize dependent G.
  (* :) *)
  Admitted.

End PL.
