(* NOTE:  This file was taken from the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL. This file will not work unless you use it inside the repo within their coq project. *)

(* Add LoadPath "../" . *)
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

Module PL.
  Inductive LForm :Set :=
  | bot (* false *)
  | atom : nat -> LForm (* atomic propositions are named with a natural number *)
  | conj : LForm -> LForm -> LForm (* conjunction *)
  | disj : LForm -> LForm -> LForm (* disjunction *)
  | impl : LForm -> LForm -> LForm (* intuitionistic implication *)
  .

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

  Reserved Notation " L ';' n '|-P-' F" (at level 80).
  Inductive sq : list LForm -> nat -> LForm -> Prop :=
  | init : forall (L L' :list LForm) a, L =mul= atom a :: L' -> L ; 0 |-P- atom a
  | botL : forall (L L' :list LForm) G , L =mul= bot :: L' -> L ; 0 |-P- G
  | cR : forall L F G n m , L ; n |-P- F -> L ; m |-P- G -> L ; S (max n m) |-P- conj F G
  | cL : forall L G G' F L' n, L =mul= (conj G G') :: L' -> G :: G' :: L' ; n |-P- F -> L ; S n |-P- F
  | dR1 : forall L F G n, L ;  n |-P- F -> L ; S n |-P- disj F G
  | dR2 : forall L F G n, L ;  n |-P- G -> L ; S n |-P- disj F G
  | dL : forall L L' F G H n m, L =mul= disj F G :: L' ->  F :: L' ;  n |-P- H -> G :: L' ;  m |-P- H  -> L ;  S (max n m) |-P- H 
  | impR : forall L F G n , F :: L ; n |-P- G ->  L ; S n |-P- impl F G
  | impL : forall L L' F G H n m,  L =mul= impl F G :: L' -> L ; n |-P- F -> G :: L' ; m |-P- H -> L ; S (max n m)|-P- H
  where "L ; n |-P- F" := (sq L n F).

  Example Ex1: exists n, [ (atom 3)] ;n|-P- impl (conj (atom 1) (atom 2)) (conj (atom 2) (conj (atom 3) (atom 1))).
  eexists.
  eapply impR;eauto.
  eapply cL;eauto.
  eapply cR;eauto.
  eapply init;eauto.
  eapply cR;eauto.
  eapply init;eauto.
  eapply init;eauto.
  Qed.

  (* Exchange *)
  Theorem Exch : forall L L' F n, L =mul= L' -> L ; n |-P-F -> L' ;n  |-P-F.
    intros.
    generalize dependent L.
    generalize dependent L'.
    generalize dependent F.
    induction n using strongind;intros;subst.
    + (* base *)
      inversion H0;subst.
      rewrite H in H1.
      eapply init;auto.

      rewrite H in H1.
      eapply botL;auto.
    + (* inductive *)
      inversion H1;subst.

      (* cR *) 
      - apply cR.
      eapply H with (L:=L);auto.
      eapply H with (L:=L);auto.

      (* cL *)
      - rewrite H0 in H3.
      eapply cL.
      -- apply H3.
      -- apply H5.

      (* dR1 *)
      - apply H with (L' := L') in H4;auto.
      apply dR1;auto.

      (* dR2 *)
      - apply H with (L' := L') in H4;auto.
      apply dR2;auto.

      (* dL *)
      - rewrite H0 in H4.
      eapply dL;eauto.


      (* impl R *)  
      - eapply H with (L' := F0 :: L') in H4;auto.
      eapply impR;auto.

      (* impl L *)
      - eapply H with (L' := L') in H5;auto.
      eapply impL;eauto.
  Qed.

(* MY VERSION *)

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
  | rules_impl_l   : forall G_impl_l G A B C,
                            (G_impl_l =mul= impl A B :: G)
                            -> G_impl_l |- A
                            -> B :: G |- C
                            -> G_impl_l |- C
where " G '|-' C " := (rules G C).

Example Ex1_my_ver: [(atom 3)] |- impl (conj (atom 1) (atom 2)) (conj (atom 2) (conj (atom 3) (atom 1))).
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

(* two contexts equivalent modulo exchange are *)
Theorem Exch_my_ver : forall G D C, G =mul= D -> G |- C -> D |- C.
    intros.
    generalize dependent D.


    induction H0;intros;subst.

    (* base case 1: init *)
    -
    rewrite H in H0.
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
  Qed.

End PL.
