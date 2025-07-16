(** * CaRVe implementation in Rocq

    We follow the first sections of the Beluga context as resource vectors library,
    and define a small fragment of intuitionistic logic.

    Some simplifications:

    - We don't work with named assumptions.
    - We don't have contexts length-indexed.
    - It seems that Beluga has everything as propositions / relations. We follow that but we make some fixpoint equivalents if convenient.

 *)

(** * ILL fragment

The intuitionistic linear logic fragment the paper is concerned with is:

<<
---------------- hyp
    A |- A

    D_1 |- A    D_2, A |- B
------------------------------ cut
        D_1, D_2 |- B

     D, A |- B
------------------- -o R
    D |- A -o B

   D_1 |- A   D_2, B |- C
---------------------------- -o L
   D_1, D_2, A -o B |- C
>>

 *)


(** * Infrastructure of CaRVE

The carve infrastructure includes:
    - variables of type A annotated by multiplicities (We do not use variables for now for simplicity)
    - multiplicites come from a resource monoid \M = (M, op, e)
    - contexts: D = (x_i :^a_i A_i, ..., x_n :^a_n A_n) (list)
    - context merge : merge op, parametrized by op
    - context merge monoid : D{M}
    - context update
    - context look-up in terms of update

    Which we then use to define ILL.

From the artifact read-me, we are concerned with:
*)

(*

Definitions

| Definition                                   | Paper           | File / folder                        | Definition name                                   |
|----------------------------------------------|-----------------|------------------------------------- |---------------------------------------------------|
| Typing contexts                              | §2, §4.1        | common/defs/ctx.bel                  | lctx                                              |
| Linear multiplicities                        | §2.1, §4.1      | common/defs/mult/lin_aff.bel         | mult, •, hal                                      |
| Context merge                                | §2.1, §4.1      | common/defs/ctx.bel                  | merge                                             |
| Exhaustedness                                | §2.2, §4.1      | common/defs/ctx.bel                  | exh                                               |
| Context update                               | §2.3, §4.1      | common/defs/ctx.bel                  | upd                                               |
| Context element permutation                  | §2.3, §4.1      | common/defs/ctx.bel                  | exch                                              |
| Context look-up                              | §2.3, §4.1      | common/defs/ctx.bel                  | lookup_intm, lookup_n                             |
| Context well-formedness                      | §4.1            | common/defs/ctx.bel                  | Wf                                                |
| Linear natural deduction terms               | §3.1            | case_studies/seq-nd/tm.bel           | obj                                               |
| Lin. seq. / nat. deduction types             | §4.2            | case_studies/seq-nd/tp.bel           | tp                                                |
| Linear sequent calculus typing judgment      | §3.1            | case_studies/seq-nd/seq.bel          | seq                                               |

*)

(*

Theorems

| Theorem                                      | Paper           | File / folder                        | Definition name                                   |
|----------------------------------------------|-----------------|-------------------------------- ---  |---------------------------------------------------|
| Algebraic properties of lin. multiplicities  | §2.1            | common/lemmas/mult/lin_aff.bel       | mult_func, mult_canc, mult_assoc,                 |
|                                              |                 |                                      | mult_comm, mult_zsfree                            |
| Algebraic properties of context merge        | §2.1, Prop 2.1  | common/lemmas/merge/halid.bel        | merge_id                                          |
|                                              |                 | common/lemmas/merge/main.bel         | merge_assoc, merge_comm                           |
|                                              |                 | common/lemmas/merge/cancl.bel        | mult_canc                                         |
| Well-formedness properties of context merge  | §2.1, Prop 2.2  | common/lemmas/mult/merge/            | wf_merge, wf_merge_l                              |
| Algebraic properties of context update       | §2.3, Prop 2.3  | common/lemmas/upd/main.bel           | upd_func, upd_refl, upd_symm, upd_trans, upd_conf |
|                                              |                 | common/lemmas/merge/main.bel         | merge_upd                                         |
| Properties of context look-up                | §2.3, Prop 2.4  | common/lemmas/upd/main.bel           | lookup_unq, lookup_upd                            |
|                                              |                 | common/lemmas/merge/main.bel         | merge_lookup, merge_lookup2                       |
| Well-formedness properties of context update | §2.1, Prop 2.5  | common/lemmas/upd/main.bel           | lookup_neq_nat2var, lookup_neq_var2nat,           |
|                                              |                 | common/lemmas/wf.bel                 | wf_upd, wf_upd_neq                                |
| Properties of substitution                   | §3.2, Lemma 3.1 | case_studies/seq-nd/lemmas/subst.bel | subst_exh, subst_merge, subst_upd                 |
| Equivalence theorem (seq. / nat. deduction)  | §3.2, Thm. 3.2  | case_studies/seq-nd/thms.bel         | seq2nd, chk2seq, syn2seq                          |

 *)

(** Let's try doing most of the definitions from section 2.1, i.e. the file ctx.bel. Then we try 3.1 *)

(** Relational: WE try yet again to do most of this relationally, but IF it makes more sense not to,
    we define both relational and functional versions and prove that they are equivalent. *)

(**  * Linear multiplicities
     - file: [lin_aff.bel]
     - Here we are implementing the resource monoid.
     - [m_0] : available once
     - [m_1] : used

 *)

Module lmult.

Inductive mult : Type :=
| m_0
| m_1.

(**Monoid operator *)

Inductive op : mult -> mult -> mult -> Type :=
| op_00 : op m_0 m_0 m_0
| op_10 : op m_1 m_0 m_1
| op_01 : op m_0 m_1 m_1.

(** Note on functional [op]

We could have written [op_fn], because this is quite awkward.
But, recall [op_m 1 1] is undefined.

<<
Fixpoint op_fn (m_a m_b : mult) : mult :=
  match m_a, m_b with
  | m_0, m_0 => m_0
  | m_1, m_0 => m_1
  | m_0, m_1 => m_1
  | m_1, m_1 => ??
  end.
>>
*)

(** *** Harmlessness
    - [hal a]: multiplicity a is harmless
    - In this ILL fragment, this means that the multiplicity is zero or that the resource is unavailable.

 *)

Inductive hal : mult -> Prop :=
| hal_0 : hal m_0.

(** *** Identity element
    - [ident_rel] : identity element w.r.t to op
    - [ident_e] : alias

 *)

Inductive ident_rel : mult -> Prop :=
| ident_0 : ident_rel m_0.

Definition ident_e : mult := m_0.

(** *** Multiplicity equality
    - [mult_eq]: two mults are equal if they are reflexively equal in terms of a relation
    - [mult_eq]: two mults are equal if they are "equal" equal (Coq-level?).

*)

Inductive mult_eq : mult -> mult -> Prop :=
  | mult_refl a : mult_eq a a.

(* [added] *)
Theorem mult_eq_eq :
  forall a b, mult_eq a b -> a = b.
Proof.
  intros.
  inversion H;subst.
  reflexivity.
Qed.

Theorem eq_mult_eq :
  forall a b, a = b -> mult_eq a b.
Proof.
  intros.
  inversion H;subst.
  apply mult_refl.
Qed.

(** Since we've shown [mult_eq] is equivalent to [=], moving forward we stick with [mult_eq] for
    correspondence with the Beluga code.

 *)

End lmult.

(** *  Explicit contexts
    - file: [ctx.bel] *)

Module lctx.

Import lmult.

Definition var := nat.
Definition var_type := Set.

(** ** Length indexed typing contexts *)

(** Note: The beluga lctx is length indexed, which makes lctx a dependent type and also somewhat complicates merge and everything else that works on lctx. Binders are also implicitly quantified.

<<

    Inductive lctx : nat -> Prop :=
    | nil : lctx 0
    | cons : forall n, lctx n -> var -> var_type -> mult -> lctx (S n).

>>

    The above was a first attempt, highlighting how the dependent type makes it a bit harder to write.
    Coq should work with dependent types ANYWAY, so this is my unfamiliarity with it speaking.

 *)

Inductive lctx : Type :=
| lnil : lctx
| lcons : lctx -> var -> var_type -> mult -> lctx.



(** ** Typing context equality

    In the original beluga implementation, this is written:

<<
    LF cx_eq : lctx N → lctx N → type =
    | cx/refl : cx_eq Δ Δ;
>>

  It's a relation.

 *)

Inductive lctx_eq : lctx -> lctx -> Prop :=
| lctx_refl : forall D, lctx_eq D D.

(** * Merge

In beluga, it is written :

<<
LF merge : lctx N → lctx N → lctx N → type =
| mg/n : merge nil nil nil
| mg/c : merge Δ₁ Δ₂ Δ → • α₁ α₂ α → merge (cons Δ₁ X A α₁) (cons Δ₂ X A α₂) (cons Δ X A α);
>>

 *)

(*

Old attempt, with dependent types:

Inductive merge n : lctx n -> lctx n -> lctx n -> Prop :=
| merge_nil : merge 0 nil nil nil
| merge_cons n : forall D1 D2 a1 a2 X A,
    exists D, merge n D1 D2 D ->
              exists a, op a1 a2 a -> merge (cons D1 X A a1) (cons D2 X A a2) (cons D X A a).
*)



(** * Splitting / merging typing contexts
    - [Δ₁ ⋈ Δ₂ = Δ]
    - Deterministic merge, or viewed bottom-up, non-deterministic split.

 *)

Inductive merge : lctx -> lctx -> lctx -> Prop :=
| merge_lnil : merge lnil lnil lnil
| merge_lcons :
  forall D1 D2 D a1 a2 a X A,
    merge D1 D2 D -> op a1 a2 a ->
    merge (lcons D1 X A a1) (lcons D1 X A a2) (lcons D X A a).

(** * Update
    - [Δ[x :α A ↦ₙ y :β B] = Δ']
    - 9 arguments:
    - New context [D'] is [D] with assumption [x :a A] in position [n] replaced with [y :b B].

 *)

Inductive upd :
  lctx -> nat -> var -> var -> var_type -> var_type -> mult -> mult -> lctx -> Prop :=
| upd_hd : forall D n X X' A A' a a',
    upd (lcons D X A a) (S n) X X' A A' a a' (lcons D X' A a')
| upd_tl : forall D n X X' A A' a a' B b D' Y,
    upd D n X X' A A' a a' D' -> upd (lcons D Y B b) n X X' A A' a a' (lcons D' Y B b).

(** * Exhausted context
   - Only harmless assumptions appear in D.
   - For this particular type system (linear), recall an assumption is harmless if it is unavailable. Hence an exhausted context for this linear system is a context with all multiplicities set to 0 ('practically an empty context').

 *)

Inductive exh : lctx -> Prop :=
| exh_lnil : exh lnil
| exh_lcons : forall D m v v_typ, exh D -> hal m -> exh (lcons D v v_typ m).

(** * same_elts :
    - [Δ ≈ Δ', Δ = Δ'] up to varying multiplicities
    - Comment: last case in beluga is written: [same_elts (cons Δ X A _) (cons Δ' X A _)]. What does that placeholder "_" imply -- can they be different? Yes. Because we don't care about multiplicities.  Could we use _ in Coq? Only in matches (pattern matching), as far as I am aware.

 *)

Inductive same_elts : lctx -> lctx -> Prop :=
| same_elts_lnil : same_elts lnil lnil
| same_elts_lcons : forall D D' X A a b, same_elts (lcons D X A a) (lcons D' X A b).

(**  *  Shorthands
     - file: [ctx.bel]
     - TBD

 *)

Inductive exch : lctx -> nat -> var -> nat -> var -> lctx -> Prop :=
| exch_u :
  forall (n m : nat)  D n X Y A B a b D'' m D',
  n <> m -> upd D n X Y A B a b D'' -> upd D'' m Y X B A b a D' ->
  exch D n X m Y D'.

Inductive lookup : var -> var_type -> mult -> lctx -> Prop :=
| look :
  forall D n X A a,
  upd D n X X A A a a D -> lookup X A a D.

Definition lookup_ D n X A a := upd D n X X A A a a D.

Inductive lookup_n : var -> lctx -> Prop :=
| lookn : forall D X a b c d e f g,
    upd D a X b c d e f g -> lookup_n X D.


(** * Algebraic properties of linear multiplicities
      - file: [common/lemmas/mult/lin_aff.bel]
    Most or all of the proofs proceed by enumerating the possible cases for [op].
 *)

(** ** Functionality
    If [α₁ ∙ α₂ = α] and [α₁ ∙ α₂ = α'], then [α = α'].
 *)

Theorem lmult_functionality : forall a1 a2 a a', op a1 a2 a' -> op a1 a2 a -> mult_eq a a'.
Proof.
  intros.
  inversion H;subst;inversion H0;subst;apply mult_refl.
Qed.

(** Interesting note: Beluga is like Agda in that proofs are done by providing the proof inhabitant.
    This is the proof for functionality of op:

<<
  rec mult_func : [ ⊢ • α₁ α₂ α] → [ ⊢ • α₁ α₂ α'] → [ ⊢ mult_eq α α'] =
  / total /
  fn m1, m2 ⇒ case m1 of
  | [ ⊢ •/00] ⇒ let [ ⊢ •/00] = m2 in [ ⊢ mult/refl]
  | [ ⊢ •/10] ⇒ let [ ⊢ •/10] = m2 in [ ⊢ mult/refl]
  | [ ⊢ •/01] ⇒ let [ ⊢ •/01] = m2 in [ ⊢ mult/refl]
  ;
>>

  There is some odd syntax going on.
  But again, the proof is essentially destructing the given op relations, which have finite cases.

 *)


(** ** Identity
    If [α₁ ∙ α₂ = α] and [α₁] is an identity element, then [α₂ = α]
    For any [α], obtain an identity element [β] such that [β • α = α]
 *)

Theorem lmult_identity :
  forall a1 a2 a, op a1 a2 a -> ident_rel a1 -> mult_eq a2 a.
Proof.
  intros.
  destruct H0.
  inversion H;subst;apply mult_refl.
Qed.

(** ** Zero-sum-freedom
    If [α₁ ∙ α₂ = α] and [α] is an identity element, then [α₁ = α].
 *)

Theorem lmult_zero_sum_free :  forall (a b c : mult),
    op a b c ->
    mult_eq c m_0 ->
    mult_eq a m_0 /\ mult_eq b m_0.
Proof.
  intros.
  split;inversion H;subst;auto;apply mult_refl.
Qed.

(** ** Commutativity
    If [α₁ ∙ α₂ = α], then [α₂ ∙ α₁ = α] *)

Theorem lmult_comm :
  forall a1 a2 a, op a1 a2 a -> op a2 a1 a.
Proof.
  intros.
  destruct H.
  - apply op_00.
  - apply op_01.
  - apply op_10.
Qed.

(** TBD:
    I'm not sure what's happening here.

<<
LF get_u∙ : mult → type =
| get-u∙ : ident β → • β α α → get_u∙ α;

rec mult_get_id : {α:[ ⊢ mult]} [ ⊢ get_u∙ α] =
  / total /
  mlam α ⇒ case [ ⊢ α] of
  | [ ⊢ 𝟘] ⇒ [ ⊢ get-u∙ ident/0 •/00]
  | [ ⊢ 𝟙] ⇒ [ ⊢ get-u∙ ident/0 •/01]
  ;
>>
 *)

(** ** Associativity
        If [(α₁ • α₂) • α₃ = α], then [α₁ • (α₂ • α₃) = α]
        TBD: slightly awkward to do when op is a relation
 *)

(** ** Cancellativity
    If [α₁ ∙ α₂ = α] and [α₁ ∙ α₂' = α], then [α₂ = α₂'].
 *)

Theorem lmult_cancellative:
  forall a1 a2 a2' a,
    op a1 a2 a -> op a1 a2' a -> mult_eq a2 a2'.
Proof.
  intros.
  inversion H;subst;inversion H0;subst;apply mult_refl.
Qed.

(** ** Corollaries *)

Lemma lmult_ident_inv :
  forall a2 a, op m_0 a2 a -> mult_eq a2 a.
Proof.
  intros.
  inversion H;subst;apply mult_refl.
Qed.

Lemma lmult_zsf_inv :
  forall a1 a2, op a1 a2 m_0 -> mult_eq a1 m_0.
Proof.
  intros.
  inversion H;subst;apply mult_refl.
Qed.

(** TBD:
<<
rec mult_get_id_cor : {α:[ ⊢ mult]} [ ⊢ • 𝟘 α α] =
  / total /
  mlam α ⇒ let [ ⊢ get-u∙ ident/0 M] = mult_get_id [ ⊢ α] in [ ⊢ M]
  ;
>>
 *)

(** ** Properties of harmless elements *)

Lemma mult_hal_id : forall a,
    hal a -> op a a a.
Proof.
  intros.
  inversion H; subst.
  apply op_00.
Qed.

Lemma mult_ident_hal : forall a,
    ident_rel a -> hal a.
Proof.
  intros.
  inversion H; subst.
  apply hal_0.
Qed.

Lemma mult_hal_ident : forall a,
    hal a -> ident_rel a.
Proof.
  intros.
  inversion H; subst.
  apply ident_0.
Qed.

(** * Algebraic properties of context merge
    - files: [common/lemmas/merge/halid.bel]; [main.bel]; [cancl.bel]
    The proofs are slightly more complicated.
 *)

(** ** Merge cancellativity
    - file: [cancl.bel]
    Note: this property depends on the resource algebra operation [op] being cancellative.
 *)

Theorem merge_cancellative :
  forall D1 D2 D2' D, merge D1 D2 D -> merge D1 D2' D -> lctx_eq D2 D2'.
Proof.
  intros D1 D2 D2' D H1 H2.
  inversion H1; subst.
  - (* merge_lnil *)
    inversion H2; subst.
    apply lctx_refl.
  - inversion H2;subst.
    apply lmult_cancellative with (a2 := a2) in H11 as H12.
    2 : { apply H0. }
    apply mult_eq_eq in H12;subst.
    apply lctx_refl.
Qed.

(** *** Compare with

rec merge_cancl : (Ψ:ctx) (Δ:[Ψ ⊢ lctx N[]]) [Ψ ⊢ merge Δ₁ Δ₂ Δ] → [Ψ ⊢ merge Δ₁ Δ₂' Δ] → [Ψ ⊢ cx_eq Δ₂ Δ₂'] =
  / total 1 /
  fn m1, m2 ⇒ case m1 of
  | [_ ⊢ mg/n] ⇒ let [_ ⊢ mg/n] = m2 in [_ ⊢ cx/refl]
  | [_ ⊢ mg/c M1 T1[]] ⇒
    let [_ ⊢ mg/c M2 T2[]] = m2 in
    let [_ ⊢ cx/refl] = merge_cancl [_ ⊢ M1] [_ ⊢ M2] in
    let [ ⊢ mult/refl] = mult_canc [ ⊢ T1] [ ⊢ T2] in
    [_ ⊢ cx/refl]
  ;
 *)

(**  ** Merge w/ harmless elements
     - file: [halid.bel]
     Note: These properties only hold if all harmless elements are identity elements
 *)

Theorem merge_id :
  forall D1 D2 D, merge D1 D2 D -> exh D1 -> lctx_eq D2 D.
Proof.
  Admitted.

Theorem merge_id_r :
  forall D1 D2 D, merge D1 D2 D -> exh D2 -> lctx_eq D1 D.
Proof.
  Admitted.

(** Note: this odd presentation has to do with the contextual modal type system of beluga. *)

(** LF merge_ident : merge _ _ _ → type =
  mg_ident : {M:merge Δ Δ Δ} merge_ident M;

rec merge_zsfree : (Ψ:ctx) (Δ:[Ψ ⊢ lctx N[]]) [Ψ ⊢ exh Δ] → {M:[Ψ ⊢ merge Δ₁ Δ₂ Δ]} [Ψ ⊢ merge_ident M] =
  / total 1 /
  fn e ⇒ mlam M ⇒ case [_ ⊢ M] of
  | [_ ⊢ mg/n] ⇒ [_ ⊢ mg_ident _]
  | [_ ⊢ mg/c M1 T1[]] ⇒
    let [_ ⊢ exh/c E1 U1[]] = e in
    let [ ⊢ mult/refl] = mult_zsfree [ ⊢ T1] (mult_hal_ident [ ⊢ U1]) in
    let [ ⊢ mult/refl] = mult_zsfree (mult_comm [ ⊢ T1]) (mult_hal_ident [ ⊢ U1]) in
    let [_ ⊢ mg_ident _] = merge_zsfree [_ ⊢ E1] [_ ⊢ M1] in
    [_ ⊢ mg_ident _]
  ;
 *)

Inductive merge_ident_rel : Prop :=
  | mg_ident : forall D, merge D D D -> merge_ident_rel.

Theorem merge_zsfree :
  forall D D1 D2, exh D -> merge D1 D2 D -> merge_ident_rel.
Proof.
  intros.
  inversion H0; subst.
  - apply mg_ident with (D := lnil).
    apply merge_lnil.
  - inversion H; subst.
    inversion H8; subst.
    apply lmult_zero_sum_free in H2 as [H2a H2b].
    2 : { apply mult_refl. }
    destruct H2a.
    destruct H2b.
    Admitted.

(** ** Properties of context merge
    Very TBD
    file: [main.bel]
 *)

(** *** Prune merge
    TBD
 *)

(** *** Functionality
    If [Δ₁ ⋈ Δ₂ = Δ] and [Δ₁ ⋈ Δ₂ = Δ'], then [Δ = Δ'],
 *)

Theorem merge_functionality :
  forall D1 D2 D D', merge D1 D2 D -> merge D1 D2 D' -> lctx_eq D D'.
Proof.
  intros.
  inversion H;subst.
  - inversion H0; subst. apply lctx_refl.
  - Admitted.

(** *** Commutativity
    If [Δ₁ ⋈ Δ₂ = Δ], then [Δ₂ ⋈ Δ₁ = Δ].
 *)

Theorem merge_commutativity :
  forall D1 D2 D, merge D1 D2 D -> merge D2 D1 D.
Proof.
  Admitted.

(** *** Existence of identity context
   [Δ ⋈ 0Δ = Δ] for any [Δ].
 *)

Inductive mg_getid : lctx -> Prop :=
| mg_getid_c : forall D D', merge D D' D -> exh D' -> mg_getid D.

Theorem merge_identity : forall D,
    mg_getid D.
Proof.
  Admitted.

(** *** Associativity
    (1) If [(Δ₁ ⋈ Δ₂) ⋈ Δ₃ = Δ], then [Δ₁ ⋈ (Δ₂ ⋈ Δ₃)]
    (2) If [(Δ₁ ⋈ Δ₂) ⋈ Δ₃ = Δ], then [(Δ₁ ⋈ Δ₃) ⋈ Δ₂] (corollary of (1) using commutativity)
 *)

(** How to actually write this? *)
Inductive mg_assoc : Prop :=
| mg_assoc_c : forall D1 D2 D3 D12 D23 D,
    merge D2 D3 D23 -> merge D1 D23 D -> merge D12 D3 D -> merge D1 D2 D12 -> mg_assoc.

Theorem merge_assoc : forall D1 D2 D12 D3 D,
    merge D12 D3 D -> merge D1 D2 D12 -> mg_assoc.
Proof.
Admitted.

Inductive mg_assoc_2 : Prop :=
| mg_assoc_2_c : forall D1 D2 D3 D13 D12 D,
    merge D1 D3 D12 -> merge D13 D2 D -> merge D12 D3 D -> merge D1 D2 D12 -> mg_assoc_2.

Theorem merge_assoc_2 : forall D1 D2 D3 D12 D,
    merge D12 D3 D -> merge D1 D2 D12 -> mg_assoc.
Proof.
  Admitted.

(** ** Merge interaction with update *)

(** *** Preservation of lookup under merge

        AKA: Merging preserves elements and combines multiplicities

    - (1) If [(x :α A) ∈ₙ (Δ₁ ⋈ Δ₂)], then [(x :α₁ A) ∈ₙ Δ₁] and [(x :α₂ A) ∈ₙ Δ₂] for some [α₁, α₂] such that [α₁ ∙ α₂ = α]
      English: If an element with some multiplicity is in the merge of two contexts, then that same element is in both contexts, but with multiplicities split such that they add up correctly when merged.

    - (2) If [(x :α₁ A) ∈ₙ Δ₁] and [Δ₁ ⋈ Δ₂ = Δ], then [(x :α₂ A) ∈ₙ Δ₂, (x :α A) ∈ₙ Δ] for [α₁, α₂] such that [α₁ ∙ α₂ = α]
      English: If an element with some multiplicity is in a context, and then that context is merged with another, then that element is in both the other context and their merge but with multiplicities split such that they add up correctly when merged.

TBD

 *)

(** *** Distributivity of updating
TBD
 *)

(** ** Corollaries
TBD
 *)

End lctx.
