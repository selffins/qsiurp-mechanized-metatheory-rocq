(** For now, 1 file contains all the modules. *)

(** *  Lists
    Coq version of [abella-reasoning/lib/list.thm]
 *)

(** ** Contains:
    Status: all proved
    + means my addition

    - [append_rel]
       - + equivalences to [append]
    - [rev_rel]
       - + equivalences to [rev]
    - [can_append]
    - [can_rev]

    In the abella style, [append] and [rev] are relational, so we have relational [append] and [rev] as well in Coq.
 **)

From Stdlib Require Export Sets.Multiset.
From Stdlib Require Export List.
From Stdlib Require Import Arith.EqNat.
Export ListNotations.

Module Type Eqset_dec.
  Parameter Eqset_T : Type.
  Parameter eqA_dec : forall x y : Eqset_T, {x = y} + {x <> y}.
End Eqset_dec.

Module Type lists_abella (ELT : Eqset_dec).

  (** ** Elements *)
  Import ELT.
  Definition o := Eqset_T.

  (** ** Append *)

  Inductive append_rel : list o -> list o -> list o -> Prop :=
  | append_nil (L : list o): append_rel [] L L
  | append_cons e J K L (H : append_rel J K L): append_rel (e :: J) K (e :: L).

  (** *** Examples *)

  Example append_rel_12_34_1234 :
    forall (o1 o2 o3 o4 : o),
    append_rel ([o1 ; o2]) ([o3 ; o4]) ([o1 ; o2 ; o3 ; o4]).
  Proof.
    intros.
    apply append_cons.
    apply append_cons.
    apply append_nil.
  Qed.

  Example append_rel_12_nil_12 :
    forall o1 o2,
    append_rel ([o1; o2]) ([]) ([o1; o2]).
  Proof.
    intros.
    apply append_cons.
    apply append_cons.
    apply append_nil.
  Qed.

  Example append_rel_12_nil_13_fail :
    forall o1 o2 o3,
      o2 <> o3 ->
    not (append_rel ([o1 ; o2]) [] ([o1 ; o3])).
  Proof.
    intros.
    unfold not.
    intros.
    inversion H0;subst.
    inversion H4.
    contradiction.
  Qed.

  (** *** Equivalence to Rocq's [append] *)

  Theorem append_append_rel :
    forall J K, append_rel J K (J ++ K).
  Proof.
    intros.
    induction J as [ | j ].
    - simpl. apply append_nil.
    - simpl. apply append_cons. apply IHJ.
  Qed.

  Theorem append_append_rel_inv :
    forall J K L, J ++ K = L -> append_rel J K L.
  Proof.
    intros;subst. apply append_append_rel.
  Qed.

  Theorem append_rel_append :
    forall J K L, append_rel J K L -> J ++ K = L.
  Proof.
    intros.
    induction H.
    - reflexivity.
    - simpl. f_equal. apply IHappend_rel.
  Qed.

  Theorem append_rel_singleton :
    forall L a, append_rel [a] L (a :: L).
  Proof.
    intros.
    apply append_cons.
    apply append_nil.
  Qed.

  (** ** Reversing a list *)

  Inductive rev_rel : list o -> list o -> Prop :=
  | rev_nil : rev_rel [] []
  | rev_cons e J L (H : exists K, rev_rel J K /\ append_rel K (e :: []) L ) : rev_rel (e :: J) L.

  (** The induction principle is problematic as well.
   TBD: rewrite without the existential quantifier. *)

  Inductive rev_rel_2 : list o -> list o -> Prop :=
  | rev_nil_2 : rev_rel_2 [] []
  | rev_cons_2 : forall e J L K, rev_rel_2 J K -> append_rel K (e :: []) L -> rev_rel_2 (e :: J) L.

  Example rev_123_321 :
    forall o1 o2 o3,
    rev_rel [o1 ; o2 ; o3] [o3 ; o2 ; o1].
  Proof.
    intros.
    eapply rev_cons.
    exists [o3 ; o2].
    split.
    - eapply rev_cons.
      exists [o3].
      split.
      -- eapply rev_cons. exists []. split.
         --- apply rev_nil.
         --- apply append_nil.
      -- apply append_cons. apply append_nil.
    - apply append_cons. apply append_cons. apply append_nil.
  Qed.

  Theorem can_append_rel : forall J K, exists L, append_rel J K L.
  Proof.
    intros.
    induction J as [ | j ].
    - exists K. apply append_nil.
    - destruct IHJ as [M].
      exists (j :: M).
      apply append_cons.
      apply H.
  Qed.

  (** In the Abella version, they define [is_list]. I think this is similar to providing an inductive definition of list.
      For the Abella proof of this one, they actually state [can_rev] as [forall J, is_list J -> exists K, rev J K].
      So, then they induct (and case) on [is_list J], which is doing the same thing as inducting on [J] in coq
      and having cases based on the shape of [J].

      This is the first proof which I've compared Abella with Coq. I will annotate it by the corresponding
      Abella code.
   *)

  Theorem can_rev_rel : forall J, exists K, rev_rel J K.
  Proof.
    (* induction on 1. intros. case H1. (Inducts on the list) *)
    intros.
    induction J as [ | A L ].
    (* Base case: J is nil. Goal: exists K, rev nil K.
       Reversing nil obviously gives us nil.
       In Abella this is handled easily by using "search", which
       presumably finds evidence for you. *)
    - exists []. apply rev_nil.
    (* Inductive case.
       We have the IH "forall J, is_list J * -> (exists K, rev J K)" in Abella.
       The asterisks mean that we can use this IH for is_list J hypothesis that is
       smaller than the original is_list J in the theorem statement.

       The abella proof proceeds with:
       apply IH to H3.  ;; H3 here is "is_list L", L comes from J being (A :: L) in this case
       apply can_append to _ _ with J = K, K = A :: nil.
       apply rev_2_is_list to H4. search.
       search.
     *)
    - destruct IHL as [K].
      (* The abella proof invokes "can_append" on K and (cons A nil).
         They get that K ++ (cons A nil) = L1.
         can_append here seems to be the way to show K == (cons A nil) is the append of K and (cons A nil). Which they use for the
         evidence for rev_rel. We can of course provide K ++ (cons A nil) instead to rev_rel.
       *)
      assert (H1 : exists L1, append_rel K [A] L1).
      {
        exists (K ++ [A]). apply append_append_rel.
      }
      destruct H1 as [L1].
      exists L1.
      apply rev_cons.
      exists K.
      split.
      -- apply H.
      -- apply H0.
  Qed.

  Theorem rev_singleton: forall a,
      rev_rel [a] [a].
  Proof.
    intros.
    apply rev_cons.
    exists []. split.
    - apply rev_nil.
    - apply append_nil.
  Qed.

  Theorem rev_cons_singleton : forall J K a,
      rev_rel J K -> rev_rel (J ++ [a]) (a :: K).
  Proof.
    intros.
    generalize dependent a. generalize dependent K.
    induction J.
    - intros. inversion H;subst. simpl. apply rev_singleton.
    - intros. inversion H;subst. destruct H3. destruct H0.
      simpl. apply rev_cons. exists (a0 :: x).
      split.
      -- apply IHJ. apply H0.
      -- apply append_cons. apply H1.
  Qed.

  Theorem rev_nil_inv : forall J,
      J = [] -> rev_rel J [].
  Proof.
    intros;subst. apply rev_nil.
  Qed.

  Theorem rev_symm : forall J K,
      rev_rel J K -> rev_rel K J.
  Proof.
    intros.
    generalize dependent K.
    induction J;intros.
    - inversion H;subst. apply rev_nil.
    - inversion H;subst. destruct H3. destruct H0.
      apply append_rel_append in H1;subst.
      apply rev_cons_singleton. apply IHJ. apply H0.
  Qed.

(** * Permutations
    -   Coq version of [abella-reasoning/lib/perm.thm]
 *)

Section perm_abella.

  (** ** Contains:
      [*] denotes my addition.
      Status: incomplete

<<
    - adj
    1. adj_exists
    2. *adj_cons_comm_1
    3. *adj_cons_comm_2
    4. adj_swap
    5. adj_same
    6. adj_append_1 / adj_1_append

    - perm
    7. perm_refl
    8. perm_sym
    9. perm_cons_1
    10. perm_cons_2
    11. adj_preserves_perm
    12. perm_trans_lem
    13. perm_trans
    14. adj_same_source
    15. adj_same_result
    16. adj_same_result_diff
    17. adj_same_result_diff_both
    18. perm_invert
    19. adj_perm_source
    20. adj_nil_1
    21. perm_nil_1
    22. adj_det
    23. perm_singleton

    - append and perm
    24. append_perm
    25. adj_perm
    26. adj_perm_full

    - set theoretic semantics of adj and perm
    27. adj_member
    28. member_adj
    29. member_adj_rel
    30. adj_preserves_member_lem
    31, adj_preserves_member
    32. perm_preserves_member
>>

   For some proofs, induction on adj and especially induction on perm does not work.
   We will need to take a look at the inductive principle first...
   *)

  (** ** Adj *)

  Inductive adj : list o -> o -> list o -> Prop :=
  | adj_hd : forall L A, adj L A (A :: L)
  | adj_tl : forall B K A L, adj K A L -> adj (B :: K) A (B :: L).

  (** Note:
      The abella library did not have these commutativity stuff.
      I needed it to prove some theorems, particularly example [adj_1_23_321]. *)

  Theorem adj_cons_comm_1 : forall A B K C L, adj (A :: B :: K) C L -> adj (B :: A :: K) C L.
  Admitted. (** Not part of the lib *)

  Theorem adj_cons_comm_2 : forall A B K C L, adj K C (A :: B :: L) -> adj K C (B :: A :: L).
  Admitted. 

  (** *** Examples of adj *)

  Example adj_1_23_123 :
    forall o1 o2 o3,
    adj ([o2 ; o3]) o1 ([o1 ; o2 ; o3]).
  Proof.
    intros.
    apply adj_hd.
  Qed.

  Example adj_1_23_213 :
    forall o1 o2 o3,
    adj ([o2 ; o3]) o1 ([o2 ; o1 ; o3]).
  Proof.
    intros.
    apply adj_tl.
    apply adj_hd.
  Qed.

  Example adj_1_23_321 : forall o1 o2 o3,
      adj ([o2 ; o3]) o1 ([o3 ; o2 ; o1]).
  Proof.
    intros.
    apply adj_cons_comm_1.
    apply adj_tl.
    apply adj_tl.
    apply adj_hd.
  Qed.

  Theorem adj_exists : forall A L, exists M, adj L A M.
  Proof.
    intros.
    exists (A :: L).
    apply adj_hd.
  Qed.

  (** Note:
      Here is the Abella proof of [adj_swap] (annotations e.g. bullet points + comments mine):
  *)

  (*
  Theorem adj_swap : forall A J K B L, adj J A K -> adj K B L -> exists U, adj J B U /\ adj U A L.

      induction on 2.
      intros.
          - case H2.                                (* Case on adj K B L @ *)
          - case H1.                                (* Case on adj J A K *)
              -- search.                            (* Provide B :: J *)
              -- apply adj_1_is_list to H6.
              search.                               (* Provide B :: B1 :: K1 *)
           - case H1.                               (* Case on adj J A (B1 :: K1) *)
               -- apply adj_3_is_list to H4.
                  search.                           (* Provide L1 *)
               -- apply IH to H6 H4.                (* IH on [K2 A ~ K1], [K1 B ~ L1] gives [K2 B ~ U'] [U' A ~ L1]. *)
              search.                               (* Provide B1 :: U' *)
   *)

  Theorem adj_tl_inv : forall B K A L, adj (B :: K) A (B :: L) -> adj K A L.
  Proof.
    intros.
    inversion H;subst.
    - apply adj_hd.
    - apply H3.
  Qed.

  Theorem adj_L_is_A_cons_K : forall B K A L, adj K A L -> adj (A :: K) B (B :: L).
  Proof.
    intros.
    induction H.
    - apply adj_hd.
    - apply adj_cons_comm_1. apply adj_cons_comm_2. apply adj_tl. apply IHadj.
  Qed.

  Theorem adj_swap : forall A J K B L, adj J A K -> adj K B L -> exists U, adj J B U /\ adj U A L.
  Proof.
    intros. generalize dependent J.
    induction H0;intros.
    - (* case on J A ~ L *)
      inversion H;subst.
      -- exists (A0 :: J).
         split.
         --- apply adj_hd.
         --- apply adj_tl. apply H.
      -- exists (A0 :: B :: K).
         split.
         --- apply adj_hd.
         --- apply adj_tl. apply H.
    - inversion H;subst.
      -- exists (A0 :: K).
         split.
         --- apply adj_hd.
         --- apply adj_L_is_A_cons_K. apply H0.
      -- apply IHadj in H4. destruct H4 as [X [H4a H4b]].
         exists (B :: X).
         split.
         --- apply adj_tl. apply H4a.
         --- apply adj_tl. apply H4b.
  Qed.

  (** Note:

      Here is the Abella proof of [adj_same]:
<<
      induction on 1.            (* Induction on adj L A (B :: L) *)
      intros.
      case H1.
      - search.
      - apply IH to H3. search.
>>

      It is short, so I wonder why I couldn't prove it in Coq. There is something forgotten when I apply induction.  We do not seem to have the [H1] that this proof cases on.
      So for now we admit.

      Update: We simply needed to use the remember tactic: [B :: L'] isn't of the more generic shape [L], which causes induction to forget some structure.
   *)

  Theorem adj_same : forall A L B, adj L A (B :: L) -> A = B.
  Proof.
    intros. remember (B :: L) as F.
    induction H.
    - inversion HeqF. reflexivity.
    - apply IHadj. inversion HeqF. reflexivity.
  Qed.

  (** Note:

      Here is the Abella proof of [adj_append 1]:

<<
      induction on 1. intros.
      case H1.
      - case H2.
      -- apply append_2_is_list to H6.
      -- apply append_3_is_list to H6. search.
      - case H2.
      apply IH to H4 H6. search.
>>

      The corresponding proof diverges a little bit from this
      because I leverage [append_rel]'s equivalence with append in Coq.

      [append_rel] has a [exists] part relating the two appendees(?)
      but [append] is actually something that constructs such a list.

      We write [append_rel] (and [rev_rel]) to have a clearer correspondence with the relational style in Abella.
      It also means only the theorems about [append_rel] and [rev_rel] are in the library - there is less clutter.

   *)

  Theorem adj_append_1 : forall J A K L KL,
      adj J A K ->
      append_rel K L KL ->
      exists JL, append_rel J L JL /\ adj JL A KL.
  Proof.
    intros. generalize dependent L. generalize dependent KL.
    induction H;intros.
    - inversion H0;subst.
      exists (L ++ L0).
      split.
      apply append_append_rel.
      apply append_rel_append in H4. rewrite H4. apply adj_hd.
    - inversion H0;subst.
      apply append_rel_append in H0. inversion H0. subst.
      edestruct IHadj as [X].
      -- apply H5.
      -- destruct H1. exists (B :: X).
         split.
         --- apply append_cons. apply H1.
         --- apply adj_tl. apply H2.
  Qed.


  Theorem adj_1_append : forall J A K L JL,
      adj J A K ->
      append_rel J L JL ->
      exists KL, append_rel K L KL /\ adj JL A KL.
  Proof.
    intros. generalize dependent L. generalize dependent JL.
    induction H;intros.
    (* adj_hd? : J = L, K = A :: L*)
    - inversion H0;subst.
      -- exists ([A] ++ JL). split.
         --- apply append_append_rel.
         --- simpl. apply adj_hd.
      -- exists ((A :: e :: J) ++ L0).
         split.
         --- apply append_append_rel.
         --- apply append_rel_append in H. subst. simpl. apply adj_hd.
    (* adj_tl  *)
    - inversion H0;subst. edestruct IHadj as [X].
      -- apply H5.
      -- exists ((B :: L) ++ L0). split.
         --- apply append_append_rel.
         --- destruct H1. apply append_rel_append in H1. subst.
             simpl. apply adj_tl. apply H2.
  Qed.

  (** ** Perm *)

  (** Abella version: (notice the existential quantifier)
<<
       perm J K : J and K have the same elements
       Define perm : olist -> olist -> prop by
       ; perm nil nil
       ; perm K L :=
       exists A KK LL, adj KK A K /\ adj LL A L /\ perm KK LL.
>>
   *)

  (** This version without exists is more behaved regarding induction because the [KK] and [LL] can be used outside of the existential quantifier. *)

  Inductive perm  : list o -> list o -> Prop :=
  | perm_nil : perm nil nil
  | perm_split : forall K L A KK LL, adj KK A K -> adj LL A L -> perm KK LL -> perm K L.

  (*
    Check perm_ind.

    perm_ind
     : forall P : list o -> list o -> Prop,
       P [] [] ->
       (forall (K L : list o) (A : o) (KK LL : list o), adj KK A K -> adj LL A L -> perm KK LL -> P KK LL -> P K L) ->
       forall l l0 : list o, perm l l0 -> P l l0
   *)

  (** *** Examples of [perm] *)

  Example perm_123_321 :
    forall o1 o2 o3, perm [o1 ; o2 ; o3] [o3 ; o2 ; o1].
  Proof.
    intros.
    eapply perm_split.
    - apply adj_tl. apply adj_tl. apply adj_hd.
    - apply adj_hd.
    - eapply perm_split; repeat split.
      -- apply adj_hd.
      -- apply adj_tl. apply adj_hd.
      -- eapply perm_split; repeat split.
         --- apply adj_hd.
         --- apply adj_hd.
         --- apply perm_nil.
  Qed.

  (** ** [Perm] theorems *)

  Theorem perm_sym : forall K L, perm K L -> perm L K.
  Proof.
    intros.
    induction H.
    - apply perm_nil.
    - eapply perm_split. repeat split.
      -- apply H0.
      -- apply H.
      -- apply IHperm.
  Qed.

  Theorem perm_refl : forall L, perm L L.
  Proof.
    intros.
    induction L.
    - apply perm_nil.
    - inversion IHL;subst.
      -- eapply perm_split.
         --- assert (H : adj [] a [a]). { apply adj_hd. } apply H.
         --- assert (H : adj [] a [a]). { apply adj_hd. } apply H.
         --- apply perm_nil.
      -- eapply perm_split.
         --- apply adj_hd.
         --- apply adj_hd.
         --- apply IHL.
  Qed.

  Theorem perm_cons_1 : forall A K L,
      perm (A :: K) L ->
      exists J, adj J A L /\ perm K J.
  Proof.
    intros.
    remember (A :: K) as X.
    induction H;subst.
    - discriminate.
    - inversion H;subst.
      -- exists LL. auto.
      -- destruct IHperm as [J [IHa IHb]].
  Admitted.

  Theorem perm_cons_2 : forall A K L,
      perm K (A :: L) ->
      exists J, adj J A K /\ perm J L.
  Proof.
    intros.
    apply perm_sym in H.
    eapply perm_cons_1 in H.
    destruct H as [J' [H1 H2]].
    exists J'.
    split.
    - apply H1.
    - apply perm_sym. apply H2.
  Qed.

  Theorem adj_preserves_perm : forall A JJ J KK K,
      adj JJ A J ->
      adj KK A K ->
      perm JJ KK ->
      perm J K.
  Proof.
    intros.
    eapply perm_split.
    apply H. apply H0. apply H1.
  Qed.

  Theorem perm_trans_lem : forall J K L, perm J K -> perm K L -> perm J L.
  Proof.
    intros. generalize dependent L.
    induction H;intros.
    - apply H0.
    - (* Long proof, follow on paper *)
  Admitted.

  Theorem perm_trans : forall J K L, perm J K -> perm K L -> perm J L.
  Proof.
    intros.
    eapply perm_trans_lem.
    apply H.
    apply H0.
  Qed.

  (** Interesting how the abella proof is 4 tactics. *)

  Theorem adj_same_source : forall J A K L,
      adj J A K -> adj J A L ->
      perm K L.
  Proof.
    intros.
    inversion H;inversion H0;subst.
    - apply perm_refl.
    - eapply perm_split.
      -- apply H.
      -- apply H0.
      -- apply perm_refl.
    - eapply perm_split.
      -- apply adj_hd.
      -- apply adj_tl. apply adj_hd.
      -- eapply perm_split.
         --- apply H1.
         --- apply adj_hd.
         --- apply perm_refl.
    - inversion H6;subst.
      eapply perm_split.
      apply H.
      apply H0.
      apply perm_refl.
  Qed.

  Theorem adj_same_result : forall J K A L,
      adj J A L ->
      adj K A L ->
      perm J K.
  Proof.
    (*  Induction on adj J A L and casing on adj K A L *)
    intros. generalize dependent K.
    induction H;intros.
    - inversion H0;subst.
      -- apply perm_refl.
      -- eapply perm_split.
         --- apply H3.
         --- apply adj_hd.
         --- apply perm_refl.
    - inversion H0;subst.
      -- eapply perm_split.
         --- apply adj_hd.
         --- apply H.
         --- apply perm_refl.
      -- eapply perm_split.
         --- apply adj_hd.
         --- apply adj_hd.
         --- apply IHadj in H4. apply H4.
  Qed.


  Theorem adj_same_result_diff : forall J A K B L,
      adj J A L ->
      adj K B L ->
      (A = B /\ perm J K) \/
        exists KK, adj KK A K.
  Proof.
    (*  Induction on adj J A L and casing on adj K B L, giving a witness from IH *)
    intros. generalize dependent K. generalize dependent B.
    induction H; intros.
    - inversion H0;subst.
      -- left. split. reflexivity. apply perm_refl.
      -- right. exists K0. apply adj_hd.
    - inversion H0;subst.
      -- right. exists K. apply H.
      -- apply IHadj in H4. destruct H4 as [[H4a1 H4a2] | H4b1];subst.
         --- left. split.  reflexivity.
             eapply perm_split.
             ---- apply adj_hd.
             ---- apply adj_hd.
             ---- apply H4a2.
         --- destruct H4b1 as [X].
             right.
             exists (B :: X).
             apply adj_tl.
             apply H1.
  Qed.

  Theorem adj_same_result_diff_both : forall J A K B L,
      adj J A L ->
      adj K B L ->
      (A = B /\ perm J K) \/
        exists JJ KK, adj JJ B J /\ adj KK A K /\ perm JJ KK.
  Proof.
    (* Induction on adj J A L and casing on adj K B L*)
    intros. generalize dependent K.
    induction H;intros.
    - inversion H0;subst.
      -- left. split. reflexivity. apply perm_refl.
      -- right. exists K0. exists K0. repeat split.
         --- apply H3.
         --- apply adj_hd.
         --- apply perm_refl.
    - inversion H0;subst.
      -- right. exists K. exists K. repeat split.
         --- apply adj_hd.
         --- apply H.
         --- apply perm_refl.
      -- apply IHadj in H4 as [[IHa1 IHa2] | IHb].
         --- inversion IHa2;subst.
             ---- left. split. reflexivity. apply perm_refl.
             ---- left. split. reflexivity. eapply perm_split.
                  ----- apply adj_hd.
                  ----- apply adj_hd.
                  ----- apply IHa2.
         --- destruct IHb as [X [Y [IHb1 [IHb2 IHb3]]]].
             right. exists (B0 :: X). exists (B0 :: Y).
             repeat split.
             ---- apply adj_tl. apply IHb1.
             ---- apply adj_tl. apply IHb2.
             ---- eapply perm_split.
                  ----- apply adj_hd.
                  ----- apply adj_hd.
                  ----- apply IHb3.
  Qed.

  Theorem perm_invert : forall A J K JJ KK,
      perm J K ->
      adj JJ A J ->
      adj KK A K ->
      perm JJ KK.
  Proof.
    (* Induction on perm J K, one casing on adj JJ A J, applying many previous theorems *)
    intros. Admitted.

  (*  Proof in abella:

induction on 1. intros. case H1.
  case H2.
  apply adj_same_result_diff to H2 H4. case H7.
    apply adj_same_result_diff to H3 H5. case H9.
      apply perm_trans to *H8 *H6. apply perm_sym to *H10. backchain perm_trans.
      apply adj_same_result to H3 H5. apply perm_trans to *H8 *H6. apply perm_sym to *H11. backchain perm_trans.
    apply adj_same_result_diff to H3 H5. case H9.
      apply perm_sym to *H10. apply perm_trans to *H6 *H11.
       apply adj_same_result to H2 H4. backchain perm_trans.
      apply IH to H6 H8 H10.
       apply adj_swap to *H10 *H5. apply adj_swap to *H8 *H4.
       apply adj_same_result to *H2 *H15. apply adj_same_result to *H13 *H3.
       apply adj_preserves_perm to *H14 *H12 *H11.
       apply perm_trans to *H16 *H18. backchain perm_trans.

There are many usages of adj theorems. It might be more productive to look at the Abella interactive proof
- see the hypotheses, and then figure out how they are manipulated. *)

  Theorem adj_perm_result : forall J K A JJ,
      perm J K ->
      adj JJ A J ->
      exists KK, adj KK A K /\ perm JJ KK.
  Proof.
  (*  Revisit, was broken when switched perm.
  intros. generalize dependent JJ. generalize dependent A.
  induction H;intros.
  - inversion H0.
  - inversion H0;subst.
    -- eapply adj_same_result_diff with (J := JJ) (A := A) in H2.
      destruct H2. destruct H2;subst.
      --- destruct H. subst.
          exists L'.
          split.
          ---- apply H0.
          ---- apply perm_trans with (J := JJ) in Hc;auto.
      --- destruct H as [X].
          apply adj_same_result_diff with (J := L') (A := B) in H.
          destruct H. destruct H;subst.
          exists X. split.
          ---- Admitted.
   (** Induction on perm J K and casing on adj JJ A J *)
   *) Admitted.

  Theorem adj_perm_source : forall J K A L,
      perm J K ->
      adj J A L ->
      exists LL, adj K A LL /\ perm L LL.
  Proof.
    intros.
    exists (A :: K).
    split.
    - apply adj_hd.
    - eapply perm_split.
      -- apply H0.
      -- apply adj_hd.
      -- apply H.
  Qed.

  Theorem adj_nil_1 : forall A L,
      adj nil A L -> L = A :: nil.
  Proof.
    intros. inversion H;subst. reflexivity.
  Qed.

  Theorem perm_nil_1 : forall L,
      perm nil L -> L = nil.
  Proof.
    intros.
    inversion H;subst.
    - reflexivity.
    - inversion H0.
  Qed.

  Theorem adj_det : forall A B L,
      adj L A (B :: nil) -> A = B /\ L = nil.
  Proof.
    intros.
    inversion H;subst;split.
    - reflexivity.
    - reflexivity.
    - inversion H3.
    - inversion H3.
  Qed.

  Theorem perm_singleton : forall A L,
      perm (A :: nil) L -> L = (A :: nil).
  Proof.
    intros.
    inversion H;subst.
    apply adj_det in H0 as [H0a H0b]. subst.
    apply perm_nil_1 in H2. subst.
    apply adj_nil_1 in H1.
    apply H1.
  Qed.

  (** ** [append] and [perm] theorems *)

  Theorem append_perm : forall J K L JJ KK,
      append_rel J K L ->
      perm J JJ ->
      perm K KK ->
      exists LL, append_rel JJ KK LL /\ perm L LL.
  Proof.
  (* Revisit
    intros. generalize dependent JJ. generalize dependent KK.
    induction H;intros.
    - inversion H0;subst.
      -- exists KK. split.
         --- apply append_nil.
         --- apply H1.
      -- destruct H as [B [K [L' [H2 [H3 H4]]]]].
         inversion H2.
    - apply perm_cons_1 in H0 as [J' [foo1 foo2]].
      apply IHappend_rel with (JJ := J') in H1.
      Admitted. (** Try again, almost done, needs proper application of IH *)
   *)
  Admitted.

  Theorem adj_perm : forall J K JJ A,
      perm J K ->
      adj JJ A J ->
      exists KK, adj KK A K.
  Proof.
    intros. generalize dependent K.
    induction H0;intros.
    - apply perm_cons_1 in H as [X [Ha Hb]]. exists X. apply Ha.
    - apply perm_cons_1 in H as [X [Ha Hb]].
      apply IHadj in Hb as [KK'].
      eapply adj_swap in Ha as [U [Ha1 Ha2]].
      exists U. apply Ha2.
      apply H.
  Qed.

  Theorem adj_perm_full : forall J K JJ A,
      perm J K ->
      adj JJ A J ->
      exists KK, adj KK A K /\ perm JJ KK.
  Proof.
    intros. generalize dependent K.
    induction H0;intros;eapply perm_cons_1 in H as [X [Ha Hb]].
    - exists X. split.
      -- apply Ha.
      -- apply Hb.
    - apply IHadj in Hb as [KK' [IHadj1 IHadj2]].
      eapply adj_swap in Ha.
      -- destruct Ha as [U [Ha1 Ha2]].
         exists U.
         split.
         --- apply Ha2.
         --- eapply perm_split.
             ---- apply adj_hd.
             ---- apply Ha1.
             ---- apply IHadj2.
      --  apply IHadj1.
  Qed.

  (** ** Set-theoretic semantics of [adj] *)

  (** This section connects the adj relation with the set membership relation,
      which is intuitive - [adj L A K] says [K] is [L] with [A] inserted "somewhere"
      (i.e. set membership).

     We could use [In] (from [Stdlib.Lists]) as our set membership relation, but we will instead use the [member] relation defined in the Abella standard library, which is what they used in their implementation.

     Here is how it's defined:
<<
     Type   nil     olist.
     Type   ::      o -> olist -> olist.

     Define member : o -> olist -> prop by
     member A (A :: L);
     member A (B :: L) := member A L.
>>

   *)

  Inductive member : o -> list o -> Prop :=
  | member_hd  : forall A L, member A (A :: L)
  | member_tl  : forall A B L, member A L -> member A (B :: L).

  Theorem adj_member : forall J A L,
      adj J A L -> member A L.
  Proof.
    intros.
    induction H.
    - apply member_hd.
    - apply member_tl. apply IHadj.
  Qed.

  Theorem member_adj : forall A L,
      member A L -> exists J, adj J A L.
  Proof.
    intros.
    induction H. 
    - exists L. apply adj_hd.
    - inversion H;subst.
      -- exists (B :: L0). apply adj_tl. apply adj_hd.
      -- destruct IHmember as [X].
         exists (B :: X).
         apply adj_tl.
         apply H1.
  Qed.

  Theorem member_adj_rel : forall JJ A J B,
      adj JJ A J -> member B J ->
      A = B \/ member B JJ.
  Proof.
    intros. generalize dependent B.
    induction H;intros.
    - inversion H0;subst;auto.
    - inversion H0;subst.
      -- right. apply member_hd.
      -- destruct IHadj with (B := B0).
         --- apply H3.
         --- left. apply H1.
         --- right. apply member_tl. apply H1.
  Qed.

  Theorem adj_preserves_member_lem : forall A J B L,
      member A J -> adj J B L -> member A L.
  Proof.
    intros. generalize dependent B. generalize dependent L.
    induction H;intros.
    - inversion H0;subst.
      -- apply member_tl. apply member_hd.
      -- apply member_hd.
    - inversion H0;subst.
      -- apply member_tl. apply member_tl. apply H.
      -- apply IHmember with (B := B0). (*  Need to check abella proof / handwrite *)
  Admitted.


  Theorem adj_preserves_member : forall A J B L,
      member A J -> adj J B L -> member A L.
  Proof.
    intros.
    eapply adj_preserves_member_lem.
    apply H.
    apply H0.
  Qed.

  Theorem perm_preserves_member : forall A K L,
      perm K L ->
      member A K -> member A L.
  Proof.
    intros. generalize dependent L.
    induction H0;intros;eapply perm_cons_1 in H as [X [Ha Hb]].
    - eapply adj_member.
      apply Ha.
    - apply IHmember in Hb.
      eapply adj_preserves_member.
      apply Hb.
      apply Ha.
  Qed.

End perm_abella.


(** * Merge
    - Coq version of [abella-reasoning/lib/merge.thm]
 *)

(** ** Contains:
    Status: majority unproved
<<
    1. merge
    2. perm_merge_1
    3. perm_merge_2
    4. perm_merge_3
    5. merge_sym
    6. merge_nil_perm
    7. merge_adj_1
    8. merge_unadj_1
    9. merge_adj_2
    10. merge_unadj_2
    11. merge_unadj_3
    12. merge_invert_1
    13. merge_invert_2
    14. merge_move_12
    15. merge_move_21
    16. add_to_merge_right
    17. add_to_merge_left
    18. merge_nil_equal
    19. merge_exists
    20. merge_head_lemma
    21. adj_implies_merge
    22. merge_assoc
    23. change_merge_order
    24. change_merge_order2
    25. merge_perm_det
    26. merge_preserves_perm_lem
    27. merge_preserves_perm
    28. merge_sub
    29. merge_to_adj
    30. merge_same_result_diff
    31. subset_1_is_list
    32. subset_2_is_list
>>
 *)

Section merge_abella.

  (** ** Definition

      merge J K L : J union K equals L.

      In abella,
  *)

  (*  Define merge : olist -> olist -> olist -> prop by
      ; merge nil nil nil
      ; merge J K L :=
      exists A JJ LL,
      adj JJ A J /\ adj LL A L /\ merge JJ K LL
      ; merge J K L :=
      exists A KK LL,
     adj KK A K /\ adj LL A L /\ merge J KK LL
   *)

  (** A more direct translation of [merge] retaining the existential quantifiers resluts in a problematic indcution principle. *)

  (*
      Inductive merge : list o -> list o -> list o -> Prop :=
      | merge_nil : merge nil nil nil
      | merge_l J K L (H : exists A JJ LL, adj JJ A J /\ adj LL A L /\ merge JJ K LL) : merge J K L
      | merge_r J K L (H : exists A KK LL, adj KK A K /\ adj LL A L /\ merge J KK LL) : merge J K L.

      Check merge_ind.

      merge_ind
      : forall P : list o -> list o -> list o -> Prop,
       P [] [] [] ->
       (forall J K L : list o,
        (exists (A : o) (JJ LL : list o), adj JJ A J /\ adj LL A L /\ merge JJ K LL) ->
        P J K L) ->
       (forall J K L : list o,
        (exists (A : o) (KK LL : list o), adj KK A K /\ adj LL A L /\ merge J K LL) -> P J K L) ->
       forall l l0 l1 : list o, merge l l0 l1 -> P l l0 l1
   *)

   (** Problematic because the smaller lists [KK] and [LL] are not used outside of the existential quantifier, in the IHa.
       So, we write it as:
   *)

  Inductive merge : list o -> list o -> list o -> Prop :=
  | merge_nil : merge nil nil nil
  | merge_l : forall J K L A JJ LL, adj JJ A J -> adj LL A L -> merge JJ K LL ->  merge J K L
  | merge_r : forall J K L A KK LL, adj KK A K -> adj LL A L -> merge J KK LL -> merge J K L.

  (* Check merge_ind. *)

  (** Now we have the following, which does use the smaller lists correctly: *)

  (* merge_ind
     : forall P : list o -> list o -> list o -> Prop,
       P [] [] [] ->
       (forall (J K L : list o) (A : o) (JJ LL : list o),
        adj JJ A J -> adj LL A L -> merge JJ K LL -> P JJ K LL -> P J K L) ->
       (forall (J K L : list o) (A : o) (KK LL : list o),
        adj KK A K -> adj LL A L -> merge J KK LL -> P J KK LL -> P J K L) ->
       forall l l0 l1 : list o, merge l l0 l1 -> P l l0 l1
 *)
  
  (** *** [perm_merge] theorems *)

  Theorem perm_merge_1 : forall J K L JJ,
      merge J K L ->
      perm J JJ ->
      merge JJ K L.
  Proof.
    intros. generalize dependent JJ.
    induction H;intros.
    - apply perm_nil_1 in H0. subst. apply merge_nil.
    - eapply adj_perm in H2 as H3.
      destruct H3 as [X].
      eapply perm_invert in H3 as H4.
      -- eapply IHmerge in H4.
         eapply merge_l.
         apply H3.
         apply H0.
         apply H4.
      -- apply H2.
      -- apply H.
      -- apply H.
    - eapply IHmerge in H2.
      eapply merge_r.
      apply H.
      apply H0.
      apply H2.
  Qed.

  Theorem perm_merge_2 : forall J K L KK,
      merge J K L ->
      perm K KK ->
      merge J KK L.
  Proof.
    intros. generalize dependent KK.
    induction H;intros.
    - apply perm_nil_1 in H0;subst. apply merge_nil.
    - eapply IHmerge in H2.
      eapply merge_l.
      -- apply H.
      -- apply H0.
      -- apply H2.
    - eapply adj_perm in H as H3.
      -- destruct H3 as [KK2].
         eapply perm_invert in H3 as H4.
         --- eapply IHmerge in H4.
             eapply merge_r.
             ---- apply H3.
             ---- apply H0.
             ---- apply H4.
         --- apply H2.
         --- apply H.
      -- apply H2.
  Qed.

  Theorem perm_merge_3 : forall J K L LL,
      merge J K L ->
      perm L LL ->
      merge J K LL.
  Proof.
    intros. generalize dependent LL.
    induction H;intros.
    - apply perm_nil_1 in H0;subst. apply merge_nil.
    - eapply adj_perm_result in H2 as H0a.
      -- destruct H0a as [KK [H3 H4]].
         eapply IHmerge in H4 as H5.
         eapply merge_l.
         --- apply H.
         --- apply H3.
         --- apply H5.
      -- apply H0.
    - eapply adj_perm_result in H2 as H0a.
      -- destruct H0a as [KK' [H3 H4]].
         eapply IHmerge in H4 as H5.
         eapply merge_r.
         --- apply H.
         --- apply H3.
         --- apply H5.
      -- apply H0.
  Qed.

  Theorem merge_sym : forall J K L,
      merge J K L ->
      merge K J L.
  Proof.
    intros.
    induction H.
    - apply merge_nil.
    - eapply merge_r.
      -- apply H.
      -- apply H0.
      -- apply IHmerge.
    - eapply merge_l.
      -- apply H.
      -- apply H0.
      -- apply IHmerge.
  Qed.

    (** Something weird is happening, regarding induction again. There are 3 cases for the Abella proof, but not here. Also, we don't know anything about [adj K].
      - Fixed: [remember nil]
   *)

  Theorem merge_nil_perm : forall K L,
      merge nil K L -> perm K L.
  Proof.
    intros. remember nil.
    induction H.
    - apply perm_nil.
    - subst.
      inversion H.
    - apply IHmerge in Heql as IH.
      eapply perm_split.
      -- apply H.
      -- apply H0.
      -- apply IH.
  Qed.

  (** *** Theorems about [merge] and [adj] *)

  Theorem merge_adj_1 : forall A JJ J K LL,
      merge JJ K LL -> adj JJ A J -> exists L, adj LL A L /\ merge J K L.
  Proof.
    intros.
    exists (A :: LL).
    split.
    - apply adj_hd.
    - eapply merge_l.
      apply H0.
      apply adj_hd.
      apply H.
  Qed.

  Theorem merge_unadj_1 : forall J K L JJ A,
      merge J K L -> adj JJ A J -> exists LL, adj LL A L /\ merge JJ K LL.
  Proof.
    intros. generalize dependent A. generalize dependent JJ.
    induction H;intros.
    - inversion H0.
    - inversion H0;subst.
      -- eapply adj_same_result_diff in H2.
         --- destruct H2 as [[H2a H2b] | H2c].
  (* induction on 1. intros. case H1.
  case H2.
  apply adj_same_result_diff to H2 H3. case H6.
    apply perm_sym to *H7. apply perm_merge_1 to *H5 *H8. search.
    apply IH to *H5 H7. apply adj_swap to H8 H4. apply adj_swap to H7 H3.
     assert merge U1 K U. apply adj_same_result to H13 H2.
     apply perm_merge_1 to *H14 *H15. search.
  apply IH to H5 H2. apply adj_swap to H6 H4. assert merge JJ K U. search.
   *)
  Admitted.

  Theorem merge_adj_2 : forall A J KK K LL,
      merge J KK LL -> adj KK A K -> exists L, adj LL A L /\ merge J K L.
  Proof.
  (* intros.
apply adj_2_is_o to H2. apply merge_3_is_list to H1.
apply adj_exists to *H3 *H4.
search. *)
  intros.
  exists (A :: LL).
  split.
  - apply adj_hd.
  - eapply merge_r.
    -- apply H0.
    -- apply adj_hd.
    -- apply H.
  Qed.

  Theorem merge_unadj_2 : forall J K L KK A,
      merge J K L -> adj KK A K -> exists LL, adj LL A L /\ merge J KK LL.
  Proof.
    intros.
    apply merge_sym in H.
    eapply merge_unadj_1 in H0 as [LL [H0a H0b]].
    - exists LL. split.
      -- apply H0a.
      -- apply merge_sym in H0b. apply H0b.
    - apply H.
  Qed.

  Theorem merge_unadj_3 : forall J K L LL A,
      merge J K L -> adj LL A L ->
      (exists JJ, adj JJ A J /\ merge JJ K LL)
      \/ (exists KK, adj KK A K /\ merge J KK LL).
  Proof.

  (* Long one:

induction on 1. intros. case H1.
  case H2.

  apply adj_same_result_diff to H4 H2. case H6.
    apply perm_merge_3 to *H5 *H7. search.
    apply adj_swap to H7 H2. apply adj_same_result to H9 H4.
     apply adj_perm to H10 H8. apply IH to H5 H11. case H12.
       apply adj_swap to H13 H3.
        assert merge U1 K LL.
          apply adj_swap to H11 H4.
          apply adj_same_result to H18 H2.
          backchain perm_merge_3.
        search.
       apply adj_swap to H11 H4.
        assert merge J KK2 U1.
        apply adj_same_result to H16 H2. apply perm_merge_3 to *H17 *H18.
        search.

  apply adj_same_result_diff to H4 H2. case H6.
    apply perm_merge_3 to *H5 *H7. search.
    apply adj_swap to H7 H2. apply adj_same_result to H9 H4.
     apply adj_perm to H10 H8. apply IH to H5 H11. case H12.
       apply adj_swap to H11 H4.
        assert merge JJ K U1.
        apply adj_same_result to H16 H2. apply perm_merge_3 to *H17 *H18.
        search.
       apply adj_swap to H13 H3.
        assert merge J U1 LL.
          apply adj_swap to H11 H4.
          apply adj_same_result to H18 H2.
          backchain perm_merge_3.
        search.
   *)
  Admitted.

  (** *** Consequences of merge and adj *)
  Theorem merge_invert_1 : forall A JJ J K LL L,
      merge J K L ->
      adj JJ A J ->
      adj LL A L ->
      merge JJ K LL.
  Proof.
    intros.
    apply merge_unadj_1 with (JJ := JJ) (A := A) in H as [LL1 [H2a H2b]].
    apply adj_same_result with (K := LL) in H2a.
    apply perm_merge_3 with (L := LL1).
    - apply H2b.
    - apply H2a.
    - apply H1.
    - apply H0.
  Qed.

  Theorem merge_invert_2 : forall A J KK K LL L,
      merge J K L ->
      adj KK A K ->
      adj LL A L ->
      merge J KK LL.
  Proof.
    intros.
    apply merge_sym in H.
    apply merge_sym.
    eapply merge_invert_1.
    - apply H.
    - apply H0.
    - apply H1.
  Qed.

  Theorem merge_move_12 : forall A JJ J KK K L,
      adj JJ A J ->
      adj KK A K ->
      merge J KK L ->
      merge JJ K L.
  Proof.
    intros.
    eapply merge_unadj_1 in H1 as [LL [H1a H1b]].
    eapply merge_r. apply H0. apply H1a. apply H1b. apply H.
  Qed.

  Theorem merge_move_21 : forall A JJ J KK K L,
      adj JJ A J ->
      adj KK A K ->
      merge JJ K L ->
      merge J KK L.
  Proof.
    intros.
    eapply merge_unadj_2 in H1 as [LL [H1a H1b]].
    eapply merge_l. apply H. apply H1a. apply H1b. apply H0.
  Qed.

  (** ** [add_to_merge] *)

  Theorem add_to_merge_right : forall A J K KK L,
      adj KK A K ->
      merge J KK L ->
      exists M, merge J K M /\ adj L A M.
  Proof.
    intros.
    exists (A :: L). split.
    - eapply merge_r. apply H. apply adj_hd. apply H0.
    - apply adj_hd.
  Qed.

  Theorem add_to_merge_left : forall A J JJ K L,
      adj JJ A J ->
      merge JJ K L ->
      exists M, merge J K M /\ adj L A M.
  Proof.
    intros.
    exists (A :: L). split.
    - eapply merge_l. apply H. apply adj_hd. apply H0.
    - apply adj_hd.
  Qed.

  Theorem merge_nil_equal : forall L,
      merge nil L L.
  Proof.
    intros.
    induction L.
    - apply merge_nil.
    - eapply merge_r.
      apply adj_hd.
      apply adj_hd.
      apply IHL.
  Qed.

  Theorem merge_exists : forall J K,
    exists L, merge J K L.
  Proof.
    intros.
    induction J.
    - exists K. apply merge_nil_equal.
    - destruct IHJ as [X]. exists (a :: X).
      eapply merge_l.
      -- apply adj_hd.
      -- apply adj_hd.
      -- apply H.
  Qed.

  Theorem merge_head_lemma : forall L A,
      merge L (A :: nil) (A :: L).
  Proof.
    intros.
    induction L as [| Y L'].
    - apply merge_nil_equal.
    - eapply add_to_merge_left in IHL' as [M [IHa IHb]].
      eapply merge_r.
      -- apply adj_hd.
      -- apply adj_hd.
      -- apply merge_sym. apply merge_nil_equal.
      -- apply adj_hd. Unshelve. apply A.
  Qed.

  (** Note: the contrary is not true, since adj is order-sensitive *)
  Theorem adj_implies_merge : forall L J A,
      adj L A J -> merge L (A :: nil) J.
  Proof.
    intros.
    induction H.
    - apply merge_head_lemma.
    - eapply merge_l.
      -- apply adj_hd.
      -- apply adj_hd.
      -- apply IHadj.
  Qed.


  (** *** Associativity of [merge] *)
  Theorem merge_assoc : forall J K L JK KL JKL1 JKL2,
      merge J K JK -> merge K L KL ->
      merge J KL JKL1 -> merge JK L JKL2 ->
      perm JKL1 JKL2.
  Proof.
  (* induction on 1. intros. case H1.
    apply merge_nil_perm to *H2. apply merge_nil_perm to *H3. apply merge_nil_perm to *H4.
    backchain perm_trans with K = L. backchain perm_sym. backchain perm_trans.

    apply merge_unadj_1 to *H4 H6.
    apply merge_unadj_1 to *H3 H5.
    apply IH to *H7 *H2 *H11 *H9.
    search.

    apply merge_unadj_1 to *H2 H5.
    apply merge_unadj_1 to *H4 H6.
    apply merge_unadj_2 to *H3 H8.
    apply IH to *H7 *H9 *H13 *H11.
    search. *)
  Admitted.

  Theorem change_merge_order : forall J K L JK KL JKL,
      merge JK L JKL -> merge J K JK -> merge K L KL ->
      merge J KL JKL.
  Proof.
  (* intros.
    apply merge_1_is_list to H2. apply merge_3_is_list to H3.
    apply merge_exists to H4 H5.
    apply merge_assoc to H2 H3 H6 H1.
    apply perm_merge_3 to H6 H7.
    search. *)
  Admitted.

  Theorem change_merge_order2 : forall J K JK L KL JKL,
      merge J K JK -> merge K L KL -> merge J KL JKL ->
      merge JK L JKL.
  Proof.
  (* intros.
  apply merge_3_is_list to H1. apply merge_2_is_list to H2.
  apply merge_exists to *H4 *H5.
  apply merge_assoc to *H1 *H2 *H3 H6. apply perm_sym to *H7.
  backchain perm_merge_3. *)
  Admitted.

  Theorem merge_perm_det : forall J K L1 L2,
      merge J K L1 ->
      merge J K L2 ->
      perm L1 L2.
  Proof.
  (* induction on 1. intros. case H1.
    backchain merge_nil_perm.
    apply merge_unadj_1 to H2 H3.
    apply IH to H5 H7.
    search.
    apply merge_unadj_2 to H2 H3.
    apply IH to H5 H7.
    search. *)
  Admitted.

  Theorem merge_preserves_perm_lem : forall L LL J K,
      merge L J K ->
      merge LL J K ->
      perm L LL.
  Proof.
  (* induction on 1. intros. case H1.
    apply merge_sym to H2. apply merge_nil_perm to *H4.
    apply merge_sym to H3. apply merge_nil_perm to *H6.
    apply perm_sym to *H7. backchain perm_trans.
    apply merge_unadj_2 to H2 _. apply merge_unadj_2 to H3 _.
    apply adj_same_result to H8 H6.
    apply perm_merge_3 to *H9 *H10.
    apply IH to *H5 *H7 *H11. search. *)
  Admitted.

  Theorem merge_preserves_perm : forall L LL J K,
      merge L J K ->
      merge LL J K ->
      perm L LL.
  Proof.
  (* intros. apply merge_2_is_list to H1.
    backchain merge_preserves_perm_lem. *)
  Admitted.

  Theorem merge_sub : forall J K L JK JL JKL,
      merge J K JK ->
      merge JK L JKL ->
      merge JL K JKL ->
      merge J L JL.
  Proof.
  (* intros.
    apply merge_1_is_list to H1. apply merge_2_is_list to H2.
    apply merge_exists to H4 H5.
    apply merge_sym to H1.
    apply merge_2_is_list to H1. apply merge_3_is_list to H6.
    apply merge_exists to H8 H9.
    apply merge_assoc to H7 H6 H10 H2.
    apply merge_sym to H10.
    apply perm_merge_3 to H12 H11.
    apply merge_preserves_perm to H13 H3.
    apply perm_merge_3 to H6 H14.
    search. *)
  Admitted.


  Theorem merge_to_adj : forall J L A,
      merge J (A :: nil) L ->
      exists JJ, perm J JJ /\ adj JJ A L.
  Proof.
    intros.
  (* induction on 1. intros. case H1.
    apply IH to H4. apply adj_swap to H6 H3. search.
    apply adj_det to H2. apply merge_sym to H4.
    apply merge_nil_perm to H5. search. *)
  Admitted.

  Theorem merge_same_result_diff : forall J A K B L,
      merge J (A :: nil) L ->
      merge K (B :: nil) L ->
      (A = B /\ perm J K) \/
        exists KK, merge KK (A :: nil) K.
  Proof.
  (* intros.
    apply merge_to_adj to H1.
    apply merge_to_adj to H2.
    apply adj_same_result_diff to H4 H6.
    case H7.
    apply perm_trans to H3 H8. apply perm_sym to H5.
    apply perm_trans to H9 H10. search.
    apply adj_implies_merge to H8. apply perm_sym to H5.
    apply perm_merge_3 to H9 H10. search. *)
  Admitted.

  (** *** Subsets

  In abella,

<<
  Define subset : olist -> olist -> prop by
  subset J L := exists K, merge J K L.
>>

  TBD: rewrite

  *)

  Inductive subset : list o -> list o -> Prop :=
  | subset_e : forall J L K, merge J K L  -> subset J L.

End merge_abella.

End lists_abella.

(** * Proof of concept: MLL using lists-modulo permutation *)
Module PL.

  (** * Formulas *)
  Inductive formula : Set :=
  | bot
  | one
  | atom : nat -> formula
  | natom : nat -> formula
  | tens : formula -> formula -> formula
  | par : formula -> formula -> formula.

  Theorem LForm_dec_eq : forall F G : formula, {F = G} + {F <> G}.
  Admitted.

  Module F_dec <: Eqset_dec.
    Definition Eqset_T := formula.
    Definition eqA_dec := LForm_dec_eq.
  End F_dec.

  Declare Module LMPFormulas : lists_abella F_dec.
  Export LMPFormulas.

  Fixpoint negation (A : formula) : formula :=
    match A with
    | bot => one
    | one => bot
    | atom v => natom v
    | natom v => atom v
    | tens A B => par (negation A) (negation B)
    | par A B => tens (negation A) (negation B)
    end.

  (** * Context representation *)
  Definition ctx := list formula.

  (*

Define mll : olist -> prop by
; mll L :=
    exists A, adj (natom A :: nil) (atom A) L

; mll L :=
    exists A B LL JJ KK J K,
      adj LL (tens A B) L /\
      merge JJ KK LL /\
      adj JJ A J /\ mll J /\
      adj KK B K /\ mll K

; mll (one :: nil)

; mll L :=
    exists A B LL J K,
      adj LL (par A B) L /\
      adj LL A J /\
      adj J B K /\
      mll K

; mll L :=
    exists LL,
      adj LL bot L /\
      mll LL
.

   *)

  (** * Inference rules *)
  Reserved Notation " '|-' B " (at level 80).
  Inductive mll : ctx -> Prop :=
  | rules_id : forall L A, adj (natom A :: nil) (atom A) L -> mll L
  | rules_tens : forall L A B LL JJ KK J K,
      adj LL (tens A B) L ->
      merge JJ KK LL ->
      adj JJ A J -> mll J ->
      adj KK B K -> mll K -> mll L
  | rules_one : mll ([one])
  | rules_par : forall L A B LL J K,
      adj LL (par A B) L ->
      adj LL A J ->
      adj J B K ->
      mll K ->
      mll L
  | rules_bot : forall L LL,
      adj LL bot L -> mll LL -> mll L
    where " '|-' B " := (mll B).

  (** ** Example derivations *)

  (** Interesting things:
      - [rules_par] can be applied in many ways due to how [adj] works.
      If you apply [rules_par] using [eapply] (without specifying arguments), you actually end up reversing the list.
      But the hypothesis we have is in a different order (is sorted).
      So it's important to be explicit about how you want the resulting list order to be afterwards.
      (Well, that is, if you don't have the exchange theorem yet.)
   *)

  Example a1_par_a2_a3_par_a4_1 : forall A1 A2 A3 A4,
        |- [A1 ; A2 ; A3 ; A4] -> |- [par A1 A2; par A3 A4].
  Proof.
    intros.
    eapply rules_par with (K := [A1 ; A2 ; par A3 A4]).
    - apply adj_hd.
    - apply adj_hd.
    - apply adj_tl. apply adj_hd.
    - eapply rules_par with (J := [A1; A2; A3]) (K := [A1; A2; A3; A4]).
    -- apply adj_tl. apply adj_tl. apply adj_hd.
    -- apply adj_tl. apply adj_tl. apply adj_hd.
    -- apply adj_tl. apply adj_tl. apply adj_tl. apply adj_hd.
    -- apply H.
  Qed.

  (** ** Metatheorems *)
  (** *** Negation *)

  Fixpoint dual F :=
    match F with
    | atom A => natom A
    | natom A => atom A
    | tens A' B' => par (dual A') (dual B')
    | par A' B' => tens (dual A') (dual B')
    | one => bot
    | bot => one
    end.

  Inductive dual_rel : formula -> formula -> Prop :=
  | dual_atom_natom    : forall A, dual_rel (atom A) (natom A)
  | dual_one_bot : dual_rel one bot
  | dual_par_tens : forall A nA B nB, dual_rel A nA -> dual_rel B nB -> dual_rel (par A B) (tens nA nB).

  Theorem dual_comm : forall A B, dual_rel A B -> dual_rel B A.
  Admitted.

  Theorem dual_involutive : forall A, dual (dual A) = A.
  Proof.
    intros.
    induction A;try reflexivity.
    - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
    - simpl. rewrite IHA1. rewrite IHA2. reflexivity.
  Qed.

  Theorem dual_rel_dual_1 : forall A, dual_rel A (dual A).
  Proof.
    intros.
    induction A.
    - simpl. apply dual_comm. apply dual_one_bot.
    - simpl. apply dual_one_bot.
    - simpl. apply dual_atom_natom.
    - simpl. apply dual_comm. apply dual_atom_natom.
    - simpl. apply dual_comm. apply dual_par_tens.
      -- apply dual_comm. apply IHA1.
      -- apply dual_comm. apply IHA2.
    - simpl. apply dual_par_tens.
      -- apply IHA1.
      -- apply IHA2.
  Qed.

  Theorem dual_dual_rel : forall A B, dual A = B -> dual_rel A B.
  Proof.
    intros. subst. apply dual_rel_dual_1.
  Qed.

  Theorem dual_rel_inv : forall A B, dual_rel A B -> dual A = B.
  Proof.
    intros.
    induction H.
    - reflexivity.
    - reflexivity.
    - simpl. rewrite <- IHdual_rel1.  rewrite <- IHdual_rel2. reflexivity.
  Qed.

  (** ** Identity *)
  Theorem Identity : forall A B, dual_rel A B -> |- [A; B].
  Proof.
    intros.
    induction H.
    - apply rules_id with (A := A). apply adj_hd.
    - apply rules_bot with (LL := [one]).
      apply adj_tl. apply adj_hd.
      apply rules_one.
    - eapply rules_par with (A := A) (B := B) (LL := [tens nA nB]).
      -- apply adj_hd.
      -- apply adj_tl. apply adj_hd.
      -- apply adj_hd.
      -- eapply rules_tens with (A := nA) (B := nB).
         --- apply adj_tl. apply adj_hd.
         --- eapply merge_r with (A := B) (L := [B; A]).
             ---- apply adj_hd.
             ---- apply adj_hd.
             ---- eapply merge_l with (A := A).
                  ----- apply adj_hd.
                  ----- apply adj_hd.
                  ----- apply merge_nil.
         --- apply adj_tl. apply adj_hd.
         --- apply IHdual_rel1.
         --- apply adj_tl. apply adj_hd.
             --- apply IHdual_rel2.
  Qed.

  (** ** Exchange *)
  Theorem Exchange : forall K L,
      |- K -> perm K L -> |- L.
  Proof.
    intros. generalize dependent L.
    induction H;intros.
    (* id *)
    - inversion H;subst.
      -- apply perm_cons_1 in H0 as [J [H1a H1b]].
         apply perm_cons_1 in H1b as [J1 [H2a H2b]].
         inversion H2b;subst.
         --- inversion H2a;subst. eapply rules_id. apply H1a.
         --- inversion H0.
      -- apply perm_cons_1 in H0 as [J [H1a H1b]].
         apply adj_nil_1 in H5; subst.
         apply perm_cons_1 in H1b as [J1 [H2a H2b]].
         apply adj_swap with (J := J1) (A := atom A) (K := J) (B := natom A) (L := L0) in H2a as [U [H3a H3b]].
         --- apply perm_nil_1 in H2b; subst. apply adj_nil_1 in H3a; subst.
         eapply rules_id. apply H3b.
         --- apply H1a.
    (* tens *)
    - rename K into K1.
      assert (perm J (A :: JJ)). {
        eapply perm_split.
        * apply H1.
        * apply adj_hd.
        * apply perm_refl.
      }
      assert (perm K1 (B :: KK)). {
        eapply perm_split.
        * apply H3.
        * apply adj_hd.
        * apply perm_refl.
      }
      apply IHmll1 in H6.
      apply IHmll2 in H7.
      rename L into K. rename L0 into L.
      apply adj_perm_full with (J := K) (K := L) in H as [KK1 [H8a H8b]].
      -- apply perm_merge_3 with (L := LL) (LL := KK1) in H0.
         --- eapply rules_tens.
             ---- apply H8a.
             ---- apply H0.
             ---- apply H1.
             ---- apply H2.
             ---- apply H3.
             ---- apply H4.
         --- apply H8b.
      -- apply H5.
    (* one *)
    - inversion H0;subst.
      inversion H;subst.
      -- apply perm_nil_1 in H2;subst. apply adj_nil_1 in H1;subst.
         apply rules_one.
      -- inversion H6.
    (* par *)
    - rename K into K1. rename L into K. rename L0 into L.
      apply adj_perm_full with (K := L) (JJ := LL) (A := par A B) (J := K) in H as [KK [H4a H4b]].
      assert (perm J (A :: KK)). {
        eapply perm_split. apply H0. apply adj_hd. apply H4b.
      }
      assert (perm K1 (B :: A :: KK)). {
        eapply perm_split. apply H1. apply adj_hd. apply H.
      }
      apply IHmll in H4.
      eapply rules_par.
      -- apply H4a.
      -- apply adj_hd.
      -- apply adj_hd.
      -- apply H4.
      -- apply H3.
    (* bot *)
    - rename L into K. rename L0 into L.
      apply adj_perm_full with (K := L) (JJ := LL) (A := bot) (J := K) in H as [KK [H2a H2b]].
      -- apply IHmll in H2b.
         eapply rules_bot.
         --- apply H2a.
         --- apply H2b.
      -- apply H1.
  Qed.

End PL.
