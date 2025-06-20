(** For now, 1 file contains all the modules. *)

(** ##########################################

                     olist.v

    ##########################################

    Coq version of abella-reasoning/lib/list.thm
 *)

(** Contains:
    * means my addition

    1. append_rel
       + equivalences to append
    2. rev_rel
       + equivalences to rev
    3. can_append
    4. can_rev

    In the abella style, append and rev are relational, so we have relational append and rev as well in Coq.
 **)

From Stdlib Require Export Sets.Multiset.
From Stdlib Require Export List.
Export ListNotations.

Module lists_abella.

  Definition o := nat.

  Inductive append_rel : list o -> list o -> list o -> Prop :=
  | append_nil (L : list o): append_rel [] L L
  | append_cons e J K L (H : append_rel J K L): append_rel (e :: J) K (e :: L).

  Example append_rel_12_34_1234 :
    append_rel ([1 ; 2]) ([3 ; 4]) ([1 ; 2 ; 3 ; 4]).
  Proof.
    apply append_cons.
    apply append_cons.
    apply append_nil.
  Qed.

  Example append_rel_12_nil_12 :
    append_rel ([1; 2]) ([]) ([1; 2]).
  Proof.
    apply append_cons.
    apply append_cons.
    apply append_nil.
  Qed.

  Example append_rel_12_nil_13_fail :
    not (append_rel ([1 ; 2]) [] ([1 ; 3])).
  Proof.
    unfold not.
    intros.
    inversion H;subst.
    inversion H3;subst.
  Qed.

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

  Inductive rev_rel : list o -> list o -> Prop :=
  | rev_nil : rev_rel [] []
  | rev_cons e J L (H : exists K, rev_rel J K /\ append_rel K (e :: []) L ) : rev_rel (e :: J) L.

  Example rev_123_321 : rev_rel [1 ; 2 ; 3] [3 ; 2 ; 1].
  Proof.
    eapply rev_cons.
    exists [3 ; 2].
    split.
    - eapply rev_cons.
      exists [3].
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

  Theorem can_rev_rel : forall J, exists K, rev_rel J K.
  Proof.
    intros.
    induction J as [ | j ].
    - exists []. apply rev_nil.
    - destruct IHJ as [L].
      exists (L ++ [j]).
      apply rev_cons.
      exists L.
      split.
      -- apply H.
      -- apply append_append_rel.
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

End lists_abella.

(** ##########################################

                     perm.v

    ##########################################

    Coq version of abella-reasoning/lib/perm.thm
 *)

Module perm_abella.

  Import lists_abella.

  (** Members. * denotes my addition.
      Status: 13/32 admitted

    - adj
    1. adj_exists
    2. *adj_cons_comm_1             [Admitted]
    3. *adj_cons_comm_2             [Admitted]
    4. adj_swap
    5. adj_same                     [Admitted]
    6. adj_append_1 / adj_1_append

    - perm
    7. perm_refl
    8. perm_sym                     [Admitted]
    9. perm_cons_1                  [Admitted]
    10. perm_cons_2
    11. adj_preserves_perm
    12. perm_trans_lem              [Admitted]
    13. perm_trans
    14. adj_same_source             [Admitted]
    15. adj_same_result             [Admitted]
    16. adj_same_result_diff        [Admitted]
    17. adj_same_result_diff_both   [Admitted]
    18. perm_invert                 [Admitted]
    19. adj_perm_source
    20. adj_nil_1
    21. perm_nil_1
    22. adj_det
    23. perm_singleton

    - append and perm
    24. append_perm                 [Admitted]
    25. adj_perm
    26. adj_perm_full

    - set theoretic semantics of adj and perm
    27. adj_member
    28. member_adj
    29. member_adj_rel
    30. adj_preserves_member_lem    [Admitted]
    31, adj_preserves_member
    32. perm_preserves_member

   For some proofs, induction on adj and especially induction on perm does not work.
   We will need to take a look at the inductive principle first...

   *)

  Check rev_rel.
  Locate rev_rel.
  About rev_rel.

  (** ====================== Adj ======================== *)

  Inductive adj : list o -> o -> list o -> Prop :=
  | adj_hd : forall L A, adj L A (A :: L)
  | adj_tl : forall B K A L, adj K A L -> adj (B :: K) A (B :: L).

Check adj_ind.

  (** Note:
      The abella library did not have these commutativity stuff.
      I needed it to prove some theorems, including example adj_1_23_321.
      eI wonder if it cause  something cyclical. I need to try proving them. *)

  Theorem adj_cons_comm_1 : forall A B K C L, adj (A :: B :: K) C L -> adj (B :: A :: K) C L.
  Admitted.

  Theorem adj_cons_comm_2 : forall A B K C L, adj K C (A :: B :: L) -> adj K C (B :: A :: L).
  Admitted.

  Example adj_1_23_123 : adj ([2 ; 3]) 1 ([1 ; 2 ; 3]).
  Proof.
    apply adj_hd.
  Qed.

  Example adj_1_23_213 : adj ([2 ; 3]) 1 ([2 ; 1 ; 3]).
  Proof.
    apply adj_tl.
    apply adj_hd.
  Qed.

  Example adj_1_23_321 : adj ([2 ; 3]) 1 ([3 ; 2 ; 1]).
  Proof.
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
      Here is the Abella proof of adj_swap (annotations e.g. bullet points + comments mine):

      Theorem adj_swap : forall A J K B L, adj J A K -> adj K B L -> exists U, adj J B U /\ adj U A L.

      induction on 2.
      intros.
          - case H2.                                (* Case on adj K B L @ *)
          - case H1.                                (* Case on adj J A K *)
              -- search.                            (* Provide B :: J *)
              -- apply adj_1_is_list to H6.
              search.                               (* Provide B :: B1 :: K1 *)
          - case H1.                                (* Case on adj J A (B1 :: K1) *)
               -- apply adj_3_is_list to H4.
                  search.                           (* Provide L1 *)
               -- apply IH to H6 H4.                (* IH on [K2 A ~ K1], [K1 B ~ L1] gives [K2 B ~ U'] [U' A ~ L1]. *)
              search.                               (* Provide B1 :: U' *)

      Notice how in our version, it is much longer due to the lack of "search" which Abella
      has for free via their definitions. Instead we have to provide the evidence.
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

      Here is the Abella proof of adj_same:

      induction on 1.            (* Induction on adj L A (B :: L) *)
      intros.
      case H1.
      - search.
      - apply IH to H3. search.

      It is short, so I wonder why I couldn't prove it in Coq.
      There is something forgotten when I apply induction.
      We do not seem to have the "H1" that this proof cases on.
      So for now we admit.
 Update: We simply needed to use the remember tactic:
 B :: L isn't of the more generic shape L, which causes induction to forget some structure.
   *)


(*
  Inductive adj : list o -> o -> list o -> Prop :=
  | adj_hd : forall L A, adj L A (A :: L)
  | adj_tl : forall B K A L, adj K A L -> adj (B :: K) A (B :: L).
 *)

  Theorem adj_same : forall A L B, adj L A (B :: L) -> A = B.
  Proof.
  intros. remember (B :: L) as F.
  induction H.
  - inversion HeqF. reflexivity.
  - apply IHadj. inversion HeqF. reflexivity.
  Qed.

  (** Note:

      Here is the Abella proof of adj_append 1:

      induction on 1. intros.
      case H1.
      - case H2.
      -- apply append_2_is_list to H6.
      -- apply append_3_is_list to H6. search.
      - case H2.
      apply IH to H4 H6. search.

      The corresponding proof diverges a little bit from this
      because I leverage append_rel's equivalence with append in Coq.

      append_rel has a "exists' part relating the two appendees(?)
      but append is actually something that constructs such a list.

      We write append_rel (and rev_rel) to have a clearer correspondence with the relational style in Abella.
      It also means only the theorems about append_rel and rev_rel are in the library - there is less clutter.
      Either way, it would be a minor task to change instances of append_rel to append.
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

  (** ====================== Perm ======================== *)

  (**  perm J K : J and K have the same elements *)
  Inductive perm  : list o -> list o -> Prop :=
  | perm_nil : perm nil nil
  | perm_split : forall K L (H: exists A K' L', adj K' A K /\ adj L' A L /\ perm K' L'), perm K L.

  Check perm_ind.
  Print perm_ind.

  Example perm_123_321 : perm [1 ; 2 ; 3] [3 ; 2 ; 1].
  Proof.
    apply perm_split.
    exists 3. exists [1; 2]. exists [2; 1].
    split;try split.
    - apply adj_tl. apply adj_tl. apply adj_hd.
    - apply adj_hd.
    - apply perm_split.
      exists 1. exists [2]. exists [2].
      split;try split.
      -- apply adj_hd.
      -- apply adj_tl. apply adj_hd.
      -- apply perm_split. exists 2. exists nil. exists nil.
         split;try split.
         --- apply adj_hd.
         --- apply adj_hd.
         --- apply perm_nil.
  Qed.

  Theorem perm_refl : forall L, perm L L.
  Proof.
    intros.
    induction L.
    - apply perm_nil.
    - apply perm_split. exists a. exists L. exists L.
      repeat split.
      -- apply adj_hd.
      -- apply adj_hd.
      -- apply IHL.
  Qed.

  Theorem perm_sym : forall K L, perm K L -> perm L K.
  Proof.
    intros.
    induction H.
    - apply perm_nil.
    - destruct H as [A [K' [L' [H1 [H2 H3]]]]].
      apply perm_split.
      exists A. exists L'. exists K'.
      repeat split.
      -- apply H2.
      -- apply H1.
      -- Admitted.


  Theorem perm_cons_1 : forall A K L,
      perm (A :: K) L ->
      exists J, adj J A L /\ perm K J.
  Admitted.

  Theorem perm_cons_2 : forall A K L,
      perm K (A :: L) ->
      exists J, adj J A K /\ perm J L.
  Proof.
    intros.
    apply perm_sym in H.
    apply perm_cons_1 in H.
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
    apply perm_split.
    exists A. exists JJ. exists KK.
    auto.
  Qed.

  Theorem perm_trans_lem : forall J K L, perm J K -> perm K L -> perm J L.
  Proof.
  Admitted. (** Long proof *)

Theorem perm_trans : forall J K L, perm J K -> perm K L -> perm J L.
Proof.
  intros.
  eapply perm_trans_lem.
  apply H.
  apply H0.
Qed.

Theorem adj_same_source : forall J A K L,
    adj J A K -> adj J A L ->
    perm K L.
Proof.

  (** Notes:
      (1) Abella proof is shorter and is quite different from this one. Need to check
      (2) A *lot* of repetition regarding witnesses. Compare to Abella's "search".
      (3) We got stuck at the end. It might be an induction on H instead, which we have not fixed yet,
      or we are missing something. I am using inversion because induction does not work :)
   *)

  intros.
  inversion H;inversion H0;subst.
  - apply perm_refl.
  - apply perm_split.
    exists A. exists (B :: K0). exists (B :: K0).
    repeat split.
    -- apply H.
    -- apply H0.
    -- apply perm_refl.
  - apply perm_split.
    exists B. exists L0. exists (A :: K0).
    repeat split.
    -- apply adj_hd.
    -- apply adj_tl. apply adj_hd.
    -- apply perm_split.
       exists A. exists K0. exists K0.
       repeat split.
       --- apply H1.
       --- apply adj_hd.
       --- apply perm_refl.
  - inversion H6;subst.
    apply perm_split.
    exists B. exists L0. exists L0.
    repeat split.
    3 : {  apply perm_refl. }
    1: { apply adj_hd. }
    Admitted.

Theorem adj_same_result : forall J K A L,
      adj J A L ->
      adj K A L ->
      perm J K.
Proof.
  (** Induction on adj J A L and casing on adj K A L *)
  intros. generalize dependent K.
  induction H;intros.
  - inversion H0;subst.
    -- apply perm_refl.
    -- apply perm_split.
       exists A. exists K0. exists K0.
       repeat split.
       --- apply H3.
       --- apply adj_hd.
       --- apply perm_refl.
  - inversion H0;subst.
    -- apply perm_split. exists B. exists K. exists K.
       repeat split.
       --- apply adj_hd.
       --- apply H.
       --- apply perm_refl.
    -- apply perm_split.
       exists B.
       exists K.
       exists K1.
       repeat split.
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
  (** Induction on adj J A L and casing on adj K B L, giving a witness from IH *)
  intros. generalize dependent K. generalize dependent B.
  induction H; intros.
  - inversion H0;subst.
    -- left. split. reflexivity. apply perm_refl.
    -- right. exists K0. apply adj_hd.
  - inversion H0;subst.
    -- right. exists K. apply H.
    -- apply IHadj in H4. destruct H4 as [[H4a1 H4a2] | H4b1];subst.
       --- left. split.  reflexivity.
           apply perm_split.
           exists B. exists K. exists K1.
           repeat split.
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
  (** Induction on adj J A L and casing on adj K B L*)
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
           ---- left. split. reflexivity. apply perm_split.
                exists B0. exists K. exists K1.
                repeat split.
                ----- apply adj_hd.
                ----- apply adj_hd.
                ----- apply IHa2.
       --- destruct IHb as [X [Y [IHb1 [IHb2 IHb3]]]].
           right. exists (B0 :: X). exists (B0 :: Y).
           repeat split.
           ---- apply adj_tl. apply IHb1.
           ---- apply adj_tl. apply IHb2.
           ---- apply perm_split.
                exists B0. exists X. exists Y.
                repeat split.
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
  (** Induction on perm J K, one casing on adj JJ A J, applying many previous theorems *)
  intros. generalize dependent JJ. generalize dependent A. generalize dependent KK.
  induction H;intros.
  (** Proof in abella:

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
  - inversion H1.
  - destruct H as [B [K' [L' [Ha [Hb Hc]]]]].
    Admitted.

Theorem adj_perm_result : forall J K A JJ,
      perm J K ->
      adj JJ A J ->
      exists KK, adj KK A K /\ perm JJ KK.
Proof.
  intros. generalize dependent JJ.
  induction H;intros.
  - inversion H0.
  - inversion H0;subst.
    -- destruct H as [B [K' [L' [Ha [Hb Hc]]]]].
      apply adj_same_result_diff with (J := JJ) (A := A) in Ha.
      destruct Ha.
      --- destruct H. subst.
          exists L'.
          split.
          ---- apply Hb.
          ---- apply perm_trans with (J := JJ) in Hc;auto.
      --- destruct H as [X].
          apply adj_same_result_diff with (J := L') (A := B) in H.
          destruct H. destruct H;subst.
          exists X. split.
          ---- Admitted.
  (** Induction on perm J K and casing on adj JJ A J *)

  Theorem adj_perm_source : forall J K A L,
      perm J K ->
      adj J A L ->
      exists LL, adj K A LL /\ perm L LL.
  Proof.
    intros.
    exists (A :: K).
    split.
    - apply adj_hd.
    - apply perm_split.
      exists A. exists J. exists K.
      repeat split.
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
    - destruct H0 as [A [K [L' [H1 [H2 H3]]]]].
      inversion H1.
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
    destruct H0 as [B [K [L' [H1 [H2 H3]]]]].
    apply adj_det in H1 as [H1a H1b]. subst.
    apply perm_nil_1 in H3. subst.
    apply adj_nil_1 in H2.
    apply H2.
  Qed.

  (** ================== append and perm ==================== *)

  Theorem append_perm : forall J K L JJ KK,
      append_rel J K L ->
      perm J JJ ->
      perm K KK ->
      exists LL, append_rel JJ KK LL /\ perm L LL.
  Proof.
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

  Theorem adj_perm : forall J K JJ A,
      perm J K ->
      adj JJ A J ->
      exists KK, adj KK A K.
  Proof.
    intros. generalize dependent K.
    induction H0;intros;apply perm_cons_1 in H as [X [Ha Hb]].
    - exists X. apply Ha.
    - apply IHadj in Hb as [KK'].
      eapply adj_swap in Ha as [U [Ha1 Ha2]].
      2 : {  apply H. }
      exists U.
      apply Ha2.
  Qed.

  Theorem adj_perm_full : forall J K JJ A,
      perm J K ->
      adj JJ A J ->
      exists KK, adj KK A K /\ perm JJ KK.
  Proof.
    intros. generalize dependent K.
    induction H0;intros;apply perm_cons_1 in H as [X [Ha Hb]].
    - exists X. split;auto.
    - apply IHadj in Hb as [KK' [IHadj1 IHadj2]].
      eapply adj_swap in Ha.
      2 : { apply IHadj1. }
      destruct Ha as [U [Ha1 Ha2]].
      exists U.
      split.
      -- apply Ha2.
      -- apply perm_split.
         exists B. exists K. exists KK'.
         repeat split.
         --- apply adj_hd.
         --- apply Ha1.
         --- apply IHadj2.
  Qed.

  (** ================== set-theoretic semantics =================== *)

  Locate In.
  (** This section connects the adj relation with the set membership relation,
      which is intuitive - adj L A K says K is L with A inserted "somewhere"
      (i.e. set membership).

     We could use "In" (from Stdlib.Lists) as our set membership relation,
     but we will instead use the member relation from the Abella standard library,
     which is what they used in their implementation.

     Here is how it's defined:

     Type   nil     olist.
     Type   ::      o -> olist -> olist.

     Define member : o -> olist -> prop by
     member A (A :: L);
     member A (B :: L) := member A L.
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
      -- apply IHmember with (B := B0). (**  Need to check abella proof / handwrite *)
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
    induction H0;intros;apply perm_cons_1 in H as [X [Ha Hb]].
    - eapply adj_member.
      apply Ha.
    - apply IHmember in Hb.
      eapply adj_preserves_member.
      apply Hb.
      apply Ha.
  Qed.

End perm_abella.


(** ##########################################

                     merge.v

    ##########################################

    Coq version of abella-reasoning/lib/merge.thm
 *)

(** Contains:
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
 *)
Module merge_abella.

Import lists_abella.
Import perm_abella.

(** ================ Merge ================ *)

(** merge J K L : J union K equals L. *)

(** Define merge : olist -> olist -> olist -> prop by
; merge nil nil nil
; merge J K L :=
    exists A JJ LL,
      adj JJ A J /\ adj LL A L /\ merge JJ K LL
; merge J K L :=
    exists A KK LL,
      adj KK A K /\ adj LL A L /\ merge J KK LL
*)

Inductive merge : list o -> list o -> list o -> Prop :=
| merge_nil : merge nil nil nil
| merge_l J K L (H : exists A JJ LL, adj JJ A J /\ adj LL A L /\ merge JJ K LL) : merge J K L
| merge_r J K L (H : exists A KK LL, adj KK A K /\ adj LL A L /\ merge J K LL) : merge J K L.

(** perm_merge *)
Theorem perm_merge_1 : forall J K L JJ,
  merge J K L ->
  perm J JJ ->
  merge JJ K L.
Proof.
intros. generalize dependent JJ.
induction H;intros.
- inversion H0;subst.
  -- apply merge_nil.
  -- destruct H as [A [K' [L' [Ha [Hb Hc]]]]].
     inversion Ha.
- inversion H0;subst.
  -- destruct H as [A [K' [L' [Ha [Hb Hc]]]]].
     inversion Ha.
  -- destruct H as [A [JJ' [LL' [Ha [Hb Hc]]]]].
     destruct H1 as [A' [K'' [L'' [H1a [H1b H1c]]]]].
     
(** induction on 1. intros.
    case H1.
    - case H2. search.
    - case H3.
      apply adj_perm to H2 H3.
      apply perm_invert to H2 H3 H6.
      apply IH to H5 H7. search.
      apply IH to H5 H2. search. *)
Admitted.

Theorem perm_merge_2 : forall J K L KK,
  merge J K L ->
  perm K KK ->
  merge J KK L.
Proof.
(** induction on 1. intros. case H1.
  case H2. search. case H3.
  apply IH to H5 H2. search.
  apply adj_perm to H2 H3.
   apply perm_invert to H2 H3 H6.
   apply IH to H5 H7. search. *)
Admitted.

Theorem perm_merge_3 : forall J K L LL,
  merge J K L ->
  perm L LL ->
  merge J K LL.
Proof.
(** induction on 1. intros. case H1.
  case H2. search. case H3.
  apply adj_perm_result to H2 H4.
   apply IH to H5 H7. search.
  apply adj_perm_result to H2 H4.
   apply IH to H5 H7. search.
*)
Admitted.

Theorem merge_sym : forall J K L,
  merge J K L ->
  merge K J L.
Proof.
(** induction on 1. intros. case H1.
  search.
  apply IH to H4. search.
  apply IH to H4. search. *)
Admitted.

Theorem merge_nil_perm : forall K L,
  merge nil K L -> perm K L.
Proof.
(** induction on 1. intros. case H1.
  search.
  case H2.
  apply IH to H4. search. *)
Admitted.

(** merge and adj *)
Theorem merge_adj_1 : forall A JJ J K LL,
  merge JJ K LL -> adj JJ A J -> exists L, adj LL A L /\ merge J K L.
Proof.
(** intros.
apply adj_2_is_o to H2. apply merge_3_is_list to H1.
apply adj_exists to *H3 *H4.
search. *)
Admitted.

Theorem merge_unadj_1 : forall J K L JJ A,
  merge J K L -> adj JJ A J -> exists LL, adj LL A L /\ merge JJ K LL.
Proof.
(** induction on 1. intros. case H1.
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
(** intros.
apply adj_2_is_o to H2. apply merge_3_is_list to H1.
apply adj_exists to *H3 *H4.
search. *)
Admitted.

Theorem merge_unadj_2 : forall J K L KK A,
  merge J K L -> adj KK A K -> exists LL, adj LL A L /\ merge J KK LL.
Proof.
(** intros. apply merge_sym to *H1. apply merge_unadj_1 to *H3 *H2.
 apply merge_sym to *H5. search. *)
Admitted.

Theorem merge_unadj_3 : forall J K L LL A,
  merge J K L -> adj LL A L ->
  (exists JJ, adj JJ A J /\ merge JJ K LL)
  \/ (exists KK, adj KK A K /\ merge J KK LL).
Proof.
(** Long one:
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

(** consequences of merge and adj *)
Theorem merge_invert_1 : forall A JJ J K LL L,
  merge J K L ->
  adj JJ A J ->
  adj LL A L ->
  merge JJ K LL.
Proof.
(** intros. apply merge_unadj_1 to H1 H2.
apply adj_same_result to *H4 *H3.
backchain perm_merge_3. *)
Admitted.

Theorem merge_invert_2 : forall A J KK K LL L,
  merge J K L ->
  adj KK A K ->
  adj LL A L ->
  merge J KK LL.
Proof.
(** intros. apply merge_sym to *H1.
apply merge_invert_1 to *H4 *H2 *H3.
backchain merge_sym. *)
Admitted.

Theorem merge_move_12 : forall A JJ J KK K L,
  adj JJ A J ->
  adj KK A K ->
  merge J KK L ->
  merge JJ K L.
Proof.
(** intros. apply merge_unadj_1 to H3 H1.
    search. *)
Admitted.

Theorem merge_move_21 : forall A JJ J KK K L,
  adj JJ A J ->
  adj KK A K ->
  merge JJ K L ->
  merge J KK L.
Proof.
(** intros. apply merge_unadj_2 to H3 H2. search. *)
Admitted.

(** ==== add_to_merge ==== *)

Theorem add_to_merge_right : forall A J K KK L,
  adj KK A K ->
  merge J KK L ->
  exists M, merge J K M /\ adj L A M.
Proof.
(** intros.
  apply adj_2_is_o to H1.
  apply merge_3_is_list to H2.
  apply adj_exists to H3 H4. search. *)
Admitted.

Theorem add_to_merge_left : forall A J JJ K L,
  adj JJ A J ->
  merge JJ K L ->
  exists M, merge J K M /\ adj L A M.
Proof.
(** intros.
  apply adj_2_is_o to H1.
  apply merge_3_is_list to H2.
  apply adj_exists to H3 H4. search. *)
Admitted.

Theorem merge_nil_equal : forall L,
  merge nil L L.
Proof.
(** induction on 1. intros. case H1.
  search.
  apply IH to H3. search. *)
Admitted.

Theorem merge_exists : forall J K,
  exists L, merge J K L.
Proof.
(** induction on 1. intros. case H1.
  apply merge_nil_equal to H2. search.
  apply IH to H4 H2. assert (adj L A (A :: L)).
    apply add_to_merge_left to H6 H5. search. *)
Admitted.

Theorem merge_head_lemma : forall L A,
  merge L (A :: nil) (A :: L).
Proof.
(** induction on 2. intros. case H2 (keep).
  assert (is_list (A :: nil)). apply merge_nil_equal to H3. search.
  assert (adj L1 A1 (A1 :: L1)).
   apply IH to H1 H4.
   apply add_to_merge_left to H5 H6.
   search. *)
Admitted.

(** Note: the contrary is not true, since adj is order-sensitive *)
Theorem adj_implies_merge : forall L J A,
  adj L A J -> merge L (A :: nil) J.
Proof.
(** induction on 1. intros. case H1.
  apply merge_head_lemma to H2 H3. search.
  apply IH to H3.
   apply adj_1_is_list to H3.
   assert (adj K B (B :: K)).
   apply add_to_merge_left to H6 H4.
   apply adj_3_is_list to H3. search. *)
Admitted.

(** ======== Associativity ======== *)

Theorem merge_assoc : forall J K L JK KL JKL1 JKL2,
  merge J K JK -> merge K L KL ->
  merge J KL JKL1 -> merge JK L JKL2 ->
  perm JKL1 JKL2.
Proof.
(** induction on 1. intros. case H1.
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
(** intros.
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
(** intros.
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
(** induction on 1. intros. case H1.
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
(** induction on 1. intros. case H1.
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
(** intros. apply merge_2_is_list to H1.
    backchain merge_preserves_perm_lem. *)
Admitted.

Theorem merge_sub : forall J K L JK JL JKL,
  merge J K JK ->
  merge JK L JKL ->
  merge JL K JKL ->
  merge J L JL.
Proof.
(** intros.
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
(** induction on 1. intros. case H1.
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
(** intros.
    apply merge_to_adj to H1.
    apply merge_to_adj to H2.
    apply adj_same_result_diff to H4 H6.
    case H7.
    apply perm_trans to H3 H8. apply perm_sym to H5.
    apply perm_trans to H9 H10. search.
    apply adj_implies_merge to H8. apply perm_sym to H5.
    apply perm_merge_3 to H9 H10. search. *)
Admitted.

(** ======== subsets ======== *)

(** Define subset : olist -> olist -> prop by
  subset J L := exists K, merge J K L. *)

Inductive subset : list o -> list o -> Prop :=
| subset_e : forall J L (H: exists K, merge J K L), subset J L.

End merge_abella.
