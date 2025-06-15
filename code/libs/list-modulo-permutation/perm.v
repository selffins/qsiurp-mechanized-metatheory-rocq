(** Coq version of abella-reasoning/lib/perm.thm *)

(** Members
    [ ] 1. adj
    - adj_exists
    - adj_swap
    - adj_same
    - adj_append_1 / adj_1_append

    [ ] 2. perm
    - perm_refl
    - perm_sym
    - perm_cons
    - adj_preserves_perm
    - perm_trans_lem
    - perm_trans
    - adj_same_source
    - adj_same_result
    - adj_same_result_diff
    - adj_same_result_diff_both
    - perm_invert
    - adj_perm_source
    - adj_nil_1
    - perm_nil_1
    - adj_det
    - perm_singleton

    [ ] 3. append and perm
    - append_perm
    - adj_perm
    - adj_perm_full

    [ ] 4. set theoretic semantics of adj and perm
    - adj_member
    - member_adj
    - member_adj_rel
    - adj_preserves_member_lem
    - adj_preserves_member
    - perm_preserves_member
*)


(** TBD: move perm module from the olist.v file into here. *)
