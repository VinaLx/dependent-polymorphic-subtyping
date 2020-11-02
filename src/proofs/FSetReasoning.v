Require Import LanguageUtil.

Import AtomSetProperties.

Lemma notin_subset : forall x s1 s2,
    s1 [<=] s2 -> x `notin` s2 -> x `notin` s1.
Proof.
  intros. intro.
  assert (x `in` s2) by (eapply in_subset; eauto).
  contradiction.
Qed.

Hint Resolve notin_subset : core.

Lemma dom_insert_subset : forall Γ2 Γ1 a (A : expr),
    union (dom Γ2) (dom Γ1) [<=] dom (Γ1 , a : A ,, Γ2).
Proof.
  induction Γ2; simpl; intros.
  - apply subset_add_2. intro. intros.
    now apply empty_union_1 in H.
  - destruct a. intro. intros.
    apply union_add in H.
    assert (add a (union (dom Γ2) (dom Γ1)) [<=] add a (dom (Γ1 , a0 : A ,, Γ2))).
    + apply subset_add_3. auto.
      apply subset_add_2. apply IHΓ2.
    + now apply H0.
Qed.

Lemma fv_subst_inclusion : forall e x v,
    fv_eexpr ([v ⋆/ x] e) [<=] fv_eexpr v `union` fv_eexpr e.
Proof.
  induction e; simpl; intros;
    try solve
        [ auto
        | apply subset_empty
        | destruct (x == x0); simpl;
          solve [apply union_subset_1 | apply union_subset_2]
        ]; (* solves most of the easy cases *)
    (* and here goes the magic *)
    apply union_subset_3; eapply subset_trans; eauto;
      solve
        [ eapply subset_trans;
          [> apply union_subset_1
          |  apply subset_equal; apply union_assoc
          ]
        | eapply subset_trans;
          [> apply union_subset_1
          |  apply subset_equal; eapply equal_trans;
             [> apply union_assoc
             | apply union_equal_2; apply union_sym
             ]
          ]
        ].
Qed.
