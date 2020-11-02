Require Import KindProperties.
Require Import LanguageUtil.
Require Import Properties.
Require Import BoxReasoning.

Theorem gen_head_kind_uniqueness : forall Γ e A k,
    Γ ⊢ e : A -> forall n B, head_kind A k n -> Γ ⊢ e : B -> head_kind B k n.
Proof.
  intros Γ e A k Hsub.
  dependent induction Hsub; intros n' B' Hk Hsubr.
  - eapply head_kind_var_consistent; eauto.
  - inversion Hk.
  - apply star_type_inversion in Hsubr. subst. assumption.
  - apply int_of_star in Hsubr. subst. assumption.
  - dependent induction Hsubr.
    + inversion Hk. subst. constructor. pick fresh x.
      eapply head_kind_invert_subst_var.
        eapply H2 with x; eauto.
    + eauto 3 using head_kind_sub_r.
  - dependent induction Hsubr.
    + pick fresh x. apply H2 with x; auto 2.
    + eauto 3 using head_kind_sub_r.
  - dependent induction Hsubr.
    + apply head_kind_invert_subst in Hk as [|].
      * destruct k.
        ++ eapply head_kind_star_of_box in Hsubr1; eauto 2. subst.
           now apply pi_box_impossible in Hsubr2.
        ++ now apply head_kind_box_never_welltype with (n := n') in Hsubr1.
      * assert (head_kind (e_pi A0 B0) k (S n')) by eauto 3.
        inversion H2. subst.
        now apply head_kind_subst.
    + eauto 3 using head_kind_sub_r.
  - dependent induction Hsubr.
    + inversion Hk; constructor.
    + eauto 3 using head_kind_sub_r.
  - dependent induction Hsubr.
    + assumption.
    + eauto 3 using head_kind_sub_r.
  - dependent induction Hsubr. assumption. eauto 3 using head_kind_sub_r.
  - destruct k.
    + conclude_type_refl Hsub2. inversion H.
      box_reasoning. assert False by eauto using expr_of_box_never_be_reduced'.
      contradiction.
    + conclude_type_refl Hsub2. inversion H.
      assert False by eauto using box_never_be_reduced.
      contradiction.
  - dependent induction Hsubr; eauto 3 using head_kind_sub_r.
  - dependent induction Hsubr; eauto 3 using head_kind_sub_r.
  - dependent induction Hsubr; eauto 3 using head_kind_sub_r.
  - eauto 3 using head_kind_sub_l.
Qed.


Corollary gen_kind_uniqueness : forall Γ e A k,
    Γ ⊢ e : (e_kind k) -> Γ ⊢ e : A -> A = e_kind k.
Proof.
  intros.  assert (head_kind A k 0).
  apply gen_head_kind_uniqueness with Γ e (e_kind k); eauto.
  now inversion H1.
Qed.

Corollary kind_uniqueness : forall Γ e k1 k2,
    Γ ⊢ e : e_kind k1 -> Γ ⊢ e : e_kind k2 -> k1 = k2.
Proof.
  intros.
  assert (e_kind k1 = e_kind k2) by
    (eapply gen_kind_uniqueness; eauto).
  now inversion H1.
Qed.
