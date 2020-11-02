Require Import LanguageUtil.
Require Import BasicProperties.
Require Import Extraction.

Lemma notin_fv_open_rec : forall x e1 e2 n,
    x # e1 <n> ^^ e2 -> x # e1.
Proof.
  intros. generalize dependent n. induction e1; simpl; intros; eauto.
Qed.

Lemma notin_fv_open_var : forall x e y,
    x # e ^` y -> x # e.
Proof.
  eauto using notin_fv_open_rec.
Qed.

Lemma notin_fv_open : forall x e1 e2,
    x # e1 ^^ e2 -> x # e1.
Proof.
  eauto using notin_fv_open_rec.
Qed.

Hint Resolve notin_fv_open : core.

Lemma fresh_ctx_fresh_expr : forall Γ a A x,
    Γ ⊢ a : A -> x `notin` dom Γ -> x # a.
Proof.
  intros. generalize dependent x.
  dependent induction H; intros; auto 3; simpl.
  - induction G.
    + inversion H0.
    + destruct a. inversion H. subst.
      destruct H0.
      * inversion H0. subst. simpl in H1. auto.
      * apply IHG; auto.
  - pick fresh x0. apply notin_union_3. auto.
    eapply notin_fv_open_var. apply H3; auto.
  - pick fresh x0. apply notin_union_3. auto.
    eapply notin_fv_open_var. apply H3; auto.
  - pick fresh x0. apply notin_union_3; auto.
    eapply notin_fv_open_var. apply H3; auto.
  - pick fresh x0. apply notin_union_3; auto.
    eapply notin_fv_open_var. apply H2; auto.
  - pick fresh x0. apply notin_union_3; auto.
    eapply notin_fv_open_var. apply H4; auto.
  - pick fresh x0. apply notin_union_3; auto.
    eapply notin_fv_open_var. apply H1; auto.
Qed.

Lemma fresh_ctx_fresh_expr_l : forall Γ a b A x,
    Γ ⊢ a <: b : A -> x `notin` dom Γ -> x # a.
Proof.
  intros.
  apply reflexivity_l in H. eauto 2 using fresh_ctx_fresh_expr.
Qed.

Lemma fresh_ctx_fresh_expr_r : forall Γ a b A x,
    Γ ⊢ a <: b : A -> x `notin` dom Γ -> x # b.
Proof.
  intros.
  apply reflexivity_r in H. eauto 2 using fresh_ctx_fresh_expr.
Qed.

Lemma fresh_ctx_fresh_type : forall Γ e1 e2 A x,
    Γ ⊢ e1 <: e2 : A -> x `notin` dom Γ -> x # A.
Proof.
  intros * Sub. induction Sub; intros; simpl in *;
                  eauto 3 using fresh_ctx_fresh_expr.
  - induction G.
    + auto.
    + destruct a. inversion H. subst. destruct H0.
      * inversion H0. subst. eapply fresh_ctx_fresh_expr; eauto.
      * eapply IHG; eauto.
  - pick fresh x'. apply notin_union_3; eauto using fresh_ctx_fresh_expr.
  - apply fresh_open; eauto 3 using fresh_ctx_fresh_expr.
    specialize (IHSub2 H0). auto.
  - pick fresh x'. apply notin_union_3; eauto using fresh_ctx_fresh_expr.
Qed.

Ltac solve_simple_freshness :=
  match goal with
  | _ : ?x `notin` dom ?Γ |- ?x # ?e =>
    match goal with
    | _ : Γ ⊢ e <: _ : _ |- _ => eapply fresh_ctx_fresh_expr_l; eassumption
    | _ : Γ ⊢ _ <: e : _ |- _ => eapply fresh_ctx_fresh_expr_r; eassumption
    | _ : Γ ⊢ _ <: _ : e |- _ => eapply fresh_ctx_fresh_type; eassumption
    end
  end
.

Hint Extern 1 (_ # _) => solve_simple_freshness : core.

Lemma fresh_binded : forall Γ1 x A Γ2,
    ⊢ Γ1 , x : A ,, Γ2 -> x # A.
Proof.
  induction Γ2; simpl; intros.
  - inversion H. subst. eapply fresh_ctx_fresh_expr; eauto.
  - apply IHΓ2. now inversion H.
Qed.


Lemma notin_dom_bind_fresh : forall Γ x A x',
    x' `notin` dom Γ -> x : A ∈ Γ -> ⊢ Γ -> x' # A.
Proof.
  induction Γ; simpl; intros.
  - inversion H0.
  - destruct a. inversion H1. subst. destruct H0.
    + inversion H0. subst. destruct (eq_dec x' x);
        eauto using fresh_ctx_fresh_expr.
    + apply IHΓ with x; auto.
Qed.

Lemma notin_open_var_notin_open_rec : forall e x n,
    x `notin` fv_eexpr (e ⋆n^^ (ee_var_f x)) ->
    forall v, e ⋆n^^ v = e.
Proof.
  intros e x.
  induction e; unfold open_eexpr_wrt_eexpr in *; simpl; intros; auto;
    try solve [rewrite IHe; auto | rewrite IHe1; auto; rewrite IHe2; auto].
  - destruct (n0 == n).
    + contradict H. simpl. auto.
    + easy.
Qed.

Lemma notin_open_var_notin_open : forall e x v,
    x `notin` fv_eexpr (e ⋆^` x) ->
    e ⋆^^ v = e.
Proof.
  intros.
  eapply notin_open_var_notin_open_rec; auto.
Qed.
