Require Import LanguageUtil.

Lemma extract_open_distr_rec : forall e e' n,
    extract (e <n> ^^ e') = extract e ⋆n^^ extract e'.
Proof.
  induction e; simpl; intros;
    try solve
        [ auto
        | now rewrite IHe
        | now rewrite IHe1, IHe2
        | now rewrite IHe2 ].
  - now destruct (n0 == n).
Qed.

Lemma extract_open_distr : forall e e',
    extract (e ^^ e') = extract e ⋆^^ extract e'.
Proof.
  intros. apply extract_open_distr_rec.
Qed.

Lemma extract_open_var : forall e x,
    extract (e ^` x) = extract e ⋆^` x.
Proof.
  intros. apply extract_open_distr.
Qed.

Lemma lc_extract_lc : forall e,
    lc_expr e -> lc_eexpr (extract e).
Proof.
  intros.
  induction H; simpl; auto;
    econstructor; eauto;
      intros; instantiate_cofinites; solve [now rewrite <- extract_open_var].
Qed.

Hint Resolve lc_extract_lc : core.

Ltac solve_evalue :=
  constructor; auto;
  econstructor; auto;
  intros; instantiate_cofinites; try rewrite <- extract_open_var; eauto.

Lemma value_evalue : forall e,
    value e -> evalue (extract e).
Proof.
  intros. induction H; simpl; solve [auto | inversion H0; subst; solve_evalue].
Qed.

Lemma evalue_value : forall e,
    lc_expr e -> evalue (extract e) -> value e.
Proof.
  intros e LC.
  induction LC; simpl; intros EV; try solve [inversion EV | eauto].
Qed.

Lemma subst_extract : forall e x v,
    extract ([v / x] e) = [(extract v) ⋆/ x] extract e.
Proof.
  induction e; simpl; intros;
    try solve
        [ auto
        | now destruct (x == x0)
        | now rewrite IHe
        | now rewrite IHe2
        | now rewrite IHe1, IHe2].
Qed.
