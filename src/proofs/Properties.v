Require Import Declarative.BasicProperties.
Require Import Declarative.KindProperties.
Require Import Declarative.OccurenceReasoning.
Require Import Declarative.FSetReasoning.
Require Import Extraction.

Require Import Program.Tactics.

Lemma binds_subst : forall Γ1 Γ2 x x' A B e,
    ⊢ Γ1, x' : B,, Γ2 ->
    x : A ∈ Γ1, x' : B,, Γ2 -> x <> x' -> x : [e / x'] A ∈ Γ1 ,, [e // x'] Γ2.
Proof.
  induction Γ2; simpl; intros.
  - destruct H0.
    + inversion H0. subst. contradiction.
    + inversion H. subst.
      assert (x' # A) by (eapply notin_dom_bind_fresh; eauto).
      rewrite fresh_subst_eq; auto.
  - destruct a. destruct H0.
    + inversion H0. subst. auto.
    + right. inversion H. apply IHΓ2 with B; auto.
Qed.

Lemma subst_ctx_distr_cons : forall Γ x A y e,
    [e // y] Γ , x : [e / y] A = [e // y] (Γ , x : A).
Proof. reflexivity. Qed.

Lemma ctx_app_cons_assoc : forall (Γ1 Γ2 : context) x A,
    Γ1 ,, Γ2 , x : A = Γ1 ,, (Γ2 , x : A).
Proof. reflexivity. Qed.

Hint Rewrite ctx_app_cons_assoc : substitution.
Hint Rewrite subst_ctx_distr_cons : substitution.
Hint Rewrite subst_open_var_assoc : substitution.
Hint Rewrite subst_extract : substitution.

Ltac crush_lc :=
  repeat
    match goal with
    | |- forall x, x `notin` _ -> lc_expr _ => intros
    | _ => first
            [ progress auto
            | progress eauto using lc_subst, lc_open_preserve
            | progress autorewrite with assoc; auto ]
    | H : lc_expr ?T |- lc_expr (?e ^^ _) =>
      match T with
      | context [e] => inversion H; subst
      end
    | |- lc_expr ([_ / _] _) => apply lc_subst
    end
.

Hint Extern 1 (lc_expr _) => crush_lc : lc.
Hint Extern 1 (forall x, x `notin` _ -> lc_expr _) => crush_lc : lc.

Lemma value_subst : forall e x v,
    lc_expr v -> value e -> value ([v / x] e).
Proof.
  intros * Lc V. induction V; simpl; eauto 4 with lc.
Qed.

Hint Resolve mono_lc : mono.
Hint Resolve subst_mono : mono.
Hint Resolve value_subst : value.

Lemma reduce_subst : forall A B,
    A ⟶ B -> forall x e, mono_type e -> ([e / x] A) ⟶ ([e / x] B).
Proof with try rewrite subst_open_distr; eauto 4 with lc mono value.
  intros A B Hr.
  induction Hr; simpl; intros...
  - simpl. constructor. crush_lc.
    inversion H0; subst.
    apply lc_e_mu with (add x L); crush_lc.
Qed.

Lemma dom_subst_equal : forall Γ x v,
    dom ([v // x] Γ) = dom Γ.
Proof.
  induction Γ; intros.
  + reflexivity.
  + destruct a. simpl. now rewrite (IHΓ x v).
Qed.

Ltac subst_gather_helper e :=
  match type of e with
  | mono_type ?t => constr:(fv_eexpr (extract t))
  end
.

Ltac gather_for_substitution :=
  let L1 := gather_atoms_with (fun L : atoms => L) in
  let L2 := gather_atoms_with (fun x : atom => singleton x) in
  let L3 := gather_atoms_with_tactic subst_gather_helper in
  constr:(L1 `union` L2 `union` L3).

Ltac substitution_strategy :=
  match goal with
  | _ => solve [auto 3]
  | _ => progress autorewrite with substitution
  | |- _ ⊢ e_app _ _ <: e_app _ _ : [_ / _] _ ^^ _ =>
    (* [v / x] A ^^ e = [v / x] A ^^ [v / x] e *)
    rewrite -> subst_open_distr
  | |- _ ⊢ ([?v / ?x] ?e1) ^^ _ <: _ : _ =>
    rewrite <- subst_open_distr
  | |- _ `notin` fv_eexpr _ => solve [eauto 4 using fv_subst_inclusion]
  | |- _ ⟶ _ => solve [eauto using reduce_subst]
  | _ => try_constructors
  | _ => solve [eauto]
  end
.

Ltac apply_substitution_strategy :=
  repeat (intros; substitution_strategy).

Ltac solve_subst :=
  solve [
      adjust_cofinites_for gather_for_substitution;
      apply_substitution_strategy].

Theorem substitution : forall Γ1 Γ2 x A B e1 e2 e3,
  Γ1 , x : B ,, Γ2 ⊢ e1 <: e2 : A ->
  Γ1 ⊢ e3 : B -> mono_type e3 ->
  Γ1 ,, [e3 // x] Γ2 ⊢ [e3 / x] e1 <: [e3 / x] e2 : [e3 / x] A.
Proof.
  intros until e3. intros Hsub Hsub3 Mono.
  remember (Γ1 , x : B ,, Γ2) as Γ.
  generalize dependent HeqΓ.
  generalize x Γ2. clear x Γ2.
  apply sub_mut with
      (P := fun Γ e1 e2 A => fun (_ : Γ ⊢ e1 <: e2 : A) =>
         forall x Γ2, Γ = Γ1, x : B,, Γ2 ->
         Γ1 ,, [e3 // x] Γ2 ⊢ [e3 / x] e1 <: [e3 / x] e2 : [e3 / x] A)
      (P0 := fun Γ => fun (_ : ⊢ Γ) =>
         forall x Γ2, Γ = Γ1 , x : B,, Γ2 -> ⊢ Γ1 ,, [e3 // x] Γ2);
      simpl; intros; subst.
  - destruct (x == x0).
    + subst. assert (A0 = B) by (eapply binds_type_equal; eauto). subst.
      rewrite fresh_subst_eq. apply weakening_app; auto.
      apply prefix_wf in w. inversion w. subst.
      eapply fresh_ctx_fresh_expr; eauto.
    + apply s_var. auto. apply binds_subst with B; auto.
  - solve_subst.
  - solve_subst.
  - solve_subst.
  - solve_subst.
  - solve_subst.
  - solve_subst.
  - solve_subst.
  - adjust_cofinites_for gather_for_substitution.
    eapply s_mu.
    + inversion m. subst.
      pick fresh x' and apply mono_mu; autorewrite with assoc; eauto.
    + apply_substitution_strategy.
    + apply_substitution_strategy.
  - solve_subst.
  - solve_subst.
  - apply s_forall_l with (add x L) ([e3 / x] t) k;
      apply_substitution_strategy.
  - solve_subst.
  - solve_subst.
  - solve_subst.

  - destruct Γ2; inversion H.
  - destruct Γ2; inversion H1; subst; simpl in *.
    + auto.
    + apply wf_cons with k; auto.
      rewrite dom_app. rewrite dom_subst_equal.
      eauto using dom_insert_subset.
  - assumption.
Qed.

Corollary substitution_cons : forall Γ x A B e1 e2 e3,
    Γ, x : B ⊢ e1 <: e2 : A ->
    Γ ⊢ e3 : B -> mono_type e3 ->
    Γ ⊢ [e3 / x] e1 <: [e3 / x] e2 : [e3 / x] A.
Proof.
  intros *.
  replace (Γ , x : B) with (Γ ,, one (pair x B) ,, nil) by reflexivity.
  intros.
  replace Γ with (Γ ,, [e3 // x] nil) by reflexivity.
  eapply substitution; simpl in *; eauto.
Qed.

Lemma ctx_type_correct : forall Γ x A,
    ⊢ Γ -> x : A ∈ Γ -> exists k, Γ ⊢ A : e_kind k.
Proof.
  intros * Wf.
  induction Wf; simpl; intros.
  - inversion H.
  - destruct H1.
    + inversion H1. subst.
      eauto.
    + destruct (IHWf H1) as [k0 IH].
      eauto.
Qed.

Theorem type_correctness : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> A = BOX \/ exists k, Γ ⊢ A : e_kind k.
Proof.
  intros * Sub.
  induction Sub; eauto with wf.
  - eauto 3 using ctx_type_correct.
  - pick fresh x.
    destruct (H2 x Fr) as [H' | [k H']].
    + auto.
    + apply kind_sub_inversion_l in H' as (E1 & E2 & E3). subst. eauto with wf.
  - destruct IHSub2 as [H0 | [k H0]]. inversion H0.
    dependent induction H0.
    + clear H1 H3 IHusub IHusub.
      pick fresh x for (L `union` fv_expr B).
      assert (Fr2 : x `notin` L) by auto.
      specialize (H2 x Fr2).
      right. exists k.
      rewrite open_subst_eq with (x := x); auto.
      replace (e_kind k) with ([t / x] e_kind k) by reflexivity.
      eapply substitution_cons; eauto.
    + apply IHusub1 with A k; auto.
      apply kind_sub_inversion_l in H0_0 as (E1 & E2 & E3). now subst.
Qed.

Ltac conclude_type_refl H :=
  match type of H with
  | ?G ⊢ _ <: _ : ?A =>
    let k := fresh "k" in
    let H := fresh "H" in
    let EBox := fresh "Ebox" in
    assert (A = BOX \/ exists k, G ⊢ A : e_kind k) as [Ebox | [k H]]
        by (eapply type_correctness; eassumption);
    [inversion EBox; subst |]
  end
.
