Require Export Declarative.LanguageUtil.
Require Import Program.Equality.

Import ListNotations.

Lemma binded_type_correct : forall Γ x A e1 e2 B,
    Γ, x : A ⊢ e1 <: e2 : B -> exists k, Γ ⊢ A : e_kind k.
Proof.
  intros. eauto using wf_ctx_type_correct_cons with wf.
Qed.


Local Ltac conclude_relevant_refl_in_ctx :=
  repeat match goal with
  | H : forall x, x `notin` ?L -> ?G, x : ?A ⊢ _ <: _ : _ |- ?g =>
    match g with
    | context [A] => progress
      match goal with
      | H' : G ⊢ A <: A : _ |- _ => idtac
      | _ =>
        let H' := fresh "H" in
        let k  := fresh "k" in
        pose cofinite H as H';
        apply binded_type_correct in H' as (k & H')
      end
    end
  end
.

Theorem reflexivity_l : forall Γ e1 e2 A, Γ ⊢ e1 <: e2 : A -> Γ ⊢ e1 : A.
Proof.
  intros. induction H; conclude_relevant_refl_in_ctx; eauto 3.
Qed.

Theorem reflexivity_r : forall Γ e1 e2 A, Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 : A.
Proof.
  intros. induction H; conclude_relevant_refl_in_ctx; eauto 3.
Qed.

Ltac gather_for_weakening :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : context => dom x) in
  constr:(A `union` B `union` C).

Tactic Notation "pick" "fresh" ident(x) "and" "apply" constr(H) "for" "weakening" :=
  apply_fresh_base_fixed H gather_for_weakening x.

Lemma wf_eauto_helper : forall Γ1 Γ2 x A,
    ⊢ Γ1 ,, Γ2 , x : A -> ⊢ Γ1 ,, (Γ2 , x : A).
Proof. easy. Qed.

Hint Resolve wf_eauto_helper : weakening.

Hint Resolve reflexivity_r : refl.
Hint Resolve reflexivity_l : refl.

Hint Extern 4 (⊢ _ , _ : _) => eauto 4 with refl : weakening.

Ltac something := econstructor 5 with (L := empty).

Theorem weakening : forall Γ1 Γ2 Γ3 e1 e2 A,
    Γ1 ,, Γ3 ⊢ e1 <: e2 : A ->
    ⊢ Γ1 ,, Γ2 ,, Γ3 ->
    Γ1 ,, Γ2 ,, Γ3 ⊢ e1 <: e2 : A.
Proof with autorewrite with assoc; eauto with weakening.
  intros until A. intro Hsub.
  dependent induction Hsub; intro Hwf; auto.
  - pick fresh x and apply s_abs for weakening...
  - pick fresh x and apply s_pi for weakening...
  - apply s_app with A...
  - pick fresh x and apply s_bind for weakening...
  - pick fresh x and apply s_mu for weakening...
  - eauto.
  - eauto.
  - pick fresh x and apply s_forall_l for weakening...
  - pick fresh x and apply s_forall_r for weakening...
  - pick fresh x and apply s_forall for weakening...
  - eauto.
Qed.

Corollary weakening_cons : forall Γ x X e1 e2 A,
    Γ ⊢ e1 <: e2 : A ->
    ⊢ Γ , x : X ->
    Γ , x : X ⊢ e1 <: e2 : A.
Proof.
  intros. replace (Γ , x : X) with (Γ ,, (x ~ X) ,, nil) by reflexivity.
  now apply weakening.
Qed.

Hint Resolve reflexivity_r : core.
Hint Resolve reflexivity_l : core.
Hint Resolve weakening_cons : core.

Corollary weakening_app : forall Γ Γ' e1 e2 A,
    Γ ⊢ e1 <: e2 : A ->
    ⊢ Γ ,, Γ' ->
    Γ ,, Γ' ⊢ e1 <: e2 : A.
Proof.
  intros. replace (Γ ,, Γ') with (Γ ,, Γ' ,, nil) by reflexivity.
  now apply weakening.
Qed.

Theorem ctx_narrowing : forall Γ1 Γ2 x A B C e1 e2 k,
  Γ1 , x : B ,, Γ2 ⊢ e1 <: e2 : C ->
  Γ1 ⊢ A <: B : e_kind k ->
  Γ1 , x : A ,, Γ2 ⊢ e1 <: e2 : C.
Proof with autorewrite with assoc; eauto 3.
  intros.
  remember (Γ1 , x : B ,, Γ2) as Γ.
  generalize Γ2, HeqΓ. clear HeqΓ Γ2.
  apply sub_mut with
    (P := fun Γ e1 e2 C (_ : Γ ⊢ e1 <: e2 : C) =>
        forall Γ2, Γ = Γ1 , x : B ,, Γ2 -> Γ1 , x : A ,, Γ2 ⊢ e1 <: e2 : C)
    (P0 := fun Γ (_ : ⊢ Γ) =>
        forall Γ2, Γ = Γ1 , x : B ,, Γ2 -> ⊢ Γ1 , x : A ,, Γ2); intros; subst.
  - assert ({x = x0} + {x <> x0}) as [E | NE] by apply eq_dec.
    + subst. apply weakening_app; auto.
      assert (A0 = B) by now apply binds_type_equal with Γ1 x0 Γ2. subst.
      apply s_sub with A k.
      * apply s_var; eauto with wf.
      * apply weakening_cons; eauto with wf.
    + apply s_var.
      * auto.
      * now apply binds_type_not_equal with B.
  - auto.
  - auto.
  - auto.
  - pick fresh x' and apply s_abs...
  - pick fresh x' and apply s_pi...
  - eauto.
  - pick fresh x' and apply s_bind...
  - pick fresh x' and apply s_mu...
  - eauto.
  - eauto.
  - pick fresh x' and apply s_forall_l...
  - pick fresh x' and apply s_forall_r...
  - pick fresh x' and apply s_forall...
  - eauto.

  (* ⊢ Γ1 , x : B ,, Γ2 → Γ1 ⊢ A <: B : * → ⊢ Γ1 , x : A ,, Γ2 *)
  - destruct Γ2; inversion H1.
  - destruct Γ2; try destruct p; inversion H3; subst.
    + eapply wf_cons; eauto.
    + eapply wf_cons; auto.

  - assumption.
Qed.

Corollary ctx_narrowing_cons : forall Γ1 x A B C e1 e2 k,
    Γ1 , x : A ⊢ e1 <: e2 : C ->
    Γ1 ⊢ B <: A : e_kind k ->
    Γ1, x : B ⊢ e1 <: e2 : C.
Proof.
  intros.
  replace (Γ1 , x : B) with (Γ1 ,, x ~ B ,, nil) by reflexivity.
  apply ctx_narrowing with A k; auto.
Qed.
