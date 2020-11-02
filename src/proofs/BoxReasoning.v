Require Import LanguageUtil.
Require Import BasicProperties.
Require Import Properties.
Require Import KindProperties.

Lemma wf_never_bind_box : forall Γ x,
    ⊢ Γ -> not (x : BOX ∈ Γ).
Proof.
  intros. intro.
  apply binds_inversion in H0 as (Γ1 & Γ2 & E). subst.
  apply wf_ctx_type_correct in H as (k & Sub).
  eapply box_never_welltype. eassumption.
Qed.

Ltac box_welltype_contradiction :=
  repeat progress
    match goal with
    | H : _ ⊢ BOX <: BOX : _ |- _ => contradict H; apply box_never_welltype
    | H : _ : BOX ∈ _ |- _ => contradict H; apply wf_never_bind_box; eauto
    | H : _ ⊢ BOX <: _ : _ |- _ => apply reflexivity_l in H
    | H : _ ⊢ _ <: BOX : _ |- _ => apply reflexivity_r in H
    end
.

Lemma open_is_box_rec : forall e1 e2 n,
    e1 <n> ^^ e2 = BOX -> e1 = BOX \/ e2 = BOX.
Proof.
  induction e1; simpl; intros; try solve [inversion H]; auto.
  - destruct (n0 == n); eauto.
Qed.

Lemma open_is_box : forall e1 e2,
    e1 ^^ e2 = BOX -> e1 = BOX \/ e2 = BOX.
Proof.
  intros. eapply open_is_box_rec. eauto.
Qed.

Lemma open_var_is_box : forall e x,
    e ^` x = BOX -> e = BOX.
Proof.
  intros. apply open_is_box in H. destruct H. auto. inversion H.
Qed.

Lemma head_kind_box_impossible : forall Γ e1 e2 A n,
    Γ ⊢ e1 <: e2 : A -> head_kind A k_box n -> A = BOX \/ False.
Proof.
  intros.
  apply type_correctness in H.
  destruct H as [E | (k & Sub)].
  + auto.
  + eauto using head_kind_box_never_welltype.
Qed.

Lemma pi_head_box_impossible : forall Γ e1 e2 A,
    not (Γ ⊢ e1 <: e2 : e_pi A BOX).
Proof.
  intros. intro. eapply head_kind_box_impossible in H.
  - destruct H. inversion H. auto.
  - constructor. apply h_kind. Unshelve. exact 0.
Qed.

Ltac solve_open_is_box :=
  repeat
    match goal with
    | H : _ ^^ _ = BOX |- _ => apply open_is_box in H as [|]; subst
    | H : _ ⊢ _ <: _ : e_pi _ BOX |- _ => contradict H; apply pi_head_box_impossible
    | _ => solve [box_welltype_contradiction]
    end
.

Lemma box_only_head_kind_star : forall Γ e,
    Γ ⊢ e : BOX -> exists n, head_kind e k_star n.
Proof.
  intros.
  dependent induction H; box_welltype_contradiction; instantiate_cofinites.
  (* star *)
  - exists 0. eauto.
  (* pi *)
  - instantiate_trivial_equals.
    destruct H1. apply head_kind_invert_subst_var in H1. eauto.
  (* app impossible *)
  - solve_open_is_box.
Qed.

Lemma box_never_reduce : forall Γ e,
    Γ ⊢ e : BOX -> forall e', not (e ⟶ e').
Proof.
  intros * Sub.
  dependent induction Sub; intros; intro R;
    try solve [inversion R | box_welltype_contradiction].
  (* r_app *)
  - solve_open_is_box.
Qed.

Lemma castup_box_never_welltype : forall Γ A B,
    not (Γ ⊢ e_castup A BOX : B).
Proof.
  intros. intro.
  dependent induction H.
  - box_welltype_contradiction.
  - eauto.
Qed.

Lemma app_box_never_welltype : forall Γ f1 f2 A,
    not (Γ ⊢ e_app f1 BOX <: e_app f2 BOX : A).
Proof.
  intros. intro.
  dependent induction H.
  - box_welltype_contradiction.
  - eauto.
Qed.

Lemma lambda_box_never_welltype : forall Γ A B,
    not (Γ ⊢ e_abs A BOX : B).
Proof.
  intros. intro.
  dependent induction H.
  - instantiate_cofinites. unfold open_expr_wrt_expr in *. simpl in *.
    box_welltype_contradiction.
  - eauto.
Qed.

Lemma app_of_box_impossible : forall Γ e1 e2 e,
    not (Γ ⊢ e_app e1 e <: e_app e2 e : BOX).
Proof.
  intros. intro.
  inversion H; subst.
  - solve_open_is_box.
  - box_welltype_contradiction.
Qed.

Lemma castdn_of_box_impossible : forall Γ e1 e2,
    not (Γ ⊢ e_castdn e1 <: e_castdn e2 : BOX).
Proof.
  intros. intro.
  inversion H; box_welltype_contradiction.
Qed.

Ltac find_typing_refl_of e H1 :=
  match goal with
  | H : _ ⊢ e : _ |- _ => rename H into H1
  | H : _ ⊢ e <: _ : _ |- _ =>
    pose proof H as H1; apply reflexivity_l in H1
  | H : _ ⊢ _ <: e : _ |- _ =>
    pose proof H as H1; apply reflexivity_r in H1
  end
.

Ltac conclude_head_kind_of e H := repeat
  match goal with
  | _ : head_kind  e _ _ |- _ => fail 1
  | _ : head_kind' e _   |- _ => fail 1
  | _ =>
    match goal with
    | H1 : _ ⊢ e : BOX |- _ =>
      let n := fresh "n" in
      apply box_only_head_kind_star in H1 as [n H]
    | H1 : _ ⊢ e <: _ : BOX |- _ =>
      pose proof H1 as H; apply reflexivity_l in H
    | H1 : _ ⊢ _ <: e : BOX |- _ =>
      pose proof H1 as H; apply reflexivity_r in H
    end
  end
.

Hint Resolve head_kind_box_never_welltype : box.


Ltac box_reasoning :=
  repeat
    progress match goal with
    (* base cases *)
    | _ =>
      solve [box_welltype_contradiction | eauto 3 with box]
    | H : _ ⊢ _ <: _ : e_pi BOX _ |- _ =>
      apply pi_box_impossible in H; contradiction
    | H : _ ⊢ e_app ?e1 ?e <: e_app ?e2 ?e : BOX |- _ =>
      apply app_of_box_impossible in H; contradiction
    | H : _ ⊢ e_castup _ BOX : _ |- _ =>
      apply castup_box_never_welltype in H; contradiction
    | H : _ ⊢ e_app _ BOX <: e_app _ BOX : _ |- _ =>
      apply app_box_never_welltype in H; contradiction
    | H : _ ⊢ e_abs _ BOX : _ |- _ =>
      apply lambda_box_never_welltype in H; contradiction
    | H : _ ⊢ e_castdn _ <: e_castdn _ : BOX |- _ =>
      apply castdn_of_box_impossible in H; contradiction
    (* reasoning *)
    | H1 : head_kind ?e _ _ |- _ =>
      match goal with
      (* if hypothesis exists in the form of binded expression *)
      | _ : _ ⊢ e ^` _ : BOX |- _ => fail 1
      | _ : _ ⊢ e ^` ?x : _ |- _ => apply head_kind_subst_var with (x := x) in H1
      end
    | H1 : head_kind ?e k_star _ |- _ =>
      match goal with
      | _ : _ ⊢ e      : BOX |- _ => fail 1
      | _ : _ ⊢ e : ?A |- _ =>
        let E := fresh "E" in
        assert (E : A = BOX) by eauto using head_kind_star_of_box;
        discharge_equality E
      | H : _ ⊢ e <: _ : _ |- _ => apply reflexivity_l in H
      | H : _ ⊢ _ <: e : _ |- _ => apply reflexivity_r in H
      end
    | H1 : head_kind ?e k_box _ |- _ =>
      let H2 := fresh H1 in
      find_typing_refl_of e H2;
      eapply head_kind_box_never_welltype in H2; [easy | eauto]
    | H : head_kind (?e1 ^^ ?e2) _ _ |- _ =>
      apply head_kind_invert_subst in H as [H | H]; try solve [inversion H]
    | E : ?e ^` _ = BOX |- _ =>
      apply open_var_is_box in E; discharge_equality E
    | E : ?e1 ^^ ?e2 = BOX |- _ =>
      apply open_is_box in E as [E | E]; discharge_equality E
    | H : _ ⊢ ?e : BOX |- _ => conclude_head_kind_of e H
    | H : _ ⊢ ?e1 <: ?e2 : BOX |- _ =>
      match goal with
      | _ =>
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        conclude_head_kind_of e1 H1; conclude_head_kind_of e2 H2
      end
    end
.

Lemma app_head_kind_impossible : forall Γ f1 f2 e A,
    Γ ⊢ e_app f1 e <: e_app f2 e : A -> forall n k, head_kind e k n -> False.
Proof.
  intros.
  dependent induction H.
  - destruct k; box_reasoning.
  - eauto 2.
Qed.

Lemma lambda_head_kind_impossible : forall Γ A e B,
    Γ ⊢ e_abs A e : B -> forall n k, head_kind e k n -> False.
Proof.
  intros.
  dependent induction H.
  - instantiate_cofinites.
    destruct k; box_reasoning.
  - eauto 2.
Qed.

Lemma mu_head_kind_impossible : forall Γ A e B,
    Γ ⊢ e_mu A e : B -> forall n k, head_kind e k n -> False.
Proof.
  intros.
  dependent induction H.
  - instantiate_cofinites. destruct k0; box_reasoning.
  - eauto 2.
Qed.

Lemma castup_head_kind_box_impossible : forall Γ A e B,
    Γ ⊢ e_castup A e : B -> forall n, head_kind e k_box n -> False.
Proof.
  intros.
  dependent induction H.
  - eauto using head_kind_box_never_welltype.
  - eauto.
Qed.

Hint Resolve app_head_kind_impossible : box.
Hint Resolve lambda_head_kind_impossible : box.
Hint Resolve castup_head_kind_box_impossible : box.
Hint Resolve mu_head_kind_impossible : box.

Lemma box_never_be_reduced : forall e e',
    e ⟶ e' -> forall n, head_kind e' k_box n -> forall Γ A, Γ ⊢ e : A -> False.
Proof with eauto 2 with box.
  intros * R.
  dependent induction R; intros.
  (* r_app *)
  - inversion H0.
  (* r_beta *)
  - box_reasoning.
    + dependent induction H3...
  (* r_inst *)
  - inversion H3.
  (* r_mu *)
  - box_reasoning.
  (* r_castdn *)
  - inversion H.
  (* r_cast_inst *)
  - inversion H2.
  (* r_cast_elim *)
  - dependent induction H2...
Qed.

Hint Resolve box_never_be_reduced : box.

Lemma expr_of_box_never_be_reduced' : forall e' e,
    e' ⟶ e -> forall Γ A, Γ ⊢ e : BOX -> forall Γ', Γ' ⊢ e' : A -> False.
Proof.
  intros * R.
  induction R; intros.
  (* r_app *)
  - box_reasoning.
  (* r_beta *)
  - dependent induction H3; box_reasoning.
  (* r_inst *)
  - box_reasoning.
  (* r_mu *)
  - box_reasoning.
  (* r_castdn *)
  - box_reasoning.
  (* r_inst *)
  - box_reasoning.
  (* r_cast_elim *)
  - dependent induction H2.
    + clear IHusub1 IHusub2 H2.
      dependent induction H2_0; box_reasoning.
      Unshelve. exact 0.
    + eauto 2.
Qed.

Hint Resolve expr_of_box_never_be_reduced' : box.
