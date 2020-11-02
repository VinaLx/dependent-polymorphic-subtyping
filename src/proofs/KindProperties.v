Require Import Declarative.BasicProperties.

Lemma box_never_welltype : forall Γ A,
    ~ (Γ ⊢ BOX : A).
Proof.
  intros. intro.
  dependent induction H; auto.
Qed.

Lemma star_type_inversion : forall Γ A,
    Γ ⊢ * : A -> A = BOX.
Proof.
  intros.
  dependent induction H.
  - reflexivity.
  - assert (A = BOX) by auto. subst.
    apply reflexivity_l in H0. apply box_never_welltype in H0. contradiction.
Qed.


Lemma star_type_inversion_r : forall Γ A B,
    Γ ⊢ * <: A : B -> B = BOX.
Proof.
  intros. apply star_type_inversion with Γ.
  now apply reflexivity_l with A.
Qed.

Lemma star_type_inversion_l : forall Γ A B,
    Γ ⊢ A <: * : B -> B = BOX.
Proof.
  intros.
  apply star_type_inversion with Γ.
  now apply reflexivity_r with A.
Qed.

Lemma star_sub_inversion_l : forall Γ A B,
    Γ ⊢ A <: * : B -> A = *.
Proof.
  intros.
  dependent induction H.
  - reflexivity.
  - apply star_type_inversion_l in H2. discriminate.
  - now apply IHusub1.
Qed.

Lemma star_sub_inversion_r : forall Γ A B,
    Γ ⊢ * <: A : B -> A = *.
Proof.
  intros.
  dependent induction H.
  - reflexivity.
  - apply star_type_inversion in H0. discriminate.
  - now apply IHusub1.
Qed.

Lemma num_not_of_star : forall Γ n,
    Γ ⊢ e_num n : * -> False.
Proof.
  intros. dependent induction H.
  - assert (e_kind k = BOX).
    eapply star_type_inversion_l; eauto. inversion H1. subst.
    apply star_sub_inversion_l in H0.
    now eapply IHusub1.
Qed.

Lemma int_of_star : forall Γ A,
    Γ ⊢ e_int : A -> A = *.
Proof.
  intros.
  dependent induction H.
  - reflexivity.
  - assert ( A = * ) by now apply IHusub1. subst.
    now eapply star_sub_inversion_r in H0.
Qed.

Lemma abs_not_of_star : forall Γ A B,
    Γ ⊢ e_abs A B : * -> False.
Proof.
  intros.
  dependent induction H.
  - apply star_sub_inversion_l in H0.
    now eapply IHusub1.
Qed.

Lemma bind_not_of_star : forall Γ A B,
    Γ ⊢ e_bind A B : * -> False.
Proof.
  intros.
  dependent induction H.
  - apply star_sub_inversion_l in H0.
    now eapply IHusub1.
Qed.

Lemma var_star_inversion : forall Γ x,
    Γ ⊢ e_var_f x : * -> x : * ∈ Γ.
Proof.
  intros.
  dependent induction H.
  - assumption.
  - apply star_sub_inversion_l in H0.
    now apply IHusub1.
Qed.

Lemma kind_sub_inversion_l : forall Γ ek kr k,
    Γ ⊢ ek <: e_kind kr : k -> ek = * /\ kr = k_star /\ k = BOX.
Proof.
  intros.
  dependent induction H.
  - auto.
  - edestruct IHusub3. reflexivity. destruct H6. discriminate.
  - edestruct IHusub1 as [E1 [E2 E3]]; auto.
    subst.
    apply reflexivity_l in H0. now apply box_never_welltype in H0.
Qed.

Inductive head_kind : expr -> kind -> nat -> Prop :=
| h_kind   : forall k n, head_kind (e_kind k) k n
| h_pi     : forall A B k n,
    head_kind B k n -> head_kind (e_pi A B) k (S n)
(*| h_forall : forall A B k n,
    head_kind B k n -> head_kind (e_all A B) k (S n) *)
.

Hint Constructors head_kind : core.

Lemma head_kind_S : forall e k n, head_kind e k n -> head_kind e k (S n).
Proof.
  intros. induction H; auto.
Qed.

Hint Resolve head_kind_S : core.

Lemma head_kind_invert_subst_rec : forall A e k m n,
    head_kind (A <n> ^^ e) k m ->
    head_kind e k m \/ head_kind A k m.
Proof.
  induction A; simpl; intros e k' m' n' K; try solve [inversion K].
  - destruct (n' == n); auto.
  - auto.
  - inversion K; subst. destruct IHA2 with e k' n (S n'); auto.
Qed.

Lemma head_kind_invert_subst : forall A e k n,
    head_kind (A ^^ e) k n -> head_kind e k n \/ head_kind A k n.
Proof.
  unfold open_expr_wrt_expr.
  intros. now apply head_kind_invert_subst_rec with 0.
Qed.

Lemma head_kind_invert_subst_var : forall A x k n,
    head_kind (A ^` x) k n -> head_kind A k n.
Proof.
  intros.
  apply head_kind_invert_subst in H as [|].
  + inversion H.
  + assumption.
Qed.

Lemma head_kind_subst_rec : forall A e k m n,
    head_kind A k m -> head_kind (A <n> ^^ e) k m.
Proof.
  induction A; simpl; intros e k' m' n' K; inversion K; eauto.
Qed.

Lemma head_kind_subst : forall A e k n,
    head_kind A k n -> head_kind (A ^^ e) k n.
Proof.
  intros. now apply head_kind_subst_rec.
Qed.

Lemma head_kind_subst_var : forall A x k n,
    head_kind A k n -> head_kind (A ^` x) k n.
Proof.
  intros. now apply head_kind_subst_rec.
Qed.

Hint Resolve head_kind_invert_subst_var : core.
Hint Resolve head_kind_subst : core.
Hint Resolve head_kind_invert_subst_var : core.

Lemma head_kind_not_star : forall Γ e k n,
    Γ ⊢ e : * -> head_kind e k n -> False.
Proof.
  intros. generalize dependent k.
  dependent induction H; intros k' K; inversion K; subst.
  - pick fresh x. apply H3 with x k'; eauto.
  - apply kind_sub_inversion_l in H0 as [E1 [E2 E3]]. subst.
    apply kind_sub_inversion_l in H as [E4 [E5 E6]]. subst.
    inversion E6.
  - apply kind_sub_inversion_l in H0 as [E1 [E2 E3]]. subst.
    now apply IHusub1 with k'.
Qed.

Lemma head_kind_sub_r : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> forall k n, head_kind e1 k n -> head_kind e2 k n.
Proof.
  intros Γ e1 e2 k Hsub.
  dependent induction Hsub; intros k' n' K; try solve [inversion K].
  - assumption.
  - pick fresh x. inversion K. eauto.
  - eapply head_kind_not_star in Hsub2; eauto. contradiction.
  - eauto.
Qed.

Lemma head_kind_sub_l : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> forall k n, head_kind e2 k n -> head_kind e1 k n.
Proof.
  intros Γ e1 e2 A Hsub.
  induction Hsub; intros k' n' K; try solve [inversion K].
  - assumption.
  - pick fresh x. inversion K; eauto.
  - assert False.
    + eapply head_kind_not_star. eapply reflexivity_l. eauto.
      eapply IHHsub3. eassumption.
    + contradiction.
  - eauto.
Qed.

Lemma head_kind_var_consistent : forall Γ x A B k n,
    Γ ⊢ e_var_f x : A -> x : B ∈ Γ -> head_kind B k n -> head_kind A k n.
Proof.
  intros until n. intro Hsub.
  dependent induction Hsub; intros.
  - assert (A = B) by (eapply binds_consistent; eauto).
    now rewrite H3.
  - eapply head_kind_sub_r. apply Hsub2.
    now eapply IHHsub1.
Qed.

Lemma head_kind_unique : forall e k1 k2 n,
    head_kind e k1 n -> head_kind e k2 n -> k1 = k2.
Proof.
  intros.
  generalize dependent k2.
  induction H; intros k2' K; inversion K; subst;
    pick fresh x; eauto.
Qed.

Lemma head_kind_star_of_box : forall Γ e A n,
    Γ ⊢ e : A -> head_kind e k_star n -> A = BOX.
Proof.
  intros Γ e A n Hsub Hk. dependent induction Hsub; try solve [inversion Hk].
  - reflexivity.
  - inversion Hk; subst.
    pick fresh x. apply H2 with x; auto.
  - assert (A = BOX) by auto. subst.
    apply reflexivity_l in Hsub2. now apply box_never_welltype in Hsub2.
Qed.

Lemma head_kind_box_never_welltype : forall Γ e A n,
    Γ ⊢ e : A -> head_kind e k_box n -> False.
Proof.
  intros Γ e A n Hsub Hk.
  dependent induction Hsub; inversion Hk; subst;
    solve [auto | pick_fresh x; eauto ].
Qed.

Lemma pi_box_never_welltype : forall Γ A B,
    Γ ⊢ e_pi BOX A : B -> False.
Proof.
  intros. dependent induction H.
  - now apply box_never_welltype in H.
  - now apply IHusub1 with A.
Qed.

Lemma bind_type_welltype : forall Γ x A,
    ⊢ Γ -> x : A ∈ Γ -> exists k, Γ ⊢ A : e_kind k.
Proof.
  induction Γ; intros x A Hwf Hsub.
  - inversion Hsub.
  - destruct a as [y B]. destruct Hsub; inversion Hwf.
    + inversion H. subst. eauto.
    + subst. destruct IHΓ with x A; eauto.
Qed.

Inductive tail_kind : expr -> kind -> Prop :=
| tk_pi : forall A k, tail_kind (e_pi (e_kind k) A) k
| ti_ind : forall A B k, tail_kind B k -> tail_kind (e_pi A B) k
.

Hint Constructors tail_kind : core.

Lemma tail_kind_subst_rec : forall A e k n,
    tail_kind A k ->
    tail_kind (A <n> ^^ e) k.
Proof.
  induction A; simpl; intros e k' n' Htk; try solve [inversion Htk].
  - inversion Htk; subst; simpl; auto.
Qed.

Lemma tail_kind_subst_var : forall A x k,
    tail_kind A k -> tail_kind (A ^` x) k.
Proof.
  intros. now apply tail_kind_subst_rec.
Qed.

Hint Resolve tail_kind_subst_var : core.

Lemma tail_box_never_welltype : forall Γ e A,
    Γ ⊢ e : A -> tail_kind e k_box -> False.
Proof.
  intros Γ e A Hsub Htk.
  dependent induction Hsub; try solve [inversion Htk].
  - inversion Htk; subst.
    + now apply box_never_welltype in Hsub.
    + pick fresh x. apply H2 with x; eauto.
  - auto.
Qed.

Lemma open_is_kind_inversion : forall A e k n,
    e_kind k = A <n> ^^ e -> A = e_kind k \/ e = e_kind k.
Proof.
  induction A; simpl; intros e k' n' E; try solve [inversion E].
  - destruct (n' == n); auto.
  - auto.
Qed.

Lemma tail_kind_invert_subst_rec : forall A e k n,
    tail_kind (open_expr_wrt_expr_rec n e A) k ->
    tail_kind A k \/ tail_kind e k \/ e = e_kind k.
Proof.
  induction A; simpl; intros e k' n' Htk; try solve [inversion Htk].
  - destruct (n' == n); auto.
  - inversion Htk; subst.
    + apply open_is_kind_inversion in H0 as [E | E]; subst; auto.
    + edestruct IHA2 as [H|[H|H]]; eauto.
Qed.

Lemma tail_box_never_reduce : forall A B,
    tail_kind A k_box -> not (A ⟶ B).
Proof.
  intros. destruct H; intro Contra; inversion Contra.
Qed.

Lemma tail_box_impossible : forall Γ e A,
    Γ ⊢ e : A -> tail_kind A k_box -> False.
Proof.
  intros Γ e A Hsub Htk.
  dependent induction Hsub; try solve [inversion Htk].
  - apply bind_type_welltype in H0 as [k Hsub]; auto.
    eapply tail_box_never_welltype; eauto.
  - inversion Htk; subst.
    + now apply box_never_welltype in Hsub.
    + pick fresh x. eauto.
  - apply tail_kind_invert_subst_rec in Htk as [Htk | [Htk | E]].
    + auto.
    + apply tail_box_never_welltype with G t A; auto.
    + subst. now apply box_never_welltype in Hsub1.
  - pick fresh x. eapply H1; eauto.
  - eapply tail_box_never_reduce; eauto.
  - eapply tail_box_never_welltype. exact Hsub1. assumption.
  - apply reflexivity_r in Hsub2. eapply tail_box_never_welltype; eauto.
Qed.

Lemma pi_box_impossible : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : e_pi BOX A -> False.
Proof.
  intros.
  apply reflexivity_l in H.
  assert (tail_kind (e_pi BOX A) k_box) by auto.
  apply tail_box_impossible in H; auto.
Qed.

Inductive head_kind' : expr -> kind -> Prop :=
| h_kind'   : forall k, head_kind' (e_kind k) k
| h_pi'     : forall A B k,
    head_kind' B k -> head_kind' (e_pi A B) k
.

Hint Constructors head_kind' : core.

Lemma hk_hk' : forall e k n,
    head_kind e k n -> head_kind' e k.
Proof.
  intros. induction H; eauto.
Qed.

Lemma hk'_hk : forall e k,
    head_kind' e k -> exists n, head_kind e k n.
Proof.
  intros. induction H.
  - exists 0. eauto.
  - destruct IHhead_kind'. eauto using ex_intro.
Qed.
