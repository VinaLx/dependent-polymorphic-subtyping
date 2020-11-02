Require Import LanguageUtil.
Require Import BasicProperties.
Require Import Properties.
Require Import Transitivity.
Require Import Extraction.
Require Import KindProperties.
Require Import BoxReasoning.
Require Import OccurenceReasoning.

Require Import Program.Tactics.

Definition Progressive (e : expr) : Prop := value e \/ exists e', e ⟶ e'.
Definition EProgressive (e : eexpr) := evalue e \/ exists e', e ⋆⟶ e'.

Hint Unfold Progressive : core.
Hint Unfold EProgressive : core.

Hint Rewrite extract_open_distr : reassoc.

Ltac find_impossible_reduction :=
  simpl in *;
  match goal with
  | _ : ee_app _ _ ⋆⟶ _ |- _ => fail
  | _ : e_app  _ _ ⟶  _ |- _ => fail
  | _ : e_app _ _ ⟹ _ |- _ => fail
  | H : _ ⋆⟶ _ |- _ => solve [inversion H]
  | H : _ ⟶  _ |- _ => solve [inversion H]
  | H : _ ⟹ _ |- _ => solve [inversion H]
  end
.

Ltac solve_impossible_reduction := try find_impossible_reduction.

Lemma dreduce_deterministic : forall e e1 e2,
    e ⟹ e1 -> e ⟹ e2 -> e1 = e2.
Proof.
  intros. generalize dependent e2.
  induction H; intros.
  - inversion H1; subst; solve_impossible_reduction.
    rewrite (IHdreduce e6); auto.
  - inversion H2; subst; solve_impossible_reduction.
    auto.
  - inversion H1; subst; auto.
Qed.

Ltac conclude_refls H :=
  match type of H with
  | ?G ⊢ ?e1 <: ?e2 : ?A =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    assert (H1 : G ⊢ e1 : A) by eauto;
    assert (H2 : G ⊢ e2 : A) by eauto;
    conclude_type_refl H
  end
.

Lemma castdn_not_of_star : forall Γ e,
    Γ ⊢ e_castdn e : * -> False.
Proof.
  intros.
  dependent induction H.
  - assert (e_kind k = BOX) by (eapply star_type_inversion; eauto).
    inversion H2; subst.
    conclude_type_refl H1.
    + inversion H0.
    + eauto using expr_of_box_never_be_reduced'.
  - apply star_sub_inversion_l in H0. subst.
    eapply IHusub1; eauto.
Qed.

Lemma castup_not_of_star : forall Γ A e,
    Γ ⊢ e_castup A e : * -> False.
Proof.
  intros.
  dependent induction H.
  - inversion H0.
  - apply star_sub_inversion_l in H0. subst.
    eapply IHusub1; eauto.
Qed.

Lemma abs_le : forall Γ A b e T,
    Γ ⊢ e_abs A b <: e : T ->
    exists c, e = e_abs A c.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - now apply abs_not_of_star in H0.
  - now eapply IHusub1.
Qed.

Lemma abs_ge : forall Γ A b e T,
    Γ ⊢ e <: e_abs A b : T ->
    exists c, e = e_abs A c.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - apply reflexivity_r in H2.
    now apply abs_not_of_star in H2.
  - now eapply IHusub1.
Qed.

Lemma bind_le : forall Γ A b e T,
    Γ ⊢ e_bind A b <: e : T ->
    exists c, e = e_bind A c.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - now apply bind_not_of_star in H0.
  - now eapply IHusub1.
Qed.

Lemma bind_ge : forall Γ A b e T,
    Γ ⊢ e <: e_bind A b : T ->
    exists c, e = e_bind A c.
Proof.
  intros. dependent induction H.
  - eauto.
  - apply reflexivity_r in H2. now apply bind_not_of_star in H2.
  - now eapply IHusub1.
Qed.

Lemma castup_le : forall Γ A b e T,
    Γ ⊢ e_castup A b <: e : T ->
    exists c, e = e_castup A c.
Proof.
  intros. dependent induction H.
  - eauto.
  - now apply castup_not_of_star in H0.
  - now eapply IHusub1.
Qed.

Lemma castup_ge : forall Γ A b e T,
    Γ ⊢ e <: e_castup A b : T ->
    exists c, e = e_castup A c.
Proof.
  intros. dependent induction H.
  - eauto.
  - apply reflexivity_r in H2. now apply castup_not_of_star in H2.
  - now eapply IHusub1.
Qed.

Lemma castdn_le : forall Γ a e T,
    Γ ⊢ e_castdn a <: e : T ->
    exists b, e = e_castdn b.
Proof.
  intros. dependent induction H.
  - eauto.
  - now apply castdn_not_of_star in H0.
  - now eapply IHusub1.
Qed.

Lemma castdn_ge : forall Γ a e T,
    Γ ⊢ e <: e_castdn a: T ->
    exists b, e = e_castdn b.
Proof.
  intros. dependent induction H.
  - eauto.
  - apply reflexivity_r in H2. now apply castdn_not_of_star in H2.
  - now eapply IHusub1.
Qed.


Ltac invert_sub_hyp :=
  let b := fresh "b" in
  let E := fresh "E" in
  let H' := fresh "H" in
  match goal with
  | _ : _ ⊢ e_abs    ?A _ <: e_abs    ?A _ : _ |- _ => idtac
  | _ : _ ⊢ e_bind   ?A _ <: e_bind   ?A _ : _ |- _ => idtac
  | _ : _ ⊢ e_castdn    _ <: e_castdn    _ : _ |- _ => idtac
  | _ : _ ⊢ e_castup ?A _ <: e_castup ?A _ : _ |- _ => idtac
  | H : _ ⊢ e_abs _ _ <: _ : _ |- _ =>
    pose (H' := H); apply abs_le in H' as (b & E)
  | H : _ ⊢ _ <: e_abs _ _ : _ |- _ =>
    pose (H' := H); apply abs_ge in H' as (b & E)
  | H : _ ⊢ e_bind _ _ <: _ : _ |- _ =>
    pose (H' := H); apply bind_le in H' as (b & E)
  | H : _ ⊢ _ <: e_bind _ _ : _ |- _ =>
    pose (H' := H); apply bind_ge in H' as (b & E)
  | H : _ ⊢ e_castup _ _ <: _ : _ |- _ =>
    pose (H' := H); apply castup_le in H' as (b & E)
  | H : _ ⊢ _ <: e_castup _ _ : _ |- _ =>
    pose (H' := H); apply castup_ge in H' as (b & E)
  | H : _ ⊢ e_castdn _ _ <: _ : _ |- _ =>
    pose (H' := H); apply castdn_le in H' as (b & E)
  | H : _ ⊢ _ <: e_castdn _ _ : _ |- _ =>
    pose (H' := H); apply castdn_ge in H' as (b & E)
  end; inversion E; subst; simpl in *
.

Lemma abs_pi_principal : forall Γ A b1 b2 T,
    Γ ⊢ e_abs A b1 <: e_abs A b2 : T ->
    exists B k, Γ ⊢ e_abs A b1 <: e_abs A b2 : e_pi A B /\ Γ ⊢ e_pi A B <: T : e_kind k.
Proof.
  intros.
  dependent induction H.
  - assert (Sub : G ⊢ e_abs A b1 <: e_abs A b2 : e_pi A B) by eauto.
    conclude_type_refl Sub. eauto.
  - edestruct IHusub1 as (B' & k' & Sub & Subpi); eauto.
    exists B', k'. split.
    + assumption.
    + eapply transitivity; eauto.
Qed.


Lemma pi_sub_inversion : forall Γ A B C D k,
    Γ ⊢ e_pi A B <: e_pi C D : e_kind k ->
    exists k' L,
      Γ ⊢ C <: A : e_kind k' /\
      forall x, x `notin` L -> Γ, x : C ⊢ B ^` x <: D ^` x : e_kind k.
Proof.
  intros.
  dependent induction H.
  - exists k1, L. auto.
  - apply IHusub1; auto.
    apply kind_sub_inversion_l in H0. destruct_pairs. congruence.
Qed.

Lemma abs_inversion : forall Γ A b1 b2 T,
    Γ ⊢ e_abs A b1 <: e_abs A b2 : T ->
    forall B k,
    Γ ⊢ T <: e_pi A B : e_kind k ->
    exists L, forall x, x `notin` L -> Γ, x : A ⊢ b1 ^` x <: b2 ^` x : B ^` x.
Proof.
  intros * Sub.
  dependent induction Sub; intros.
  - apply pi_sub_inversion in H3 as (k' & L' & H').
    exists (L `union` L'). intros.
    destruct_pairs. instantiate_cofinites. eauto.
  - apply IHSub1 with k; eauto using transitivity.
Qed.

Lemma abs_principal_inversion : forall Γ A b1 b2 B,
    Γ ⊢ e_abs A b1 <: e_abs A b2 : e_pi A B ->
    exists L, forall x, x `notin` L -> Γ, x : A ⊢ b1 ^` x <: b2 ^` x : B ^` x.
Proof.
  intros.
  conclude_type_refl H.
  now apply abs_inversion with (e_pi A B) k.
Qed.

Lemma castup_inversion : forall Γ e1 e2 A B,
    Γ ⊢ e_castup A e1 <: e_castup A e2 : B ->
    exists C k, Γ ⊢ e1 <: e2 : C /\ A ⟶ C /\ Γ ⊢ A <: B : e_kind k.
Proof.
  intros. dependent induction H.
  - eauto.
  - edestruct IHusub1 as (C & k1 & Sub1 & R & Sub2); eauto.
    exists C, k1; eauto using transitivity.
Qed.

Ltac rewrite_open_with_subst_impl G :=
  match G with
  | context [?e ^^ ?v] =>
    progress
      match v with
      | e_var_f _ => idtac
      | _ => erewrite (open_subst_eq e); eauto 3
      end
  end
.

Ltac rewrite_open_with_subst :=
  repeat
    match goal with
    | |- ?g => rewrite_open_with_subst_impl g
    end
.

Lemma type_preservation' : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> forall k n e1' e2', head_kind A k n -> e1 ⟹ e1' -> e2 ⟹ e2' -> Γ ⊢ e1' <: e2' : A.
Proof.
  intros * Sub.
  induction Sub; intros k' n' e1' e2' K R1 R2;
    try solve [inversion K | inversion R1 | inversion R2].
  - inversion R1; inversion R2; subst.
    + box_reasoning.
      * destruct k'; box_reasoning.
      * conclude_type_refl Sub2.
        apply s_app with A; auto.
        eapply IHSub2; eauto.
    + invert_sub_hyp. solve_impossible_reduction.
    + invert_sub_hyp. solve_impossible_reduction.
    + invert_sub_hyp.
      box_reasoning.
      * destruct k'; box_reasoning.
      * apply abs_pi_principal in Sub2 as (B' & k2 & Sub2 & Sub3).
        apply pi_sub_inversion in Sub3 as (k3 & L2 & Sub3 & Sub4).
        apply abs_principal_inversion in Sub2 as (L3 & Sub2).
        pick fresh x for (L3 `union` L2 `union` fv_expr b `union` fv_expr e0 `union` fv_expr B).
        instantiate_cofinites.
        rewrite (open_subst_eq b x t), (open_subst_eq e0 x t), (open_subst_eq B x t); auto.
        eauto 4 using substitution_cons, ctx_narrowing_cons.
  - inversion R1; inversion R2; subst.
    assert (G ⊢ e_mu t s : t) by eauto.
    instantiate_cofinites. conclude_freshes. rewrite_open_with_subst.
    pose (t' := t); assert (t' = t) as E by auto.
    replace (e_mu t s) with (e_mu t' s) by auto.
    replace t with ([(e_mu t s) / x] t). rewrite E.
    eapply substitution_cons; eauto.
    now apply fresh_subst_eq.

  - assert (head_kind A k' n') by (eapply head_kind_sub_l; eauto).
    eauto.
Qed.

Corollary type_preservation : forall Γ e1 e2 e1' e2' k,
    Γ ⊢ e1 <: e2 : e_kind k -> e1 ⟹ e1' -> e2 ⟹ e2' -> Γ ⊢ e1' <: e2' : e_kind k.
Proof.
  intros.
  eapply type_preservation'; eauto.
  Unshelve. exact 0.
Qed.

Hint Extern 1 (lc_expr _) => instantiate_cofinites : inst.

Ltac cleanup_hyps := instantiate_trivial_equals; destruct_pairs; clear_dups.
Ltac solve_progress_value := auto || left; eauto with inst.

Lemma pi_ge_inversion : forall Γ e A B k,
    Γ ⊢ e <: e_pi A B : k -> (exists A' B', e = e_pi A' B') \/ (exists C' D', e = e_all C' D').
Proof.
  intros.
  dependent induction H.
  - eauto.
  - eauto.
  - now apply IHusub1 with A B.
Qed.

Lemma normal_form_forall_pi : forall Γ e A,
    Γ ⊢ e : A -> value e ->
    forall C D, A = e_all C D \/ A = e_pi C D ->
    forall E F k, Γ ⊢ A <: e_pi E F : k ->
    (exists A' b, e = e_abs A' b) \/ (exists A' b, e = e_bind A' b).
Proof.
  intros * H V.
  dependent induction H.
    all: try solve [inversion V]. (* solving cases where `e` is not value *)
    all: intros C' D' [E | E]; inversion E; (* solving invalid cases *)
      subst; intros; solve_impossible_reduction; eauto. (* solving trivial base cases *)
  - assert (G ⊢ A <: e_pi E F : (e_kind k)).
    now apply transitivity with (e_all C' D') k0.
    apply pi_ge_inversion in H3. destruct H3; destruct_exists; subst.
    eapply IHusub1; eauto.
    eapply IHusub1; auto.
    apply transitivity with (e_all C' D') k0; eauto.
  - assert (G ⊢ A <: e_pi E F : (e_kind k)).
    now apply transitivity with (e_pi C' D') k0.
    apply pi_ge_inversion in H3. destruct H3; destruct_exists; subst.
    eapply IHusub1; eauto.
    eapply IHusub1; auto.
    apply transitivity with (e_pi C' D') k0; eauto.
Qed.

Lemma normal_form_pi : forall Γ e A B,
    Γ ⊢ e : e_pi A B -> value e ->
    (exists A' b, e = e_abs A' b) \/ (exists A' b, e = e_bind A' b).
Proof.
  intros. conclude_type_refl H.
  eapply normal_form_forall_pi; eauto.
Qed.


Ltac invert_to_normal_forms H :=
  match type of H with
  | _ ⊢ _ <: _ : e_pi ?A ?B => apply normal_form_pi in H; eauto; destruct H
  end; destruct_exists; subst
.

Ltac invert_operator_to_nf :=
  match goal with
  | H : _ ⊢ ?e : e_pi _ _ |- ?g =>
    match g with
    | context [e] => invert_to_normal_forms H
    | _ => fail
    end
  end
.

Ltac destruct_progressive_for_app :=
  let destruct_with_new_name H := (
      let V := fresh "V" in
      let e' := fresh "e'" in
      destruct H as [V | [e' H]])
  in
  match goal with
  | H : Progressive ?e |- exists e', e_app ?e _ ⟶ e' =>
    destruct_with_new_name H
  | H : EProgressive ?e |- exists e', ee_app ?e _ ⋆⟶ e' =>
    destruct_with_new_name H
  end
.

Definition is_castup (e : expr) : Prop :=
  match e with
  | e_castup _ _ => True
  | _ => False
  end
.

Lemma is_castup_dec : forall e,
    is_castup e \/ not (is_castup e).
Proof.
  destruct e; simpl; eauto.
Qed.

Lemma is_castup_eq : forall e,
    is_castup e -> exists A b, e = e_castup A b.
Proof.
  intros. destruct e; solve [inversion H | eauto].
Qed.

Definition is_bind (e : expr) : Prop :=
  match e with
  | e_bind _ _ => True
  | _ => False
  end
.

Lemma is_bind_dec : forall e,
    is_bind e \/ not (is_bind e).
Proof.
  destruct e; simpl; auto.
Qed.

Lemma is_bind_eq : forall e,
    is_bind e -> exists A b, e = e_bind A b.
Proof.
  intros. destruct e; solve [inversion H | eauto].
Qed.

Lemma num_type_inversion : forall Γ n A,
    Γ ⊢ e_num n : A -> Γ ⊢ e_int <: A : *.
Proof.
  intros.
  dependent induction H; eauto 3 using transitivity.
Qed.

Lemma int_le_inversion : forall Γ A B,
    Γ ⊢ e_int <: A : B -> A = e_int \/ exists B c, A = e_all B c.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma pi_le_inversion : forall Γ A B C k,
    Γ ⊢ e_pi A B <: C : k -> (exists D E, C = e_pi D E) \/ (exists D E, C = e_all D E).
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Lemma kind_le_inversion : forall Γ kl ek k,
    Γ ⊢ e_kind kl <: ek : k -> ek = * /\ kl = k_star /\ k = BOX.
Proof.
  intros.
  dependent induction H.
  - auto.
  - edestruct IHusub2; eauto. destruct H4. discriminate.
  - edestruct IHusub1 as (E1 & E2 & E3); auto; subst.
    apply reflexivity_l in H0. now apply box_never_welltype in H0.
Qed.

Lemma pi_of_kind : forall Γ A B C D E,
    Γ ⊢ e_pi A B <: e_pi C D : E -> exists k, E = e_kind k.
Proof.
  intros.
  dependent induction H; eauto.
  - edestruct IHusub1; eauto. subst.
    apply kind_le_inversion in H0.
    destruct_conjs; subst; eauto.
Qed.

Lemma forall_of_star : forall Γ A B C D E,
    Γ ⊢ e_all A B <: e_all C D : E -> E = *.
Proof.
  intros.
  dependent induction H; eauto.
  - erewrite IHusub1 in H0; eauto.
    apply kind_le_inversion in H0. now destruct_conjs.
Qed.


Lemma irreducible_value : forall Γ e A B,
    Γ ⊢ e : A -> A ⟶ B -> not (is_castup e) -> not (is_bind e) -> value e -> False.
Proof.
  intros * Sub R H1 H2 V.
  inversion V; subst.
  - apply kind_sub_inversion_l in Sub.
    destruct_conjs. subst. inversion R.
  - apply num_type_inversion, int_le_inversion in Sub.
    destruct Sub; destruct_conjs; subst; inversion R.
  - apply int_of_star in Sub. subst. inversion R.
  - apply abs_pi_principal in Sub as (C & k & _ & Sub).
    apply pi_le_inversion in Sub as [|]; destruct_conjs; subst; inversion R.
  - contradict H2. simpl. auto.
  - apply pi_of_kind in Sub as (k & E); subst.
    inversion R.
  - apply forall_of_star in Sub. subst. inversion R.
  - contradict H1. simpl. auto.
Qed.

Theorem progress : forall e1 e2 A,
    nil ⊢ e1 <: e2 : A -> Progressive e1 /\ Progressive e2.
Proof.
  intros.
  dependent induction H; cleanup_hyps;
    try solve [split; solve_progress_value].
  (* var is not value *)
  - inversion H0.
  (* app *)
  - conclude_refls H1. split; right;
    destruct_progressive_for_app;
    eauto 3; (* solves r_app cases *)
    invert_operator_to_nf.
    + inversion V; subst. exists (H5 ^^ t). eauto.
    + inversion V. inversion H11. subst.
        pick fresh x. instantiate_cofinites.
        exists (e_app (H5 ^` x) t). eauto.
    + inversion V; subst. exists (H6 ^^ t). eauto.
    + inversion V; inversion H11. subst.
        pick fresh x. instantiate_cofinites.
        exists (e_app (H6 ^` x) t). eauto.
  - split; right; eauto.
  - split.
    + destruct H2.
      * destruct (is_castup_dec e1), (is_bind_dec e1).
        -- apply is_castup_eq in H5; destruct_conjs; subst; eauto.
        -- apply is_castup_eq in H5; destruct_conjs; subst; eauto.
        -- apply is_bind_eq in H6; destruct_conjs; subst;
           eauto. Unshelve. exact 0.
        -- apply reflexivity_l in H1.
           eapply irreducible_value in H1; [easy | eauto..].
      * destruct H2. eauto.
    + destruct H3.
      * destruct (is_castup_dec e2), (is_bind_dec e2).
        -- apply is_castup_eq in H5; destruct_conjs; subst; eauto.
        -- apply is_castup_eq in H5; destruct_conjs; subst; eauto.
        -- apply is_bind_eq in H6; destruct_conjs; subst; eauto.
           Unshelve. exact 0.
        -- apply reflexivity_r in H1.
           eapply irreducible_value in H1; [easy | eauto..].
      * destruct H3. eauto.
Qed.

Ltac solve_progress_evalue := auto || left; solve_evalue.

Lemma extract_abs : forall A b,
    ee_abs (extract b) = extract (e_abs A b).
Proof.
  easy.
Qed.


Theorem extracted_progress : forall e1 e2 A,
    nil ⊢ e1 <: e2 : A -> forall e1' e2', extract e1 = e1' -> extract e2 = e2' ->
    EProgressive e1' /\ EProgressive e2'.
Proof.
  intros * H.
  dependent induction H; simpl; intros e1' e2' E1 E2; subst; auto;
    try solve [split; solve_progress_evalue].
  (* var is not value *)
  - inversion H0.
  (* app *)
  - instantiate_trivial_equals.
    destruct IHusub2 with (extract e1) (extract e2); auto.
    conclude_refls H1;
    split; right; destruct_progressive_for_app; eauto; (* solve r_app cases *)
      apply evalue_value in V; auto;
        invert_operator_to_nf; simpl.
    + exists ((extract H4) ⋆^^ (extract t)). constructor.
      replace (ee_abs (extract H4)) with (extract (e_abs H2 H4)) by reflexivity.
      all: eauto using lc_extract_lc.
    + pick fresh x. exists (ee_app (extract H4 ⋆^` x) (extract t)).
      eapply er_elim; eauto 3.
      replace (ee_bind (extract H4)) with (extract (e_bind H2 H4)) by reflexivity.
      eauto using lc_extract_lc.
    + exists ((extract H5) ⋆^^ (extract t)). constructor.
      replace (ee_abs (extract H5)) with (extract (e_abs H3 H5)) by reflexivity.
      all: eauto using lc_extract_lc.
    + pick fresh x. exists (ee_app (extract H5 ⋆^` x) (extract t)).
      eapply er_elim; eauto 3.
      replace (ee_bind (extract H5)) with (extract (e_bind H3 H5)) by reflexivity.
      eauto using lc_extract_lc.
  - split; right; exists ((extract s) ⋆^^ ee_mu (extract s));
      econstructor; replace (ee_mu (extract s)) with (extract (e_mu t s)) by auto;
      eauto using lc_extract_lc.
  (* castdn *)
  - instantiate_trivial_equals.
    destruct IHusub2 with (extract e1) (extract e2); auto.
    split.
    + destruct H2.
      * apply evalue_value in H2; auto.
        destruct (is_castup_dec e1), (is_bind_dec e1).
        -- apply is_castup_eq in H4 as (C & e1' & E). subst.
           simpl. right. exists (extract e1'). eauto.
        -- apply is_castup_eq in H4 as (C & e1' & E). subst.
           simpl. right. exists (extract e1'). eauto.
        -- apply is_bind_eq in H5 as (C & e1' & E). subst.
           simpl. right. pick fresh x. exists (ee_castdn (extract e1' ⋆^` x)).
           apply er_cast_inst with empty.
           replace (ee_bind (extract e1')) with (extract (e_bind C e1')) by reflexivity.
           eauto using lc_extract_lc. auto.
        -- apply reflexivity_l in H1.
           eapply irreducible_value in H1; [easy | eauto..].
      * destruct H2; eauto.
    + destruct H3.
      * apply evalue_value in H3; auto.
        destruct (is_castup_dec e2), (is_bind_dec e2).
        -- apply is_castup_eq in H4 as (C & e2' & E). subst.
           simpl. right. exists (extract e2'). eauto.
        -- apply is_castup_eq in H4 as (C & e2' & E). subst.
           simpl. right. exists (extract e2'). eauto.
        -- apply is_bind_eq in H5 as (C & e1' & E). subst.
           simpl. right. pick fresh x. exists (ee_castdn (extract e1' ⋆^` x)).
           apply er_cast_inst with empty.
           replace (ee_bind (extract e1')) with (extract (e_bind C e1')) by reflexivity.
           eauto using lc_extract_lc. auto.
        -- apply reflexivity_r in H1.
           eapply irreducible_value in H1; [easy | eauto..].
      * destruct H3; eauto.
  (* forall_l *)
  - split.
    + solve_progress_evalue.
    + instantiate_trivial_equals.
      now destruct IHusub3 with (extract (B ^^ t)) (extract C).
  (* forall_r *)
  - split.
    + instantiate_trivial_equals.
      now destruct IHusub2 with (extract A) (extract A).
    + solve_progress_evalue.
Qed.

Lemma bind_extraction_inversion : forall e ee,
    ee_bind ee = extract e ->
    exists A e', e = e_bind A e' /\ ee = extract e'.
Proof.
  induction e; simpl; intros; inversion H; eauto.
Qed.

Lemma abs_extraction_inversion : forall e ee,
    ee_abs ee = extract e ->
    exists A e', e = e_abs A e' /\ ee = extract e'.
Proof.
  induction e; simpl; intros; inversion H; eauto.
Qed.

Lemma castdn_extraction_inversion : forall e ee,
    ee_castdn ee = extract e ->
    exists e', e = e_castdn e' /\ ee = extract e'.
Proof.
  induction e; simpl; intros; inversion H; eauto.
Qed.

Lemma castup_extraction_inversion : forall e ee,
    ee_castup ee = extract e ->
    exists A e', e = e_castup A e' /\ ee = extract e'.
Proof.
  induction e; simpl; intros; inversion H; eauto.
Qed.

Ltac invert_extraction :=
  let A := fresh "A" in
  let e2 := fresh "e" in
  let E1 := fresh "E" in
  let E2 := fresh "E" in
  match goal with
  | H : ee_bind _ = extract _ |- _ =>
    apply bind_extraction_inversion in H as (A & e2 & E1 & E2)
  | H : ee_abs  _ = extract _ |- _ =>
    apply abs_extraction_inversion in H as (A & e2 & E1 & E2)
  | H : ee_castdn _ = extract _ |- _ =>
    apply castdn_extraction_inversion in H as (A & e2 & E1 & E2)
  | H : ee_castup _ = extract _ |- _ =>
    apply castup_extraction_inversion in H as (A & e2 & E1 & E2)
  end; subst; simpl in *
.

Ltac invert_extractions := repeat invert_extraction.


Lemma bind_inversion : forall Γ A b1 b2 T,
    Γ ⊢ e_bind A b1 <: e_bind A b2 : T ->
    exists B L, Γ ⊢ e_bind A b1 <: e_bind A b2 : e_all A B
         /\ Γ ⊢ e_all A B <: T : *
         /\ (forall x, x `notin` L -> Γ , x : A ⊢ b1 ^` x <: b2 ^` x : B ^` x)
         /\ (forall x, x `notin` L -> x `notin` fv_eexpr (extract (b1 ^` x)))
         /\ (forall x, x `notin` L -> x `notin` fv_eexpr (extract (b2 ^` x))).
Proof.
  intros. dependent induction H.
  - exists B. exists L. repeat split; eauto 2.
  - specialize (IHusub1 A b1 b2). instantiate_trivial_equals.
    destruct IHusub1 as (B' & L & IH). destruct_pairs.
    exists B', L. repeat split; eauto 3 using transitivity.
Qed.

Definition is_forall (e : expr) : Prop :=
  match e with
  | e_all _ _ => True
  | _ => False
  end
.

Lemma forall_l_sub_inversion : forall Γ A B C,
    Γ ⊢ e_all A B <: C : * ->
    not (is_forall C) ->
    exists e, mono_type e /\ Γ ⊢ e : A /\ Γ ⊢ B ^^ e <: C : *.
Proof.
  intros * Sub.
  dependent induction Sub; simpl; intros.
  + eauto.
  + contradiction.
  + contradiction.
  + eapply IHSub1; eauto.
    apply kind_sub_inversion_l in Sub2. destruct_pairs. congruence.
Qed.

Ltac split_all := repeat split.

Ltac rewrite_extract_invariant G e :=
  match G with
  | context [e ⋆^^ _] =>
    erewrite (notin_open_var_notin_open e); eauto
  end
.

Ltac find_extract_invariants :=
  repeat
    match goal with
    | H : ?x `notin` fv_eexpr (extract _) |- _  => autorewrite with reassoc in H; simpl in H
    | H : ?x `notin` fv_eexpr (?e ⋆^` ?x) |- ?G => rewrite_extract_invariant G e
    | _ => progress autorewrite with reassoc
    end
.

Lemma is_forall_eq : forall e,
    is_forall e -> exists A b, e = e_all A b.
Proof.
  intros. destruct e; simpl in *; inversion H; eauto.
Qed.

Lemma expr_of_box_never_be_reduced : forall A B a Γ1 Γ2,
    A ⟶ B -> Γ1 ⊢ a : A -> Γ2 ⊢ B : BOX -> False.
Proof.
  intros.
  conclude_type_refl H0.
  - inversion H.
  - eauto using expr_of_box_never_be_reduced'.
Qed.

Tactic Notation "absurd" "by" tactic(t) :=
  assert False by t; contradiction.

Lemma deterministic_type_reduction' : forall e e',
    e ⟶ e' -> forall Γ A n k, Γ ⊢ e : A -> head_kind A k n -> e ⟹ e'.
Proof.
  intros * R.
  induction R; intros * Sub K; eauto.
  (* r_app *)
  - dependent induction Sub.
    + box_reasoning.
      * destruct k; box_reasoning.
      * eauto.
    (* or `eauto using head_kind_sub_l` *)
    + eapply IHSub1; eauto. eapply head_kind_sub_l; eauto.
  (* r_inst *)
  - dependent induction Sub.
    + box_reasoning.
      * destruct k; box_reasoning.
      * apply bind_inversion in Sub2. destruct_conjs.
        eapply head_kind_sub_l in H6. inversion H6. eauto.
    + eapply IHSub1; eauto. eapply head_kind_sub_l; eauto.
  (* r_castdn *)
  - dependent induction Sub.
    + destruct k; box_reasoning.
      absurd by eauto 3 using expr_of_box_never_be_reduced.
    + eapply IHSub1; eauto. eapply head_kind_sub_l; eauto.
  (* r_cast_inst *)
  - dependent induction Sub.
    + destruct k; box_reasoning.
      absurd by eauto 3 using expr_of_box_never_be_reduced.
    + eapply IHSub1; eauto. eapply head_kind_sub_l; eauto.
  (* r_cast_elim *)
  - dependent induction Sub.
    + destruct k; box_reasoning.
      absurd by eauto 3 using expr_of_box_never_be_reduced.
    + eapply IHSub1; eauto. eapply head_kind_sub_l; eauto.
Qed.

Lemma deterministic_type_reduction : forall Γ e e' k,
    e ⟶ e' -> Γ ⊢ e : e_kind k -> e ⟹ e'.
Proof.
  intros.
  eapply deterministic_type_reduction'; eauto.
  Unshelve. exact 0.
Qed.

Lemma deterministic_type_reduction_2 : forall Γ e A A',
    A ⟶ A' -> Γ ⊢ e : A -> A ⟹ A'.
Proof.
  intros.
  conclude_type_refl H0.
  - inversion H.
  - eapply deterministic_type_reduction; eauto.
Qed.

Lemma deterministic_extracted_reduction : forall e e1 e2,
    extract e ⋆⟶ e1 -> extract e ⋆⟶ e2 ->
    forall Γ A, Γ ⊢ e : A -> e1 = e2.
Proof.
  induction e; simpl; intros E1 E2 R1 R2 Γ A Sub;
    solve_impossible_reduction.
  - inversion R1; inversion R2; subst;
      invert_extractions; solve_impossible_reduction.
    + dependent induction Sub.
      * assert (ee2 = ee5) by (eapply IHe1; eauto 3). now subst.
      * eauto 2.
    + now inversion H.
    + inversion H.
    + inversion H5.
    + inversion H. dependent induction Sub; eauto 2.
      clear IHSub1 IHSub2.
      apply bind_inversion in Sub2; destruct_conjs.
      pick fresh x'. instantiate_cofinites. find_extract_invariants.
  - inversion R1; inversion R2; subst. auto.
  - inversion R1; inversion R2; subst;
      invert_extractions; solve_impossible_reduction.
    + dependent induction Sub.
      * assert (ee2 = ee3) by (eapply IHe; eauto 3). now subst.
      * eauto 2.
    + inversion H. dependent induction Sub; eauto 2.
      clear IHSub1 IHSub2.
      apply bind_inversion in Sub2; destruct_conjs.
      pick fresh x'. instantiate_cofinites. find_extract_invariants.
    + inversion H3.
    + inversion H.
    + now inversion H.
Qed.

Theorem preservation : forall e1 e2 A,
    nil ⊢ e1 <: e2 : A ->
    forall e1'' e2'', extract e1 ⋆⟶ e1'' -> extract e2 ⋆⟶ e2''  ->
    exists e1' e2', extract e1' = e1''
             /\ extract e2' = e2''
             /\ e1 ⟶ e1'
             /\ e2 ⟶ e2'
             /\ nil ⊢ e1' <: e2' : A.
Proof.
  intros * Sub.
  dependent induction Sub; simpl; intros;
    solve_impossible_reduction;
    instantiate_trivial_equals.
  - inversion H0; subst.
    + inversion H1; subst.
      (* main case for r_app *)
      * destruct IHSub2 with ee2 ee0 as (e1' & e2' & IH); eauto.
        destruct_conjs. subst.
        exists (e_app e1' t), (e_app e2' t). repeat split; eauto 3.
      * invert_extractions. invert_sub_hyp. solve_impossible_reduction.
      * invert_extractions. invert_sub_hyp. solve_impossible_reduction.
    + invert_extractions. invert_sub_hyp.
      inversion H1; subst; solve_impossible_reduction.
      (* main case for r_beta *)
      exists (e ^^ t), (b ^^ t).
      autorewrite with reassoc.
      split_all; eauto.
      pose (B' := Sub2). apply abs_pi_principal in B'. destruct_conjs.
      apply pi_sub_inversion in H8 as (k' & L & Sub3).
      apply abs_principal_inversion in H5 as (L' & Sub4).
      pick fresh x for
           (L `union` L' `union` fv_expr e `union` fv_expr b `union` fv_expr B).
      instantiate_cofinites. destruct_pairs.
      rewrite_open_with_subst.
      eapply ctx_narrowing_cons in Sub4; eauto 4 using substitution_cons.
    + invert_extractions. invert_sub_hyp.
      inversion H1; subst; solve_impossible_reduction.
      (* main case for r_inst *)
      apply bind_inversion in Sub2 as (F & L1 & Hb). destruct_pairs.
      apply forall_l_sub_inversion in H6 as (m & M & Subm & Sub_inst); auto.
      exists (e_app (e ^^ m) t), (e_app (b ^^ m) t). split_all; simpl.
      * pick fresh x'. instantiate_cofinites. find_extract_invariants.
      * pick fresh x'. instantiate_cofinites. find_extract_invariants.
      * eauto.
      * eauto.
      * eapply s_app; eauto. apply s_sub with (F ^^ m) k_star; auto.
        pick fresh x' for
             (L `union` L0 `union` L1 `union`
                fv_expr e `union` fv_expr b `union` fv_expr F).
        rewrite_open_with_subst.
        eauto 3 using substitution_cons.
  - inversion H2; inversion H3; subst.
    (* r_mu *)
    assert (nil ⊢ e_mu t s : t) by eauto.
    exists (s ^^ (e_mu t s)), (s ^^ (e_mu t s)). split_all.
    + now rewrite extract_open_distr.
    + now rewrite extract_open_distr.
    + eauto.
    + eauto.
    + pick fresh x for (L `union` fv_expr t `union` fv_expr s).
      instantiate_cofinites.
      conclude_freshes. rewrite_open_with_subst.
      pose (t' := t). assert (t' = t) as E by auto.
      replace (e_mu t s) with (e_mu t' s) by auto.
      replace t with ([(e_mu t s) / x] t) by now apply fresh_subst_eq.
      rewrite E.
      eapply substitution_cons; eauto 3.
  - inversion H0; subst.
    + inversion H1; subst.
      (* main case for r_castdn *)
      * destruct IHSub2 with ee2 ee0 as (e1' & e2' & IH); eauto.
        destruct_conjs. subst.
        exists (e_castdn e1'), (e_castdn e2'). repeat split; eauto 3.
      * invert_extractions. invert_sub_hyp. inversion H3.
      * invert_extractions. invert_sub_hyp. inversion H3.
    + invert_extractions. invert_sub_hyp. inversion H1; subst; solve_impossible_reduction.
    (* main case for r_cast_inst *)
      apply bind_inversion in Sub2 as (F & L1 & Hb). destruct_pairs.
      apply forall_l_sub_inversion in H8 as (m & M & Subm & Sub_inst); auto.
      exists (e_castdn (e ^^ m)), (e_castdn (b ^^ m)). split_all; simpl.
      * pick fresh x'. instantiate_cofinites. find_extract_invariants.
      * pick fresh x'. instantiate_cofinites. find_extract_invariants.
      * eauto.
      * eauto.
      * eapply s_castdn; eauto.
        eapply s_sub with (F ^^ m) k_star; auto.
        pick fresh x' for (L `union` L0 `union` L1 `union` fv_expr e `union` fv_expr b `union` fv_expr F).
        rewrite_open_with_subst.
        eauto 3 using substitution_cons.
      * intro. apply is_forall_eq in H12. destruct_exists. subst. inversion H.
    + invert_extractions. invert_sub_hyp. inversion H1; subst; solve_impossible_reduction.
      (* main case for r_cast_elim *)
      * exists e, b. repeat split; eauto.
        apply castup_inversion in Sub2 as (C & k' & Sub & R & Sub').
        apply s_sub with C k'. auto.
        eapply type_preservation; eauto using deterministic_type_reduction. Unshelve. all: exact 0.
  - edestruct IHSub1 as (e1' & e2' & H1); eauto.
    destruct_pairs.
    exists e1', e2'. repeat split; eauto.
Qed.
