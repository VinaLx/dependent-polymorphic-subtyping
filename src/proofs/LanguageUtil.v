Require Export Declarative.Language.
Require Export List.
Require Export Program.Equality.

Export ListNotations.

Require Export Metalib.Metatheory.

Scheme sub_mut := Induction for usub       Sort Prop
  with  wf_mut := Induction for wf_context Sort Prop.

Notation "G ⊢ e : A" := (usub G e e A)
    (at level 65, e at next level, no associativity) : type_scope.
Notation "G ⊢ e1 <: e2 : A" := (usub G e1 e2 A)
    (at level 65, e1 at next level, e2 at next level, no associativity) : type_scope.

Notation "e1 ⟶ e2"  := (reduce  e1 e2)
    (at level 60, no associativity) : type_scope.
Notation "e1 ⋆⟶ e2" := (ereduce e1 e2)
    (at level 60, no associativity) : type_scope.
Notation "e1 ⟹ e2" := (dreduce e1 e2)
    (at level 60, no associativity) : type_scope.

Lemma dreduce_reduce : forall e1 e2,
    e1 ⟹ e2 -> e1 ⟶ e2.
Proof.
  intros. dependent induction H; eauto.
Qed.

Hint Resolve dreduce_reduce : core.

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.
Bind Scope ctx_scope with context.

Declare Scope expr_scope.
Delimit Scope expr_scope with exp.
Bind Scope expr_scope with expr.

Declare Scope eexpr_scope.
Delimit Scope eexpr_scope with eexp.
Bind Scope eexpr_scope with eexpr.

Notation "*"  := (e_kind k_star) : expr_scope.
Notation "'BOX'" := (e_kind k_box) : expr_scope.

Notation "` x" := (e_var_f x)
    (at level 0, x at level 0, no associativity): expr_scope.

Notation "G , x : A" := ((x, A) :: G)
    (left associativity, at level 62, x at level 0) : ctx_scope.

Notation "G1 ,, G2" := (app G2 G1)
    (left associativity, at level 62) : ctx_scope.

Notation "⊢ G" := (wf_context G)
    (no associativity, at level 65) : type_scope.

Notation "x : A ∈ G" := (binds x A G)
    (no associativity, A at next level, at level 65) : type_scope.

Notation "x # e" := (x `notin` fv_expr e)
    (no associativity, at level 65) : type_scope.

Notation "e < n > ^^ e' " := (open_expr_wrt_expr_rec n e' e)
    (at level 40, n at level 0, left associativity) : expr_scope.

Notation "e ^^ e'" := (open_expr_wrt_expr e e')
    (at level 40, left associativity) : expr_scope.

Notation "e ^` x" := (open_expr_wrt_expr e (e_var_f x))
    (at level 40, left associativity) : expr_scope.

Definition subst_ctx (e : expr) (x : exprvar) : context -> context :=
  map (subst_expr e x).

Notation "[ e1 / x ] e2" := (subst_expr e1 x e2)
    (at level 60, e1 at level 0,  x at level 0, right associativity) : expr_scope.
Notation "[ e // x ] ctx" := (subst_ctx e x ctx)
    (at level 60, e at level 0, x at level 0, right associativity) : ctx_scope.

Notation "e ⋆^^ e'" := (open_eexpr_wrt_eexpr e e')
    (at level 40, left associativity) : eexpr_scope.

Notation "e ⋆^` x" := (open_eexpr_wrt_eexpr e (ee_var_f x))
    (at level 40, left associativity) : eexpr_scope.

Notation "[ e1 ⋆/ x ] e2" := (subst_eexpr e1 x e2)
    (at level 60, e1 at level 0, x at level 0, right associativity) : eexpr_scope.

Notation "e ⋆ n ^^ e'" := (open_eexpr_wrt_eexpr_rec n e' e)
    (at level 40, n at level 0, left associativity) : eexpr_scope.

Open Scope ctx_scope.
Open Scope eexpr_scope.
Open Scope expr_scope.

Lemma binds__in_dom : forall t Γ x (A : t),
    x : A ∈ Γ -> x `in` dom Γ.
Proof.
  intros. induction Γ.
  - inversion H.
  - destruct a. destruct H.
    + inversion H. subst. simpl. auto.
    + simpl. auto.
Qed.

Lemma in_dom_insert : forall x Γ1 Γ2 (A : expr),
    x `in` dom (Γ1 , x : A ,, Γ2).
Proof.
  induction Γ2; intros.
  - simpl. auto.
  - destruct a. simpl. auto.
Qed.

Lemma binds_insert : forall Γ1 x (A : expr) Γ2,
   x : A ∈ Γ1 , x : A ,, Γ2.
Proof.
  induction Γ2; simpl.
  - auto.
  - destruct a. unfold binds. simpl. now right.
Qed.

Lemma binds_type_equal : forall Γ1 x A B Γ2,
    x : A ∈ Γ1 , x : B ,, Γ2 ->
    ⊢ Γ1 , x : B ,, Γ2 ->
    A = B.
Proof.
  unfold binds. intros. induction Γ2.
  - destruct H.
    + now inversion H.
    + inversion H0. subst.
      now apply binds__in_dom in H.
  - destruct a. destruct H.
    + inversion H. inversion H0. subst.
      now assert (x `in` dom (Γ1 , x : B ,, Γ2))
        by apply in_dom_insert.
    + inversion H0; auto.
Qed.

Lemma binds_type_not_equal : forall Γ1 x x' (A : expr) B C Γ2,
    x : A ∈ Γ1 , x' : B ,, Γ2 ->
    x' <> x ->
    x : A ∈ Γ1 , x' : C ,, Γ2.
Proof.
  intros.
  induction Γ2.
  - destruct H.
    + now inversion H.
    + auto.
  - destruct a. destruct H.
    + inversion H. subst. auto.
    + right. apply IHΓ2. assumption.
Qed.

Lemma binds_inversion : forall Γ x (A : expr),
    x : A ∈ Γ -> exists Γ1 Γ2, Γ = Γ1 , x : A ,, Γ2.
Proof.
  intros. induction Γ.
  - inversion H.
  - unfold binds in *. destruct a. destruct H.
    + inversion H. subst. exists Γ. exists []. reflexivity.
    + destruct IHΓ. assumption.
      destruct H0. subst.
      exists x0. exists (x1 , a : e). reflexivity.
Qed.

Lemma wf_uncons : forall Γ x A,
    ⊢ Γ, x : A -> ⊢ Γ.
Proof.
  intros. now inversion H.
Qed.

Hint Resolve wf_uncons : wf.

Theorem sub_ctx_wf : forall Γ e1 e2 A,
  Γ ⊢ e1 <: e2 : A -> ⊢ Γ.
Proof.
  intros.
  induction H; solve [assumption | pick fresh x; eauto with wf].
Qed.

Hint Resolve sub_ctx_wf : wf.

Lemma prefix_wf : forall Γ1 Γ2, ⊢ Γ1 ,, Γ2 -> ⊢ Γ1.
Proof.
  intros. induction Γ2.
  - assumption.
  - inversion H. auto.
Qed.

Hint Resolve prefix_wf : wf.

Lemma binds_consistent : forall Γ x A B,
    ⊢ Γ -> x : A ∈ Γ -> x : B ∈ Γ -> A = B.
Proof.
  intros.
  apply binds_inversion in H1 as [Γ1 [Γ2 E]]. subst.
  eapply binds_type_equal; eauto.
Qed.

Open Scope expr_scope.

Lemma wf_ctx_type_correct : forall Γ1 Γ2 x A,
  ⊢ Γ1 , x : A ,, Γ2 -> exists k, Γ1 ⊢ A : e_kind k.
Proof.
  induction Γ2; intros.
  - inversion H. now exists k.
  - inversion H. subst. now apply IHΓ2 with x.
Qed.

Lemma wf_ctx_type_correct_cons : forall Γ x A,
    ⊢ Γ, x : A -> exists k, Γ ⊢ A : e_kind k.
Proof.
  intros. eapply wf_ctx_type_correct.
  replace (Γ, x : A) with (Γ, x : A,, nil) in H by reflexivity.
  eassumption.
Qed.

Lemma var_in_ctx_weakening : forall Γ2 Γ1 Γ3 x (A : expr),
    x : A ∈ Γ1 ,, Γ3 ->
    x : A ∈ Γ1 ,, Γ2 ,, Γ3.
Proof.
  intros. apply binds_app_1 in H as [H | H].
  - auto.
  - rewrite <- app_assoc in *.
    now apply binds_app_3.
Qed.

Theorem fresh_open_rec : forall x e1 e2 n,
  x # e1 -> x # e2 -> x # e1 <n> ^^ e2.
Proof.
  intros x e1.
  induction e1; simpl; intros e2 n' Hfresh1 Hfresh2; eauto 4.
  - now destruct (n' == n).
Qed.

Corollary fresh_open : forall x e1 e2,
  x # e1 -> x # e2 -> x # e1 ^^ e2.
Proof.
  intros. now apply fresh_open_rec.
Qed.

Corollary fresh_open_var : forall x e y,
  x # e -> x <> y -> x # e ^` y.
Proof.
  intros. apply fresh_open; auto.
Qed.

Theorem fresh_close_rec : forall e1 e2 x n,
    x # e1 <n> ^^ e2 -> x # e1.
Proof.
  induction e1; intros; simpl in *; eauto 4.
Qed.

Theorem fresh_close : forall e1 e2 x,
    x # e1 ^^ e2 -> x # e1.
Proof.
  intros until x. apply fresh_close_rec.
Qed.

Hint Resolve fresh_open_var : fresh.
Hint Resolve fresh_close : fresh.

Fixpoint context_fresh (x : atom) (ctx : context) : Prop :=
  match ctx with
  | nil => True
  | ((pair y t) :: ctx') => x # t /\ context_fresh x ctx'
  end
.

Hint Unfold context_fresh : core.

Lemma ctx_app_cons_assoc : forall (Γ1 Γ2 : context) x A,
    Γ1 ,, Γ2 , x : A = Γ1 ,, (Γ2 , x : A).
Proof.
  easy.
Qed.

Hint Rewrite ctx_app_cons_assoc : assoc.

Lemma open_rec_eq_cancel : forall e e1 e2 m n,
    m <> n -> e <m> ^^ e1 <n> ^^ e2 = e <m> ^^ e1 ->
    e <n> ^^ e2 = e.
Proof.
  induction e; simpl; intros; auto 3;
    try solve
        [inversion H0 as [[Hinv1 Hinv2]];
         (apply IHe1 in Hinv1; apply IHe2 in Hinv2); (auto 2 || congruence)].
  - destruct (m == n).
    + destruct (n0 == n); congruence.
    + simpl in H0. destruct (n0 == n); easy.
  - inversion H0 as [[Hinv1]].
    apply IHe in Hinv1; (auto || congruence).
Qed.

Hint Resolve open_rec_eq_cancel : ln.

Lemma lc_open_eq : forall e,
    lc_expr e -> forall n e', e <n> ^^ e' = e.
Proof.
  intros e LC. induction LC; simpl; intros;
    try solve
        [ reflexivity
        | pick fresh x; rewrite IHLC;
          try erewrite open_rec_eq_cancel with (m := 0); eauto
        | now (rewrite IHLC1; rewrite IHLC2)].
Qed.

Lemma subst_open_rec_distr : forall e x v e' n,
    lc_expr v ->
    [v / x] e <n> ^^ e' = ([v / x] e) <n> ^^ ([v / x] e').
Proof.
  induction e; simpl; intros; auto;
    try solve [(rewrite IHe || rewrite IHe1, IHe2); auto].
  - destruct (n0 == n); auto.
  - destruct (x == x0). rewrite lc_open_eq; auto. auto.
Qed.

Lemma subst_open_distr : forall e x v e',
    lc_expr v ->
    [v / x] e ^^ e' = ([v / x] e) ^^ ([v / x] e').
Proof.
  intros. unfold open_expr_wrt_expr. now rewrite subst_open_rec_distr.
Qed.

Lemma subst_open_var_assoc : forall e x v y,
    y <> x -> lc_expr v ->
    ([v / x] e) ^` y = [v / x] e ^` y.
Proof.
  intros.
  assert ([v / x] e ^` y = ([v / x] e) ^^ ([v / x] `y))
    by now apply subst_open_distr.
  assert ([v / x] `y = `y) by (simpl; destruct (y == x); easy).
  now rewrite H2 in H1.
Qed.

Hint Rewrite subst_open_var_assoc : assoc.

Lemma fresh_subst_eq : forall e x e', x # e -> [e' / x] e = e.
Proof.
  induction e; simpl; intros;
    try solve [auto | (rewrite IHe || rewrite IHe1, IHe2); auto].
  - destruct (x == x0).
    + apply notin_singleton_1 in H. contradiction.
    + auto.
Qed.

Lemma open_subst_eq : forall e x v,
    x # e -> lc_expr v ->
    e ^^ v = [v / x] e ^` x.
Proof.
  intros.
  rewrite subst_open_distr. simpl.
  rewrite eq_dec_refl.
  rewrite fresh_subst_eq.
  all: easy.
Qed.


Lemma lc_subst : forall e v x,
    lc_expr e -> lc_expr v -> lc_expr ([v / x] e).
Proof.
  intros. induction H; simpl; auto.
  - destruct (x0 == x); auto.

  Ltac solve_inductive_case_with C :=
    pick fresh x' and apply C; auto; intros; rewrite subst_open_var_assoc; auto.

  - solve_inductive_case_with lc_e_abs.
  - solve_inductive_case_with lc_e_pi.
  - solve_inductive_case_with lc_e_all.
  - solve_inductive_case_with lc_e_bind.
  - solve_inductive_case_with lc_e_mu.
Qed.

Lemma lc_open_preserve : forall e e',
    (exists L, forall x, x `notin` L -> lc_expr (e ^` x)) ->
    lc_expr e' -> lc_expr (e ^^ e').
Proof.
  intros e e' [L H] H'.
  pick fresh x for (fv_expr e `union` L).
  assert (x # e) by auto.
  rewrite (open_subst_eq _ _ _ H0 H').
  apply lc_subst; auto.
Qed.

Fixpoint lc_ctx (c : context) : Prop :=
  match c with
  | nil => True
  | c', x : A => lc_expr A /\ lc_ctx c'
  end
.

Import Program.Tactics.

Ltac instantiate_cofinite_with H x :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
    let H1 := fresh "H" in
    assert (H1 : x `notin` L) by eauto;
    specialize (H x H1); clear H1
  end
.

Ltac instantiate_cofinites_with x :=
  repeat match goal with
  | H : forall x, x `notin` ?L -> _ |- _ =>
    instantiate_cofinite_with H x
  end
.

Ltac detect_fresh_var_and_do t :=
  match goal with
  | Fr : ?x `notin` ?L1 |- _ => t x
  | _ =>
    let x := fresh "x" in
    pick fresh x; t x
  end
.

Ltac instantiate_cofinites :=
  detect_fresh_var_and_do instantiate_cofinites_with.

Ltac instantiate_cofinite H :=
  let f x := instantiate_cofinite_with H x in
  detect_fresh_var_and_do f
.

Ltac pose_cofinite_with H x H' :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
    let Fr := fresh "Fr" in
    assert (Fr : x `notin` L) by eauto;
    pose proof (H x Fr) as H'; clear Fr
  end
.

Ltac pose_cofinite H H' :=
  let f x := pose_cofinite_with H x H' in
  detect_fresh_var_and_do f
.

Tactic Notation "pose" "cofinite" ident(H) :=
  let H' := fresh H in
  pose_cofinite H H'.

Tactic Notation "pose" "cofinite" ident(H) "as" ident(H') :=
  pose_cofinite H H'.

Lemma usub_lc : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> lc_ctx Γ /\ lc_expr e1 /\ lc_expr e2 /\ lc_expr A.
Proof.
  Local Ltac solve_with_pairs_in_cofinites := instantiate_cofinites; destruct_pairs; auto.

  apply sub_mut with
      (P := fun c e1 e2 A (_ : c ⊢ e1 <: e2 : A) =>
        lc_ctx c /\ lc_expr e1 /\ lc_expr e2 /\ lc_expr A)
      (P0 := fun c (_ : ⊢ c) => lc_ctx c); simpl; intros; auto;
    try solve
        [repeat split;
         solve [ solve_with_pairs_in_cofinites
               | econstructor; intros; solve_with_pairs_in_cofinites]].

  - induction G. inversion b.
    destruct a, H. inversion w. subst. destruct b.
    + inversion H1. now subst.
    + simpl. destruct IHG as (lc_G & lc_x & lc_x' & lc_A); auto.
  - repeat split; destruct_pairs; auto.
    inversion H3. subst. eauto using lc_open_preserve.
Qed.

Lemma mono_lc : forall e,
    mono_type e -> lc_expr e.
Proof.
  intros. induction H; eauto.
Qed.

Ltac solve_basic_lc :=
  match goal with
  | H : _ ⊢ ?e <: _ : _ |- lc_expr ?e => apply usub_lc in H
  | H : _ ⊢ _ <: ?e : _ |- lc_expr ?e => apply usub_lc in H
  | H : _ ⊢ _ <: _ : ?e |- lc_expr ?e => apply usub_lc in H
  | H : forall x, x `notin` ?L -> _, x : ?A ⊢ _ <: _ : _ |- lc_expr ?A =>
    instantiate_cofinite H; apply usub_lc in H; simpl in H
  end; destruct_pairs; assumption
.

Hint Resolve mono_lc : core.

Hint Extern 1 (lc_expr _) => solve_basic_lc : core.

Lemma lc_abs_param_l : forall Γ A b1 e T,
    Γ ⊢ e_abs A b1 <: e : T -> lc_expr A.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma lc_bind_param_l : forall Γ A b1 e T,
    Γ ⊢ e_bind A b1 <: e : T -> lc_expr A.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma lc_abs_param_r : forall Γ A b2 e T,
    Γ ⊢ e <: e_abs A b2 : T -> lc_expr A.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma lc_bind_param_r : forall Γ A b2 e T,
    Γ ⊢ e <: e_bind A b2 : T -> lc_expr A.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma lc_castup_l : forall Γ A b e T,
    Γ ⊢ e_castup A b <: e : T -> lc_expr A /\ lc_expr b.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma lc_castup_r : forall Γ e A b T,
    Γ ⊢ e <: e_castup A b : T -> lc_expr A /\ lc_expr b.
Proof.
  intros. dependent induction H; eauto.
Qed.

Ltac solve_more_lc :=
  match goal with
  | H : _ ⊢ e_abs ?A _ <: _ : _ |- lc_expr ?A => apply lc_abs_param_l in H
  | H : _ ⊢ _ <: e_abs ?A _ : _ |- lc_expr ?A => apply lc_abs_param_r in H
  | H : _ ⊢ e_bind ?A _ <: _ : _ |- lc_expr ?A => apply lc_bind_param_l in H
  | H : _ ⊢ _ <: e_bind ?A _ : _ |- lc_expr ?A => apply lc_bind_param_r in H
  | H : _ ⊢ e_castup ?A _ <: _ : _ |- lc_expr ?A => apply lc_castup_l in H
  | H : _ ⊢ _ <: e_castup ?A _ : _ |- lc_expr ?A => apply lc_castup_r in H
  | H : _ ⊢ e_castup _ ?b <: _ : _ |- lc_expr ?b => apply lc_castup_l in H
  | H : _ ⊢ _ <: e_castup _ ?b : _ |- lc_expr ?b => apply lc_castup_r in H
  end; destruct_conjs; assumption
.

Hint Extern 1 (lc_expr _) => solve_more_lc : core.

Lemma subst_mono : forall e x e',
    mono_type e -> mono_type e' -> mono_type ([e' / x] e).
Proof.
  intros.
  induction H; simpl; eauto.
  (* var *)
  - destruct (x0 == x); auto.
  - pick fresh x' and apply mono_pi.
    + assumption.
    + autorewrite with assoc; auto.
  - pick fresh x' and apply mono_lambda.
    + assumption.
    + autorewrite with assoc; auto.
  - pick fresh x' and apply mono_bind.
    + assumption.
    + autorewrite with assoc; auto.
  - pick fresh x' and apply mono_mu.
    + assumption.
    + autorewrite with assoc; auto.
Qed.

Hint Resolve subst_mono : core.

Ltac instantiate_trivial_equals := repeat
  match goal with
  | H : ?a ~= ?a -> _ |- _ => specialize (H JMeq_refl)
  | H : ?a  = ?a -> _ |- _ => specialize (H eq_refl)
  end
.

Lemma strengthen_cofinite : forall L' P L ,
    (forall x, x `notin` L -> P x) ->
    (forall x, x `notin` (L `union` L') -> P x).
Proof.
  intros. auto.
Qed.

(*
Adjusting the cofinite requirement in the hypothesis to
help 'eauto' inferring the often-omitted cofinite lists
*)
Ltac adjust_cofinites L' :=
  repeat
    match goal with
    | H : forall x, x `notin` ?L -> _ |- _ =>
      match L with
      | context [L'] => fail 1
      | _ =>
        let H' := fresh H in
        pose proof (strengthen_cofinite L' _ _ H) as H';
        simpl in H'; clear H
      end
    end
.

Ltac adjust_cofinites_for gather :=
  let L := gather in
  adjust_cofinites L.

(*
1. Using the '+' tactical to enable backtracking in case of fail on
   branches of one constructor
2. Putting s_forall in front of s_forall_l and s_forall_r,
   and omitting s_sub to prevent potential infinite loop, when
   try_constructors are put into a repeat match loop
*)
Ltac try_constructors :=
  eapply s_abs +
  eapply s_pi +
  eapply s_app +
  eapply s_bind +
  eapply s_mu +
  eapply s_castup +
  eapply s_castdn +
  eapply s_forall +
  eapply s_forall_l +
  eapply s_forall_r.

(*
Neither gather_atoms_with in Metalib, or gather_vars_with in TLC
allows `F` to be a tactic function.
*)
Ltac gather_atoms_with_tactic F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := F H in
      match V with
      | context [FH] => fail 1
      | _ => gather (FH `union` V)
      end
    | _ => V
    end in
  let L := gather empty in eval simpl in L.

Ltac apply_fresh_base_fixed H gather_vars atom_name :=
  let L := gather_vars in
  let L := beautify_fset L in
  pick fresh atom_name excluding L and apply H.

Ltac discharge_equality E :=
  try solve [inversion E]; subst; try (rewrite E in *; clear E).
