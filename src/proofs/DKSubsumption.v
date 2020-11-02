Require Import DKDeclarative.
Require Import LanguageUtil.
Require Import BasicProperties.
Require Import Program.Tactics.
Require Import Omega.

Ltac destruct_var_equal :=
  match goal with
  | H : context [if ?n1 == ?n2 then _ else _] |- _ => destruct (n1 == n2); subst
  | |- context [if ?n1 == ?n2 then _ else _] => destruct (n1 == n2); subst
  end
.

Ltac destruct_var_equals := repeat destruct_var_equal.

Notation "⫦ G" := (dk_wf_ctx G)
  (at level 65, no associativity) : type_scope.

Notation "G ⫦ A" := (dk_wf_tp G A)
  (at level 65, no associativity) : type_scope.

Notation "G ⫦ A <: B" := (dk_sub G A B)
  (at level 65, A at next level, no associativity) : type_scope.

Notation "x ∈ G" := (In x G)
  (at level 65, no associativity) : type_scope.

Notation "x #' A" := (x `notin` fv_type A)
    (at level 65, no associativity) : type_scope.

Notation "`' x" := (t_var_f x)
    (at level 0, x at level 0, no associativity): type_scope.

Declare Scope dk_ctx_scope.
Delimit Scope dk_ctx_scope with dk_ctx.
Bind Scope dk_ctx_scope with dkcontext.

Notation "G ,' x" := (x :: G)
    (left associativity, at level 62, x at level 0) : dk_ctx_scope.

Open Scope dk_ctx_scope.

Declare Scope dk_type_scope.
Delimit Scope dk_type_scope with dk_tp.
Bind Scope dk_type_scope with type.

Notation "e < n > ^^' e' " := (open_type_wrt_type_rec n e' e)
    (at level 40, n at level 0, left associativity) : dk_type_scope.

Notation "e ^^' e'" := (open_type_wrt_type e e')
    (at level 40, left associativity) : dk_type_scope.

Notation "e ^`' x" := (open_type_wrt_type e (t_var_f x))
    (at level 40, left associativity) : dk_type_scope.

Notation "[ e1 /' x ] e2" := (subst_type e1 x e2)
    (at level 60, e1 at level 0,  x at level 0, right associativity) : dk_type_scope.
Open Scope dk_type_scope.


Fixpoint type_size (t : type) : nat :=
  match t with
  | t_arrow A B => S (type_size A + type_size B)
  | t_all A => S (type_size A)
  | _ => 0
  end
.

Lemma size_open_var_eq_rec : forall A x n,
    type_size (A <n> ^^' `' x) = type_size A.
Proof.
  induction A; simpl; intros; destruct_var_equals; simpl; auto.
Qed.

Lemma size_open_var_eq : forall A x,
    type_size (A ^`' x) = type_size A.
Proof.
  intros. apply size_open_var_eq_rec.
Qed.


Lemma dk_open_cancel : forall e e1 e2 m n,
    m <> n -> e <m> ^^' e1 <n> ^^' e2 = e <m> ^^' e1 ->
    e <n> ^^' e2  = e.
Proof.
  induction e; simpl; intros; auto.
  - destruct_var_equals; simpl in *; auto.
    + contradiction.
    + destruct (n == n); solve [auto | contradiction].
  - inversion H0. rewrite IHe with (e1 := e1) (m := S m); auto.
  - inversion H0.
    rewrite IHe1 with (e2 := e0) (m := m).
    rewrite IHe2 with (e1 := e0) (m := m).
    all: auto.
Qed.

Lemma dk_lc_open_eq : forall t,
    lc_type t -> forall t' n, t <n> ^^' t' = t.
Proof.
  intros t Lc. induction Lc; simpl; intros; auto.
  - instantiate_cofinites.
    rewrite dk_open_cancel with (m := 0) (e1 := t_var_f x); auto.
  - now rewrite IHLc1, IHLc2.
Qed.

Lemma dk_subst_open_rec : forall t t1 t2 n x,
    lc_type t1 ->
    [t1 /' x] t <n> ^^' t2 = ([t1 /' x] t) <n> ^^' ([t1 /' x] t2).
Proof.
  induction t; simpl; intros; destruct_var_equals;
    try solve [auto | (rewrite IHt || rewrite IHt1, IHt2); auto].
  (* var *)
  - now rewrite dk_lc_open_eq.
Qed.

Lemma dk_subst_open : forall t t1 t2 x,
    lc_type t1 ->
    [t1 /' x] t ^^' t2 = ([t1 /' x] t) ^^' ([t1 /' x] t2).
Proof.
  intros.
  now apply dk_subst_open_rec.
Qed.

Lemma dk_subst_open_var : forall t t' x1 x2,
    x2 <> x1 -> lc_type t' ->
    [t' /' x1] t ^`' x2 = ([t' /' x1] t) ^`' x2.
Proof.
  intros.
  replace `' x2 with ([t' /' x1] `' x2) at 2.
  - apply dk_subst_open. auto.
  - simpl. destruct (x2 == x1); [contradiction | auto].
Qed.

Lemma dk_fresh_subst_eq : forall t x t',
    x #' t -> [t' /' x] t = t.
Proof.
  induction t; simpl; intros; destruct_var_equals; auto.
  - assert (x0 <> x0) by auto. contradiction.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Qed.


Lemma dk_open_subst_eq : forall t x t',
    x #' t -> lc_type t' ->
    t ^^' t' = [t' /' x] t ^`' x.
Proof.
  intros.
  rewrite dk_subst_open; auto. simpl.
  rewrite eq_dec_refl, dk_fresh_subst_eq; auto.
Qed.

Require Import Arith.Compare_dec.

Fixpoint shift (e : expr) (n : nat) : expr :=
  match e with
  | e_var_b n' =>
    if le_lt_dec n n' then e_var_b (S n') else (e_var_b n')
  | e_var_f x => e_var_f x
  | e_kind k => e_kind k
  | e_int => e_int
  | e_num n => e_num n
  | e_app e1 e2 => e_app (shift e1 n) (shift e2 n)
  | e_pi A B => e_pi (shift A n) (shift B (S n))
  | e_all A B => e_all (shift A n) (shift B (S n))
  | e_abs  A e => e_abs  (shift A n) (shift e (S n))
  | e_bind A e => e_bind (shift A n) (shift e (S n))
  | e_mu   A e => e_mu   (shift A n) (shift e (S n))
  | e_castup A e => e_castup (shift A n) (shift e n)
  | e_castdn   e => e_castdn (shift e n)
  end
.



Lemma eq_cofinite_impossible_1 : forall x L,
    (forall x', x' `notin` L -> `x' = `x) -> False.
Proof.
  intros. pick fresh x' for (add x L).
  instantiate_cofinites. inversion H.
  assert (x' <> x) by auto. contradiction.
Qed.

Lemma eq_cofinite_impossible_2 : forall x L,
    (forall x', x' `notin` L -> `x = `x') -> False.
Proof.
  intros.
  assert (forall x', x' `notin` L -> `x' = `x).
  intros. now instantiate_cofinites.
  eapply eq_cofinite_impossible_1; eauto.
Qed.

Lemma false_elim' : forall (e : expr) e',
    False -> e = e'.
Proof.
  intros. inversion H.
Qed.


Hint Resolve eq_cofinite_impossible_1 : cofinite_eq.
Hint Resolve eq_cofinite_impossible_2 : cofinite_eq.
Hint Resolve false_elim' : cofinite_eq.

Lemma cofinite_open_eq_rec : forall e1 e2 n L,
    (forall x, x `notin` L -> e1 <n> ^^ `x = e2 <n> ^^ `x) ->
    e1 = e2.
Proof.
  induction e1; unfold open_expr_wrt_expr; simpl; intros * H;
    destruct e2; simpl in H;
      destruct_var_equals;
      try solve
          (* solve impossible cases *)
          [ instantiate_cofinites; inversion H
          (* solve var cases involving eq_cofinite_impossible *)
          | eauto with cofinite_eq
          (* solve normal var cases *)
          | instantiate_cofinites; auto
          (* solve recursive cases with two branches *)
          | erewrite (IHe1_1 e2_1), (IHe1_2 e2_2);
            [ reflexivity
            | intros; instantiate_cofinites; inversion H; eauto ..]
          (* solve recursive cases with one branch *)
          | erewrite (IHe1 e2);
            [ reflexivity
            | intros; instantiate_cofinites; inversion H; eauto]
          ].
    Unshelve. all: auto.
Qed.

Lemma cofinite_open_eq : forall e1 e2 L,
    (forall x, x `notin` L -> e1 ^` x = e2 ^` x) ->
    e1 = e2.
Proof.
  intros.
  eapply cofinite_open_eq_rec. eauto.
Qed.

Lemma shift_open_2 : forall e x n1 n2,
    n2 > n1 ->
    shift (e <n1> ^^ `x) n2 = shift e n2 <n1> ^^ `x.
Proof.
  induction e; simpl; intros;
    try solve [auto | (rewrite IHe1, IHe2 || rewrite IHe); auto with arith].
  - destruct (n1 == n), (le_lt_dec n2 n); subst; simpl.
    + assert (not (n2 > n)) by omega. contradiction.
    + destruct (n == n); [auto | contradiction].
    + destruct (le_lt_dec n2 n), (n1 == S n); subst.
      * assert (not (n2 <= n)) by omega. contradiction.
      * auto.
      * assert (not (n2 <= n)) by omega. contradiction.
      * assert (not (n2 <= n)) by omega. contradiction.
    + destruct (le_lt_dec n2 n), (n1 == n); subst.
      * assert (not (n2 <= n)) by omega. contradiction.
      * assert (not (n2 <= n)) by omega. contradiction.
      * assert (not (n2 > n)) by omega. contradiction.
      * auto.
Qed.

Lemma shift_open_var_2 : forall e x n,
    n > 0 ->
    shift (e ^` x) n = shift e n ^` x.
Proof.
  intros.
  unfold open_expr_wrt_expr. rewrite shift_open_2; auto.
Qed.

Lemma lc_shift_eq : forall e,
    lc_expr e -> forall n, shift e n = e.
Proof.
  intros e H.
  induction H; simpl; intros; auto;
    try solve
        [ now rewrite IHlc_expr1, IHlc_expr2
        | now rewrite IHlc_expr
        (* this is ugly, but I don't think I have other choices *)
        | (assert (shift B (S n) = B) as H' || assert (shift e (S n) = e) as H');
          [ eapply cofinite_open_eq with (L := L);
            intros; rewrite <- shift_open_var_2; eauto 2 with arith
          | now rewrite H', IHlc_expr
          ]
        ].
Qed.

Reserved Notation "⌈ A ⌉" (at level 0, no associativity).

Fixpoint dk_type_to_expr (e : type) : expr :=
  match e with
  | t_var_b n => e_var_b n
  | t_var_f x => e_var_f x
  | t_int => e_int
  | t_arrow A B => e_pi ⌈ A ⌉ (shift ⌈ B ⌉ 0)
  | t_all A => e_all * ⌈ A ⌉
  end
where "⌈ A ⌉" := (dk_type_to_expr A)
.

Reserved Notation "⌈⌈ G ⌉⌉" (at level 0, no associativity).

Fixpoint dk_context_to_context (c : dkcontext) : context :=
  match c with
  | nil => nil
  | x :: G => ( pair x * ) :: ⌈⌈ G ⌉⌉
  end
where "⌈⌈ G ⌉⌉" := (dk_context_to_context G)
.

Lemma type_open_fresh_rec : forall x t1 t2 n,
    x #' t1 -> x #' t2 -> x #' t1 <n> ^^' t2.
Proof.
  induction t1; intros; simpl; destruct_var_equals; simpl; auto.
  - simpl in H.
    assert (x #' t1_1) by auto. assert (x #' t1_2) by auto.
    specialize (IHt1_1 t2 n H1 H0).
    specialize (IHt1_2 t2 n H2 H0).
    auto.
Qed.

Lemma type_open_fresh : forall x t1 t2,
    x #' t1 -> x #' t2 -> x #' t1 ^^' t2.
Proof.
  intros. eapply type_open_fresh_rec; eauto.
Qed.

Lemma notin_strengthening : forall A xs1 (x1 : A) x2 xs2,
    not (x1 ∈ xs1 ,' x2 ,, xs2) -> not (x1 ∈ xs1 ,, xs2).
Proof.
  induction xs2; simpl; intros; intro.
  - contradict H. auto.
  - destruct H0.
    + contradict H; auto.
    + apply IHxs2; auto.
Qed.

Lemma in_erase : forall A xs1 (x1 : A) x2 xs2,
    x1 ∈ xs1 ,' x2 ,, xs2 -> x1 <> x2 -> x1 ∈ xs1 ,, xs2.
Proof.
  induction xs2; simpl; intros.
  - destruct H.
    + symmetry in H. contradiction.
    + auto.
  - destruct H; auto.
Qed.

Lemma wf_strengthening : forall Γ1 x Γ2,
    ⫦ Γ1 ,' x ,, Γ2 -> ⫦ Γ1 ,, Γ2.
Proof.
  induction Γ2; simpl; intros; inversion H; subst.
  - assumption.
  - eauto using notin_strengthening.
Qed.


Lemma wft_strengthening : forall Γ1 Γ2 x A,
    Γ1 ,' x ,, Γ2 ⫦ A -> x #' A -> Γ1 ,, Γ2 ⫦ A.
Proof.
  intros.
  dependent induction H; simpl in *.
  - constructor.
    + eauto using wf_strengthening.
    + eapply in_erase. eassumption. auto.
  - eauto using wf_strengthening.
  - eauto.
  - pick fresh x' excluding (add x (union L (fv_type A))) and apply wf_tp_all.
    replace (x' :: Γ2 ++ Γ1) with ((x' :: Γ2) ++ Γ1) by auto.
    eapply H0; simpl; eauto.
    eapply type_open_fresh; eauto.
Qed.

Lemma wft_lc : forall Γ A,
    Γ ⫦ A -> lc_type A.
Proof.
  intros. induction H; eauto.
Qed.

Hint Resolve wft_lc : dk.

Lemma wft_strengthening_cons : forall Γ x A,
    Γ ,' x ⫦ A -> x #' A -> Γ ⫦ A.
Proof.
  intros.
  replace Γ with (Γ ,, nil) by auto.
  eapply wft_strengthening; eauto.
Qed.

Lemma lc_subst_reverse_impl : forall n, forall A, type_size A <= n -> forall B C x,
    lc_type ([B /' x] A) -> lc_type B -> lc_type C -> lc_type ([C /' x] A).
Proof.
  induction n; simpl; intros; destruct A; simpl in *; destruct_var_equals; auto.
  - assert (S (type_size A) = 0) by omega. inversion H3.
  - assert (S (type_size A1 + type_size A2) = 0) by omega. inversion H3.
  - inversion H0; subst.
    pick fresh x' and apply lc_t_all.
    rewrite <- dk_subst_open_var; eauto 3 with dk.
    apply IHn with B; auto.
    + rewrite size_open_var_eq. omega.
    + rewrite dk_subst_open_var; eauto 3 with dk.
  - inversion H0; subst.
    constructor; solve [apply IHn with B; auto; omega].
Qed.

Lemma lc_subst_reverse : forall A B C x,
    lc_type ([B /' x] A) -> lc_type B -> lc_type C -> lc_type ([C /' x] A).
Proof.
  intros.
  eapply (lc_subst_reverse_impl (type_size A)); eauto.
Qed.


Lemma dk_mono_lc : forall e,
    dk_mono e -> lc_type e.
Proof.
  intros. induction H; auto.
Qed.

Hint Resolve dk_mono_lc : dk.

Lemma dk_sub_lc : forall Γ A B,
    Γ ⫦ A <: B -> lc_type A /\ lc_type B.
Proof.
  intros. induction H; simpl in *; destruct_conjs; split; auto.
  - pick fresh x excluding (fv_type A) and apply lc_t_all.
    rewrite dk_open_subst_eq with (x := x); auto with dk.
    apply lc_subst_reverse with C; auto with dk.
    rewrite <- dk_open_subst_eq with (x := x); auto with dk.
  - instantiate_cofinites. now destruct H0.
  - pick fresh x and apply lc_t_all.
    instantiate_cofinites. now destruct H0.
Qed.

Lemma notin_dom_not_in : forall x Γ,
    x `notin` ctx_dom Γ -> not (x ∈ Γ).
Proof.
  induction Γ; simpl; intros; intro.
  - inversion H0.
  - destruct H0; subst.
    + assert (x <> x) by auto. contradiction.
    + assert (x `notin` ctx_dom Γ) by auto.
      assert (not (x ∈ Γ)) by auto.
      contradiction.
Qed.

Hint Resolve notin_dom_not_in : dk.

Lemma in_insert : forall Γ1 (x : tpvar) Γ2 x',
    x ∈ Γ1 ,, Γ2 -> x ∈ Γ1 ,' x' ,, Γ2.
Proof.
  induction Γ2; simpl; intros; auto.
  - destruct H; auto.
Qed.

Lemma wft_weakening : forall Γ1 x Γ2 t,
    Γ1 ,, Γ2 ⫦ t -> ⫦ Γ1 ,' x ,, Γ2 -> Γ1 ,' x ,, Γ2 ⫦ t.
Proof.
  intros * Wft.
  dependent induction Wft; intros.
  - eauto using in_insert.
  - auto.
  - eauto.
  - pick fresh x' excluding (add x (union (ctx_dom (Γ1 ,' x,, Γ2)) L))
         and apply wf_tp_all.
    replace (Γ1,' x,, Γ2,' x') with (Γ1,' x,, (Γ2,' x')) by reflexivity.
    apply H0; simpl; eauto with dk.
Qed.

Lemma wft_wf_ctx : forall Γ t,
    Γ ⫦ t -> ⫦ Γ.
Proof.
  intros. induction H; simpl; auto.
  instantiate_cofinites. now inversion H0.
Qed.

Hint Resolve wft_wf_ctx : dk.

Lemma wft_weakening_cons : forall Γ x t,
    Γ ⫦ t -> x `notin` ctx_dom Γ -> Γ,' x ⫦ t.
Proof.
  intros. replace (Γ,' x) with (Γ ,' x ,, nil) by reflexivity.
  eapply wft_weakening; simpl; eauto with dk.
Qed.

Lemma wft_open : forall A, lc_type A -> forall B C Γ x,
    Γ ⫦ [B /' x] A -> Γ ⫦ B -> Γ ⫦ C -> Γ ⫦ [C /' x] A.
Proof.
  intros A H.
  induction H; simpl; intros.
  - destruct (x == x0); auto.
  - auto.
  - inversion H1; subst.
    pick fresh x' excluding (ctx_dom Γ `union` add x L `union` L0)
         and apply wf_tp_all.
    rewrite <- dk_subst_open_var; eauto 3 with dk.
    apply H0 with B; eauto 3 using wft_weakening_cons.
    rewrite dk_subst_open_var; eauto 3 with dk.
  - inversion H1; subst. eauto.
Qed.

Hint Unfold In : dk.

Lemma dk_sub_wft : forall Γ A B,
    Γ ⫦ A <: B -> Γ ⫦ A /\ Γ ⫦ B.
Proof.
  intros. induction H; destruct_conjs; split; auto.
  - pick fresh x excluding (fv_type A `union` ctx_dom G) and apply wf_tp_all.
    rewrite dk_open_subst_eq with (x := x); auto.
    rewrite dk_open_subst_eq with (x := x) in H2; auto with dk.
    apply wft_open with (B := C).
    + rewrite dk_open_subst_eq with (x := x); auto with dk.
      eapply lc_subst_reverse with (B := C); eauto with dk.
    + eauto using wft_weakening_cons.
    + eauto using wft_weakening_cons.
    + constructor.
      eauto with dk.
      simpl. auto.
  - pick fresh x for (L `union` fv_type A).
    destruct H0 with x. auto.
    eapply wft_strengthening_cons; eauto.
  - econstructor. intros.
    instantiate_cofinites. now destruct H0.
Qed.

Import AtomSetImpl.
Import AtomSetProperties.

Lemma in_add : forall (x : var) a G,
    x `in` add a G -> x = a \/ x `in` G.
Proof.
  intros.
  assert (x `in` union (singleton a) G).
  - apply in_subset with (add a G). assumption.
    intro. intros.
    edestruct add_union_singleton. eauto.
  - eapply union_1 in H0 as [|].
    + left. apply singleton_1 in H0. auto.
    + now right.
Qed.


Lemma not_in_notin_dom : forall x Γ,
    not (List.In x Γ) -> x `notin` dom ⌈⌈ Γ ⌉⌉.
Proof.
  induction Γ; simpl; intros.
  - auto.
  - intro. apply in_add in H0 as [|].
    + subst. contradict H. auto.
    + assert (not (List.In x Γ)).
      contradict H. auto.
      specialize (IHΓ H1). contradiction.
Qed.

Hint Resolve not_in_notin_dom : dk.

Lemma dk_wf_subsumption : forall Γ,
    ⫦ Γ -> ⊢ ⌈⌈ Γ ⌉⌉.
Proof.
  intros. induction H; simpl.
  - auto.
  - constructor 2 with k_box; eauto with dk.
Qed.

Hint Resolve dk_wf_subsumption : dk.

Lemma bind_promote : forall x G,
    x ∈ G -> x : * ∈ ⌈⌈ G ⌉⌉.
Proof.
  induction G; simpl; intros.
  - inversion H.
  - destruct H; subst; auto.
Qed.

Hint Resolve bind_promote : dk.


Lemma shift_open_1 : forall e e' n1 n2,
    n2 <= n1 -> lc_expr e' ->
    shift (e <n1> ^^ e') n2 = shift e n2 <(S n1)> ^^ e'.
Proof.
  induction e; simpl; intros;
   try solve [auto | (rewrite IHe1, IHe2 || rewrite IHe); auto with arith].
  - destruct (n1 == n), (le_lt_dec n2 n); subst; simpl.
    + destruct (S n == S n).
      * rewrite lc_shift_eq; auto.
      * contradiction.
    + assert (not (n2 <= n)) by omega. contradiction.
    + destruct (le_lt_dec n2 n).
      * destruct (S n1 == S n).
        -- inversion e; contradiction.
        -- auto.
      * assert (not (n2 <= n)) by omega. contradiction.
    + destruct (le_lt_dec n2 n).
      * destruct (S n1 == n).
        -- subst. assert (not (n2 <= S n1)) by omega. contradiction.
        -- assert (not (n2 <= n)) by omega. contradiction.
      * destruct (S n1 == n).
        -- subst. assert (not (n2 <= n1)) by omega. contradiction.
        -- auto.
Qed.

Lemma shift_open_var_1 : forall e x n1 n2,
    n2 <= n1 ->
    shift (e <n1> ^^ ` x) n2 = shift e n2 <(S n1)> ^^ ` x.
Proof.
  intros.
  eapply shift_open_1; auto.
Qed.

Lemma dk_open_promote_rec : forall A B n,
    lc_expr ⌈ B ⌉ ->
    ⌈ A <n> ^^' B ⌉ = ⌈ A ⌉ <n> ^^ ⌈ B ⌉.
Proof.
  induction A; simpl; intros.
  - destruct (n0 == n); simpl; auto.
  - auto.
  - auto.
  - rewrite IHA; auto.
  - rewrite IHA1, IHA2; auto.
    rewrite shift_open_1; simpl; auto with arith.
Qed.

Lemma dk_open_promote : forall A B,
    lc_expr ⌈ B ⌉ ->
    ⌈ A ^^' B ⌉ = ⌈ A ⌉ ^^ ⌈ B ⌉.
Proof.
  intros. unfold open_expr_wrt_expr, open_type_wrt_type.
  now apply dk_open_promote_rec.
Qed.

Lemma dk_open_var_promote : forall A x,
    ⌈ A ^`' x ⌉ = ⌈ A ⌉ ^` x.
Proof.
  intros.
  unfold open_expr_wrt_expr, open_type_wrt_type.
  rewrite dk_open_promote_rec; simpl; auto.
Qed.

Lemma lc_open_var_eq : forall e x,
    lc_expr e -> e ^` x = e.
Proof.
  intros. unfold open_expr_wrt_expr.
  now rewrite lc_open_eq.
Qed.


Lemma dk_lc_promote : forall A,
    lc_type A -> lc_expr ⌈ A ⌉.
Proof.
  intros. induction H; simpl in *; eauto.
  - pick fresh x and apply lc_e_all; eauto.
    instantiate_cofinites.
    unfold open_type_wrt_type in H0.
    rewrite dk_open_promote_rec in H0; simpl; eauto.

  - pick fresh x and apply lc_e_pi; eauto.
    rewrite lc_shift_eq, lc_open_var_eq; auto.
Qed.

Lemma dk_open_promote' : forall A B,
    lc_type B ->
    ⌈ A ^^' B ⌉ = ⌈ A ⌉ ^^ ⌈ B ⌉.
Proof.
  intros.
  eauto using dk_lc_promote, dk_open_promote.
Qed.

Lemma dk_wftype_welltyped : forall Γ A,
    Γ ⫦ A -> ⌈⌈Γ⌉⌉ ⊢ ⌈A⌉ : *.
Proof.
  intros. induction H; simpl in *.
  - eauto 4 with dk.
  - eauto 3 with dk.
  - rewrite lc_shift_eq.
    + pick fresh x excluding (dom ⌈⌈ G ⌉⌉) and apply s_pi.
      * eauto.
      * rewrite lc_open_var_eq; eauto 4 using weakening_cons with wf.
      * rewrite lc_open_var_eq; eauto 4 using weakening_cons with wf.
    + auto.
  - pick fresh x and apply s_forall.
    + instantiate_cofinites. eauto with wf.
    + rewrite <- dk_open_var_promote. eauto.
Qed.


Lemma dk_mono_mono : forall A,
    dk_mono A -> mono_type ⌈ A ⌉.
Proof.
  intros. induction H; simpl in *.
  - auto.
  - auto.
  - pick fresh x and apply mono_pi.
    + auto.
    + rewrite lc_shift_eq, lc_open_var_eq; auto.
Qed.

Hint Resolve dk_mono_mono : dk.

Lemma dk_sub_subsumption : forall Γ A B,
    Γ ⫦ A <: B -> ⌈⌈ Γ ⌉⌉ ⊢ ⌈ A ⌉ <: ⌈ B ⌉ : *.
Proof.
  intros.
  induction H; simpl in *.
  (* var *)
  - eauto 4 using bind_promote with dk.
  (* int *)
  - eauto with dk.
  (* arrow *)
  - repeat rewrite lc_shift_eq; auto.
    pick fresh x excluding (dom ⌈⌈G⌉⌉) and apply s_pi.
    + eauto.
    + repeat rewrite lc_open_var_eq; auto.
      eapply weakening_cons; eauto 4 with wf.
    + repeat rewrite lc_open_var_eq; auto.
      eapply weakening_cons; eauto 4 with wf.
  (* forall_l *)
  - assert (G ⫦ t_all A <: B) by eauto.
    apply dk_sub_wft in H2 as [].
    inversion H2; subst.
    pick fresh x and apply s_forall_l.
    + eapply dk_mono_mono; eassumption.
    + eauto 3 with wf.
    + now apply dk_wftype_welltyped.
    + rewrite <- dk_open_promote'. auto.
      now apply dk_mono_lc.
    + instantiate_cofinites. apply dk_wftype_welltyped in H6. simpl in H6.
      now rewrite <- dk_open_var_promote.
  (* forall_r *)
  - assert (G ⫦ A <: t_all B) by eauto.
    apply dk_sub_wft in H1 as [].
    pick fresh x and apply s_forall_r.
    + instantiate_cofinites. eauto with wf.
    + now apply dk_wftype_welltyped.
    + rewrite <- dk_open_var_promote. eauto.
Qed.
