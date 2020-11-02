Require Import Declarative.LanguageUtil.
Require Import BasicProperties.
Require Import KindProperties.
Require Import KindUniqueness.
Require Import Properties.
Require Import OccurenceReasoning.
Require Import FSetReasoning.
Require Import Extraction.

Require Import Program.Tactics.
Require Import Omega.

Reserved Notation "G ⊢ e1 <: e2 : A | n"
  (at level 65, e1 at next level, e2 at next level, A at next level,
   no associativity).

Inductive sized_usub : context -> expr -> expr -> expr -> nat -> Prop :=    (* defn sized_usub *)
 | ss_var : forall (G:context) (x:exprvar) (A:expr),
     ⊢ G -> x : A ∈ G ->
     G ⊢ `x <: `x : A | 0
 | ss_lit : forall (G:context) (n:number),
     ⊢ G ->
     G ⊢ e_num n <: e_num n : e_int | 0
 | ss_star : forall (G:context),
     ⊢ G ->
     G ⊢ * <: * : BOX | 0
 | ss_int : forall (G:context),
     ⊢ G ->
     G ⊢ e_int <: e_int : * | 0
 | ss_abs : forall (L:vars) (G:context) (A e1 e2 B:expr) (k1 k2:kind) n1 n2 n3,
     G ⊢ A <: A : e_kind k1 | n1 ->
     (forall x , x \notin L -> G , x : A ⊢ B ^` x <: B ^` x : e_kind k2 | n2) ->
     (forall x , x \notin L -> G , x : A ⊢ e1 ^` x <: e2 ^` x : B ^` x | n3) ->
     G ⊢ e_abs A e1 <: e_abs A e2 : e_pi A B | S (n1 + n2 + n3)
 | ss_pi : forall (L:vars) (G:context) (A1 B1 A2 B2:expr) (k2 k1:kind) n1 n2 n3,
      G ⊢ A2 <: A1 : e_kind k1 | n1 ->
      (forall x, x \notin  L -> G , x : A1 ⊢ B1 ^` x <: B1 ^` x : e_kind k2 | n2)  ->
      (forall x, x \notin  L -> G , x : A2 ⊢ B1 ^` x <: B2 ^` x : e_kind k2 | n3)  ->
      G ⊢ e_pi A1 B1 <: e_pi A2 B2 : e_kind k2 | S (n1 + n2 + n3)
 | ss_app : forall (G:context) (e1 e e2 B A:expr) n1 n2,
     G ⊢ e  <: e  : A        | n1 ->
     G ⊢ e1 <: e2 : e_pi A B | n2 ->
     mono_type e ->
     G ⊢ e_app e1 e <: e_app e2 e : B ^^ e | S (n1 + n2)
 | ss_bind : forall (L:vars) (G:context) (A e1 e2 B:expr) (k:kind) n1 n2 n3,
     G ⊢ A <: A : e_kind k | n1 ->
     (forall x , x \notin L -> G , x : A ⊢ B  ^` x <: B  ^` x : * | n2) ->
     (forall x , x \notin L -> G , x : A ⊢ e1 ^` x <: e2 ^` x : B ^` x | n3) ->
     (forall x , x \notin L -> x `notin` fv_eexpr (extract (e1 ^` x))) ->
     (forall x , x \notin L -> x `notin` fv_eexpr (extract (e2 ^` x))) ->
     G ⊢ e_bind A e1 <: e_bind A e2 : e_all A B | S (n1 + n2 + n3)
 | ss_mu : forall (L:vars) (G:context) (A e:expr) (k:kind) n1 n2,
     mono_type (e_mu A e) ->
     G ⊢ A <: A : e_kind k | n1 ->
     (forall x , x \notin L -> G , x : A ⊢ e ^` x <: e ^` x : A | n2) ->
     G ⊢ e_mu A e <: e_mu A e : A | S (n1 + n2)
 | ss_castup : forall (G:context) (A e1 e2:expr) (k:kind) (B:expr) n1 n2,
     G ⊢ A <: A : e_kind k | n1 ->
     A ⟶ B ->
     G ⊢ e1 <: e2 : B | n2 ->
     G ⊢ e_castup A e1 <: e_castup A e2 : A | S (n1 + n2)
 | ss_castdn : forall (G:context) (B e1 e2:expr) (k:kind) (A:expr) n1 n2,
     G ⊢ B <: B : e_kind k | n1 ->
     A ⟶ B ->
     G ⊢ e1 <: e2 : A | n2 ->
     G ⊢ e_castdn e1 <: e_castdn e2 : B | S (n1 + n2)
 | ss_forall_l : forall (L:vars) (G:context) (A B C e:expr) (k:kind) n1 n2 n3 n4,
     mono_type e ->
     G ⊢ A <: A : e_kind k | n1 ->
     G ⊢ e <: e : A        | n2 ->
     G ⊢ B ^^ e <: C : * | n3 ->
     (forall x, x \notin L -> G , x : A ⊢ B ^` x <: B ^` x : * | n4)  ->
     G ⊢ e_all A B <: C : * | S (n1 + n2 + n3 + n4)
 | ss_forall_r : forall (L:vars) (G:context) (A B C:expr) (k:kind) n1 n2 n3,
     G ⊢ B <: B : e_kind k | n1 ->
     G ⊢ A <: A : * | n2 ->
     (forall x, x \notin L -> G , x : B ⊢ A <: C ^` x : * | n3) ->
     G ⊢ A <: e_all B C : * | S (n1 + n2 + n3)
 | ss_forall : forall (L:vars) (G:context) (A B C:expr) (k:kind) n1 n2,
     G ⊢ A <: A : e_kind k | n1 ->
     (forall x, x \notin L -> G , x : A ⊢ B ^` x <: C ^` x : * | n2)  ->
     G ⊢ e_all A B <: e_all A C : * | S (n1 + n2)
 | ss_sub : forall (G:context) (e1 e2 B A:expr) (k:kind) n1 n2,
     G ⊢ e1 <: e2 : A | n1 ->
     G ⊢ A  <: B  : e_kind k | n2 ->
     G ⊢ e1 <: e2 : B | S (n1 + n2)
where "G ⊢ e1 <: e2 : A | n" := (sized_usub G e1 e2 A n).

Hint Constructors sized_usub : core.

Lemma sized_unsized : forall Γ e1 e2 A n,
    Γ ⊢ e1 <: e2 : A | n -> Γ ⊢ e1 <: e2 : A.
Proof.
  intros. induction H; eauto 3.
Qed.

Hint Resolve sized_unsized : core.

Ltac distribute_sized_ctx :=
  match goal with
  | |- (?g1 ,, ?g2 , ?x : ?A) ⊢ _ <: _ : _ | _ =>
    replace (g1 ,, g2 , x : A) with
      (g1 ,, (g2 , x : A)) by auto
  end
.

Hint Extern 1 (_ ,, _ , _ : _ ⊢ _ <: _ : _ | _) => distribute_sized_ctx : core.

Ltac capture_wf_dom :=
    match goal with
    | _ : ⊢ ?Γ |- _ =>
      let L := fresh "L" in set (L := dom Γ)
    end.

Ltac solve_weakening_with IH :=
  distribute_sized_ctx; apply IH; eauto 3; eapply wf_cons; eauto 4.

Theorem sized_weakening : forall Γ1 Γ2 Γ3 e1 e2 A n,
    Γ1 ,, Γ3 ⊢ e1 <: e2 : A | n ->
    ⊢ Γ1 ,, Γ2 ,, Γ3 ->
    Γ1 ,, Γ2 ,, Γ3 ⊢ e1 <: e2 : A | n.
Proof.
  intros * Sub.
  generalize dependent Γ2.
  dependent induction Sub; intros; auto; capture_wf_dom.
  - pick fresh x and apply ss_abs; eauto.
    solve_weakening_with H0.
    solve_weakening_with H2.
  - pick fresh x and apply ss_pi; eauto.
    solve_weakening_with H0.
    solve_weakening_with H2.
  - eauto.
  - pick fresh x and apply ss_bind; eauto.
    solve_weakening_with H0.
    solve_weakening_with H2.
  - pick fresh x and apply ss_mu; eauto.
    solve_weakening_with H1.
  - eauto.
  - eauto.
  - pick fresh x and apply ss_forall_l; eauto.
    solve_weakening_with H1.
  - pick fresh x and apply ss_forall_r; eauto.
    solve_weakening_with H0.
  - pick fresh x and apply ss_forall; eauto.
    solve_weakening_with H0.
  - eauto.
Qed.

Corollary sized_weakening_cons : forall Γ e1 e2 A x B n,
    Γ ⊢ e1 <: e2 : A | n ->
    ⊢ Γ , x : B ->
    Γ , x : B ⊢ e1 <: e2 : A | n.
Proof.
  intros.
  replace (Γ , x : B) with (Γ ,, one (pair x B) ,, nil) by reflexivity.
  now apply sized_weakening.
Qed.


Ltac find_open_inequality_impl e :=
  match e with
  | context [([_ / ?x] _) ^` ?x'] => assert (x' <> x) by auto 2
  end
.

Ltac find_open_inequality :=
  match goal with
  | |- ?G => find_open_inequality_impl G
  end
.

Ltac assimilate_basic_type_from G :=
  match G with
  | context [ ([?x' / ?x] _) ] =>
    match G with
    | _ ⊢ _ <: _ : ?A | _ =>
      match A with
      | [x' / x] _ => idtac
      | _ => replace A with ([x' / x] A) by reflexivity
      end
    end
  end
.

Ltac redistribute_subst :=
  repeat (rewrite subst_open_var_assoc; auto);
  match goal with
  | |- ?G => assimilate_basic_type_from G
  end
.

Ltac distribute_sized_ctx_for_subst :=
  match goal with
  | |- _ ,, [?e // ?x] ?Γ , ?x0 : [?e / ?x] ?A ⊢ _ <: _ : _ | _ =>
    distribute_sized_ctx;
    replace ([e // x] Γ , x0 : [e / x] A) with
        ([e // x] (Γ , x0 : A)) by reflexivity
  end
.

Ltac assoc_goal :=
  try find_open_inequality;
  try redistribute_subst;
  try distribute_sized_ctx_for_subst
.

Ltac assoc_goal_and_apply IH :=
  assoc_goal; eapply IH; simpl; eauto 3.

Ltac pick_fresh_with_dom_and_apply H :=
  match goal with
  | |- ?Γ ⊢ _ <: _ : _ | _ =>
    let L := fresh "L" in
    let x := fresh "x" in
    set (L := dom Γ); pick fresh x and apply H
  end
.

Lemma fresh_dom_fresh_binds: forall Γ x x' A,
    ⊢ Γ -> x `notin` dom Γ -> x' : A ∈ Γ -> x # A.
Proof.
  intros * Wf. induction Wf; simpl; intros.
  - inversion H0.
  - destruct H2.
    + inversion H2; subst. eauto.
    + apply IHWf; eauto.
Qed.

Lemma sized_renaming : forall Γ1 x A Γ2 x' e1 e2 B n,
    Γ1, x : A,, Γ2 ⊢ e1 <: e2 : B | n ->
    ⊢ Γ1 , x' : A ,, [`x' // x] Γ2 ->
    Γ1, x' : A,, [`x' // x]Γ2 ⊢ [`x' / x] e1 <: [`x' / x] e2 : [`x' / x] B | n.
Proof.
  intros * Sub.
  dependent induction Sub; intros; simpl; auto.
  - destruct (x0 == x).
    + subst. assert (A0 = A) by (eapply binds_type_equal; eauto). subst.
      assert (x # A) by (eapply fresh_binded; eauto).
      replace ([`x' / x] A) with A by now rewrite fresh_subst_eq.
      auto.
    + induction Γ2.
      * simpl in *. inversion H; subst. destruct H0.
        -- inversion H0. subst. contradiction.
        -- rewrite fresh_subst_eq. eauto.
           eapply fresh_dom_fresh_binds; eauto.
      * destruct a. simpl in *. destruct H0.
        -- inversion H0; subst. eauto.
        -- inversion H; subst. inversion H1; subst.
           apply sized_weakening_cons; eauto.
  - pick_fresh_with_dom_and_apply ss_abs; eauto.
    + assoc_goal_and_apply H0. eapply wf_cons; eauto.
    + assoc_goal_and_apply H2. eapply wf_cons; eauto.
  - pick_fresh_with_dom_and_apply ss_pi; eauto.
    + assoc_goal_and_apply H0. eapply wf_cons; eauto.
    + assoc_goal_and_apply H2. eapply wf_cons; eauto.
  - rewrite subst_open_distr; eauto.
  - pick_fresh_with_dom_and_apply ss_bind; eauto.
    + assoc_goal_and_apply H0. eapply wf_cons; eauto.
    + assoc_goal_and_apply H2. eapply wf_cons; eauto.
    + rewrite subst_open_var_assoc, subst_extract; auto 2.
      eauto 4 using fv_subst_inclusion.
    + rewrite subst_open_var_assoc, subst_extract; auto 2.
      eauto 4 using fv_subst_inclusion.
  - pick_fresh_with_dom_and_apply ss_mu; eauto.
    + inversion H. subst. pick fresh x'' and apply mono_mu. auto.
      autorewrite with assoc; auto 3.
    + assoc_goal_and_apply H1. eapply wf_cons; eauto.
  - eauto using reduce_subst.
  - eauto using reduce_subst.
  - apply ss_forall_l with
      (add x (add x' L) `union` dom (Γ1 , x' : A ,, [`x' // x] Γ2)) ([`x' / x] e) k; eauto.
    + rewrite <- subst_open_distr; eauto.
    + intros. assoc_goal_and_apply H1. eapply wf_cons; eauto.
  - pick_fresh_with_dom_and_apply ss_forall_r; eauto.
    + assoc_goal_and_apply H0. eapply wf_cons; eauto.
  - pick_fresh_with_dom_and_apply ss_forall; eauto.
    + assoc_goal_and_apply H0. eapply wf_cons; eauto.
  - eauto.
Qed.

Lemma sized_renaming_cons : forall Γ x A x' e1 e2 B n,
    Γ, x  : A ⊢ e1 <: e2 : B | n ->
    x' `notin` dom Γ ->
    Γ, x' : A ⊢ [`x' / x] e1 <: [`x' / x] e2 : [`x' / x] B | n.
Proof.
  intros.
  replace (Γ , x' : A) with (Γ , x' : A ,, [`x' // x] nil) by reflexivity.
  apply sized_renaming.
  - assumption.
  - assert (⊢ Γ , x : A) by eauto 3 using sub_ctx_wf.
    inversion H1. subst. simpl. eauto.
Qed.

Ltac reconstruct_sub :=
  match goal with
  | |- exists _, ?Γ ⊢ ?e1 <: ?e2 : ?A | _ =>
      let H := fresh "Sub" in assert (H : Γ ⊢ e1 <: e2 : A) by eauto 3
  end.

Ltac discover_fresh_dom x :=
  match goal with
  | H : ?Γ, x : ?A ⊢ _ <: _ : _ |- _ =>
    let Fr := fresh "Fr" in
    assert (Fr : x `notin` dom Γ) by eauto with wf sized
  end
.

Lemma wf_cons_notin_dom : forall Γ x A,
    ⊢ Γ, x : A -> x `notin` dom Γ.
Proof. intros. now inversion H. Qed.

Hint Resolve wf_cons_notin_dom : sized.


Ltac conclude_freshness_of x e :=
  match goal with
  | _ : x # e |- _ => idtac
  | _ => let Fr := fresh "Fr" in
        assert (Fr : x # e) by solve_simple_freshness
  end.

Ltac discover_fresh_expr x :=
  repeat
    match goal with
    | Fr : x `notin` dom ?G |- _ =>
      progress repeat match goal with
      | Sub : G ⊢ ?e1 <: ?e2 : ?A |- _ =>
        progress (
          conclude_freshness_of x e1;
          conclude_freshness_of x e2;
          conclude_freshness_of x A)
      end
    end; simpl in *; clear_dups
.

Ltac conclude_freshes :=
  match goal with
  | _ : ?x `notin` ?L |- _ =>
    discover_fresh_dom x; discover_fresh_expr x
  end
.

Ltac rewrite_open_or_subst e x x0 :=
  match e with
  | ?e' ^` x0 => rewrite (open_subst_eq e' x); eauto
  | _ => replace e with ([`x0 / x] e) by
    solve [reflexivity | rewrite fresh_subst_eq; auto ]
  end
.

Ltac rewrite_for_rename :=
  match goal with
  | _ : ?x `notin` dom ?Γ |- ?Γ, ?x0 : ?A ⊢ ?e1 <: ?e2 : ?e3 | _ =>
    match x with
    | x0 => fail 1
    | _ =>
      let A' := fresh A in
      let E := fresh "E" in
      pose (A' := A); assert (A' = A) as E by auto;
      (* this is in case of e1 e2 or e3 appear in A,
         then the rewrite could pollute the Γ, x : A *)
      replace (Γ, x0 : A) with (Γ, x0 : A') by auto;
      rewrite_open_or_subst e3 x x0;
      rewrite_open_or_subst e1 x x0;
      (match e1 with
      | e2 => idtac
      | _ => rewrite_open_or_subst e2 x x0
      end); rewrite E; clear E A'
    end
  end
.

Ltac solve_unsized_sized_with H :=
  pick_fresh_with_dom_and_apply H; eauto;
  rewrite_for_rename; apply sized_renaming_cons; eauto.

Set Ltac Backtrace.

Hint Extern 1 (_, _ : _ ⊢ _ <: _ : _ | _) => rewrite_for_rename : sized.

Ltac try_sized_constructors :=
  eapply ss_abs +
  eapply ss_pi +
  eapply ss_bind +
  eapply ss_mu +
  eapply ss_forall +
  eapply ss_forall_l +
  eapply ss_forall_r
.

Ltac unsized_sized_strategy :=
  match goal with
  | _ => solve [eassumption | auto 2 | eauto 2]
  | _ => progress destruct_exists
  | |- exists n, _ ⊢ _ <: _ : _ | n => eapply ex_intro
  | |- _ ⊢ e_bind _ _ <: e_bind _ _ : _ | _ =>
    let L' := gather_for_weakening in
    eapply ss_bind with (L := L')
  | _ => try_sized_constructors
  | |- ?g =>
    match g with
    | context [ [_ / _] _ ] => fail 1
    | _ => rewrite_for_rename
    end
  | _ => solve [eauto 4 using sized_renaming_cons]
  end
.

Ltac apply_unsized_sized_strategy :=
  repeat (intros; unsized_sized_strategy).

Ltac solve_unsized_sized :=
  try solve
      [ destruct_exists; eauto 3
      | (try reconstruct_sub); instantiate_cofinites;
        conclude_freshes; apply_unsized_sized_strategy
       ].

Lemma unsized_sized : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> exists n, Γ ⊢ e1 <: e2 : A | n.
Proof.
  intros.
  induction H; try solve_unsized_sized.
  (* a little special for bind, for the strategy inappropriately instantiating freshness
     involving extracted expression *)
  - reconstruct_sub.
    instantiate_cofinite H0. instantiate_cofinite H1.
    instantiate_cofinite H2. instantiate_cofinite H3.
    conclude_freshes. apply_unsized_sized_strategy.
Qed.

Fixpoint forall_order (e : expr) : nat :=
  match e with
  | e_app  f a => forall_order f + forall_order a
  | e_abs  A B => forall_order A + forall_order B
  | e_pi   A B => forall_order A + forall_order B
  | e_bind A B => forall_order A + forall_order B
  | e_all  A B => S (forall_order A + forall_order B)
  | e_castup A e => forall_order A + forall_order e
  | e_castdn   e => forall_order e
  | e_mu   A e => forall_order A + forall_order e
  | _ => 0
  end
.

Fixpoint esize (e : expr) : nat :=
  match e with
  | e_var_b _ => 0
  | e_var_f _ => 0
  | e_kind _ => 0
  | e_num _ => 0
  | e_int => 0
  | e_app  f a => S (esize f + esize a)
  | e_abs  A B => S (esize A + esize B)
  | e_pi   A B => S (esize A + esize B)
  | e_all  A B => S (esize A + esize B)
  | e_bind A B => S (esize A + esize B)
  | e_mu   A e => S (esize A + esize e)
  | e_castup A e => S (esize A + esize e)
  | e_castdn e => S (esize e)
  end
.

Lemma open_var_size_eq_rec : forall A x n,
    esize (A <n> ^^ `x) = esize A.
Proof.
  induction A; simpl; intros; auto.
  now destruct (n0 == n).
Qed.

Lemma open_var_size_eq : forall A x,
    esize (A ^` x) = esize A.
Proof.
  intros. apply open_var_size_eq_rec.
Qed.

Lemma open_var_forall_order_eq_rec : forall A x n,
    forall_order (A <n> ^^ `x) = forall_order A.
Proof.
  induction A; simpl; intros; auto.
  now destruct (n0 == n).
Qed.

Lemma open_var_forall_order_eq : forall A x,
    forall_order (A ^` x) = forall_order A.
Proof.
  intros. apply open_var_forall_order_eq_rec.
Qed.

Lemma mono_type_order : forall e,
    mono_type e -> forall_order e = 0.
Proof.
  intros. induction H; simpl; auto;
  try solve [ now rewrite IHmono_type1, IHmono_type2
        | instantiate_cofinites; rewrite open_var_forall_order_eq in H1;
          now rewrite IHmono_type, H1].
Qed.

Lemma open_mono_order_rec : forall e v n,
    mono_type v -> forall_order (e <n> ^^ v) = forall_order e.
Proof.
  induction e; simpl; intros; auto.
  - destruct (n0 == n).
    + now apply mono_type_order.
    + auto.
Qed.

Lemma open_mono_order : forall e v,
    mono_type v -> forall_order (e ^^ v) = forall_order e.
Proof.
  intros. now apply open_mono_order_rec.
Qed.

Lemma open_var_order : forall e x,
    forall_order (e ^` x) = forall_order e.
Proof.
  intros. apply open_mono_order. auto.
Qed.

Ltac extract_eq :=
  match goal with
  | H : ?e1 + ?e2 <= 0 |- _ =>
    let E1 := fresh H in
    let E2 := fresh H in
    assert (e1 = 0 /\ e2 = 0) as [E1 E2] by omega;
    clear H; try subst e1 e2
  | H : ?e <= 0 |- _ =>
    let E := fresh H in
    assert (e = 0) as E by omega;
    clear H; try subst e
  | H : ?e1 + ?e2 = 0 |- _ =>
    let E1 := fresh H in
    let E2 := fresh H in
    assert (e1 = 0 /\ e2 = 0) as [E1 E2] by omega;
    clear H; try subst e1 e2
  end
.

Ltac extract_eqs := repeat extract_eq.

Ltac invert_and_subst H := inversion H; subst.

Ltac solve_tree_size_base :=
  repeat match goal with
  | H : ?Γ ⊢ ?e1 <: ?e2 : ?A | 0 |- _ =>
      invert_and_subst H; clear H
  end; auto
.

Ltac solve_size_inconsistency :=
  repeat match goal with
  | E : esize _ = 0 |- _ => progress try solve [inversion E]
  | E : forall_order _ = 0 |- _ => progress try solve [inversion E]
  end
.

Ltac find_IHorder :=
  match goal with
  | H : forall (_ : nat) (_ : nat) _ _ _ _ _ _ _ _,
      _ + _ + _ <= _ -> _ |- _ => H
  end
.

Ltac find_IHesz :=
  match goal with
  | H : forall (_ : nat) _ _ _ _ _ _ _ _, _ + _ + _ <= _ -> _ |- _ => H
  end
.

Ltac find_IHtsz :=
  match goal with
  | H : forall _ _ _ _ _ _ _ _, _ + _ + _ <= _ -> _ |- _ => H
  end
.

Ltac solve_left_subsumption_impl IH :=
  match goal with
  | _ : ?Γ ⊢ ?A0 <: ?A : e_kind ?k | _ |- ?Γ ⊢ ?e1 <: ?e3 : ?A => match goal with
    | Hl : Γ ⊢ e1 <: ?e2 : A0 | ?n1 |- _ => match goal with
      | Hr : Γ ⊢ ?e2 <: e3 : ?B | ?n2 |- _ =>
        apply s_sub with A0 k; eauto 3; apply IH with e2 B n1 n2; eauto 3; omega
end end end
.

Ltac solve_left_subsumption :=
  let H := find_IHtsz in solve_left_subsumption_impl H.

Ltac solve_right_subsumption_impl IH := match goal with
| Hr : ?Γ ⊢ ?e2 <: ?e3 : ?B | ?n2 |- _ ⊢ ?e1 <: ?e3 : ?A => match goal with
  | _ : Γ ⊢ B <: _ : e_kind ?k | _ |- _ => match goal with
    | Hl : Γ ⊢ ?e1 <: e2 : A | ?n1 |- _ =>
       apply IH with e2 B n1 n2; eauto 3; omega
end end end
.

Ltac solve_right_subsumption :=
  let H := find_IHtsz in solve_right_subsumption_impl H.

Ltac unify_kind k A :=
  let E := fresh in
  match A with
  | e_kind k => idtac
  | e_kind ?k2 =>
    assert (k = k2) as E by eauto using kind_uniqueness;
    discharge_equality E
  | _ =>
    assert (A = e_kind k) as E by eauto using gen_kind_uniqueness;
    discharge_equality E
  end
.

Ltac unify_kinds :=
  repeat match goal with
  | Hk : _ ⊢ ?A <: ?A : e_kind ?k | _ |- _ =>
    progress repeat
      match goal with
      | _ : _ ⊢ _ <: A : ?B | _ |- _ => progress (unify_kind k B)
      | _ : _ ⊢ A <: _ : ?B | _ |- _ => progress (unify_kind k B)
      end
  end
.

Ltac star_absurd :=
  match goal with
  | H : _ ⊢ * <: * : ?A | _ |- _ =>
    match A with
    | e_kind k_box => fail
    | _ => let H := fresh in
      assert (A = BOX) as H by eauto using star_type_inversion; inversion H
    end
  end
.

Lemma sized_sub_wf : forall Γ e1 e2 A n,
    Γ ⊢ e1 <: e2 : A | n -> ⊢ Γ.
Proof.
  intros. apply sized_unsized in H.
  eapply sub_ctx_wf. eassumption.
Qed.

Hint Resolve sized_weakening_cons : core.
Hint Resolve sized_sub_wf : core.

Hint Rewrite open_var_size_eq : trans.
Hint Rewrite open_var_forall_order_eq : trans.
Hint Rewrite open_mono_order : trans.

Ltac solve_with_IHorder :=
  instantiate_cofinites; match goal with
  | Hl : _ ⊢ ?e1 <: ?e2 : * | ?n1
         |- _ ⊢ ?e1 <: ?e3 : * => match goal with
    | Hr : _ ⊢ e2 <: ?e3 : ?B | ?n2 |- _ =>
      let IH := find_IHorder in
      apply IH with (esize e1 + esize e3) (n1 + n2) e2 B n1 n2;
      eauto 4 using sized_weakening_cons;
      autorewrite with trans; auto; simpl in *; omega
     end
   end
.

Ltac solve_right_forall_r :=
  let x := fresh "x" in
  pick fresh x and apply s_forall_r for weakening; eauto 3; solve_with_IHorder.

Ltac solve_left_forall_l :=
  eapply s_forall_l; eauto 3; solve_with_IHorder.

Theorem substitution_cons : forall Γ x A B e1 e2 e3,
  Γ , x : B ⊢ e1 <: e2 : A ->
  Γ ⊢ e3 : B -> mono_type e3 ->
  Γ ⊢ [e3 / x] e1 <: [e3 / x] e2 : [e3 / x] A.
Proof.
  intros *.
  replace (Γ , x : B) with (Γ , x : B ,, nil) by reflexivity.
  apply substitution.
Qed.

Ltac prepare_left_judgement :=
  match goal with
  | H : forall x, x `notin` ?L -> ?Γ, x : ?B ⊢ ?e1 <: ?C ^` x : * | _
        |- ?Γ ⊢ ?e1 <: ?e3 : * => match goal with
    | _ : mono_type ?e |- _ =>
      let x := fresh "x" in
      let H := fresh "H" in
      let Hl := fresh "Hl" in
      let n := fresh "n" in
      pick fresh x for (L `union` fv_expr e1 `union` fv_expr C);
      assert (H : Γ ⊢ e1 <: C ^^ e : *) by
        (replace * with ([e / x] * ) by reflexivity;
         rewrite <- (fresh_subst_eq e1 x e); auto;
         rewrite (open_subst_eq C x e); auto;
         apply substitution_cons with B; eauto);
      apply unsized_sized in H as (Hl & n)
    end
  end
.

Ltac solve_l_forall_r_r_forall :=
  pick fresh x and apply s_forall_r; eauto 3;
  solve_with_IHorder.


Ltac solve_l_forall_r_r_forall_l :=
  prepare_left_judgement; solve_with_IHorder.

Ltac prepare_left_judgement_2 :=
  match goal with
  | H : forall x, x `notin` ?L -> ?Γ, x : ?A ⊢ ?B ^` x <: ?C ^` x : * | _
        |- ?Γ ⊢ e_all ?A ?B <: _ : * => match goal with
    | _ : mono_type ?e |- _ =>
      let x := fresh "x" in
      let H := fresh "H" in
      let Hl := fresh "Hl" in
      let n := fresh "n" in
      pick fresh x for (L `union` fv_expr B `union` fv_expr C);
      assert (H : Γ ⊢ B ^^ e <: C ^^ e : *) by
        (rewrite (open_subst_eq B x e), (open_subst_eq C x e); auto;
         replace * with ([e / x] * ) by reflexivity;
         eapply substitution_cons; eauto);
      apply unsized_sized in H as (n & Hl)
    end
  end
.

Ltac solve_l_forall_r_forall_l :=
  prepare_left_judgement_2;
  pick fresh x and apply s_forall_l; eauto 4; solve_with_IHorder.

Ltac solve_l_forall_r_forall :=
  match goal with
  | |- _ ⊢ e_all _ _ <: e_all _ _ : _ =>
    pick fresh x and apply s_forall; eauto 3; solve_with_IHorder
  end
.

Ltac solve_with_IHtsz :=
  instantiate_cofinites;
  match goal with
  | Hl : ?Γ ⊢ ?e1 <: ?e2 : ?A | ?n1 |- ?Γ ⊢ ?e1 <: ?e3 : _ =>
    match goal with
    | Hr : ?Γ ⊢ ?e2 <: ?e3 : ?B | ?n2 |- _ =>
      let IH := find_IHtsz in
      apply IH with e2 B n1 n2; eauto 3; simpl in *;
      autorewrite with trans; auto; simpl in *; omega
    end
  end
.

Ltac solve_abs :=
  match goal with
  | |- _ ⊢ e_abs _ _ <: e_abs _ _ : _ =>
    pick fresh x and apply s_abs; eauto; solve_with_IHtsz
  end
.

Ltac solve_app :=
  match goal with
  | _ : ?Γ ⊢ ?f1 <: _ : e_pi ?A ?B | _
      |- ?Γ ⊢ e_app ?f1 _ <: e_app _ _ : ?B ^^ ?e =>
    apply s_app with A; eauto; solve_with_IHtsz
  end
.

Ltac solve_bind :=
  match goal with
  | |- _ ⊢ e_bind _ _ <: e_bind _ _ : _ =>
    pick fresh x and apply s_bind; eauto; solve_with_IHtsz
  end
.

Ltac solve_castup :=
  match goal with
  | |- _ ⊢ e_castup _ _ <: e_castup _ _ : _ =>
    eapply s_castup; try solve_with_IHtsz; eauto
  end
.

Ltac solve_castdn :=
  match goal with
  | |- _ ⊢ e_castdn _ <: e_castdn _ : _ =>
    eapply s_castdn; try solve_with_IHtsz; eauto
  end
.

Corollary sized_narrowing : forall Γ x A B k e1 e2 T n1 n2,
    Γ , x : A ⊢ e1 <: e2 : T | n1 ->
    Γ ⊢ B <: A : e_kind k | n2 ->
    exists n, Γ , x : B ⊢ e1 <: e2 : T | n.
Proof.
  intros.
  apply unsized_sized.
  apply ctx_narrowing_cons with A k; eauto.
Qed.

Ltac solve_with_IHesz :=
  match goal with
  | _ : ?Γ ⊢ ?e1 <: ?e2 : ?A | ?n1 |- ?Γ ⊢ ?e1 <: ?e3 : _ =>
    match goal with
    | _ : ?Γ ⊢ ?e2 <: ?e3 : ?B | ?n2 |- _ =>
      let IH := find_IHesz in
      apply IH with (n1 + n2) e2 B n1 n2; eauto 3;
      autorewrite with trans; auto; simpl in *; omega
    end
  end
.

Ltac narrowing_return_type_ctx :=
  match goal with
  | _ : ?Γ , ?x : ?A2 ⊢ ?e1 <: ?e2 : ?k | _
      |- ?Γ , ?x : ?A3 ⊢ ?e1 <: ?e3 : _ =>
    match goal with
    | _ : Γ , x : A3 ⊢ e2 <: e3 : _ | _ |- _ =>
      let n := fresh "n" in
      let Hl := fresh "Hl" in
      assert (exists n, Γ , x : A3 ⊢ e1 <: e2 : k | n) as (n & Hl)
      by (eapply sized_narrowing; eauto)
    end
  end
.

Ltac solve_pi_return_type :=
  instantiate_cofinites; unify_kinds;
  narrowing_return_type_ctx; solve_with_IHesz.

Ltac solve_pi :=
  match goal with
  | |- _ ⊢ e_pi _ _ <: e_pi _ _ : _ =>
    pick fresh x and apply s_pi; eauto; solve
    [ solve_with_IHtsz | solve_pi_return_type]
  end
.

Ltac easy_solves_l := try solve [solve_left_forall_l | solve_left_subsumption].

Ltac easy_solves_r :=
  try solve
      [ auto
      | eauto 2
      | star_absurd
      | solve_right_subsumption
      | solve_right_forall_r
      | solve_abs
      | solve_pi
      | solve_app
      | solve_bind
      | solve_castdn
      | solve_castup
      | solve_l_forall_r_r_forall_l
      | solve_l_forall_r_r_forall
      | solve_l_forall_r_forall_l
      | solve_l_forall_r_forall
      ]
.

Ltac solve_by_case_analysis :=
  match goal with
  | H1 : ?Γ ⊢ ?e1 <: _ : _ | _ |- ?Γ ⊢ ?e1 <: ?e3 : _ =>
    invert_and_subst H1; solve_size_inconsistency; easy_solves_l;
    match goal with
    | H2 : Γ ⊢ _ <: e3 : _ | _ |- _ => invert_and_subst H2
    end;
    solve_size_inconsistency; unify_kinds; easy_solves_r
  end
.

Theorem transitivity' : forall order esz tsz,
    forall Γ e1 e2 e3 A B n1 n2,
      forall_order e1 + forall_order e2 + forall_order e3 <= order ->
      esize e1 + esize e3 <= esz ->
      n1 + n2 <= tsz ->
      Γ ⊢ e1 <: e2 : A | n1 -> Γ ⊢ e2 <: e3 : B | n2 -> Γ ⊢ e1 <: e3 : A.
Proof.
  induction order; induction esz; induction tsz;
    intros * Eorder Eesz Etsz Subl Subr;
    extract_eqs.
  all: try solve_tree_size_base.
  - solve_by_case_analysis.
  - solve_by_case_analysis.
  - solve_by_case_analysis.
  - solve_by_case_analysis.
Qed.

Corollary transitivity : forall Γ e1 e2 e3 A B,
    Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 <: e3 : B -> Γ ⊢ e1 <: e3 : A.
Proof.
  intros.
  apply unsized_sized in H as (n1 & Hl).
  apply unsized_sized in H0 as (n2 & Hr).
  apply transitivity' with
      (forall_order e1 + forall_order e2 + forall_order e3)
      (esize e1 + esize e3) (n1 + n2) e2 B n1 n2; eauto.
Qed.
