Require Import TLC.LibLogic TLC.LibTactics TLC.LibVar.

Set Implicit Arguments.


(** ** Typing environments *)

(** A typing environment is a list of formulas (p) and bindings for variables (x: T) *)

Section Definitions.
Variable typ : Type.
Variable formula : Type.

Inductive env : Type :=
| empty_env : env
| push_binding : env -> var -> typ -> env
| push_formula : env -> formula -> env.


Fixpoint concat E F:=
  match F with
  | empty_env => E
  | push_binding F' x T => push_binding (concat E F') x T
  | push_formula F' p => push_formula (concat E F') p
  end.

Fixpoint get x E :=
  match E with
  | empty_env => None
  | push_binding E' x' T => If x' = x then Some T else get x E'
  | push_formula E' p => get x E'
  end.
Definition binds x T E : Prop := get x E = Some T.

(** The domain of an environment is the set of bound variables *)
Fixpoint dom E :=
  match E with
  | empty_env => \{}
  | push_binding E' x  T => (dom E') \u \{x}
  | push_formula E' p => dom E'
  end.

Inductive ok : env -> Prop :=
| ok_empty : ok empty_env
| ok_push : forall E x T,
    ok E -> x \notin dom E -> ok (push_binding E x T)
| ok_push_formula : forall E p,
    ok E -> ok (push_formula E p).

End Definitions.

Implicit Arguments empty_env [typ formula].

Notation "E « x : T" := (push_binding E x T) (at level 26, x at level 0, T at level 0) : env_scope.
Notation "E « p" := (push_formula E p) (at level 26, p at level 0) : env_scope.
Notation "E & F" := (concat E F) (at level 28, left associativity) : env_scope.

Delimit Scope env_scope with env.
Open Scope env_scope.

Section Properties.
Variable typ : Type.
Variable formula : Type.

Implicit Types x : var.
Implicit Types E F : env typ formula.
Implicit Types T : typ.

(** * Rewriting properties *)
Lemma concat_assoc : forall E F G, (E & F) & G = E & (F & G).
Proof. intros. induction G; simpl; congruence. Qed.

Lemma push_binding_concat : forall E F x T, E & F « x : T = (E & F) « x: T.
Proof. auto. Qed.

Lemma push_formula_concat: forall E F p, E & (F « p) = (E & F) « p.
Proof. auto. Qed.

Lemma empty_concat_r : forall E, E = E & empty_env.
Proof. auto. Qed.

Lemma empty_concat_l : forall E, E = empty_env & E.
Proof. induction E; simpl; auto; rewrite* <- IHE. Qed.

Lemma empty_env_middle : forall E x T F, E « x : T & F = E & (empty_env « x : T) & F.
Proof. intros. auto. Qed.

Lemma dom_middle_formula : forall E p F, dom (E « p & F) = dom (E & F).
Proof. induction F; intros; simpl; auto. rewrite* IHF. Qed.

Lemma dom_concat : forall E F, dom (E & F) = dom E \u dom F. 
Proof. induction F; simpl; try assumption.
   * rewrite* union_empty_r.
   * rewrite IHF. rewrite* union_assoc.
Qed.

(** * Various Properties *)

Lemma empty_concat_inv :  forall {E F}, empty_env = E & F -> empty_env = F /\ empty_env = E.
Proof. intros. gen E. induction F; intro; split; simpl in H; inversion H; reflexivity. Qed.

(** * Properties of binds *)
Lemma get_push : forall x y T E,
    get x (E « y: T) = If x = y then Some T else get x E.
Proof. intros. case_if; simpl; case_if; auto. Qed.

Lemma binds_push_inv : forall x1 x2 T1 T2 E,
    binds x1 T1 (E « x2 : T2) ->
    (x1 = x2 /\ T1 = T2) \/ (x1 <> x2 /\ binds x1 T1 E).
Proof. intros. unfolds binds. rewrite get_push in H. case_if*. inversion* H. Qed.

Lemma binds_concat_inv : forall x T E F,
    binds x T (E & F) -> binds x T F \/ (x \notin dom F /\ binds x T E).
Proof.
  intros. induction F; simpl in *; auto. 
  apply binds_push_inv in H. destruct H.
  + destruct H. left. unfold binds. rewrite get_push. subst. case_if*.
  + destruct H. apply IHF in H0. destruct H0.
    * left. unfold binds. rewrite get_push. case_if*.
    * right. destruct H0. auto.
Qed.

Lemma binds_push_eq_inv : forall x T S E,
  binds x T (E « x : S) -> S = T.
Proof.
  intros. unfolds binds. simpls. case_if. inversion* H.
Qed.

Lemma binds_push_neq_inv : forall {x T E} y S,
  binds x T (E « y : S) -> x <> y -> binds x T E.
Proof. introv H. inversion H; intros. case_if*. Qed.

Lemma binds_fresh_inv : forall x T E,
  binds x T E -> x \notin dom E -> False.
Proof. introv Binds. induction E; intro Nin; auto. 
  * simpl in Nin. inversion Binds.
  * simpl in Nin. apply binds_push_neq_inv in Binds; auto.
Qed.

Lemma binds_concat_left_inv : forall x T E F,
  binds x T (E & F) ->
  x \notin dom F ->
  binds x T E.
Proof.  
  (* introv H ?. lets* [? | [? ?]]: binds_concat_inv H. *)
  introv Binds ?. apply binds_concat_inv in Binds as [? | [? ?]]; auto.
  exfalso. apply* binds_fresh_inv.
Qed.

Lemma binds_push : forall x T E, binds x T (E « x : T).
Proof. intros. unfold binds. cbn. case_if*. Qed.

Lemma binds_push_formula : forall E x T p, binds x T E -> binds x T (E « p).
Proof. introv Binds. unfold binds. simpl. assumption. Qed.

Lemma binds_push_neq : forall x y T S E,
    x <> y -> binds x T E -> binds x T (E « y : S).
Proof. intros. unfold binds. simpl. case_if*. Qed.

Lemma binds_concat_right : forall x T E F, binds x T F -> binds x T (E & F).
Proof.
  intros. induction F; auto.
  * inversion H.
  * apply binds_push_inv in H. destruct H.
    + destruct H; subst. apply binds_push.
    + destruct H. apply IHF in H0. simpl. 
      apply* binds_push_neq.
Qed.

Lemma binds_concat_left : forall x T E F,
    binds x T E -> x \notin dom F -> binds x T (E & F).
Proof.
  introv Binds Nin. induction F; auto. simpl in Nin.
  rewrite push_binding_concat. apply binds_push_neq; auto.
Qed.

Lemma binds_middle : forall E x T F,
    x \notin dom F ->
    binds x T (E « x : T & F).
Proof. introv Notin. apply binds_concat_left. apply binds_push. assumption. Qed.


(** ** Well formed environments and binds *)

Lemma binds_concat_left_ok : forall x T E G,
  ok (E & G) ->
  binds x T E ->
  binds x T (E & G).
Proof.
  introv Ok Binds. induction G; auto.
  + inversion Ok; subst. rewrite push_binding_concat; auto. apply binds_push_neq; auto.
    intro_subst. apply binds_fresh_inv in Binds; rewrite dom_concat in H3; auto.
  + unfold binds. simpl. inversion Ok. apply IHG. assumption.
Qed.


Lemma ok_middle_inv : forall E F x v,
  ok (E « x : v & F) -> x \notin dom E /\ x \notin dom F.
Proof.
  introv Ok. induction F; inversion Ok; simpl; splits*.
  rewrite dom_concat in H3. simpl in H3. apply IHF in H1 as [? ?]. auto.
Qed.

Lemma binds_middle_neq_inv : forall {x x' T S E F},
    x <> x' ->
    binds x T (E « x' : S & F) ->
    ok (E « x' : S & F) ->
    binds x T ( E & F).
Proof.
  introv Neq Binds Ok. induction F; inversion Ok.
  + simpls. apply binds_push_neq_inv in Binds; auto.
  + unfolds binds. simpls. case_if*. 
  + simpl. apply binds_push_formula. auto.
Qed.

Lemma binds_middle_eq_inv : forall {x T S E F},
    binds x T (E « x : S & F) ->
    ok (E « x : S & F) ->
    T = S.
Proof.
  introv H O. lets [? ?] : ok_middle_inv O.
  forwards* M: binds_concat_left_inv H.
  apply binds_push_eq_inv in M; auto.
Qed.

Lemma ok_concat : forall E F, ok (E & F) -> ok E.
Proof. introv Ok. induction F; inversion Ok; auto. Qed.

Lemma binds_weaken : forall E F G x T,
    binds x T (E & G) ->
    ok (E & F & G) ->
    binds x T (E & F & G).
Proof.
  intros. apply binds_concat_inv in H. destruct H.
  * apply* binds_concat_right.
  * destruct H. apply* binds_concat_left. apply* binds_concat_left_ok.
    apply ok_concat in H0. assumption.
Qed.

End Properties.
