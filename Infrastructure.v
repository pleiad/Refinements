Require Import TLC.LibLN Definitions.

(* ********************************************************************** *)

(** * Mutual Induction principles *)

(** We define some mutual induction principles to make simultaneus proofs about types,
    formulas and logical values *)

Scheme typ_mut := Induction for typ Sort Prop
with formula_mut := Induction for formula Sort Prop
with logical_value_mut := Induction for logical_value Sort Prop.

(** The Scheme command doesn't generate a mutual indution hypothesis for logical_value so
    we must combine it ourself *)

Combined Scheme typ_combined_aux from typ_mut, formula_mut.

Theorem typ_combined
     : forall (P : typ -> Prop) (P0 : formula -> Prop) (P1 : logical_value -> Prop),
       (forall B p, P0 p -> P { v : B | p}%typ) ->
       (forall T, P T -> forall S, P S -> P (T) --> S%typ) ->
       (forall p, P0 p -> forall q, P0 q -> P0 (p \/ q)%logic) ->
       (forall p, P0 p -> forall q, P0 q -> P0 (p /\ q)%logic) ->
       (forall p, P0 p -> forall q, P0 q -> P0 (p ==> q)%logic) ->
       (forall p, P0 p -> P0 (~ p)%logic) ->
       P0 formula_true ->
       (forall v, P1 v -> forall u, P1 u -> P0 (v = u)%logic) ->
       (forall n, P1 (logical_nat n)) ->
       P1 logical_true ->
       P1 logical_false ->
       (forall n, P1 (logical_bvar n)) ->
       (forall x, P1 (logical_fvar x)) ->
       (forall x, P1 (logical_abs_var x)) ->
       (forall T, P T) /\ (forall p : formula, P0 p) /\ (forall v, P1 v).
Proof. intros. rewrite <- and_assoc. split. eapply typ_combined_aux; eauto.
       apply logical_value_ind; auto. Qed.

Scheme type_mut := Minimality for type Sort Prop
with closed_formula_mut := Minimality for closed_formula Sort Prop
with closed_logical_value_mut := Minimality for closed_logical_value Sort Prop.

Combined Scheme type_combined_aux from type_mut, closed_formula_mut.

Theorem type_combined
     : forall (P : typ -> Prop) (P0 : formula -> Prop) (P1 : logical_value -> Prop),
       (forall L B p,
        (forall x, x \notin L -> closed_formula (p ^ x)) ->
        (forall x, x \notin L -> P0 (p ^ x)%logic) ->
        P { v : B | p}%typ) ->
       (forall L T1 T2,
        type T1 ->
        P T1 ->
        (forall x, x \notin L -> type (T2 ^^ logical_fvar x)) ->
        (forall x, x \notin L -> P (T2 ^^ logical_fvar x)%typ) ->
        P (T1) --> T2%typ) ->
       (forall p1 p2,
        closed_formula p1 ->
        P0 p1 -> closed_formula p2 -> P0 p2 -> P0 (p1 \/ p2)%logic) ->
       (forall p1 p2,
        closed_formula p1 ->
        P0 p1 -> closed_formula p2 -> P0 p2 -> P0 (p1 /\ p2)%logic) ->
       (forall p1 p2,
        closed_formula p1 ->
        P0 p1 -> closed_formula p2 -> P0 p2 -> P0 (p1 ==> p2)%logic) ->
       (forall p, closed_formula p -> P0 p -> P0 (~ p)%logic) ->
       P0 formula_true ->
       (forall v1 v2,
        closed_logical_value v1 ->
        P1 v1 -> closed_logical_value v2 -> P1 v2 -> P0 (v1 = v2)%logic) ->
       (forall n, P1 (logical_nat n)) ->
       P1 logical_true ->
       P1 logical_false ->
       (forall x, P1 (logical_fvar x)) ->
       (forall x, P1 (logical_abs_var x)) ->
       (forall T, type T -> P T) /\
       (forall p, closed_formula p -> P0 p) /\
       (forall v, closed_logical_value v -> P1 v).
Proof. intros. rewrite <- and_assoc. split. eapply type_combined_aux; eauto.
       apply closed_logical_value_ind; auto. Qed.

(** * Body of abstraction and types *)

Definition trm_body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

Definition typ_body T :=
  exists L, forall x, x \notin L -> type (T ^ x).


(** * Tactics *)

(** The library LibLN define some generic tactics to deal with cofinite quantification. To
    use them we must provide a way to ghater non fresh variables in the context of a proof. *)
   
Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : trm => trm_fv x) in
  let E := gather_vars_with (fun x : typ => typ_fv x) in
  let F := gather_vars_with (fun x : formula => formula_fv x) in
  let G := gather_vars_with (fun x : logical_value => logical_value_fv x) in
  constr:(A \u B \u C \u D \u E \u F \u G).

(** The tactic [pick_fresh] pick a fresh variable in the context *)
Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in (pick_fresh_gen L x).

(** The tactic [apply_fresh T as y] takes a lemma T of the form 
    [forall L ..., (forall x, x \notin L, P x) -> ... -> Q.]
    and applies it by instantiating L as the set of variables occuring in the context
    Moreover, for each subgoal of the form [forall x, x \notin L, P x] being generated, the
    tactic automatically introduces the name [x] as well as the hypothesis [x \notin L].
*)
Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; autos*.


(** * Automation *)

(** ** Solve in *)
Ltac in_simpl :=
  match goal with
  | |- context[_ \in (_ \u _)] =>  rewrite in_union; in_simpl
  | |- _ => first [progress cbn; in_simpl | idtac]
  end.
Ltac in_simpl_context :=
  match goal with
  | H: context[_ \in (_ \u _)] |-  _ =>  rewrite in_union in H; in_simpl_context
  | |- _ => first[ progress cbn; in_simpl_context | idtac]
  end.

Ltac in_solve_context_case:=
  match goal with
  | H: (?E \/ ?F)%type |- _ =>
    match E with
    | context[_ \in _] => destruct H; in_solve_context_case
    | _ => match F with
          | context[_ \in _] => destruct H; in_solve_context_case
          | _ => fail 20
          end
    end
  | _ => idtac
  end. 
 
Ltac in_solve_base :=
  match goal with
  | |- (?E \/ ?F)%type  => first [left; in_solve_base | right; in_solve_base]
  | |- ?x \in \{?x} => rewrite in_singleton; reflexivity
  | H: ?x \in ?E |- ?x \in ?E => apply H
  end.
Tactic Notation "in_simpls" := in_simpl; in_simpl_context.
Tactic Notation "in_solve" :=
  in_simpls; in_solve_context_case; try solve [in_solve_base].
Hint Extern 1 (_ \in _) => in_solve.
Hint Extern 1 (_ \in (_ \u _)) => in_solve.

(** ** Some basic automation to solve subset *)

Ltac subset_solve_one :=
  match goal with
  | |- \{} \c _ => apply subset_empty_l
  | |- _  => idtac
  end.

Ltac simpl_set :=
  repeat rewrite union_empty_l; repeat rewrite union_empty_r.

Hint Extern 1 (_ \c _) => simpl_set; subset_solve_one.

(** * Lemma about finite sets *)

Lemma subset_transitive : forall A (E F G : fset A), E \c F -> F \c G -> E \c G.
Proof. red. intros. apply H in H1. apply H0 in H1. assumption. Qed.

Lemma subset_empty_inv : forall {A} {E : fset A}, E \c \{} -> E = \{}.
Proof. introv Subset. apply fset_extens; auto. Qed.

Lemma subset_weaken : forall A (E F G H : fset A),
    E \c (F \u H) -> E \c (F \u G \u H).
Proof. unfolds subset. intros. rewrite union_comm with (E:=G).
       rewrite union_assoc. in_simpl. left. rewrite <- in_union. eauto. Qed.

Lemma singleton_subset : forall (x:var) A, x \in A -> \{x} \c A.
Proof. intros_all.  rewrite in_singleton in *. subst*. Qed.

Lemma union_subset : forall A (E F G : fset A), E \c G -> F \c G -> E \u F \c G.
Proof. unfolds subset. intros. in_simpls. destruct H1; auto. Qed.

Lemma union_subset_inv : forall A (E F G : fset A), E \u F \c G -> E \c G /\ F \c G.
Proof.
  unfolds subset; intros; split; intros. apply H. in_simpl. left*.
  apply H. in_simpl. right*.
Qed.
Lemma subset_union_l : forall A (E F G : fset A), E \c F -> E \c (F \u G).
Proof. unfolds subset. intros. auto. Qed.
Lemma subset_union_r : forall A (E F G : fset A), E \c G -> E \c (F \u G).
Proof. unfolds subset. intros. auto. Qed.

Lemma union_empty : forall {A} (E F : fset A), E \u F = \{} -> E = \{} /\ F = \{} .
Proof.
  intros. split. 
  * apply fset_extens. rewrite <- H. apply subset_union_weak_l.
    apply subset_empty_l.
  * apply fset_extens. rewrite <- H. apply subset_union_weak_r.
    apply subset_empty_l.
Qed.

(** * Properties of fv *)
Lemma open_var_rec_in_typ_fv : forall x E,
    x \in E ->
    (forall T k, typ_fv T \c E ->
            typ_fv ({k ~> logical_fvar x} T) \c E) /\
    (forall p k, formula_fv p \c E ->
            formula_fv ({k ~> logical_fvar x} p) \c E) /\
    (forall v k, logical_value_fv v \c E ->
            logical_value_fv ({k ~> logical_fvar x} v) \c E).
Proof.
  introv In. apply typ_combined; unfolds subset; intros; simpl in *;
             in_solve; eauto.
  case_if; auto. simpl in *. rewrite in_singleton in H0; subst*.
Qed.

Lemma open_var_rec_notin_typ_fv : forall y E,
    (forall T k, y \notin typ_fv T ->
                typ_fv ({k ~> logical_fvar y} T) \c \{y} \u E ->
                typ_fv T \c E) /\
    (forall p k, y \notin formula_fv p ->
                formula_fv ({k ~> logical_fvar y} p) \c \{y} \u E ->
                formula_fv p \c E) /\
    (forall v k, y \notin logical_value_fv v ->
                logical_value_fv ({k~>logical_fvar y} v) \c \{y} \u E ->
                logical_value_fv v \c E).
Proof.
  intros. apply typ_combined; unfolds subset; intros; simpl in *;
          in_solve; eauto.
  * exfalso. rewrite in_empty in H1. auto.
  * exfalso. rewrite in_empty in H1. auto.
  * exfalso. rewrite in_empty in H1. auto.
  * exfalso. rewrite in_empty in H1. auto.
  * exfalso. rewrite in_empty in H1. auto.
  * rewrite in_singleton in H1. red in H. subst. forwards*: (H0 x). in_simpls.
    destruct* H1. rewrite in_singleton in H1. subst. exfalso. auto.
  * exfalso. rewrite in_empty in H1. auto.
Qed.

(** * Properties of terms *)
Open Scope trm_scope.
Lemma open_rec_term_core :forall t j v i s,
    i <> j ->
    {j ~> v}t = {i ~> s}({j ~> v}t) -> t = {i ~> s}t.
Proof.
  induction t; intros; simpl; inversion H0; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t s,
    term t -> forall k,
    t = {k ~> s} t.
Proof.
  intros t s H.
  induction H; intros; simpl; f_equal*.
  unfolds open_trm. pick_fresh_gen L x.
  apply* (@open_rec_term_core t 0 (trm_fvar x)).
  unfolds open_trm. pick_fresh_gen L x.
  apply* (@open_rec_term_core t2 0 (trm_fvar x)).
Qed.

Lemma subst_fresh : forall x t s,
    x \notin (trm_fv t) ->
    [x ~> s] t = t.
Proof. intros. induction t; simpl in *; f_equal*. case_var*. Qed.

Lemma subst_open : forall x s (t1 t2 : trm),
    term s -> 
    [x ~> s] (t1 ^^ t2) = ([x ~> s]t1) ^^ ([x ~> s]t2).
Proof.
  intros. unfold open_trm. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

Lemma subst_open_var : forall x y s t,
    y <> x -> term s ->
    ([x ~> s]t) ^ y = [x ~> s] (t ^ y).
Proof.
  introv Neq H. 
  rewrite* subst_open. simpl. case_var*.
Qed.

Lemma subst_intro : forall x t s,
    x \notin (trm_fv t) -> term s ->
    t ^^ s = [x ~> s] (t ^ x) .
Proof.
  intros.
  rewrite* subst_open. simpl. case_var. rewrite* subst_fresh.
Qed.
Close Scope trm_scope.


Lemma term_abs_to_body : forall lbl t, term (trm_abs lbl t) -> trm_body t.
Proof. introv H. inversion H. exists L; assumption. Qed.
Hint Resolve term_abs_to_body.

Lemma term_let_to_body : forall t1 t2, term (trm_let t1 t2) -> trm_body t2.
Proof. introv H. inversion H. exists L; assumption. Qed.
Hint Resolve term_let_to_body.

Lemma body_to_term_abs : forall lbl t, trm_body t -> term (trm_abs lbl t).
Proof. destruct 1. econstructor. eassumption. Qed.
Hint Resolve body_to_term_abs.

Lemma body_to_term_let : forall t1 t2, term t1 -> trm_body t2 -> term (trm_let t1 t2).
Proof. destruct 2. econstructor; eauto. Qed.
Hint Resolve body_to_term_let.

Lemma subst_term : forall x t s,
    term t -> term s ->
    term ([x ~> s] t).
Proof.
  intros. induction H; simpls; auto.
  case_var*.
  apply_fresh* term_abs. intros. rewrite* subst_open_var.
  apply_fresh* term_let. intros. rewrite* subst_open_var.
Qed.

Lemma open_term : forall t s, trm_body t -> term s -> term (t ^^ s).
Proof.
  intros t s H H0.
  destruct H as [L]. pick_fresh x.
  rewrite* (subst_intro x).
  apply* subst_term.
Qed.

(** * Properties of types *)

Lemma open_rec_type_core : forall v u,
    (forall T j i, i <> j -> {j ~> v} T = {i ~> u}({j ~> v} T) ->
              T = {i ~> u} T)%typ /\
    (forall p j i, i <> j -> {j ~> v} p = {i ~> u}({j ~> v} p) ->
              p = {i ~> u} p)%logic /\
    (forall v' j i, i <> j -> {j ~> v} v' = {i ~> u}({j ~> v} v') ->
               v' = {i ~> u} v')%logic_val.
Proof.
  intros. apply typ_combined; intros; simpl in *;
          try solve [auto; inversion H1; f_equal* | inversion H2; f_equal*].
  case_nat*. case_nat*.
Qed.

Lemma open_rec_type : forall v,
    (forall T, type T -> forall k, T = {k ~> v} T)%typ /\
    (forall p, closed_formula p -> forall k, p = {k ~> v} p)%logic /\
    (forall u, closed_logical_value u -> forall k, u = {k ~> v} u)%logic_val.
Proof.
  introv. apply type_combined; intros; simpl; f_equal*.
  * pick_fresh x. eapply open_rec_type_core. unify ?j 0. auto. unify ?v (logical_fvar x).
    apply* H0. 
  * pick_fresh_gen L x. eapply open_rec_type_core. unify ?j 0. auto.
    unify ?v (logical_fvar x). apply* H2.
Qed.

Lemma subst_open_logical_value : forall x k (b u v : logical_value),
    closed_logical_value v -> 
    ([x ~> v] ({k ~> u} b) = {k ~> [x ~> v]u } ([x ~> v] b))%logic_val.
Proof. intros. destruct b; simpl; f_equal*. case_nat*. case_var*.
       destruct u; simpl; destruct* H. Qed.

Open Scope logic.
Lemma subst_open_formula : forall x p k (u v : logical_value),
    closed_logical_value v -> 
    ([x ~> v] ({k ~> u} p) = {k ~> [x ~> v] u} ([x ~> v] p)).
Proof.
  intros. unfold open_formula. generalize 0.
  induction p; intros; simpl; f_equal; auto using subst_open_logical_value.
Qed.
Close Scope logic.

Lemma subst_open_typ : forall x T (u v : logical_value),
    closed_logical_value v -> 
    ([x ~> v] (T ^^ u) = ([x ~> v] T) ^^ ([x ~> v]u))%typ.
Proof.
  intros. unfold open_typ. generalize 0.
  induction T; intros; simpl; f_equal; auto using subst_open_formula.
Qed.

Lemma open_closed_type : forall v T,
    type T -> T = (T ^^ v)%typ.
Proof. intros. apply* open_rec_type. Qed.

Lemma subst_fresh_mut : forall x v,
    (forall T, x \notin (typ_fv T) -> [x ~> v] T = T)%typ /\
    (forall p, x \notin (formula_fv p) -> [x ~> v] p = p)%logic /\
    (forall u, x \notin (logical_value_fv u) -> [x ~> v] u = u)%logic_val.
Proof.
  intros. apply typ_combined; intros; simpl in *; f_equal*.
  case_var*.
Qed.
Lemma subst_fresh_typ : forall x v T,
    x \notin (typ_fv T) -> ([x ~> v] T = T)%typ.
Proof. apply* subst_fresh_mut. Qed.

Lemma subst_fresh_formula : forall x v p,
    x \notin (formula_fv p) -> (([x ~> v] p)%logic = p).
Proof. apply* subst_fresh_mut. Qed.


Lemma subst_open_rec : forall x u v,
    closed_logical_value u ->
    (forall T k, [x ~> u] {k ~> v} T = {k ~> [x ~> u] v} ([x ~> u] T))%typ /\
    (forall p k, [x ~> u] {k ~> v} p = {k ~> [x ~> u] v} ([x ~> u] p))%logic /\
    (forall v' k, [x ~> u] {k ~> v} v' = {k ~> [x ~> u] v} ([x ~> u] v'))%logic_val.
Proof.
  introv H. apply typ_combined; intros; cbn; f_equal*.
  * case_nat*.
  * case_var*. inversion H; subst; auto.
Qed.
Lemma subst_open_rec_typ : forall x u v T k,
    closed_logical_value u ->
    [x ~> u] {k ~> v} T %typ= {k ~> [x ~> u] v} ([x ~> u] T)%typ.
Proof. intros; apply* subst_open_rec. Qed.
Lemma subst_open_rec_formula : forall x u v p k,
    closed_logical_value u ->
    [x ~> u] {k ~> v} p %logic= {k ~> [x ~> u] v} ([x ~> u] p)%logic.
Proof. intros; apply* subst_open_rec. Qed.

Lemma subst_open_typ_var : forall x y u,
    x <> y -> closed_logical_value u ->
    (forall T, [x ~>u] T ^ y = [x ~> u] (T ^ y))%typ /\
    (forall p, [x ~>u] p ^ y = [x ~> u] (p ^ y))%logic /\
    (forall v, [x ~>u] v ^ y = [x ~> u] (v ^ y))%logic_val.
Proof.
  intros. unfold open_typ, open_formula, open_logical_value.
  apply typ_combined; intros; simpl; f_equal*.
  rewrite subst_open_rec_formula; simpl; auto. case_var*.
  rewrite subst_open_rec_typ; simpl; auto. case_var*.
  case_nat*. simpl. case_var*.
  case_var*. inversion* H0.
Qed.
Lemma subst_open_var_typ : forall T x y u,
    x <> y -> closed_logical_value u ->
    ([x ~>u] T ^ y = [x ~> u] (T ^ y))%typ.
Proof. intros. apply* subst_open_typ_var. Qed.
Lemma subst_open_var_formula : forall p x y u,
    x <> y -> closed_logical_value u ->
    ([x ~>u] p ^ y)%logic = [x ~> u] (p ^ y)%logic.
Proof. intros. apply* subst_open_typ_var. Qed.

Lemma subst_type : forall x u,
    closed_logical_value u ->
    (forall T, type T -> type ([x ~> u] T)) /\
    (forall p, closed_formula p -> closed_formula ([x ~> u] p)) /\
    (forall v, closed_logical_value v -> closed_logical_value ([x ~> u] v)).
Proof.
  intros. apply type_combined; intros; simpl; auto. 
  apply_fresh type_refinement. rewrite* subst_open_var_formula.
  apply_fresh* type_arrow. rewrite* subst_open_var_typ.
  case_var*.
Qed.

Lemma subst_intro_typ : forall x T u,
    x \notin (typ_fv T) ->  closed_logical_value u ->
    (T ^^ u)%typ = [x ~> u] (T ^ x)%typ.
Proof.
  intros. unfold open_typ. rewrite subst_open_rec_typ; simpl; auto.
  case_var. rewrite* subst_fresh_typ.
Qed.

Lemma subst_intro_formula : forall x p u,
    x \notin (formula_fv p) -> closed_logical_value u ->
    (p ^^ u)%logic = [x ~> u] (p ^ x)%logic.
Proof.
  intros. unfold open_formula. rewrite subst_open_rec_formula; simpl; auto.
  case_var. rewrite* subst_fresh_formula.
Qed.


Lemma open_type : forall T u, typ_body T -> closed_logical_value u -> type (T ^^ u).
Proof. intros. destruct H as [L]. pick_fresh x.
       rewrite* (@subst_intro_typ x). apply* subst_type.
Qed.


(** * Properties of environments *)

Lemma env_concat_assoc : forall E F G, (E & F) & G = E & (F & G).
Proof. intros. induction G; simpl; congruence. Qed.

Lemma binding_env_concat : forall E F x T, E & F « x : T = (E & F) « x: T.
Proof. auto. Qed.

Lemma formula_env_concat: forall E F p, E & (F « p) = (E & F) « p.
Proof. auto. Qed.


Lemma empty_env_concat_r : forall E, E = E & empty_env.
Proof. auto. Qed.

Lemma empty_env_concat_l : forall E, E = empty_env & E.
Proof. induction E; simpl; auto; try solve [rewrite* <- IHE]. Qed.

Lemma empty_env_middle : forall E x T F, E « x : T & F = E & (empty_env « x : T) & F.
Proof. intros. auto. Qed.

Lemma empty_env_concat_inv_r :  forall {E F}, empty_env = E & F -> empty_env = F.
Proof.
  intros. gen E. induction F; intros; auto. 
  simpl in H. inversion H. simpl in H.  inversion H.
Qed.

Lemma empty_env_concat_inv_l : forall E F, empty_env = E & F -> empty_env = E.
Proof. 
  intros. gen E. induction F; intros; auto. 
  simpl in H. inversion H. simpl in H.  inversion H.
Qed.


Lemma dom_middle_formula : forall E p F, dom (E « p & F) = dom (E & F).
Proof. induction F; intros; simpl; auto. rewrite* IHF. Qed.

Lemma dom_concat : forall E F, dom (E & F) = dom E \u dom F. 
Proof. induction F; simpl; auto.
       rewrite* union_empty_r.
       rewrite IHF. rewrite* union_comm_assoc.
Qed.

Lemma subst_env_concat : forall E F x u,
    [x~>u] (E & F) = [x~>u] E & [x~>u] F.
Proof. intros. induction F; simpl; auto; rewrite* IHF. Qed.
Lemma binds_in_dom : forall {x E} T, binds x T E -> x \in (dom E).
Proof.
  intros. induction E.
  * inversion H.
  * unfolds binds. simpl. unfolds get. case_var*.
  * simpl. auto.
Qed.

Lemma dom_env_subst : forall E x u, dom ([x ~> u] E) = dom E.
Proof. intros. induction E; auto. simpl. rewrite* IHE. Qed.

Lemma subst_env_notin_dom : forall E x u,
    |~ E ->
    x \notin dom E ->
    [x~>u] E = E.
Proof.
  introv Wf Nin. induction E; simpl; auto.
  * rewrite IHE; simpls; auto. inversion Wf. rewrite notin_union in Nin.
    rewrite* subst_fresh_typ. intros_all. forwards* : (H4 x H5). inversion* Wf.
  * rewrite IHE; simpls; auto. inversion Wf. 
    rewrite* subst_fresh_formula. intros_all. forwards* : (H2 x H3). inversion* Wf.
Qed.

Hint Extern 1 (_ \notin dom _) => repeat (rewrite dom_concat in *).
Hint Extern 1 (_ \in dom _) => repeat (rewrite dom_concat in *).
Hint Extern 1 (?x \in dom ?E) =>
match goal with
| H: binds x ?T E |- _ => apply binds_in_dom in H
end.

(** * Properties of binds *)

Lemma binds_tail : forall x T E, binds x T (E « x : T).
Proof. intros. unfold binds. cbn. case_var*. Qed.

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
  intros. unfolds binds. simpls. case_var. inversion* H.
Qed.

Lemma binds_push_neq : forall x y T S E,
    x <> y -> binds x T E -> binds x T (E « y : S).
Proof. intros. unfold binds. simpl. case_if*. Qed.

Lemma binds_push_neq_inv : forall {x T E} y S,
  binds x T (E « y : S) -> x <> y -> binds x T E.
Proof. introv H. inversion H; intros. case_if*. Qed.

Lemma binds_concat_right : forall x T E F, binds x T F -> binds x T (E & F).
Proof.
  intros. induction F; auto.
  * inversion H.
  * apply binds_push_inv in H. destruct H.
    + destruct H; subst. apply binds_tail.
    + destruct H. apply IHF in H0. simpl. 
      apply* binds_push_neq.
Qed.


Lemma binds_concat_left : forall x T E F,
    binds x T E -> x \notin dom F -> binds x T (E & F).
Proof.
  intros. induction F; auto.
  do_rew <- binding_env_concat (apply binds_push_neq); simpl in H0; auto.
Qed.

Lemma binds_fresh_inv : forall x T E,
  binds x T E -> x \notin dom E -> False.
Proof.
  intros. induction E; auto. 
Qed.


Lemma binds_concat_left_inv : forall x T E F,
  binds x T (E & F) ->
  x \notin dom F ->
  binds x T E.
Proof.  
  introv H ?. lets* [? | [? ?]]: binds_concat_inv H.
  exfalso. apply* binds_fresh_inv.
Qed.

Lemma binds_concat_left_ok : forall x T E G,
  |~ (E & G) ->
  binds x T E ->
  binds x T (E & G).
Proof.
  introv wf H. induction G; auto.
  + inversion wf; subst. do_rew* <- binding_env_concat (apply binds_push_neq).
    intro_subst. apply binds_fresh_inv in H; auto.
  + unfold binds. simpl. inversion wf. apply* IHG.
Qed.

(** * Properties of well-formedness *)

(** ** Well formed environments *)

Lemma wf_env_concat_inv : forall {E F}, |~ (E & F) -> |~ E.
Proof. introv Wf. gen E. induction F; intros; inversion Wf; auto. Qed.

Lemma wf_env_middle_inv : forall {E x T F}, |~ (E « x : T & F) -> x \notin dom E /\ x \notin dom F.
Proof.
  intros. split.
  * apply wf_env_concat_inv in H. inversion* H.
  *  induction F; simpl; auto.
    + inversion H. subst. rewrite dom_concat in H4. simpls*. 
    + inversion H. rewrite dom_concat in H3. simpls*.
Qed.

Lemma wf_env_strengthen : forall {E F} p, |~ (E « p & F) -> |~ (E & F).
Proof.
  introv wf. induction F; simpl in *; inversion* wf; subst.
  * constructor*. rewrite dom_middle_formula in H4. auto.
  * constructor*. rewrite dom_middle_formula in H2. auto.
Qed.

Hint Extern 1 (|~ ?E) =>
  match goal with
  | H: |~ (?F « ?p) |- _ => match F with context[E] => inversion H end
  | H: |~ (?F « _ : _ ) |- _ => match F with context[E] => inversion H end
  | H: |~ (?F & ?G) |- _ => match F with context[E] => apply wf_env_concat_inv in H end
  | H: |~ (?F « ?p  & ?G) |- _ => match F with context[E] => apply (wf_env_strengthen H) end
  end.

Hint Extern 1 (|~ (?E & ?F)) =>
  match goal with
  | H: |~ (?E « ?p  & ?F) |- _ => apply (wf_env_strengthen p H)
  end.


(** ** Well formed environments and binds *)

Lemma ok_middle_inv : forall E F x v,
  |~ (E « x : v & F) -> x \notin dom E /\ x \notin dom F.
Proof.
  intros. induction F; inversion H; simpl; splits*.
  forwards [? ?] : (IHF H3). simpl. apply notin_union. splits*.
  rewrite dom_concat in H4. apply notin_union in H4. destructs H4.
  simpls. apply notin_union in H4. destructs H4. apply* notin_singleton_swap.
Qed.

Lemma binds_middle_neq_inv : forall {x x' T S E F},
    x <> x' ->
    binds x T (E « x' : S & F) ->
    |~ (E « x' : S & F) ->
    binds x T ( E & F).
Proof.
  introv Neq Binds Wf.  induction F.
  + simpls. apply binds_push_neq_inv in Binds; auto.
  + unfolds binds. simpls. case_var*.
  + unfolds binds. simpl. apply* IHF. inversion* Wf.
Qed.
Lemma binds_middle_eq_inv : forall {x T S E F},
    binds x T (E « x : S & F) ->
    |~ (E « x : S & F) ->
    T = S.
Proof.
  introv H O. lets [? ?] : ok_middle_inv O.
  forwards~ M: binds_concat_left_inv H.
  apply binds_push_eq_inv in M; auto.
Qed.

(** ** Well formed Types *)

Lemma type_wf_strengthen : forall {E F T} p, E « p & F |~ T -> E & F |~ T.
Proof.
  introv Typ. destructs Typ. splits 3; auto.
  rewrite dom_middle_formula in H1. auto. 
Qed.
 
Lemma type_wf_strengthen_r : forall {E T} p, E « p |~ T -> E |~ T.
Proof.
  intros. rewrite empty_env_concat_r with E.
  rewrite empty_env_concat_r with (E « p) in H.
  eapply type_wf_strengthen; eauto.
Qed.

    
(** * Properties of entailment *)

Lemma entails_valid : forall E p, valid p -> E |= p.
Proof.
   intros. rewrite empty_env_concat_r with E.
   rewrite empty_env_concat_l with E. apply entails_weaken.
   simpl. apply H.
Qed.

(** * Typing Judgment *)

Lemma typing_var_inv : forall E x T,
    E |~ (trm_fvar x) : T ->
    exists S, binds x S E.
Proof. introv Typ. inductions Typ; eauto. Qed.

Lemma typing_nat_inv : forall {E n T},
    E |~ (trm_nat n) : T -> exists p, T = {v : typ_nat | p}%typ.
Proof.
  introv Typ. inductions Typ.
  + exists (logical_bvar 0 = logical_nat n)%logic. eauto. 
  + destruct IHTyp. subst. inversion H. subst. exists q. auto.
Qed.

Lemma typing_bool_inv : forall {E t T},
    t = trm_true \/ t = trm_false ->
    E |~ t : T ->
    exists p, T = {v : typ_bool | p}%typ.
Proof.
  introv Eq Typ. destruct Eq; subst.
  + inductions Typ.
    - eexists; eauto.
    - destruct IHTyp. subst. inversion H. subst. exists q. auto.
  + inductions Typ.
    - eexists; eauto.
    - destruct IHTyp. subst. inversion H. subst. exists q. auto.
Qed.

Lemma typing_abs_inv : forall {E lbl t T},
    value (trm_abs lbl t) ->
    E |~ (trm_abs lbl t) : T ->
    exists U S, T = (U --> S)%typ.
Proof. introv Val Typ.
   + inductions Typ.
     - exists* T1 T2.
     - lets : (IHTyp Val). destruct H0. destruct H0; subst. inversion H; subst. exists* T21 T22. 
Qed.

Lemma open_typ_term : forall E t T,
    value t -> E |~ t : T ->
    (forall S k, typ_fv S \c dom E -> typ_fv ({k ~> !t} S) \c dom E) /\
    (forall p k, formula_fv p \c dom E -> formula_fv ({k~>!t} p) \c dom E) /\
    (forall v k, logical_value_fv v \c dom E -> logical_value_fv ({k~>!t} v) \c dom E).
Proof.
  introv Atom Typ. apply typ_combined; unfolds subset;
                   intros; simpl in *; in_solve; eauto.
  * inversion Atom; subst; case_if*. simpl in H0.
    rewrite in_singleton in H0; subst. apply typing_var_inv in Typ. destruct Typ.
    auto.
Qed.



(** * Regularity *)

(** The subtyping relation is restricted to well-formed objects. *)
Lemma sub_regular : forall {E T S}, E |~ T <: S -> |~ E /\ E |~ T /\  E |~ S.
Proof.
  introv sub. induction sub.
  * lets : H. destructs H2. splits*. 
  * destructs IHsub. destructs H2. destructs H3. splits*.
    + splits*.
      - apply_fresh* type_arrow. forwards*: (H0 y). destructs H8. destructs* H9.
      - pick_fresh y. forwards *: (H0 y). destructs H8. destructs H9.
        simpl in *. apply* union_subset. eapply open_var_rec_notin_typ_fv; eauto.
    + splits*.
      - apply_fresh* type_arrow. forwards*: (H0 y). destructs H8. destructs* H10.
      - pick_fresh y. forwards *: (H0 y). destructs H8. destructs H10.
        simpl in *. apply* union_subset. eapply open_var_rec_notin_typ_fv; eauto.
Qed.



(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall {E t T}, E |~ t : T -> |~ E /\ term t /\ E |~ T.
Proof.
  intros. induction H; auto.
  * splits*. splits 3; cbn; auto. apply_fresh type_refinement. cbn. case_if*.
  * splits*. splits 3; cbn; auto. apply_fresh type_refinement. cbn. case_if*.
  * splits*. splits 3; cbn; auto. apply_fresh type_refinement. cbn. case_if*.
  * splits*. splits 3; cbn; auto. apply_fresh type_refinement. cbn. case_if*.
    simpl_set. apply* singleton_subset.
  * splits*.
    + pick_fresh y. forwards* : (H1 y). 
    + apply_fresh term_abs. forwards* : (H1 y). 
    + destructs H. splits 3; auto. apply_fresh* type_arrow. 
      forwards* : (H1 y). destructs H4. destructs* H6.
      pick_fresh y. forwards* : (H1 y). destructs H4. destructs* H6.
      cbn. apply* union_subset. cbn in H8. eapply open_var_rec_notin_typ_fv; eauto.
  * splits*. destructs IHtyping2. apply type_wf_strengthen_r in H5. auto.
  * splits*. 
    destructs IHtyping1. splits 3; auto.
    - destructs H5. inversion H5. apply open_type. red. exists L. auto.
      inversion H0; simpl; constructor.
    - destructs H5. simpls. apply union_subset_inv in H7. destruct H7.
      eapply open_typ_term; eauto.
  * splits*. destructs IHtyping. apply_fresh* term_let. forwards* :(H1 y).
  * splits*. eapply sub_regular. eauto.
Qed.

Lemma value_regular : forall t, value t -> term t.
Proof. induction 1; auto. Qed.
Hint Resolve value_regular.

Lemma atom_regular : forall t, atom t -> value t.
Proof. induction 1; auto. Qed.

Lemma red_regular : forall {t s}, t ---> s -> term t /\ term s.
Proof. induction 1; split*.
   * apply* open_term. 
   * inversion H0. apply* open_term.
Qed.

(** Automation *)

(** Extract wf env from other judgments *)
Hint Extern 1 (|~ ?E) =>
  match goal with
  | H: (?F |~ _ <: _) |- _ => match F with context[E] => apply (sub_regular H) end
  | H: (?F |~ _ : _) |- _ => match F with context[E] => apply (typing_regular H) end
  | H: (?F |~ _ ) |- _ => match F with context[E] => inversion H as [_ [? _]] end
  end.

Hint Extern 1 (?E |~ ?T) =>
  match goal with
  | H: (E |~ T <: _) |- _ => apply (sub_regular  H)
  | H: (E |~ _ <: T) |- _ => apply (sub_regular  H)
  | H: (E |~ _ : T) |- _ => apply (typing_regular H)
  | H: (E « ?p |~ T) |- _ => apply (type_wf_strengthen_r p H)
  end.

Hint Extern 1 ((?E & ?F) |~ ?T) =>
  match goal with
  | H: (E « ?p & F |~ T) |- _ => apply (type_wf_strengthen p H)
  end.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: (_ |~ t : _) |- _ => apply (typing_regular H)
  | H: (t ---> _)  |- _ => apply (red_regular H)
  | H: (_ ---> t)  |- _ => apply (red_regular H)
  end.

Hint Extern 1 (type ?T) =>
  match goal with
  | H: (_ |~ T <: _) |- _=> apply (sub_regular H)
  | H: (_ |~ _ <: T) |- _ => apply (sub_regular H)
  | H: (_ |~ T) |- _ => destruct H as [? _]
  end.

Hint Extern 1 (closed_logical_value (!?u)) =>
  match goal with
  | H : (value u) |- _ => inversion H; simpl; auto
  end.

