Require Import TLC.LibLN Definitions Infrastructure.


Lemma entails_subst2 : forall {E p q} x v,
    |~ E ->
    x \notin dom E ->
    closed_logic_val v ->
    x \notin formula_fv p ->
    x \notin formula_fv q ->
    extract E \u \{p^x}%logic |= (q^x)%logic ->
    extract E \u \{p ^^ v}%logic |= (q^^v)%logic.
Proof.
  introv Wf Notin Closed NotinFv1 NotinFv2 Ent.
  apply (@entails_subst _ _ x v (extract E \u \{p^^v}%logic)) in Ent.
  * rewrite* <- (@subst_intro_formula x) in Ent.
  * apply subst_set_union.
    (* + rewrite <- (subst_env_notin_dom E x v) at 2; auto. apply subst_set_extract; auto. *)
    + rewrite <- (@subst_env_notin_dom _ x v) at 2; auto. apply subst_set_extract; auto.
    + rewrite (@subst_intro_formula x p v); auto. apply subst_set_singleton.
Qed.

Lemma refinement_soundness_result : refinement_soundness.
Proof.
  introv Val Typ. inductions Typ; try solve[inversion Val | cbn; case_nat; apply entails_eq].
  inversion H; subst. forwards* : (IHTyp B p0 Val). pick_fresh y. forwards* : (H6 y).
  unfolds valid. eapply (@entails_cut _ (p0 ^^ !t)%logic ). assumption.
  apply (entails_subst2 y (!t)); auto.
Qed.

Ltac get_env H :=
  match H with
  | ?E |= _ => constr:(E)
  | ?E |~ _ : _ => constr:(E)
  | |~ ?E => constr:(E)
  | ?E |~ _ <: _ => constr:(E)
  | ?E |~ _ => constr:(E)
  end.

(** * Narrowing *)
Lemma entails_narrowing : forall {E F x S1} S2 p,
    E |~ S1 <: S2 ->
    E « x : S2 & F ||= p ->
    E « x : S1 & F ||= p.
Proof.
  introv Sub Ent.
  inversion Sub; subst.
  * (* Rewriting Ent *)
    rewrite extract_concat in Ent. cbn in Ent. rewrite union_comm in Ent. rewrite union_assoc in Ent.
    (* Rewriting Goal *)
    rewrite extract_concat. cbn. rewrite union_comm. rewrite union_assoc.
    (* Rewriting H1 *)
    pick_fresh y. forwards* : (H1 y).
    apply (entails_subst2 y (logical_fvar x)) in H2; auto.
    apply (entails_monotone (extract F)) in H2. rewrite union_comm in H2. rewrite union_assoc in H2.
    apply (entails_trans (p2:=(q^x)%logic)); assumption.
 * rewrite extract_concat. rewrite extract_concat in Ent. cbn in *. assumption.
Qed.

Lemma wf_env_narrowing : forall {E F S1} S2 x,
    E |~ S1 <: S2 ->
    |~ (E « x : S2 & F) ->
    |~ (E « x : S1 & F).
Proof.
  intros. lets [? [? ?]] : (sub_regular H). induction F; simpls; auto.
  * inversion H0. destruct H2. constructor*.
  * inversion H0. constructor*. rewrite dom_concat in *; auto.
  * inversion H0. constructor*. rewrite dom_concat in *; auto.
Qed.

Lemma entails_typing_subst : forall {E F p x} s S,
    value s ->
    E |~ s : S ->
    x \notin dom F ->
    |~ (E « x : S) ->
    (E « x : S & F) ||= p ->
    ([x ~> !s] (E & F)) ||= ([x ~> !s] p).
Proof.
  introv Val Typ Notin Wf Ent.
  lets Wf2 : Wf. inversion Wf. destruct S; subst.
  * apply refinement_soundness_result in Typ; auto.
    apply (@entails_subst _ _ x (!s) (extract [x ~> !s] E \u \{f^^!s}%logic \u extract [x ~> !s] F)) in Ent.
    + rewrite (union_comm _ (extract [x ~> !s] F)) in Ent. rewrite union_assoc in Ent.
      apply (entails_cut (p:=f^^!s)%logic) in Ent.
      - rewrite subst_env_concat. rewrite extract_concat. assumption.
      - rewrite subst_env_notin_dom; auto. apply entails_monotone. assumption.
    + rewrite extract_concat. cbn. rewrite union_assoc. apply subst_set_union.
      - apply subst_set_union. apply subst_set_extract; auto.
        rewrite (@subst_intro_formula x f (!s)); auto. apply subst_set_singleton.
        cbn in H4. intros_all. auto.
      - apply subst_set_extract; auto. 
 * rewrite extract_concat in Ent. cbn in Ent.
   apply (@entails_subst _ _ x (!s) (extract [x ~> !s] E \u extract [x ~> !s] F)) in Ent.
   + rewrite subst_env_concat. rewrite extract_concat. auto.
   + apply subst_set_union. apply subst_set_extract; auto.
     apply subst_set_extract; auto. 
Qed.

Lemma wf_type_narrowing : forall E F x S1 S2 T,
    E |~ S1 <: S2 ->
    E « x : S2 & F |~ T -> E « x : S1 & F |~ T.
Proof.
  intros. destruct H0 as [? [? ?]]. lets : H0. induction H0.
  * constructor*. split. apply (wf_env_narrowing S2); auto. rewrite dom_concat in *; auto.
  * constructor*. split. apply (wf_env_narrowing S2); auto. rewrite dom_concat in *; auto.
Qed.

Lemma sub_narrowing : forall E F x S1 S2 T1 T2,
    E |~ S1 <: S2 ->
    E « x : S2 & F |~ T1 <: T2 ->
    E « x : S1 & F |~ T1 <: T2.
Proof.
  intros. inductions H0.
  * apply_fresh* subtype_refinement. apply* wf_type_narrowing. apply* wf_type_narrowing.
    do_rew* push_formula_concat (apply (entails_narrowing S2)).
  * apply_fresh* subtype_arrow. forwards* : (H1 y). rewrite* push_binding_concat. assumption. 
Qed.

(** * Subtyping *)

Lemma sub_refl : forall E T,
    E |~ T ->
    E |~ T <: T.
Proof.
  introv WfTyp. lets H : WfTyp. destructs H. gen E. inductions H; intros.
  * apply_fresh* subtype_refinement. apply entails_assumption.
  * simpls. apply union_subset_inv in H3. destructs H3.
    apply_fresh* subtype_arrow. 
    + simpls. eapply IHtype; auto. splits*.
    + apply* H1. 
        - splits*. apply* open_var_rec_in_typ_fv. simpl. apply* subset_union_l.
        - apply* open_var_rec_in_typ_fv. simpl. apply* subset_union_l.
Qed.


Lemma sub_trans : forall E T1 T2 T3, E |~ T1 <: T2 -> E |~ T2 <: T3 -> E |~ T1 <: T3.
Proof.
  introv Sub1 Sub2. assert (type T2); auto. gen E T1 T3 Sub1 Sub2.
  induction H; introv Sub1 Sub2.
  * inversion Sub1; subst. inversion Sub2; subst. apply_fresh* subtype_refinement.
    cbn in *. eapply entails_trans; auto.
  * inversion Sub1. subst. inversion Sub2. subst. apply_fresh subtype_arrow; auto.
    eapply H1; auto. rewrite empty_concat_r at 1. eapply sub_narrowing; eauto.
Qed.


(** * Weakening *)

Lemma subset_dom_weaken : forall A E F (G : ctx), A \c dom (E & G) -> A \c dom (E & F & G).
Proof. intros. repeat rewrite dom_concat in *. rewrite <- union_assoc.
       apply* subset_weaken. Qed.

Lemma wf_type_weaken : forall E F G T,
    (E & G ) |~ T ->
    |~ (E & F & G) ->
    (E & F & G) |~ T.
Proof.
  intros. inductions H. destructs H0. splits*. apply* subset_dom_weaken.
Qed.

Lemma sub_weaken : forall E F G T T',
    (E & G) |~ T <: T' ->
    |~ (E & F & G) ->
    (E & F & G) |~ T <: T'.
Proof.
  introv sub wf. inductions sub. 
  * apply_fresh* subtype_refinement; intros.
      apply* wf_type_weaken. apply* wf_type_weaken.
      cbn in *. repeat rewrite extract_concat. rewrite (union_comm (extract E) (extract F)).
      do 2 rewrite <- union_assoc. rewrite (union_comm (extract F)).
      apply entails_monotone. rewrite extract_concat in H1. rewrite union_assoc. apply* H1.
  * apply_fresh* subtype_arrow. do_rew push_binding_concat (apply H0); auto.
    constructor*. apply IHsub in wf; auto. apply sub_regular in wf. destructs wf.
    destructs* H2.
Qed.

Hint Resolve binds_weaken.
Hint Resolve subset_dom_weaken.
Lemma typing_weaken : forall {E G t T} F,
    (E & G) |~ t : T ->
    |~ (E & F & G) ->
    (E & F & G ) |~ t : T.
Proof.
  introv Typ. inductions Typ; introv wf; eauto.
  * destruct H1. constructor*. splits*.
  * apply_fresh typing_abs. apply* wf_type_weaken.
    do_rew push_binding_concat (apply H1); auto. constructor*. destructs* H.
  * econstructor; auto.
    + do_rew push_formula_concat (apply IHTyp2); auto. constructor*.
      inversion H; subst; simpl; simpl_set; try solve [apply subset_empty_l].
      apply typing_var_inv in Typ1. destruct Typ1. apply binds_in_dom in H0.
      apply* singleton_subset.
    + do_rew push_formula_concat (apply IHTyp3); auto. constructor*.
      inversion H; subst; simpl; simpl_set; try solve [apply subset_empty_l].
      apply typing_var_inv in Typ1. destruct Typ1. apply binds_in_dom in H0.
      apply* singleton_subset.
  * apply_fresh* typing_let.
    + do_rew push_binding_concat (apply H0); auto. constructor; auto.
      apply typing_regular in Typ. destructs Typ. destructs* H4.
    + apply* wf_type_weaken.
  * eapply typing_sub; eauto. apply* sub_weaken.
Qed.


Ltac simpl_env := repeat rewrite <- empty_concat_r in *;
                  repeat rewrite <- empty_concat_l in *.
                 
Tactic Notation "forwards_weaken" uconstr(Weaken) constr(Hyp) "with" constr(To) :=
  let From := get_env type of Hyp in
  match To with
  | context[?E « ?x : ?T] =>
    match From with E => rewrite (empty_concat_r E) in Hyp;
                        forwards : (Weaken (empty_env « x : T) Hyp); simpl_env
    end
  | context[?E « ?p] =>
    match From with E => rewrite (empty_concat_r E) in Hyp;
                        forwards : (Weaken (empty_env « p) Hyp); simpl_env
    end
  | ?E & ?F =>
    match From with
    | empty_env => rewrite (empty_concat_r empty_env) in Hyp; forwards : (Weaken E Hyp); simpl_env
    | E => rewrite (empty_concat_r E) in Hyp; forwards : (Weaken F Hyp); simpl_env
    | F => rewrite (empty_concat_l F) in Hyp; forwards : (Weaken E Hyp); simpl_env
    end
  | ?E =>
    match From with
    | empty_env => rewrite (empty_concat_r empty_env) in Hyp; forwards : (Weaken E Hyp); simpl_env
    end
  end.
Tactic Notation "forwards_weaken" uconstr(Weaken) constr(Hyp) :=
  let To := match goal with |- ?G => get_env G end in
  forwards_weaken Weaken Hyp with To.
Tactic Notation "forwards_weaken" "*" uconstr(Weaken) constr(Hyp) :=
  forwards_weaken Weaken Hyp; eauto.

Hint Extern 1 (?E |~ ?t : ?T) =>
  match goal with
  | H: (_ |~ t : T) |- _ => forwards_weaken typing_weaken H
  end.
  

(** * Strengthening *)

Lemma binds_strengthen : forall (E : ctx) p F T x,
    binds x T (E « p & F) -> binds x T (E & F).
Proof.
  intros. induction F; auto. unfolds binds. inversion H.
  case_var; simpl. case_var*. case_var*. rewrite* IHF.
Qed.
    
Lemma sub_strengthen : forall E p F T S,
    E « p & F |~ T <: S ->
    E ||= p ->
    E & F |~ T <: S.
Proof.
  introv Typ Ent. lets Reg: Typ. 
  inductions Typ.
  * apply_fresh* subtype_refinement; intros.
    apply (entails_cut (p:=p)).
    + apply entails_monotone. rewrite extract_concat. apply entails_monotone. assumption.
    + cbn in *. rewrite extract_concat in H1. cbn in H1. rewrite (union_comm (extract E) \{p}) in H1.
      forwards* : (H1 y).
      rewrite <- (union_assoc (\{p} \u extract E)) in H2. rewrite <- union_assoc in H2.
      rewrite (union_comm \{p}) in H2. rewrite extract_concat. rewrite union_assoc in H2.
      assumption.
  * apply_fresh* subtype_arrow. do_rew* push_binding_concat (eapply H0). 
Qed.

Lemma typing_strengthen : forall E p F t T,
    E « p & F |~ t : T ->
    E ||= p ->
    E & F |~ t : T.
Proof.
  introv Typ Ent. inductions Typ; auto.
  * econstructor; auto. eapply binds_strengthen; eauto.
  * econstructor; auto. eapply binds_strengthen; eauto.
  * apply_fresh* typing_abs. do_rew* push_binding_concat (eapply H1).
  * econstructor; eauto. do_rew* push_formula_concat (eapply IHTyp2).
    do_rew* push_formula_concat (eapply IHTyp3).
  * econstructor; eauto. 
  * apply_fresh* typing_let. do_rew* push_binding_concat (eapply H0).
  * eapply typing_sub; eauto. eapply sub_strengthen; eauto.
Qed.

Lemma typing_strengthen_r : forall E p t T,
    E « p |~ t : T ->
    E ||= p ->
    E |~ t : T.
Proof.
  intros. rewrite (empty_concat_r E). eapply typing_strengthen; eauto.
Qed.


(** * Substitution *)


Lemma trm_fv_subst : forall t x, trm_fv t \c trm_fv (t ^ x).
Proof.
  intros. unfold open_trm. generalize 0.
  induction t; intros; red; intros; simpls; auto.
  * in_solve. forwards* : (IHt1 n). forwards* : (IHt2 n). forwards* : (IHt3 n).
  * exfalso. rewrite* in_empty in H.
  * forwards* : (IHt (S n)).
  * in_solve. forwards* : (IHt1 n). forwards* : (IHt2 (S n)).
  * in_solve. forwards* : (IHt1 n). forwards* : (IHt2 n).
Qed.

Lemma typing_fv_inv : forall {E t T}, E |~ t : T -> trm_fv t \c dom E.
Proof. introv Typ. induction Typ; simpl; auto.
  * apply binds_in_dom in H0. red. intros. rewrite in_singleton in H1. subst. auto.
  * apply binds_in_dom in H0. red. intros. rewrite in_singleton in H2. subst. auto.
  * pick_fresh y. forwards* : (H1 y). lets: (trm_fv_subst t y).
    eapply subset_transitive with (E:= trm_fv t) in H2; auto.
    intros_all. forwards : (H2 x); auto. in_solve.
    rewrite in_singleton in H5. exfalso. subst. auto.
  * simpls. intros_all*. 
  * intros_all*.
  * intros_all. in_solve. auto. 
    pick_fresh y. forwards : (H0 y); auto. lets: (trm_fv_subst t2 y).
    eapply subset_transitive with (E:=trm_fv t2) in H3; auto.
    forwards : (H3 x); auto. in_solve.
    rewrite in_singleton in H5. exfalso. subst. auto.
Qed.

Lemma typing_empty_inv : forall {t T}, empty_env |~ t : T -> typ_fv T = \{} /\ trm_fv t = \{} .
Proof.
  introv Typ. lets: (typing_regular Typ). destructs H. splits.
  * destructs H1. apply subset_empty_inv in H3. auto. 
  * apply typing_fv_inv in Typ. simpls. apply subset_empty_inv in Typ; auto.
Qed.

Lemma typ_fv_subst: forall (E : ctx) x F X u,
    logic_val_fv u \c dom E ->
    (forall T, typ_fv T \c dom (E « x : X & F) -> typ_fv ([x ~> u] T) \c dom (E & F)) /\
    (forall p, formula_fv p \c dom (E « x : X & F) -> formula_fv ([x ~> u] p) \c dom (E & F)) /\
    (forall v, logic_val_fv v \c dom (E « x : X & F) -> logic_val_fv ([x ~> u] v) \c dom (E & F)).
Proof.
  intros. apply typ_combined; cbn; intros; eauto;
  try solve [apply union_subset_inv in H2; destruct H2; apply* union_subset].
  case_var*.
    + rewrite dom_concat in *. apply* subset_union_l.
    + rewrite dom_concat in *. cbn in *. red. intros. forwards : (H0 x1); auto.
      rewrite <- union_assoc in H2. rewrite in_union in H2. destruct H2; auto.
      rewrite in_union in H2. destruct H2; auto.
      rewrite in_singleton in H1. rewrite in_singleton in H2. exfalso. subst. auto.
Qed.

Lemma wf_env_subst : forall {E x F} T u,
    closed_logic_val u ->
    |~ (E « x : T & F) ->
    logic_val_fv u \c dom E ->
    |~ [x ~> u] (E & F).
Proof.
  introv Closed Wf Fv. rewrite subst_env_concat. lets M : (wf_concat_inv Wf). inversion M.
  rewrite subst_env_notin_dom at 1; auto.
  inductions F.
  * inversion* Wf.
  * inversion Wf; subst. cbn. constructor*.
    - rewrite dom_concat in *. simpls. rewrite* dom_env_subst.
    - rewrite dom_concat in *. simpls. rewrite* dom_env_subst.
      rewrite <- dom_concat. eapply (typ_fv_subst); auto. rewrite* dom_concat.
    - apply subst_type; auto.
  * inversion Wf; subst. simpl. constructor*. 
    rewrite dom_concat in *. simpls. rewrite* dom_env_subst.
    rewrite <- dom_concat. eapply typ_fv_subst; auto. rewrite* dom_concat.
    apply subst_type; auto.
  Unshelve. exact T. exact T.
Qed.

Lemma wf_env_subst_trm : forall {E x F} S s,
    |~ (E « x : S & F) ->
    value s ->
    E |~ s : S ->
    |~ [x ~> !s] (E &  F).
Proof. introv Wf Val Typ. inversion Val; simpl; try solve [eapply wf_env_subst; simpl; eauto].
  eapply wf_env_subst; eauto. simpl. subst. apply typing_var_inv in Typ. destruct Typ.
  apply binds_in_dom in H. red. intros. rewrite in_singleton in H0. subst*.
Qed.

Lemma notin_subst : forall x u,
  u <> logical_fvar x ->
  (forall T, x \notin typ_fv ([x ~> u] T)) /\
  (forall p, x \notin formula_fv ([x~>u] p)) /\
  (forall v, x \notin logic_val_fv ([x~>u] v)).
Proof.
  intros. apply typ_combined; intros; simpl; auto. case_var.
  + destruct u; simpl; auto. red. red. intros. rewrite in_singleton in H0. subst*. 
  + simpl. red. red. intros. rewrite* in_singleton in H0. 
Qed.

Lemma in_typ_fv_subst : forall x y u,
   (forall T, x \in typ_fv ([y ~> u] T) -> x \in typ_fv T \/ x \in logic_val_fv u) /\
   (forall p, x \in formula_fv ([y ~> u] p) -> x \in formula_fv p \/ x \in logic_val_fv u) /\
   (forall v, x \in logic_val_fv ([y ~> u] v) -> x \in logic_val_fv v \/ x \in logic_val_fv u).
Proof.
  intros. apply typ_combined; intros; simpls; auto;
  try solve [in_solve; [rewrite or_comm; rewrite <- or_assoc; left; rewrite* or_comm | 
                        rewrite or_assoc; right; auto]].
  case_var*.
Qed.

Lemma wf_typ_subst : forall {E F x T} S u,
    E « x : S & F |~ T ->
    closed_logic_val u ->
    logic_val_fv u \c dom E ->
    [x ~> u] (E & F) |~ [x ~> u] T.
Proof. intros. destructs H. splits.
  * apply* subst_type. 
  * apply (wf_env_subst S); auto.
  * intros_all. rewrite dom_concat in *. simpls. rewrite dom_env_subst.
    destruct (classicT (x = x0)).
    + forwards : (notin_subst x u).
      - intros_all. destruct u; inversion H5. simpls. subst v. subst.
        apply wf_concat_inv in H2. inversion H2. subst. forwards* : (H1 x0).
      - subst. apply H5 in H4. exfalso. auto. 
    + forwards : (in_typ_fv_subst x0 x u); auto. apply H5 in H4. destruct H4.
      - forwards : (H3 x0); auto. in_solve; auto. exfalso. rewrite* in_singleton in H6. 
      - forwards* : (H1 x0). 
Qed.

Lemma wf_typ_subst_trm : forall {E x F T} S s,
     E « x : S & F |~ T ->
     value s ->
     E |~ s : S ->
     [x ~> !s] (E & F) |~ [x ~> !s] T.
Proof. intros. eapply wf_typ_subst; eauto; inversion H0; simpl; auto.
       subst s. apply typing_var_inv in H1. destruct H1. apply binds_in_dom in H1.
       red. intros. rewrite in_singleton in H2. subst*.
Qed.


Lemma subtyping_subst : forall {x E F S T T'} s,
    E « x : S & F |~ T <: T' ->
    value s ->
    empty_env |~ s : S ->
    [x ~> !s] (E & F) |~ [x ~> !s] T <: [x ~> !s] T'.
Proof.
  introv Sub Val Typ. inductions Sub; simpl.
  * apply_fresh subtype_refinement. 
    forwards* : (wf_typ_subst_trm S s H Val). forwards* : (wf_typ_subst_trm S s H0 Val).
    lets : (H1 y). rewrite <- push_formula_concat in H2.
    inversion H as [_ [WfEnv _]]. apply wf_middle_inv in WfEnv as [NotinE NotinF].
    apply (entails_typing_subst s) in H2; auto. rewrite push_formula_concat in H2.
    repeat rewrite subst_open_var_formula; auto.
  * simpl. apply_fresh* subtype_arrow.
    forwards* : (H0 y). rewrite* push_binding_concat. repeat rewrite* subst_open_var_typ. 
Qed.

Lemma binds_subst : forall x y u T E, binds x T E -> binds x [y~>u] T [y~>u] E.
Proof.
  introv Binds. induction E; auto.
  * inversion Binds.
  * apply binds_push_inv in Binds. simpl. destruct Binds.
    - destruct H. subst. apply binds_push.
    - apply* binds_push_neq.
Qed.

Lemma value_subst : forall v x u, value v -> value u -> value [x ~> u] v.
Proof. intros. induction H; simpl; auto.
   * case_var*.
   * inversion H. constructor; auto. apply_fresh term_abs.
     rewrite* subst_open_var. apply* subst_term.
Qed.

Open Scope logic_val.
Lemma subst_lift : forall x u v, value v -> value u -> ![x ~> u] v = [x ~> !u] !v.
Proof.
  introv Valv Valu. destruct Valv; simpl; auto.
  case_var*. 
Qed.
Close Scope logic_val.
    
Lemma typing_subst_dependent : forall {E S F t T x} s,
    E « x : S & F |~ t : T ->
    value s ->
    empty_env |~ s : S ->
    [x ~> !s] (E & F) |~ [x ~> s] t : [x ~> (!s)] T.
Proof.
  introv TypT Val TypS. inductions TypT;
    try solve [constructor; apply (wf_env_subst_trm S); auto].
  (* Case var refinement *)
  * cbn; case_var.
    + inversion Val; simpl; subst.
      (* Case var: cannot happpen because we are typing in empty environment*)
      - apply typing_var_inv in TypS. destruct TypS. inversion H1.
      (* Case Consts *)
      - apply typing_nat_inv in TypS. destruct TypS.
        apply binds_middle_eq_inv in H0; auto. subst S. inversion* H1.
        constructor*. eapply wf_env_subst; subst; eauto. simpl. auto.
      - apply typing_bool_inv in TypS; auto. destruct TypS.
        apply binds_middle_eq_inv in H0; auto. subst S. inversion* H1.
        constructor*. eapply wf_env_subst; subst; eauto. simpl. auto.
      - apply typing_bool_inv in TypS; auto. destruct TypS.
        apply binds_middle_eq_inv in H0; auto. subst S. inversion* H1.
        constructor*. eapply wf_env_subst; subst; eauto. simpl. auto.
      (* Abs case: cannot happen because we are typing a refinement *)
      - apply typing_abs_inv in TypS; auto. destruct TypS. destruct H2. subst.
        apply binds_middle_eq_inv in H0; auto. inversion H0.
    + apply binds_middle_neq_inv in H0; auto. econstructor.
      - eapply wf_env_subst_trm; subst; eauto. 
      - forwards* : binds_subst. 
  (* Case var fun *)
  * unfold trm_subst. case_var.
    (* S = T1 --> T2, as s is typed in an empty environement S has no fre variables*)
    + apply binds_middle_eq_inv in H0; auto. subst. lets : (typing_empty_inv TypS).
      forwards_weaken typing_weaken TypS; simpl_env.
      eapply wf_env_subst_trm; eauto.
      rewrite* subst_fresh_typ. destruct H0. rewrite* H0.
    + apply binds_middle_neq_inv in H0; auto.
      simpl. apply typing_var_arrow. eapply wf_env_subst_trm; eauto.
      forwards* : binds_subst. forwards* : (wf_typ_subst_trm S s H1).
  (* Case Abs *)
  * cbn. apply_fresh typing_abs. eapply wf_typ_subst_trm; eauto.
    rewrite* subst_open_var. rewrite* subst_open_var_typ. forwards* : (H1 y).
    rewrite* <- push_binding_concat. auto.
  (* Case If *)
  * cbn. econstructor; auto.
    + apply* value_subst.
    + eapply IHTypT1; auto.
    + forwards* : IHTypT2. rewrite* <- push_formula_concat. rewrite* subst_lift.
    + forwards* : IHTypT3. rewrite* <- push_formula_concat. rewrite* subst_lift.
  * simpl. rewrite* subst_open_typ. rewrite* <- subst_lift.
    econstructor; auto. apply* value_subst. apply* value_subst. 
    simpl in *. eapply IHTypT1; auto. eapply IHTypT2; auto.
  (* Case Let *)
  * simpl. apply_fresh typing_let; auto.
    - eapply IHTypT; auto.
    - rewrite* subst_open_var. forwards* : (H0 y). rewrite* push_binding_concat. auto.
    - eapply wf_typ_subst_trm; eauto. 
  (* Case Sub *) 
  * eapply typing_sub. eapply IHTypT; auto. eapply subtyping_subst; try eassumption. 
Qed.


Lemma typing_subst : forall {E F S t T x} s,
    E « x : S & F |~ t : T ->
    E & F |~ T ->
    value s ->
    empty_env |~ s : S ->
    [x ~> !s] (E & F) |~ [x ~> s] t : T.
Proof.
  intros. rewrite* <- (@subst_fresh_typ x (!s)).
  * eapply typing_subst_dependent; eauto.
  * lets [? [_ _]] : (typing_regular H). lets [? ?] : (wf_middle_inv _ _ _ _ H3).
    inversion H0. destruct H7. intros_all. forwards : (H8 x); auto.
    rewrite dom_concat in H10; auto. in_solve. apply H4 in H10. auto. apply H5 in H10. auto.
Qed.


(** * Preservation *)

(* If we type a lambda it is possible to type the body in an extended environment *)
Lemma typing_abs_strong_inv : forall {E lbl t T},
    E |~ (trm_abs lbl t) : T ->
    forall U1 U2,
    E |~ T <: (U1 --> U2) ->
    exists S1 S2,
      (E |~ U1 <: S1) /\
      (exists L, forall x, x \notin L ->
        (* E « x : S1 |~ (t ^ x) : (S2 ^ x) /\ (E « x: U1) |~ (S2 ^ x) <: (U2 ^ x)). *)
        E « x : S1 |~ (t ^ x) : (S2 ^ x) /\ (E « x: U1) |~ (S2 ^ x) <: (U2 ^ x)).
Proof.
  introv Typ. inductions Typ; introv Sub.
  * inversion* Sub. exists T1 T2. split*. exists (L \u L0). intros. split*.
  * apply IHTyp. inversion* Sub. subst. inversion H. subst.
    eapply sub_trans; eauto.
Qed.

Lemma preservation_result : preservation.
Proof.
  (* introv Typ. gen s. inductions Typ; introv Red; try solve [inversion Red]. *)
  introv Typ. gen s. inductions Typ; introv Red; try solve[inversion Red].
  (* IF *)
  * inversion Red; subst; simpls; eapply typing_strengthen_r; eauto;
    apply entails_valid; apply valid_eq.
  (* Application *)
  * inversion Red; subst.
    forwards* : (typing_abs_strong_inv Typ1).
    + apply* sub_refl.
    + destruct H1 as [S1 [S2 [Sub [L P]]]].
      pick_fresh y. forwards*:(P y). rewrite* (subst_intro (x:=y)).
      rewrite* (subst_intro_typ (x:=y)). destruct H1.
      rewrite empty_concat_r in H1 at 1.
      forwards : (typing_subst_dependent t2 H1); auto.
      eapply typing_sub; eauto.
      rewrite empty_concat_r in H2 at 1.
      forwards* : (subtyping_subst t2 H2).
  (* let *)
  * inversion Red; subst.
    + pick_fresh y. forwards*:(H y). rewrite* (subst_intro (x:=y)).
      rewrite empty_concat_r in H2 at 1.
      forwards* : (typing_subst t1 H2).
    + apply_fresh* typing_let.
  (* Subtyping *)
  * eapply typing_sub; eauto. 
Qed.

(** Canonical forms *)
Lemma canonical_form_bool : forall t p,
    value t ->
    empty_env |~ t : {v : typ_bool | p } ->
    t = trm_true \/ t = trm_false.
Proof.
  introv Val Typ. inductions Typ; auto; try solve[inversion Val].
  * inversion H0.
  * inversion H. apply IHTyp with p0; subst; auto. 
Qed.

Lemma canonical_form_abs : forall t T1 T2,
    empty_env |~ t : (T1 --> T2) ->
    value t ->
    exists lbl t2, t = trm_abs lbl t2.
Proof.
  introv Typ Val. inductions Typ; try solve [inversion Val; auto].
  + exfalso. inversion H0.
  + exists lbl t. auto.
  + inversion H. apply IHTyp with T11 T12; auto.
Qed.


(** Progress Result *)

Lemma progress_result : progress.
Proof.
  introv Typ. inductions Typ; auto.
  * left. constructor. apply_fresh* term_abs. forwards*: (H0 y).
  * right. lets H1 : Typ1. apply canonical_form_bool in H1; auto. destruct H1.
    + subst. exists t1. constructor*. 
    + subst. exists t2. constructor*.
  * right. lets H1: Typ1. apply canonical_form_abs in H1; auto.
    destruct H1. destruct H1. subst. exists (x0 ^^ t2)%trm. constructor*.
  * right. destruct IHTyp; auto.
    + exists (t2 ^^ t1)%trm. constructor; auto. econstructor; auto.
      intros. forwards*: (H x).
    + destruct H2. exists (trm_let x t2). constructor; auto.  econstructor; auto.
      intros. forwards*: (H x0).
Qed.