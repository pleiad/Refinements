Require Import TLC.LibLN.
Require Import Env.

Set Implicit Arguments.

(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Grammars *)


(* ********************************************************************** *)
(** ** Terms *)

(** Grammar of pre-terms. We use a locally nameless representation where bound variables
    are represented as natural numbers (de Bruijn indices) and free variables are
    represented as atoms. A variable can be bound by an abstraction or a let construction.
    The type [var], defined in the library LibLN_Var, represents 'names' or 'atoms'. One
    central assumption is that it is always possible to generate a fresh atom for any given
    finite set of atoms (lemma [var_fresh]).

    Traditionally, the syntax of simple refinement-types systems is defined in A-normal form.
    This is important when defining the application rule of the typing judgment as we have
    dependent types. Here we don't make a syntactic distinction between values and other
    terms, so the resulting grammar is not in A-normal form. Instead we define a proposition
    that holds for terms that are values and we add the necessary hypothesis when needed.
    For example, the typing judgment only holds for terms that are in A-normal form.
*)

Inductive trm : Set :=
  | trm_nat : nat -> trm
  | trm_true : trm
  | trm_false : trm
  | trm_if : trm -> trm -> trm -> trm
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm 
  | trm_abs : var -> trm -> trm
  | trm_let : trm -> trm -> trm
  | trm_app : trm -> trm -> trm.

Implicit Types t s : trm.

(* ********************************************************************** *)
(** ** Types *)

(** *** Grammar of base types. *)
Inductive typ_base : Set := typ_bool | typ_nat.
Implicit Types B : typ_base.


(** *** Grammar of types *)
(** A refinement allows us to decorate base types with logical formulas. A refinement
    introduces a binder that can be mentioned in the formula to make constraints about it. As
    with terms, we also use a locally nameless representation to deal with bindings. Arrow
    types are dependent, so they also bind variables.
 *)

Inductive typ : Set :=
  | typ_refinement : typ_base -> formula -> typ
  | typ_arrow : typ -> typ -> typ

(** *** Grammar of formulas *)
(** Simple logical operators plus an equality predicate *)

with formula : Set :=
  | formula_or : formula -> formula -> formula
  | formula_and : formula -> formula -> formula
  | formula_not : formula -> formula
  | formula_true : formula
  | formula_eq : logic_val -> logic_val -> formula

(** *** Grammar of logical values *)
(** Note that the logic is syntactically separated from terms. We then define an operation
    that lifts values to introduce them into the logic. There is a corresponding logical value
    for every value in the language. The translation is straightforward except for lambdas,
    which need to be treated with care. As a simplification we treat lambdas as atomic and
    introduce them into the logic with the constructor [logical_abs_var]. *)

with logic_val : Set :=
  | logical_nat : nat -> logic_val
  | logical_true : logic_val
  | logical_false : logic_val
  | logical_bvar : nat -> logic_val
  | logical_fvar : var -> logic_val
  | logical_abs_var : var -> logic_val.

Implicit Types v u : logic_val.
Implicit Types p q : formula.
Implicit Types T S U : typ.

(** We don't need to make a mutually recursive definition, but we do it for convenience. In
    order to prove propositions about types we also need to prove similar propositions
    about formulas and logical values. If we define them mutually recursive we could make a
    combined mutual recursive principle and make proofs about the three at the same time.
    For consistency we follow the same approach for every definition involving types,
    formulas and logical values. *)

(* Notation for logical values *)
Bind Scope logical_scope with formula.
Delimit Scope logical_scope with logic.

(* Notation for formulas *)
Bind Scope logic_val_scope with logic_val.
Delimit Scope logic_val_scope with logic_val.
Notation " v1 = v2 " := (formula_eq v1 v2) : logical_scope.
Notation " v1 /\ v2 " := (formula_and v1 v2) : logical_scope.
Notation " v1 \/ v2 " := (formula_or v1 v2) : logical_scope.
Notation "~ v" := (formula_not v) : logical_scope.
(* Notation " v1 ==> v2 " := (formula_implies v1 v2) *)
(*                             (at level 90, right associativity): logical_scope. *)

(* Notation for types *)
Bind Scope typ_scope with typ.
Delimit Scope typ_scope with typ.
Notation "{ 'v' : B | p }" := (typ_refinement B p) (at level 0, B at level 0) : typ_scope.
Notation "T1 --> T2" := (typ_arrow T1 T2) (at level 0, T2 at level 0): typ_scope.



(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Opening *)

Reserved Notation "{ k ~> u } t" (at level 0, k at level 99, t at level 0).
Reserved Notation "t ^^ u" (at level 30).

(* ********************************************************************** *)
(** ** Terms *)
(** Opening replaces a bound variable with a term. We make several simplifying assumptions
    in defining [open_trm_rec]. First, we assume that the argument [s] is locally closed
    (it doesn't contain unbound de Bruijn indices). This assumption simplifies the
    implementation since we do not need to shift indices in [s] when passing under a binder.
    Second, we assume that this function is initially called with index zero and that zero
    is the only unbound index in the term. This eliminates the need to possibly subtract one
    in the case of indices. *)

Fixpoint open_trm_rec (k : nat) (s : trm) (t : trm) : trm :=
  match t with
  | trm_nat n => t
  | trm_true => t
  | trm_false => t
  | trm_if t1 t2 t3 => trm_if ({k ~> s} t1) ({k~>s} t2) ({k ~> s} t3)
  | trm_bvar i => If k = i then s else t
  | trm_fvar x => t
  | trm_abs lbl t1 => trm_abs lbl ({(S k) ~> s} t1)
  | trm_let t1 t2 => trm_let ({k ~> s} t1) ({(S k) ~> s} t2)
  | trm_app t1 t2 => trm_app ({k ~> s} t1) ({k ~> s} t2)
  end

where "{ k ~> s } t" := (open_trm_rec k s t) : trm_scope.

Definition open_trm t s := open_trm_rec 0 s t.

Notation "t ^^ s" := (open_trm t s) : trm_scope.
Notation "t ^ x" := (open_trm t (trm_fvar x)) : trm_scope.
Bind Scope trm_scope with trm.
Delimit Scope trm_scope with trm.

(* ********************************************************************** *)
(** ** Types *)
(** As we have dependent types and bindings for the refinements we need to open types and
    replace bound variables with logical values. In this case we also make the assumption
    that [u] is locally closed and 0 is the only unbound index .*)

Fixpoint open_typ_rec (k : nat) (u : logic_val) (T : typ) : typ :=
  match T with
  | {v :B | p} => typ_refinement B ({(S k) ~> u} p)
  | T1 --> T2 => ({k ~> u} T1) --> ({(S k) ~> u} T2)
  end
where "{ k ~> u } T" := (open_typ_rec k u T) : typ_scope

with open_formula_rec (k : nat) (u : logic_val) (p : formula) : formula :=
  match p with
  | p1 \/ p2 => ({k ~> u} p1) \/ ({k ~> u} p2)
  | p1 /\ p2 => ({k ~> u} p1) /\ ({k ~> u} p2)
  | ~p' => ~({k ~> u} p')
  | formula_true => formula_true
  | v1 = v2 => ({k ~> u} v1) = ({k ~> u} v2)
  end
where "{ k ~> u } p" := (open_formula_rec k u p) : logical_scope

with open_logic_val_rec
    (k : nat) (u : logic_val) (v : logic_val) : logic_val :=
  match v with
  | logical_bvar i => If k = i then u else v
  | _ => v
  end
where "{ k ~> u } v" := (open_logic_val_rec k u v) : logic_val_scope.
                           
Definition open_typ (T : typ) (u : logic_val) := (open_typ_rec 0 u T).
Notation "T ^ x" := (open_typ T (logical_fvar x)) : typ_scope.
Notation "T ^^ u" := (open_typ T u) : typ_scope.

Definition open_formula p u:= open_formula_rec 0 u p.
Notation "p ^ x" := (open_formula p (logical_fvar x)) : logical_scope.
Notation "p ^^ u" := (open_formula p u) : logical_scope.

Definition open_logic_val v u:= open_logic_val_rec 0 u v.
Notation "v ^ x" := (open_logic_val v (logical_fvar x)) : logic_val_scope.
Notation "v ^^ u" := (open_logic_val v u) : logic_val_scope.

(** We need to lift each term value to a logical value. We assume that types are always
    opened with term values *)
Definition lift_value (u : trm) := 
  match u with
    | trm_nat n => logical_nat n
    | trm_true => logical_true
    | trm_false => logical_false
    | trm_fvar x => logical_fvar x
    | trm_abs lbl _ => logical_abs_var lbl
    | _ => logical_true
  end. 
Notation "! u" := (lift_value u) (at level 61, right associativity).

(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Local Closure *)

(** ** Terms *)

(** Recall that [trm] admits terms that contain unbound indices. We say that a term is locally
    closed, when no indices appearing in it are unbound. The proposition [term e] holds when
    an expression [e] is locally closed.

    Note the use of cofinite quantification in the [term_abs] and [term_let] case. The
    hypotheses in these cases say that the rules hold for all variables except for those in
    a finite set.
*)

Inductive term : trm -> Prop :=
  | term_nat : forall n,
     term (trm_nat n)

  | term_true :
      term trm_true

  | term_false :
     term trm_false

  | term_if : forall t1 t2 t3, 
     term t1 ->
     term t2 ->
     term t3 -> 
     term (trm_if t1 t2 t3)

  | term_fvar : forall x,
     term (trm_fvar x)

  | term_abs : forall L lbl t,
     (forall x, x \notin L -> term (t ^ x)) ->
     term (trm_abs lbl t)

  | term_let : forall L t1 t2,
     term t1 ->
     (forall x, x \notin L -> term (t2 ^ x)) ->
     term (trm_let t1 t2)

  | term_app : forall t1 t2,
     term t1 ->
     term t2 ->
     term (trm_app t1 t2).
Hint Constructors term.

(** ** Types *)

(** We have the same problem of unbound indices for [typ]. The proposition [type T] holds
    when [T] is locally closed *)

Inductive type : typ -> Prop :=
  | type_refinement : forall L B p,
      (forall x, x \notin L -> 
        closed_formula (p ^ x)) ->
      type {v: B | p}

  | type_arrow : forall L T1 T2,
      type T1 ->
      (forall x, x \notin L ->
        type (T2 ^ x)) ->
      type (T1 --> T2)
           
with closed_formula : formula -> Prop :=
  | closed_formula_or : forall p1 p2,
      closed_formula p1 ->
      closed_formula p2 ->
      closed_formula (p1 \/ p2)

  | closed_formula_and : forall p1 p2,
      closed_formula p1 ->
      closed_formula p2 ->
      closed_formula (p1 /\ p2)

  | closed_formula_not : forall p,
      closed_formula p ->
      closed_formula (~p)

  | closed_formula_true : 
      closed_formula formula_true

  | closed_formula_eq : forall v1 v2,
      closed_logic_val v1 ->
      closed_logic_val v2 ->
      closed_formula (v1 = v2)

with closed_logic_val : logic_val -> Prop :=
  | closed_logical_nat : forall n,
      closed_logic_val (logical_nat n)

  | closed_logical_true: 
      closed_logic_val logical_true

  | closed_logical_false : 
      closed_logic_val logical_false

  | closed_logical_fvar : forall x,
      closed_logic_val (logical_fvar x)

  | closed_logical_fun_var : forall lbl,
      closed_logic_val (logical_abs_var lbl).

Hint Constructors closed_logic_val closed_formula.

(** * Typing *)

(* ********************************************************************** *)
(** ** Values *) 

(** The proposition [value e] holds when an expression [e] is a value. Note that the
    hypothesis in the lambda case ensures that this proposition is only defined for locally
    closed terms *)
Inductive value : trm -> Prop :=
  | value_fvar : forall x,
      value (trm_fvar x)

  | value_nat : forall n,
      value (trm_nat n)

  | value_true :
      value trm_true

  | value_false :
      value trm_false

  | value_abs : forall lbl t,
      term (trm_abs lbl t) ->
      value (trm_abs lbl t).
Hint Constructors value.

(** As we have have dependent functions we must introduce terms into types in the application
    rule of the typing judgment. One restriction is that we only allow values to appear as
    arguments of an application so we don't introduce arbitrary expressions into types. We
    must also be careful in the way we introduce lambdas an treat them independently.
    The proposition [atom e] holds for values that are not lambdas *)
Inductive atom : trm -> Prop :=
  | atom_fvar : forall x,
      atom (trm_fvar x)

  | atom_nat : forall n,
      atom (trm_nat n)

  | atom_true :
      atom trm_true

  | atom_false :
      atom trm_false.
Hint Constructors atom.


(** ** Free variables *)

(** The function [trm_fv], defined below, calculates the set of free variables in an
    expression. Because we are using locally nameless representation, where bound variables
    are represented as indices, any name we see is a free variable of a term.
    In particular, this makes the [trm_abs] case simple. *)

Fixpoint trm_fv (t : trm) {struct t} : vars :=
  match t with
  | trm_nat n => \{}
  | trm_true => \{}
  | trm_false => \{}
  | trm_if t1 t2 t3 => (trm_fv t1) \u (trm_fv t2) \u (trm_fv t3)
  | trm_bvar i => \{}
  | trm_fvar x => \{x}
  | trm_abs lbl t1 => trm_fv t1
  | trm_let t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_app t1 t2 => (trm_fv t1) \u (trm_fv t2)
  end.

(** We also define the function [typ_fv] to compute the set of free variables in a type *)

Fixpoint typ_fv (T : typ) : vars :=
  match T with
  | {v : B | p} => formula_fv p
  | T1 --> T2 => typ_fv T1 \u typ_fv T2
  end%typ

with formula_fv (p : formula) : vars :=
  match p with
  | p1 \/ p2 => formula_fv p1 \u formula_fv p2
  | p1 /\ p2 => formula_fv p1 \u formula_fv p2
  | ~p' => formula_fv p'
  | formula_true => \{}
  | v1 = v2 => (logic_val_fv v1) \u (logic_val_fv v2)
  end%logic 

with logic_val_fv (v : logic_val) : vars :=
  match v with
  | logical_fvar x => \{x}
  | _ => \{}
  end.

(** ** Environements *)

Definition ctx := env typ formula.
Bind Scope env_scope with ctx.
Arguments push_binding typ%type formula%type E%env x T%typ.
Arguments push_formula typ%type formula%type E%env p%logic.


(** ** Substitution *)

(** Substitution replaces a free variable with a term. We don't need substitution to define
    the semantic of the language, because the notion of opening a type is sufficient and we
    use substitution only to make some proofs. We introduce the definition here because we
    need it to state some axioms imposed to the logic. *)

(** The definition below is simple for
    two reasons:
      - Because bound variables are represented using indices, there
        is no need to worry about variable capture.
      - We assume that the term being substituted in is locally
        closed. Thus, there is no need to shift indices when
        passing under a binder.
*)
Reserved Notation "[ x ~> u ] t" (at level 0, x at level 99, t at level 0).

Fixpoint trm_subst (x : var) (s : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_nat n => trm_nat n
  | trm_true => trm_true
  | trm_false => trm_false
  | trm_if t1 t2 t3 => trm_if ([x ~> s] t1) ([x~>s] t2) ([x ~> s] t3)
  | trm_bvar i => trm_bvar i
  | trm_fvar x' => If x' = x then s else (trm_fvar x')
  | trm_abs lbl t1 => trm_abs lbl ([x ~> s] t1)
  | trm_let t1 t2 => trm_let ([x ~> s] t1) ([x ~> s] t2)
  | trm_app t1 t2 => trm_app ([x ~> s] t1) ([x ~> s] t2)
  end
where "[ x ~> s ] t" := (trm_subst x s t) : trm_scope.

(** We also define substitution of free variables by logical values *)
Fixpoint typ_subst (x : var) (v : logic_val) (T : typ) : typ:=
  match T with
  | {v : B | p} => {v : B | [x ~> v] p}%logic
  | T1 --> T2 => ([x ~> v] T1) --> ([x ~> v] T2)
  end
where "[ x ~> v ] T" := (typ_subst x v T) : typ_scope
  
with formula_subst (x : var) (v : logic_val) (p : formula) : formula :=
  match p with
  | p1 \/ p2 => ([x ~> v] p1) \/ ([x ~> v] p2)
  | p1 /\ p2 => ([x ~> v] p1) /\ ([x ~> v] p2)
  | ~p' => ~([x ~> v] p')
  | formula_true => formula_true
  | v1 = v2 => ([x ~> v] v1 = [x ~> v] v2)%logic_val
  end
where "[ x ~> v ] p" := (formula_subst x v p) : logical_scope

with logic_val_subst
         (x : var) (v : logic_val) (u : logic_val) :=
  match u with
  | logical_fvar x' => If x' = x then v else logical_fvar x'
  | _ => u
  end
where "[ x ~> v ] u" := (logic_val_subst x v u) : logic_val_scope.

(** We also extend the definition to type environements *)
Fixpoint env_subst (x : var) (v : logic_val) (E : ctx) : ctx :=
  match E with
  | empty_env => empty_env
  | E' « y : T => ([x ~> v] E')%env « y : ([x ~> v] T)%typ
  | E' « p => ([x ~> v] E')%env « ([x ~> v] p)%logic
  end
where "[ x ~> v ] E" := (env_subst x v E) : env_scope.

(** ** Well-formedness *)

(** A type environment is well-formed if all variables are defined before use and no duplications
    exist *)
Reserved Notation "  |~ T" (at level 69, T at level 0). 
Inductive env_wf : ctx -> Prop :=
| empty_env_wf : env_wf empty_env
| binding_env_wf : forall E x T,
    |~ E ->
    x \notin dom E ->
    typ_fv T \c dom E ->
    type T ->
    env_wf (E« x : T)
| formula_env_wf : forall E p,
    |~ E ->
    formula_fv p \c dom E ->
    closed_formula p ->
    env_wf (E«p)
where "|~ E" := (env_wf E).
Hint Constructors env_wf.

(** A type [T] is well-formed in an environment [E] ([E |~ T]) if all its free variables are
    defined in [E] and [E] itself is well-formed *)
Definition type_wf E T := type T /\ env_wf E /\ (typ_fv T \c dom E).
Notation "E |~ T" := (type_wf E T) (at level 69, T at level 0).

(** ** Subtyping *)

(* Fixpoint Embed (E : env) : formula := *)
(*   match E with *)
(*   | empty_env => formula_true *)
(*   | E'« x:{v: B | p} => Embed E' /\ (p ^ x) *)
(*   | E'« x:_ => Embed E' *)
(*   | E'« p => Embed E' /\ p *)
(*   end%logic. *)

Fixpoint extract (E : ctx) : fset formula :=
  match E with
  | empty_env => \{}
  | E'« x:{v: B | p}%typ => extract E' \u \{(p ^ x)}%logic
  | E'« x:_ => extract E'
  | E'« p => extract E' \u \{p}
  end.

(** The definition of subtyping appeals to the notion of logical consequence or entailment in
    the logic. We assume a judgment [entails E p] which means that the environment [E]
    entails the formula [p] or more precisely that the set of formulas extracted from the
    environment [E] entails the formula [p]. In the context of refinement types we assume
    that this judgment is decidable and typically associated with a call to an SMT solver.

    Other definitions appeal to the notion of validity which is in most senses equivalent
    to the notion of entailment. However, using entailment to define subtyping allows us to
    state the axioms required for the logic in a clean way. We define the notion of validity
    using entailment. *)
    
Parameter entails : forall (E : fset formula) (p : formula), Prop.
Notation "E |= p" := (entails E p) (at level 69, p at level 0).
Notation "E ||= p" := (entails (extract E) p) (at level 69, p at level 0).
Definition valid p := \{} |= p.

(** The arrow case of the subtyping relation is the typical syntactic one. The refinement
    case is more interesting and crucial for the expressiveness of the system. Intuitively
    a refinement with a formula [p] is a subtype of a refinement with a formula [q], if [q]
    is a logical consequence of [p] in the environment [E]. *)

Reserved Notation "E |~ T1 <: T2" (at level 69, T1 at level 0, T2 at level 0).
Inductive subtype : env -> typ -> typ -> Prop :=
  | subtype_refinement : forall L E B p q,
      E |~ {v: B | p} ->
      E |~ {v: B | q} ->
      (forall x, x \notin L ->
        extract (E « (p^x)%logic) |= (q ^ x))%logic ->
      E |~ {v : B | p} <: {v : B | q}

  | subtype_arrow : forall L E T11 T12 T21 T22,
      E |~ T21 <: T11 ->
      (forall x, x \notin L ->
          E « x: T21 |~ (T12 ^ x) <: (T22 ^ x) ) ->
      E |~ (T11 --> T12) <: (T21 --> T22)
where "E |~ T1 <: T2" := (subtype E T1 T2).

(** ** Typing judgment *)

(** The typing judgment has some interesting details.
    - The rules for constant and variables bound to refinements give exact types.
    - The rule for the if expression allows path sensitive reasoning, typing the then
      and else expressions in an environment extended with the appropriate assumption.
    - The application rule introduces the argument into the resulting type.
    - In the if and application rule the hypotheses ensure that we only introduce values into
      the logic.
    - Note again the use of cofinite quantification in the rules that must open terms with
      fresh variables.
*)

Reserved Notation "E |~ t : T" (at level 69, t at level 0, T at level 0) .
Inductive typing : env -> trm -> typ -> Prop :=
  | typing_nat : forall E n,
    |~ E ->
    E |~ (trm_nat n) : {v : typ_nat | (logical_bvar 0) = logical_nat n}%logic

  | typing_true : forall E,
      |~ E ->
      E |~ trm_true : {v : typ_bool | (logical_bvar 0) = logical_true}%logic

  | typing_false : forall E,
      |~ E ->
      E |~ trm_false : {v : typ_bool | (logical_bvar 0) = logical_false}%logic

  | typing_var_refinement : forall p E x B,
      |~ E ->
      binds x {v: B | p} E ->
      E |~ (trm_fvar x) : {v : B | (logical_bvar 0) = (logical_fvar x)}%logic

  | typing_var_arrow : forall E x T1 T2,
      |~ E ->
      binds x (T1 --> T2) E -> 
      E |~ (T1 --> T2) ->
      E |~ (trm_fvar x) : (T1 --> T2)

  | typing_abs : forall L E T1 T2 lbl t,
      E |~ T1 ->
      (forall x, x \notin L ->
         (E« x:T1) |~ (t ^ x) : (T2^x)) ->
      E |~ (trm_abs lbl t) : (T1 --> T2)

  | typing_if : forall E p b t1 t2 T,
      value b ->
      E |~ b : {v : typ_bool | p} ->
      E « (!b = logical_true) |~ t1 : T ->
      E « (!b = logical_false) |~ t2 : T ->
      E |~ (trm_if b t1 t2) : T

  | typing_app : forall E T11 T12 t1 t2,
      value t1 ->
      value t2 ->
      E |~ t1 : (T11 --> T12) ->
      E |~ t2 : T11 ->
      E |~ (trm_app t1 t2) : (T12 ^^ (!t2))

  | typing_let : forall L E t1 t2 T1 T2,
      E |~ t1 : T1 ->
      (forall x, x \notin L -> 
        (E « x:T1) |~ (t2 ^ x) : T2) ->
      E |~ T2 ->
      E |~ (trm_let t1 t2) : T2

  | typing_sub : forall E t T T',
      E |~ t : T ->
      E |~ T <: T' ->
      E |~ t : T'

where "E |~ t : T" := (typing E t T).
Hint Constructors typing.

(** * Axioms about the logic *)

(** In order to prove properties about subtyping a corresponding property must hold for the
    logic. Here we state all the axioms that we require for the language to be sound. The
    statements are defined so they match the statements of the properties about subtyping. *)

Definition subst_set (x : var) (v : logic_val) (E : fset formula) (F: fset formula) : 
  Prop := (forall p, p \in E -> ([x ~> v] p)%logic \in F) /\
       (forall q, q \in F -> exists p, p \in E /\ ([x ~> v] p)%logic = q).

Axiom valid_eq : forall {v}, valid (v = v).
Axiom entails_assumption : forall E p, E \u \{p} |= p.
Axiom entails_monotone : forall {E p} F,
    E |= p ->
    E \u F |= p.
Axiom entails_cut : forall {E} p q,
    E |= p ->
    E \u \{p} |= q -> E |= q.
Axiom entails_subst : forall {E q} x v F,
    E |= q ->
    subst_set x v E F ->
    F |= [x ~> v] q.

(* ********************************************************************** *)
(** * Semantics *)

(** We now define the semantics of our call-by-value lambda calculus. 
    We define values and the small-step reduction relation. Note the hypotheses 
    which ensure that relations hold only for locally closed terms. *)

Reserved Notation "t ---> t'" (at level 68).

Inductive red : trm -> trm -> Prop :=
  | red_beta : forall lbl t1 t2 ,
      term (trm_abs lbl t1) ->
      value t2 ->
      (trm_app (trm_abs lbl t1) t2) ---> (t1 ^^ t2)

  | red_let : forall t1  t2,
      value t1 ->
      term (trm_let t1 t2) ->
      (trm_let t1 t2) ---> (t2 ^^ t1)

  | red_if_true : forall t1 t2,
      term t1 ->
      term t2 ->
      (trm_if trm_true t1 t2) ---> t1

  | red_if_false : forall t1 t2,
      term t1 ->
      term t2 ->
      (trm_if trm_false t1 t2) ---> t2

  | red_let_compat : forall t1 t1' t2,
      term (trm_let t1 t2) ->
      t1 ---> t1' ->
      (trm_let t1 t2) ---> (trm_let t1' t2)

where "t ---> t'" := (red t t').

(** * Goals *)

Definition preservation := forall t s T,
    empty_env |~ t : T ->
    t ---> s ->
    empty_env |~ s : T.

Definition progress := forall t T,
    empty_env |~ t : T ->
    (value t \/ exists s, t ---> s).

Definition refinement_soundness := forall t B p E,
    value t ->
    E |~ t : { v : B | p} ->
    E ||= (p ^^ (! t)).
