(* SUBSET OF LIBTACTICS that I would want to have counterpart for in Lean *)




(* ********************************************************************** *)
(** * Tools for Programming with Ltac *)

(* ---------------------------------------------------------------------- *)
(** ** Identity Continuation *)

Ltac idcont tt :=
  idtac.

(* ---------------------------------------------------------------------- *)
(** ** Untyped Arguments for Tactics *)

(** Any Coq value can be boxed into the type [Boxer]. This is
    useful to use Coq computations for implementing tactics. *)

Inductive Boxer : Type :=
  | boxer : forall (A:Type), A -> Boxer.


(* ---------------------------------------------------------------------- *)
(** ** Optional Arguments for Tactics  *)

(** [ltac_no_arg] is a constant that can be used to simulate
    optional arguments in tactic definitions.
    Use [mytactic ltac_no_arg] on the tactic invokation,
    and use [match arg with ltac_no_arg => ..] or
    [match type of arg with ltac_No_arg  => ..] to
    test whether an argument was provided. *)

Inductive ltac_No_arg : Set :=
  | ltac_no_arg : ltac_No_arg.


(* ---------------------------------------------------------------------- *)
(** ** Wildcard Arguments for Tactics  *)

(** [ltac_wild] is a constant that can be used to simulate
    wildcard arguments in tactic definitions. Notation is [__]. *)

Inductive ltac_Wild : Set :=
  | ltac_wild : ltac_Wild.

Notation "'__'" := ltac_wild : ltac_scope.

(** [ltac_wilds] is another constant that is typically used to
    simulate a sequence of [N] wildcards, with [N] chosen
    appropriately depending on the context. Notation is [___]. *)

Inductive ltac_Wilds : Set :=
  | ltac_wilds : ltac_Wilds.

Notation "'___'" := ltac_wilds : ltac_scope.

Open Scope ltac_scope.


(* ---------------------------------------------------------------------- *)
(** ** Position Markers *)

(** [ltac_Mark] and [ltac_mark] are dummy definitions used as sentinel
    by tactics, to mark a certain position in the context or in the goal. *)

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.

(** [gen_until_mark] repeats [generalize] on hypotheses from the
    context, starting from the bottom and stopping as soon as reaching
    an hypothesis of type [Mark]. If fails if [Mark] does not
    appear in the context. *)

Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end.

(** [gen_until_mark_with_processing F] is similar to [gen_until_mark]
    except that it calls [F] on each hypothesis immediately before
    generalizing it. This is useful for processing the hypotheses. *)

Ltac gen_until_mark_with_processing cont :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => cont H; generalize H; clear H;
         gen_until_mark_with_processing cont
  end end.

(** [intro_until_mark] repeats [intro] until reaching an hypothesis of
    type [Mark]. It throws away the hypothesis [Mark].
    It fails if [Mark] does not appear as an hypothesis in the
    goal. *)

Ltac intro_until_mark :=
  match goal with
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; intro_until_mark
  end.


(* ---------------------------------------------------------------------- *)
(** ** List of Arguments for Tactics  *)

(** A datatype of type [list Boxer] is used to manipulate list of
    Coq values in ltac. Notation is [>> v1 v2 ... vN] for building
    a list containing the values [v1] through [vN]. *)
(* Note: could attempt the use of a recursive notation *)

Notation "'>>'" :=
  (@nil Boxer)
  (at level 0)
  : ltac_scope.
Notation "'>>' v1" :=
  ((boxer v1)::nil)
  (at level 0, v1 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2" :=
  ((boxer v1)::(boxer v2)::nil)
  (at level 0, v1 at level 0, v2 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::(boxer v13)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0, v13 at level 0)
  : ltac_scope.

(** The tactic [list_boxer_of] inputs a term [E] and returns a term
    of type "list boxer", according to the following rules:
    - if [E] is already of type "list Boxer", then it returns [E];
    - otherwise, it returns the list [(boxer E)::nil]. *)
Ltac list_boxer_of E :=
  match type of E with
  | List.list Boxer => constr:(E)
  | _ => constr:((boxer E)::nil)
  end.

(* ---------------------------------------------------------------------- *)
(** ** Databases of Lemmas  *)

(** Use the hint facility to implement a database mapping
    terms to terms. To declare a new database, use a definition:
    [Definition mydatabase := True.]

    Then, to map [mykey] to [myvalue], write the hint:
    [Hint Extern 1 (Register mydatabase mykey) => Provide myvalue.]

    Finally, to query the value associated with a key, run the
    tactic [ltac_database_get mydatabase mykey]. This will leave
    at the head of the goal the term [myvalue]. It can then be
    named and exploited using [intro]. *)

Inductive Ltac_database_token : Prop := ltac_database_token.

Definition ltac_database (D:Boxer) (T:Boxer) (A:Boxer) := Ltac_database_token.

Notation "'Register' D T" := (ltac_database (boxer D) (boxer T) _)
  (at level 69, D at level 0, T at level 0).

Lemma ltac_database_provide : forall (A:Boxer) (D:Boxer) (T:Boxer),
  ltac_database D T A.
Proof using. split. Qed.

Ltac Provide T := apply (@ltac_database_provide (boxer T)).

Ltac ltac_database_get D T :=
  let A := fresh "TEMP" in evar (A:Boxer);
  let H := fresh "TEMP" in
  assert (H : ltac_database (boxer D) (boxer T) A);
  [ subst A; auto
  | subst A; match type of H with ltac_database _ _ (boxer ?L) =>
               generalize L end; clear H ].

(* Note for a possible alternative implementation of the ltac_database_token:
   Inductive Ltac_database : Type :=
     | ltac_database : forall A, A -> Ltac_database.
   Implicit Arguments ltac_database [A].
*)

(* ---------------------------------------------------------------------- *)
(** ** On-the-Fly Removal of Hypotheses *)

(** In a list of arguments [>> H1 H2 .. HN] passed to a tactic
    such as [lets] or [applys] or [forwards] or [specializes],
    the term [rm], an identity function, can be placed in front
    of the name of an hypothesis to be deleted. *)

Definition rm (A:Type) (X:A) := X.

(** [rm_term E] removes one hypothesis that admits the same
    type as [E]. *)

Ltac rm_term E :=
  let T := type of E in
  match goal with H: T |- _ => try clear H end.

(** [rm_inside E] calls [rm_term Ei] for any subterm
    of the form [rm Ei] found in E *)

Ltac rm_inside E :=
  let go E := rm_inside E in
  match E with
  | rm ?X => rm_term X
  | ?X1 ?X2 =>
     go X1; go X2
  | ?X1 ?X2 ?X3 =>
     go X1; go X2; go X3
  | ?X1 ?X2 ?X3 ?X4 =>
     go X1; go X2; go X3; go X4
  | ?X1 ?X2 ?X3 ?X4 ?X5 =>
     go X1; go X2; go X3; go X4; go X5
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 =>
     go X1; go X2; go X3; go X4; go X5; go X6
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 ?X10 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9; go X10
  | _ => idtac
  end.

(** For faster performance, one may deactivate [rm_inside] by
    replacing the body of this definition with [idtac]. *)

Ltac fast_rm_inside E :=
  rm_inside E.


(* ---------------------------------------------------------------------- *)
(** ** Numbers as Arguments *)

(** When tactic takes a natural number as argument, it may be
    parsed either as a natural number or as a relative number.
    In order for tactics to convert their arguments into natural numbers,
    we provide a conversion tactic.

    Note: the tactic [number_to_nat] is extended in [LibInt] to
    take into account the [Z] type. *)

Require Coq.Numbers.BinNums Coq.ZArith.BinInt.

Definition ltac_int_to_nat (x:BinInt.Z) : nat :=
  match x with
  | BinInt.Z0 => 0%nat
  | BinInt.Zpos p => BinPos.nat_of_P p
  | BinInt.Zneg p => 0%nat
  end.

Ltac number_to_nat N :=
  match type of N with
  | nat => constr:(N)
  | BinInt.Z => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
  end.


(* ---------------------------------------------------------------------- *)
(** ** Testing Tactics *)

(** [show tac] executes a tactic [tac] that produces a result,
    and then display its result. *)

Tactic Notation "show" tactic(tac) :=
  let R := tac in pose R.

(** [dup N] produces [N] copies of the current goal. It is useful
    for building examples on which to illustrate behaviour of tactics.
    [dup] is short for [dup 2]. *)

Lemma dup_lemma : forall P, P -> P -> P.
Proof using. auto. Qed.

Ltac dup_tactic N :=
  match number_to_nat N with
  | 0 => idtac
  | S 0 => idtac
  | S ?N' => apply dup_lemma; [ | dup_tactic N' ]
  end.

Tactic Notation "dup" constr(N) :=
  dup_tactic N.
Tactic Notation "dup" :=
  dup 2.


(* ---------------------------------------------------------------------- *)
(** ** Testing evars and non-evars *)

(** [is_not_evar E] succeeds only if [E] is not an evar;
    it fails otherwise. It thus implements the negation of [is_evar] *)

Ltac is_not_evar E :=
  first [ is_evar E; fail 1
        | idtac ].

(** [is_evar_as_bool E] evaluates to [true] if [E] is an evar
    and to [false] otherwise. *)

Ltac is_evar_as_bool E :=
  constr:(ltac:(first
    [ is_evar E; exact true
    | exact false ])).

(** [has_no_evar E] succeeds if [E] contains no evars. *)

Ltac has_no_evar E :=
  first [ has_evar E; fail 1 | idtac ].


(* ---------------------------------------------------------------------- *)
(** ** Tagging of Hypotheses *)

(** [get_last_hyp tt] is a function that returns the last hypothesis
    at the bottom of the context. It is useful to obtain the default
    name associated with the hypothesis, e.g.
    [intro; let H := get_last_hyp tt in let H' := fresh "P" H in ...] *)

Ltac get_last_hyp tt :=
  match goal with H: _ |- _ => constr:(H) end.


(* ---------------------------------------------------------------------- *)
(** ** More Tagging of Hypotheses *)

(** [ltac_tag_subst] is a specific marker for hypotheses
    which is used to tag hypotheses that are equalities to
    be substituted. *)

Definition ltac_tag_subst (A:Type) (x:A) := x.

(** [ltac_to_generalize] is a specific marker for hypotheses
    to be generalized. *)

Definition ltac_to_generalize (A:Type) (x:A) := x.

Ltac gen_to_generalize :=
  repeat match goal with
    H: ltac_to_generalize _ |- _ => generalize H; clear H end.

Ltac mark_to_generalize H :=
  let T := type of H in
  change T with (ltac_to_generalize T) in H.


(* ---------------------------------------------------------------------- *)
(** ** Deconstructing Terms *)

(** [get_head E] is a tactic that returns the head constant of the
    term [E], ie, when applied to a term of the form [P x1 ... xN]
    it returns [P]. If [E] is not an application, it returns [E].
    Warning: the tactic seems to loop in some cases when the goal is
    a product and one uses the result of this function. *)

Ltac get_head E :=
  match E with
  | ?E' ?x => get_head E'
  | _ => constr:(E)
  end.

(** [get_fun_arg E] is a tactic that decomposes an application
  term [E], ie, when applied to a term of the form [X1 ... XN]
  it returns a pair made of [X1 .. X(N-1)] and [XN]. *)

Ltac get_fun_arg E :=
  match E with
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X => constr:((X1 X2 X3 X4 X5 X6 X7,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X => constr:((X1 X2 X3 X4 X5 X6,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X => constr:((X1 X2 X3 X4 X5,X))
  | ?X1 ?X2 ?X3 ?X4 ?X => constr:((X1 X2 X3 X4,X))
  | ?X1 ?X2 ?X3 ?X => constr:((X1 X2 X3,X))
  | ?X1 ?X2 ?X => constr:((X1 X2,X))
  | ?X1 ?X => constr:((X1,X))
  end.



(* ********************************************************************** *)
(** * Common Tactics for Simplifying Goals Like [intuition] *)

Ltac jauto_set_hyps :=
  repeat match goal with H: ?T |- _ =>
    match T with
    | _ /\ _ => destruct H
    | iff _ _ => destruct H
    | exists a, _ => destruct H
    | _ => generalize H; clear H
    end
  end.

Ltac jauto_set_goal :=
  repeat match goal with
  | |- exists a, _ => esplit
  | |- _ /\ _ => split
  | |- iff _ _ => split
  end.

Ltac jauto_set :=
  intros; jauto_set_hyps;
  intros; jauto_set_goal;
  unfold not in *.



(* ********************************************************************** *)
(** * Backward and Forward Chaining *)


(* ---------------------------------------------------------------------- *)
(** ** Instantiation and Forward-Chaining *)

(** [lets_base H E] adds an hypothesis [H : T] to the context, where [T] is
    the type of term [E]. If [H] is an introduction pattern, it will
    destruct [H] according to the pattern. *)

Ltac lets_base I E := generalize E; intros I.

(** The instantiation tactics are used to instantiate a lemma [E]
    (whose type is a product) on some arguments. The type of [E] is
    made of implications and universal quantifications, e.g.
    [forall x, P x -> forall y z, Q x y z -> R z].

    The first possibility is to provide arguments in order: first [x],
    then a proof of [P x], then [y] etc... In this mode, called "Args",
    all the arguments are to be provided. If a wildcard is provided
    (written [__]), then an existential variable will be introduced in
    place of the argument.

    It is very convenient to give some arguments the lemma should be
    instantiated on, and let the tactic find out automatically where
    underscores should be insterted. Underscore arguments [__] are
    interpret as follows: an underscore means that we want to skip the
    argument that has the same type as the next real argument provided
    (real means not an underscore). If there is no real argument after
    underscore, then the underscore is used for the first possible argument.

    The general syntax is [tactic (>> E1 .. EN)] where [tactic] is
    the name of the tactic (possibly with some arguments) and [Ei]
    are the arguments. Moreover, some tactics accept the syntax
    [tactic E1 .. EN] as short for [tactic (>> E1 .. EN)] for
    values of [N] up to 5.

    Finally, if the argument [EN] given is a triple-underscore [___],
    then it is equivalent to providing a list of wildcards, with
    the appropriate number of wildcards. This means that all
    the remaining arguments of the lemma will be instantiated.
    Definitions in the conclusion are not unfolded in this case. *)

(* Underlying implementation *)

Ltac app_assert t P cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ | cont(t H); clear H ].

Ltac app_evar t A cont :=
  let x := fresh "TEMP" in
  evar (x:A);
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.

Ltac app_arg t P v cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ apply v | cont(t H); try clear H ].

Ltac build_app_alls t final :=
  let rec go t :=
    match type of t with
    | ?P -> ?Q => app_assert t P go
    | forall _:?A, _ => app_evar t A go
    | _ => final t
    end in
  go t.

Ltac boxerlist_next_type vs :=
  match vs with
  | nil => constr:(ltac_wild)
  | (boxer ltac_wild)::?vs' => boxerlist_next_type vs'
  | (boxer ltac_wilds)::_ => constr:(ltac_wild)
  | (@boxer ?T _)::_ => constr:(T)
  end.

(* Note: refuse to instantiate a dependent hypothesis with a proposition;
    refuse to instantiate an argument of type Type with one that
    does not have the type Type.
*)

Ltac build_app_hnts t vs final :=
  let rec go t vs :=
    match vs with
    | nil => first [ final t | fail 1 ]
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    | (boxer ?v)::?vs' =>
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      let T := type of t in
      let T := eval hnf in T in
      match v with
      | ltac_wild =>
         first [ let U := boxerlist_next_type vs' in
           match U with
           | ltac_wild =>
             match T with
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_evar t A cont' | fail 3 ]
             end
           | _ =>
             match T with  (* should test T for unifiability *)
             | U -> ?Q => first [ app_assert t U cont' | fail 3 ]
             | forall _:U, _ => first [ app_evar t U cont' | fail 3 ]
             | ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
             | forall _:?A, _ => first [ app_evar t A cont | fail 3 ]
             end
           end
         | fail 2 ]
      | _ =>
          match T with
          | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           | forall _:Type, _ =>
              match type of v with
              | Type => first [ cont' (t v)
                              | app_evar t Type cont
                              | fail 3 ]
              | _ => first [ app_evar t Type cont
                           | fail 3 ]
              end
          | forall _:?A, _ =>
             let V := type of v in
             match type of V with
             | Prop =>  first [ app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v)
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.


(** newer version : support for typeclasses *)

Ltac app_typeclass t cont :=
  let t' := constr:(t _) in
  cont t'.

Ltac build_app_alls t final ::=
  let rec go t :=
    match type of t with
    | ?P -> ?Q => app_assert t P go
    | forall _:?A, _ =>
        first [ app_evar t A go
              | app_typeclass t go
              | fail 3 ]
    | _ => final t
    end in
  go t.

Ltac build_app_hnts t vs final ::=
  let rec go t vs :=
    match vs with
    | nil => first [ final t | fail 1 ]
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    | (boxer ?v)::?vs' =>
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      let T := type of t in
      let T := eval hnf in T in
      match v with
      | ltac_wild =>
         first [ let U := boxerlist_next_type vs' in
           match U with
           | ltac_wild =>
             match T with
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_typeclass t cont'
                                       | app_evar t A cont'
                                       | fail 3 ]
             end
           | _ =>
             match T with  (* should test T for unifiability *)
             | U -> ?Q => first [ app_assert t U cont' | fail 3 ]
             | forall _:U, _ => first
                 [ app_typeclass t cont'
                 | app_evar t U cont'
                 | fail 3 ]
             | ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
             | forall _:?A, _ => first
                 [ app_typeclass t cont
                 | app_evar t A cont
                 | fail 3 ]
             end
           end
         | fail 2 ]
      | _ =>
          match T with
          | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           | forall _:Type, _ =>
              match type of v with
              | Type => first [ cont' (t v)
                              | app_evar t Type cont
                              | fail 3 ]
              | _ => first [ app_evar t Type cont
                           | fail 3 ]
              end
          | forall _:?A, _ =>
             let V := type of v in
             match type of V with
             | Prop => first [ app_typeclass t cont
                              | app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v)
                          | app_typeclass t cont
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.
  (* --Note: use local function for first [...] *)


Ltac build_app args final :=
  first [
    match args with (@boxer ?T ?t)::?vs =>
      let t := constr:(t:T) in
      build_app_hnts t vs final;
      fast_rm_inside args
    end
  | fail 1 "Instantiation fails for:" args].

Ltac unfold_head_until_product T :=
  eval hnf in T.

Ltac args_unfold_head_if_not_product args :=
  match args with (@boxer ?T ?t)::?vs =>
    let T' := unfold_head_until_product T in
    constr:((@boxer T' t)::vs)
  end.

Ltac args_unfold_head_if_not_product_but_params args :=
  match args with
  | (boxer ?t)::(boxer ?v)::?vs =>
     args_unfold_head_if_not_product args
  | _ => constr:(args)
  end.

(** [lets H: (>> E0 E1 .. EN)] will instantiate lemma [E0]
    on the arguments [Ei] (which may be wildcards [__]),
    and name [H] the resulting term. [H] may be an introduction
    pattern, or a sequence of introduction patterns [I1 I2 IN],
    or empty.
    Syntax [lets H: E0 E1 .. EN] is also available. If the last
    argument [EN] is [___] (triple-underscore), then all
    arguments of [H] will be instantiated. *)

Ltac lets_build I Ei :=
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in
(*    let Ei''' := args_unfold_head_if_not_product Ei'' in*)
  build_app args ltac:(fun R => lets_base I R).

Tactic Notation "lets" simple_intropattern(I) ":" constr(E) :=
  lets_build I E.
Tactic Notation "lets" ":" constr(E) :=
  let H := fresh in lets H: E.
Tactic Notation "lets" ":" constr(E0)
 constr(A1) :=
  lets: (>> E0 A1).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) :=
  lets: (>> E0 A1 A2).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets: (>> E0 A1 A2 A3).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets: (>> E0 A1 A2 A3 A4 A5).

(* DEPRECATED syntax [lets I1 I2] *)
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 ":" constr(E) :=
  lets [I1 I2]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) ":" constr(E) :=
  lets [I1 [I2 I3]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
  lets [I1 [I2 [I3 I4]]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 ":" constr(E) :=
  lets [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  lets I: (>> E0 A1).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets I: (>> E0 A1 A2).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets I: (>> E0 A1 A2 A3).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets I: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets I: (>> E0 A1 A2 A3 A4 A5).

Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) :=
  lets [I1 I2]: E0 A1.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets [I1 I2]: E0 A1 A2.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets [I1 I2]: E0 A1 A2 A3.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets [I1 I2]: E0 A1 A2 A3 A4.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets [I1 I2]: E0 A1 A2 A3 A4 A5.


(** [forwards H: (>> E0 E1 .. EN)] is short for
    [forwards H: (>> E0 E1 .. EN ___)].
    The arguments [Ei] can be wildcards [__] (except [E0]).
    [H] may be an introduction pattern, or a sequence of
    introduction pattern, or empty.
    Syntax [forwards H: E0 E1 .. EN] is also available. *)

Ltac forwards_build_app_arg Ei :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  let args := args_unfold_head_if_not_product args in
  args.

Ltac forwards_then Ei cont :=
  let args := forwards_build_app_arg Ei in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args cont.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(Ei) :=
  let args := forwards_build_app_arg Ei in
  lets I: args.

Tactic Notation "forwards" ":" constr(E) :=
  let H := fresh in forwards H: E.
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) :=
  forwards: (>> E0 A1).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: (>> E0 A1 A2).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: (>> E0 A1 A2 A3).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards: (>> E0 A1 A2 A3 A4 A5).

(* --DEPRECATED syntax *)
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 ":" constr(E) :=
  forwards [I1 I2]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) ":" constr(E) :=
  forwards [I1 [I2 I3]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
  forwards [I1 [I2 [I3 I4]]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 ":" constr(E) :=
  forwards [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  forwards I: (>> E0 A1).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: (>> E0 A1 A2).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: (>> E0 A1 A2 A3).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards I: (>> E0 A1 A2 A3 A4 A5).

(** [forwards_nounfold I: E] is like [forwards I: E] but does not
    unfold the head constant of [E] if there is no visible quantification
    or hypothesis in [E]. It is meant to be used mainly by tactics. *)

Tactic Notation "forwards_nounfold" simple_intropattern(I) ":" constr(Ei) :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  build_app args ltac:(fun R => lets_base I R).

(** [forwards_nounfold_then E ltac:(fun K => ..)]
    is like [forwards: E] but it provides the resulting term
    to a continuation, under the name [K]. *)

Ltac forwards_nounfold_then Ei cont :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  build_app args cont.

(** [applys (>> E0 E1 .. EN)] instantiates lemma [E0]
    on the arguments [Ei] (which may be wildcards [__]),
    and apply the resulting term to the current goal,
    using the tactic [applys] defined earlier on.
    [applys E0 E1 E2 .. EN] is also available. *)

Ltac applys_build Ei :=
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args ltac:(fun R =>
   first [ apply R | eapply R ]).

Ltac applys_base E :=
  match type of E with
  | list Boxer => applys_build E
  | _ => first [ eapply E | applys_build E ]
  end; fast_rm_inside E.

Tactic Notation "applys" constr(E) :=
  applys_base E.
Tactic Notation "applys" constr(E0) constr(A1) :=
  applys (>> E0 A1).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) :=
  applys (>> E0 A1 A2).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) :=
  applys (>> E0 A1 A2 A3).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  applys (>> E0 A1 A2 A3 A4).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  applys (>> E0 A1 A2 A3 A4 A5).

(** [fapplys (>> E0 E1 .. EN)] instantiates lemma [E0]
    on the arguments [Ei] and on the argument [___] meaning
    that all evars should be explicitly instantiated,
    and apply the resulting term to the current goal.
    [fapplys E0 E1 E2 .. EN] is also available. *)

Ltac fapplys_build Ei :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args ltac:(fun R => apply R).

Tactic Notation "fapplys" constr(E0) :=
  match type of E0 with
  | list Boxer => fapplys_build E0
  | _ => fapplys_build (>> E0)
  end.
Tactic Notation "fapplys" constr(E0) constr(A1) :=
  fapplys (>> E0 A1).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) :=
  fapplys (>> E0 A1 A2).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) :=
  fapplys (>> E0 A1 A2 A3).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  fapplys (>> E0 A1 A2 A3 A4).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  fapplys (>> E0 A1 A2 A3 A4 A5).

(** [specializes H (>> E1 E2 .. EN)] will instantiate hypothesis [H]
    on the arguments [Ei] (which may be wildcards [__]). If the last
    argument [EN] is [___] (triple-underscore), then all arguments of
    [H] get instantiated. *)

Ltac specializes_build H Ei :=
  let H' := fresh "TEMP" in rename H into H';
  let args := list_boxer_of Ei in
  let args := constr:((boxer H')::args) in
  let args := args_unfold_head_if_not_product args in
  build_app args ltac:(fun R => lets H: R);
  clear H'.

Ltac specializes_base H Ei :=
  specializes_build H Ei; fast_rm_inside Ei.

Tactic Notation "specializes" hyp(H) :=
  specializes_base H (___).
Tactic Notation "specializes" hyp(H) constr(A) :=
  specializes_base H A.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
  specializes H (>> A1 A2).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
  specializes H (>> A1 A2 A3).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
  specializes H (>> A1 A2 A3 A4).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  specializes H (>> A1 A2 A3 A4 A5).

(* ---------------------------------------------------------------------- *)
(** ** Application Modulo Equalities *)

(** The tactic [equates] replaces a goal of the form
    [P x y z] with a goal of the form [P x ?a z] and a
    subgoal [?a = y]. The introduction of the evar [?a] makes
    it possible to apply lemmas that would not apply to the
    original goal, for example a lemma of the form
    [forall n m, P n n m], because [x] and [y] might be equal
    but not convertible.

    Usage is [equates i1 ... ik], where the indices are the
    positions of the arguments to be replaced by evars,
    counting from the right-hand side. If [0] is given as
    argument, then the entire goal is replaced by an evar. *)

Section equatesLemma.
Variables (A0 A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).
Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma equates_0 : forall (P Q:Prop),
  P -> P = Q -> Q.
Proof using. intros. subst. auto. Qed.

Lemma equates_1 :
  forall (P:A0->Prop) x1 y1,
  P y1 -> x1 = y1 -> P x1.
Proof using. intros. subst. auto. Qed.

Lemma equates_2 :
  forall y1 (P:A0->forall(x1:A1),Prop) x1 x2,
  P y1 x2 -> x1 = y1 -> P x1 x2.
Proof using. intros. subst. auto. Qed.

Lemma equates_3 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1),Prop) x1 x2 x3,
  P y1 x2 x3 -> x1 = y1 -> P x1 x2 x3.
Proof using. intros. subst. auto. Qed.

Lemma equates_4 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2),Prop) x1 x2 x3 x4,
  P y1 x2 x3 x4 -> x1 = y1 -> P x1 x2 x3 x4.
Proof using. intros. subst. auto. Qed.

Lemma equates_5 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3),Prop) x1 x2 x3 x4 x5,
  P y1 x2 x3 x4 x5 -> x1 = y1 -> P x1 x2 x3 x4 x5.
Proof using. intros. subst. auto. Qed.

Lemma equates_6 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3)(x5:A5 x4),Prop)
  x1 x2 x3 x4 x5 x6,
  P y1 x2 x3 x4 x5 x6 -> x1 = y1 -> P x1 x2 x3 x4 x5 x6.
Proof using. intros. subst. auto. Qed.

End equatesLemma.

Ltac equates_lemma n :=
  match number_to_nat n with
  | 0 => constr:(equates_0)
  | 1 => constr:(equates_1)
  | 2 => constr:(equates_2)
  | 3 => constr:(equates_3)
  | 4 => constr:(equates_4)
  | 5 => constr:(equates_5)
  | 6 => constr:(equates_6)
  | _ => fail 100 "equates tactic only support up to arity 6"
  end.

Ltac equates_one n :=
  let L := equates_lemma n in
  eapply L.

Ltac equates_several E cont :=
  let all_pos := match type of E with
    | List.list Boxer => constr:(E)
    | _ => constr:((boxer E)::nil)
    end in
  let rec go pos :=
     match pos with
     | nil => cont tt
     | (boxer ?n)::?pos' => equates_one n; [ go pos' | ]
     end in
  go all_pos.

Tactic Notation "equates" constr(E) :=
  equates_several E ltac:(fun _ => idtac).
Tactic Notation "equates" constr(n1) constr(n2) :=
  equates (>> n1 n2).
Tactic Notation "equates" constr(n1) constr(n2) constr(n3) :=
  equates (>> n1 n2 n3).
Tactic Notation "equates" constr(n1) constr(n2) constr(n3) constr(n4) :=
  equates (>> n1 n2 n3 n4).

(** [applys_eq H i1 .. iK] is the same as
    [equates i1 .. iK] followed by [applys H]
    on the first subgoal.

    DEPRECATED: use [applys_eq H] instead. *)

Tactic Notation "applys_eq" constr(H) constr(E) :=
  equates_several E ltac:(fun _ => sapply H).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) :=
  applys_eq H (>> n1 n2).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) constr(n3) :=
  applys_eq H (>> n1 n2 n3).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
  applys_eq H (>> n1 n2 n3 n4).

(** [applys_eq H] helps proving a goal of the form [P x1 .. xN]
    from an hypothesis [H] that concludes [P y1 .. yN], where the
    arguments [xi] and [yi] may or may not be convertible.
    Equalities are produced for all arguments that don't unify.

    The tactic invokes [equates] on all arguments, then calls
    [applys K], and attempts [reflexivity] on the side equalities. *)

Lemma applys_eq_init : forall (P Q:Prop),
  P = Q ->
  Q ->
  P.
Proof using. intros. subst. auto. Qed.

Lemma applys_eq_step_dep : forall B (P Q: (forall A, A->B)) (T:Type),
  P = Q ->
  P T = Q T.
Proof using. intros. subst. auto. Qed.

Lemma applys_eq_step : forall A B (P Q:A->B) x y,
  P = Q ->
  x = y ->
  P x = Q y.
Proof using. intros. subst. auto. Qed.

Ltac applys_eq_loop tt :=
  match goal with
  | |- ?P ?x =>
      first [ eapply applys_eq_step; [ applys_eq_loop tt | ]
            | eapply applys_eq_step_dep; applys_eq_loop tt ]
  | _ => reflexivity
  end.

Ltac applys_eq_core H :=
  eapply applys_eq_init;
  [ applys_eq_loop tt | applys H ];
  try reflexivity.

Tactic Notation "applys_eq" constr(H) :=
  applys_eq_core H.


(* ---------------------------------------------------------------------- *)
(** ** Absurd Goals *)

(** [false_goal] replaces any goal by the goal [False].
    Contrary to the tactic [false] (below), it does not try to do
    anything else *)

Tactic Notation "false_goal" :=
  exfalso.

(** [false_post] is the underlying tactic used to prove goals
    of the form [False]. In the default implementation, it proves
    the goal if the context contains [False] or an hypothesis of the
    form [C x1 .. xN  =  D y1 .. yM], or if the [congruence] tactic
    finds a proof of [x <> x] for some [x]. *)

Ltac false_post :=
  solve [ assumption | discriminate | congruence ].

(** [false] replaces any goal by the goal [False], and calls [false_post] *)

Tactic Notation "false" :=
  false_goal; try false_post.

(** [tryfalse] tries to solve a goal by contradiction, and leaves
    the goal unchanged if it cannot solve it.
    It is equivalent to [try solve \[ false \]]. *)

Tactic Notation "tryfalse" :=
  try solve [ false ].

(** [false E] tries to exploit lemma [E] to prove the goal false.
    [false E1 .. EN] is equivalent to [false (>> E1 .. EN)],
    which tries to apply [applys (>> E1 .. EN)] and if it
    does not work then tries [forwards H: (>> E1 .. EN)]
    followed with [false] *)

Ltac false_then E cont :=
  false_goal; first
  [ applys E
  | forwards_then E ltac:(fun M =>
      pose M; jauto_set_hyps; intros; false) ];
  cont tt.
  (* Note: is [cont] needed? *)

Tactic Notation "false" constr(E) :=
  false_then E ltac:(fun _ => idtac).
Tactic Notation "false" constr(E) constr(E1) :=
  false (>> E E1).
Tactic Notation "false" constr(E) constr(E1) constr(E2) :=
  false (>> E E1 E2).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) :=
  false (>> E E1 E2 E3).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) constr(E4) :=
  false (>> E E1 E2 E3 E4).


(* ********************************************************************** *)
(** * Introduction and Generalization *)

(* ---------------------------------------------------------------------- *)
(** ** Introduction *)

(** [introv] is used to name only non-dependent hypothesis.
 - If [introv] is called on a goal of the form [forall x, H],
   it should introduce all the variables quantified with a
   [forall] at the head of the goal, but it does not introduce
   hypotheses that preceed an arrow constructor, like in [P -> Q].
 - If [introv] is called on a goal that is not of the form
   [forall x, H] nor [P -> Q], the tactic unfolds definitions
   until the goal takes the form [forall x, H] or [P -> Q].
   If unfolding definitions does not produces a goal of this form,
   then the tactic [introv] does nothing at all. *)

(* [introv_rec] introduces all visible variables.
   It does not try to unfold any definition. *)

Ltac introv_rec :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => intro; introv_rec
  | |- _ => idtac
  end.

(* [introv_noarg] forces the goal to be a [forall] or an [->],
   and then calls [introv_rec] to introduces variables
   (possibly none, in which case [introv] is the same as [hnf]).
   If the goal is not a product, then it does not do anything. *)

Ltac introv_noarg :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => introv_rec
  | |- ?G => hnf;
     match goal with
     | |- ?P -> ?Q => idtac
     | |- forall _, _ => introv_rec
     end
  | |- _ => idtac
  end.

  (* simpler yet perhaps less efficient imlementation *)
  Ltac introv_noarg_not_optimized :=
    intro; match goal with H:_|-_ => revert H end; introv_rec.

(* [introv_arg H] introduces one non-dependent hypothesis
   under the name [H], after introducing the variables
   quantified with a [forall] that preceeds this hypothesis.
   This tactic fails if there does not exist a hypothesis
   to be introduced. *)
(* Note: __ in introv means "intros" *)

Ltac introv_arg H :=
  hnf; match goal with
  | |- ?P -> ?Q => intros H
  | |- forall _, _ => intro; introv_arg H
  end.

(* [introv I1 .. IN] iterates [introv Ik] *)

Tactic Notation "introv" :=
  introv_noarg.
Tactic Notation "introv" simple_intropattern(I1) :=
  introv_arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) :=
  introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  introv I1; introv I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  introv I1; introv I2 I3 I4 I5.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  introv I1; introv I2 I3 I4 I5 I6.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  introv I1; introv I2 I3 I4 I5 I6 I7.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9 I10.

(** [intros_all] repeats [intro] as long as possible. Contrary to [intros],
    it unfolds any definition on the way. Remark that it also unfolds the
    definition of negation, so applying [intros_all] to a goal of the form
    [forall x, P x -> ~Q] will introduce [x] and [P x] and [Q], and will
    leave [False] in the goal. *)

Tactic Notation "intros_all" :=
  repeat intro.

(** [intros_hnf] introduces an hypothesis and sets in head normal form *)

Tactic Notation "intro_hnf" :=
  intro; match goal with H: _ |- _ => hnf in H end.


(* ---------------------------------------------------------------------- *)
(** ** Introduction using [=>] and [=>>] *)

(* [=> I1 .. IN] is the same as [intros I1 .. IN] *)

Ltac ltac_intros_post := idtac.

Tactic Notation "=>" :=
  intros.
Tactic Notation "=>" simple_intropattern(I1) :=
  intros I1.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2) :=
  intros I1 I2.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  intros I1 I2 I3.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  intros I1 I2 I3 I4.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  intros I1 I2 I3 I4 I5.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  intros I1 I2 I3 I4 I5 I6.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  intros I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  intros I1 I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

(* [=>>] first introduces all non-dependent variables,
   then behaves as [intros]. It unfolds the head of the goal using [hnf]
   if there are not head visible quantifiers.

   Remark: instances of [Inhab] are treated as non-dependent and
   are introduced automatically. *)

(* NOTE: this tactic is later redefined for supporting Inhab *)
Ltac intro_nondeps_aux_special_intro G :=
  fail.

Ltac intro_nondeps_aux is_already_hnf :=
  match goal with
  | |- (?P -> ?Q) => idtac
  | |- ?G -> _ => intro_nondeps_aux_special_intro G;
                  intro; intro_nondeps_aux true
  | |- (forall _,_) => intros ?; intro_nondeps_aux true
  | |- _ =>
     match is_already_hnf with
     | true => idtac
     | false => hnf; intro_nondeps_aux true
     end
  end.

Ltac intro_nondeps tt := intro_nondeps_aux false.

Tactic Notation "=>>" :=
  intro_nondeps tt.
Tactic Notation "=>>" simple_intropattern(I1) :=
  =>>; intros I1.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2) :=
  =>>; intros I1 I2.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  =>>; intros I1 I2 I3.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  =>>; intros I1 I2 I3 I4.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  =>>; intros I1 I2 I3 I4 I5.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  =>>; intros I1 I2 I3 I4 I5 I6.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.



(* ********************************************************************** *)
(** * Rewriting *)

(** [rewrites E] is similar to [rewrite] except that
    it supports the [rm] directives to clear hypotheses
    on the fly, and that it supports a list of arguments in the form
    [rewrites (>> E1 E2 E3)] to indicate that [forwards] should be
    invoked first before [rewrites] is called. *)

Ltac rewrites_base E cont :=
  match type of E with
  | List.list Boxer => forwards_then E cont
  | _ => cont E; fast_rm_inside E
  end.

Tactic Notation "rewrites" constr(E) :=
  rewrites_base E ltac:(fun M => rewrite M ).
Tactic Notation "rewrites" constr(E) "in" hyp(H) :=
  rewrites_base E ltac:(fun M => rewrite M in H).
Tactic Notation "rewrites" constr(E) "in" "*" :=
  rewrites_base E ltac:(fun M => rewrite M in *).
Tactic Notation "rewrites" "<-" constr(E) :=
  rewrites_base E ltac:(fun M => rewrite <- M ).
Tactic Notation "rewrites" "<-" constr(E) "in" hyp(H) :=
  rewrites_base E ltac:(fun M => rewrite <- M in H).
Tactic Notation "rewrites" "<-" constr(E) "in" "*" :=
  rewrites_base E ltac:(fun M => rewrite <- M in *).

(* ---------------------------------------------------------------------- *)
(** ** Unfolding *)

(** [unfolds] unfolds the head definition in the goal, i.e. if the
    goal has form [P x1 ... xN] then it calls [unfold P].
    If the goal is an equality, it tries to unfold the head constant
    on the left-hand side, and otherwise tries on the right-hand side.
    If the goal is a product, it calls [intros] first.
    -- warning: this tactic is overriden in LibReflect. *)

Ltac apply_to_head_of E cont :=
  let go E :=
    let P := get_head E in cont P in
  match E with
  | forall _,_ => intros; apply_to_head_of E cont
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A
  end.

Ltac unfolds_base :=
  match goal with |- ?G =>
   apply_to_head_of G ltac:(fun P => unfold P) end.

Tactic Notation "unfolds" :=
  unfolds_base.

(** [unfolds in H] unfolds the head definition of hypothesis [H], i.e. if
    [H] has type [P x1 ... xN] then it calls [unfold P in H]. *)

Ltac unfolds_in_base H :=
  match type of H with ?G =>
   apply_to_head_of G ltac:(fun P => unfold P in H) end.

Tactic Notation "unfolds" "in" hyp(H) :=
  unfolds_in_base H.

(** [unfolds in H1,H2,..,HN] allows unfolding the head constant
    in several hypotheses at once. *)

Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) :=
  unfolds in H1; unfolds in H2.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) :=
  unfolds in H1; unfolds in H2 H3.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) :=
  unfolds in H1; unfolds in H2 H3 H4.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) :=
  unfolds in H1; unfolds in H2 H3 H4 H5.

(** [unfolds P1,..,PN] is a shortcut for [unfold P1,..,PN in *]. *)

Tactic Notation "unfolds" constr(F1) :=
  unfold F1 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2) :=
  unfold F1,F2 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) :=
  unfold F1,F2,F3 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) :=
  unfold F1,F2,F3,F4 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5) :=
  unfold F1,F2,F3,F4,F5 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5) "," constr(F6) :=
  unfold F1,F2,F3,F4,F5,F6 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5)
 "," constr(F6) "," constr(F7) :=
  unfold F1,F2,F3,F4,F5,F6,F7 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5)
 "," constr(F6) "," constr(F7) "," constr(F8) :=
  unfold F1,F2,F3,F4,F5,F6,F7,F8 in *.


(* ---------------------------------------------------------------------- *)
(** ** Simplification *)

(** [simpls] is a shortcut for [simpl in *]. *)

Tactic Notation "simpls" :=
  simpl in *.

(** [simpls P1,..,PN] is a shortcut for
    [simpl P1 in *; ..; simpl PN in *]. *)

Tactic Notation "simpls" constr(F1) :=
  simpl F1 in *.
Tactic Notation "simpls" constr(F1) "," constr(F2) :=
  simpls F1; simpls F2.
Tactic Notation "simpls" constr(F1) "," constr(F2)
 "," constr(F3) :=
  simpls F1; simpls F2; simpls F3.
Tactic Notation "simpls" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) :=
  simpls F1; simpls F2; simpls F3; simpls F4.


(* ---------------------------------------------------------------------- *)
(** ** Reduction *)

Tactic Notation "hnfs" := hnf in *.



(* ********************************************************************** *)
(** * Inversion *)

(* ---------------------------------------------------------------------- *)
(** ** Basic Inversion *)

(** [invert keep H] is same to [inversion H] except that it puts all the
    facts obtained in the goal. The keyword [keep] means that the
    hypothesis [H] should not be removed. *)

Tactic Notation "invert" "keep" hyp(H) :=
  pose ltac_mark; inversion H; gen_until_mark.

(** [invert keep H as X1 .. XN] is the same as [inversion H as ...] except
    that only hypotheses which are not variable need to be named
    explicitely, in a similar fashion as [introv] is used to name
    only hypotheses. *)

Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1) :=
  invert keep H; introv I1.
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  invert keep H; introv I1 I2.
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert keep H; introv I1 I2 I3.

(** [invert H] is same to [inversion H] except that it puts all the
    facts obtained in the goal and clears hypothesis [H].
    In other words, it is equivalent to [invert keep H; clear H]. *)

Tactic Notation "invert" hyp(H) :=
  invert keep H; clear H.

(** [invert H as X1 .. XN] is the same as [invert keep H as X1 .. XN]
    but it also clears hypothesis [H]. *)

Tactic Notation "invert_tactic" hyp(H) tactic(tac) :=
  let H' := fresh "TEMP" in rename H into H'; tac H'; clear H'.
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1) :=
  invert_tactic H (fun H => invert keep H as I1).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  invert_tactic H (fun H => invert keep H as I1 I2).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert_tactic H (fun H => invert keep H as I1 I2 I3).


(* ---------------------------------------------------------------------- *)
(** ** Inversion with Substitution *)

(** Our inversion tactics is able to get rid of dependent equalities
    generated by [inversion], using proof irrelevance. *)

(* --we do not import Eqdep because it imports nasty hints automatically
    From TLC Require Import Eqdep. *)

Axiom inj_pair2 :  (* is in fact derivable from the axioms in LibAxiom.v *)
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
  existT P p x = existT P p y -> x = y.
(* Proof using. apply Eqdep.EqdepTheory.inj_pair2. Qed. *)

Ltac inverts_tactic H i1 i2 i3 i4 i5 i6 :=
  let rec go i1 i2 i3 i4 i5 i6 :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y ];
                           go i1 i2 i3 i4 i5 i6
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh "TEMP" in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go i1 i2 i3 i4 i5 i6
    | |- (?P -> ?Q) => i1; go i2 i3 i4 i5 i6 ltac:(intro)
    | |- (forall _, _) => intro; go i1 i2 i3 i4 i5 i6
    end in
  generalize ltac_mark; invert keep H; go i1 i2 i3 i4 i5 i6;
  unfold eq' in *.

(** [inverts keep H] is same to [invert keep H] except that it
    applies [subst] to all the equalities generated by the inversion. *)

Tactic Notation "inverts" "keep" hyp(H) :=
  inverts_tactic H ltac:(intro) ltac:(intro) ltac:(intro)
                   ltac:(intro) ltac:(intro) ltac:(intro).

(** [inverts keep H as X1 .. XN] is the same as
    [invert keep H as X1 .. XN] except that it applies [subst] to all the
    equalities generated by the inversion *)

Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) :=
  inverts_tactic H ltac:(intros I1)
   ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2)
   ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intros I5) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intros I5) ltac:(intros I6).

(** [inverts H] is same to [inverts keep H] except that it
    clears hypothesis [H]. *)

Tactic Notation "inverts" hyp(H) :=
  inverts keep H; try clear H.

(** [inverts H as X1 .. XN] is the same as [inverts keep H as X1 .. XN]
    but it also clears the hypothesis [H]. *)

Tactic Notation "inverts_tactic" hyp(H) tactic(tac) :=
  let H' := fresh "TEMP" in rename H into H'; tac H'; clear H'.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) :=
  invert_tactic H (fun H => inverts keep H as I1).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  invert_tactic H (fun H => inverts keep H as I1 I2).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5 I6).

(** [inverts H as] performs an inversion on hypothesis [H], substitutes
    generated equalities, and put in the goal the other freshly-created
    hypotheses, for the user to name explicitly.
    [inverts keep H as] is the same except that it does not clear [H].
    --Note: maybe reimplement [inverts] above using this one *)

Ltac inverts_as_tactic H :=
  let rec go tt :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y ];
                           go tt
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh "TEMP" in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go tt
    | |- (forall _, _) =>
       intro; let H := get_last_hyp tt in mark_to_generalize H; go tt
    end in
  pose ltac_mark; inversion H;
  generalize ltac_mark; gen_until_mark;
  go tt; gen_to_generalize; unfolds ltac_to_generalize;
  unfold eq' in *.

Tactic Notation "inverts" "keep" hyp(H) "as" :=
  inverts_as_tactic H.

Tactic Notation "inverts" hyp(H) "as" :=
  inverts_as_tactic H; clear H.

Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7) :=
  inverts H as; introv I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7)
 simple_intropattern(I8) :=
  inverts H as; introv I1 I2 I3 I4 I5 I6 I7 I8.

(** [lets_inverts E as I1 .. IN] is intuitively equivalent to
    [inverts E], with the difference that it applies to any
    expression and not just to the name of an hypothesis. *)

Ltac lets_inverts_base E cont :=
  let H := fresh "TEMP" in lets H: E; try cont H.

Tactic Notation "lets_inverts" constr(E) :=
  lets_inverts_base E ltac:(fun H => inverts H).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1 I2).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1 I2 I3).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1 I2 I3 I4).


(* ---------------------------------------------------------------------- *)
(** ** Case Analysis *)


(** [case_if_post H] is to be defined later as a tactic to clean
    up hypothesis [H] and the goal.
    By defaults, it looks for obvious contradictions.
    Currently, this tactic is extended in LibReflect to clean up
    boolean propositions. *)

Ltac case_if_post H :=
  tryfalse.

(** [case_if] looks for a pattern of the form [if ?B then ?E1 else ?E2]
    in the goal, and perform a case analysis on [B] by calling
    [destruct B]. Subgoals containing a contradiction are discarded.
    [case_if] looks in the goal first, and otherwise in the
    first hypothesis that contains an [if] statement.
    [case_if in H] can be used to specify which hypothesis to consider.
    Syntaxes [case_if as Eq] and [case_if in H as Eq] allows to name
    the hypothesis coming from the case analysis. *)

Ltac case_if_on_tactic_core E Eq :=
  match type of E with
  | {_}+{_} => destruct E as [Eq | Eq]
  | _ => let X := fresh "TEMP" in
         sets_eq <- X Eq: E;
         destruct X
  end.

Ltac case_if_on_tactic E Eq :=
  case_if_on_tactic_core E Eq; case_if_post Eq.

Tactic Notation "case_if_on" constr(E) "as" simple_intropattern(Eq) :=
  case_if_on_tactic E Eq.

Tactic Notation "case_if" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [if ?B then _ else _] => case_if_on B as Eq
  | K: context [if ?B then _ else _] |- _ => case_if_on B as Eq
  end.

Tactic Notation "case_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
  match type of H with context [if ?B then _ else _] =>
    case_if_on B as Eq end.

Tactic Notation "case_if" :=
  let Eq := fresh "C" in case_if as Eq.

Tactic Notation "case_if" "in" hyp(H) :=
  let Eq := fresh "C" in case_if in H as Eq.


(* ********************************************************************** *)
(** * Equivalence *)

(** [iff H] can be used to prove an equivalence [P <-> Q] and name [H]
    the hypothesis obtained in each case. The syntaxes [iff] and [iff H1 H2]
    are also available to specify zero or two names. The tactic [iff <- H]
    swaps the two subgoals, i.e. produces (Q -> P) as first subgoal. *)

Lemma iff_intro_swap : forall (P Q : Prop),
  (Q -> P) -> (P -> Q) -> (P <-> Q).
Proof using. intuition. Qed.

Tactic Notation "iff" simple_intropattern(H1) simple_intropattern(H2) :=
  split; [ intros H1 | intros H2 ].
Tactic Notation "iff" simple_intropattern(H) :=
  iff H H.
Tactic Notation "iff" :=
  let H := fresh "H" in iff H.

Tactic Notation "iff" "<-" simple_intropattern(H1) simple_intropattern(H2) :=
  apply iff_intro_swap; [ intros H1 | intros H2 ].
Tactic Notation "iff" "<-" simple_intropattern(H) :=
  iff <- H H.
Tactic Notation "iff" "<-" :=
  let H := fresh "H" in iff <- H.


(* ********************************************************************** *)
(** * N-ary Conjunctions and Disjunctions *)

(* ---------------------------------------------------------------------- *)
(** N-ary Conjunctions Splitting in Goals *)

(** Underlying implementation of [splits]. *)

Ltac splits_tactic N :=
  match N with
  | O => fail
  | S O => idtac
  | S ?N' => split; [| splits_tactic N']
  end.

Ltac unfold_goal_until_conjunction :=
  match goal with
  | |- _ /\ _ => idtac
  | _ => progress(unfolds); unfold_goal_until_conjunction
  end.

Ltac get_term_conjunction_arity T :=
  match T with
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(8)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(7)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(6)
  | _ /\ _ /\ _ /\ _ /\ _ => constr:(5)
  | _ /\ _ /\ _ /\ _ => constr:(4)
  | _ /\ _ /\ _ => constr:(3)
  | _ /\ _ => constr:(2)
  | _ -> ?T' => get_term_conjunction_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_conjunction_arity T'
         end
         (* --TODO: warning this can loop... *)
  end.

Ltac get_goal_conjunction_arity :=
  match goal with |- ?T => get_term_conjunction_arity T end.

(** [splits] applies to a goal of the form [(T1 /\ .. /\ TN)] and
    destruct it into [N] subgoals [T1] .. [TN]. If the goal is not a
    conjunction, then it unfolds the head definition. *)

Tactic Notation "splits" :=
  unfold_goal_until_conjunction;
  let N := get_goal_conjunction_arity in
  splits_tactic N.

(** [splits N] is similar to [splits], except that it will unfold as many
    definitions as necessary to obtain an [N]-ary conjunction. *)

Tactic Notation "splits" constr(N) :=
  let N := number_to_nat N in
  splits_tactic N.


(* ---------------------------------------------------------------------- *)
(** N-ary Conjunctions Deconstruction *)

(** Underlying implementation of [destructs]. *)

Ltac destructs_conjunction_tactic N T :=
  match N with
  | 2 => destruct T as [? ?]
  | 3 => destruct T as [? [? ?]]
  | 4 => destruct T as [? [? [? ?]]]
  | 5 => destruct T as [? [? [? [? ?]]]]
  | 6 => destruct T as [? [? [? [? [? ?]]]]]
  | 7 => destruct T as [? [? [? [? [? [? ?]]]]]]
  end.

(** [destructs T] allows destructing a term [T] which is a N-ary
    conjunction. It is equivalent to [destruct T as (H1 .. HN)],
    except that it does not require to manually specify N different
    names. *)

Tactic Notation "destructs" constr(T) :=
  let TT := type of T in
  let N := get_term_conjunction_arity TT in
  destructs_conjunction_tactic N T.

(** [destructs N T] is equivalent to [destruct T as (H1 .. HN)],
    except that it does not require to manually specify N different
    names. Remark that it is not restricted to N-ary conjunctions. *)

Tactic Notation "destructs" constr(N) constr(T) :=
  let N := number_to_nat N in
  destructs_conjunction_tactic N T.


(* ---------------------------------------------------------------------- *)
(** Proving Goals that are N-ary Disjunctions *)

(** Underlying implementation of [branch]. *)

Ltac branch_tactic K N :=
  match constr:((K,N)) with
  | (_,0) => fail 1
  | (0,_) => fail 1
  | (1,1) => idtac
  | (1,_) => left
  | (S ?K', S ?N') => right; branch_tactic K' N'
  end.

Ltac unfold_goal_until_disjunction :=
  match goal with
  | |- _ \/ _ => idtac
  | _ => progress(unfolds); unfold_goal_until_disjunction
  end.

Ltac get_term_disjunction_arity T :=
  match T with
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(8)
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(7)
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(6)
  | _ \/ _ \/ _ \/ _ \/ _ => constr:(5)
  | _ \/ _ \/ _ \/ _ => constr:(4)
  | _ \/ _ \/ _ => constr:(3)
  | _ \/ _ => constr:(2)
  | _ -> ?T' => get_term_disjunction_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_disjunction_arity T'
         end
  end.

Ltac get_goal_disjunction_arity :=
  match goal with |- ?T => get_term_disjunction_arity T end.

(** [branch N] applies to a goal of the form
    [P1 \/ ... \/ PK \/ ... \/ PN] and leaves the goal [PK].
    It only able to unfold the head definition (if there is one),
    but for more complex unfolding one should use the tactic
    [branch K of N]. *)

Tactic Notation "branch" constr(K) :=
  let K := number_to_nat K in
  unfold_goal_until_disjunction;
  let N := get_goal_disjunction_arity in
  branch_tactic K N.

(** [branch K of N] is similar to [branch K] except that the
    arity of the disjunction [N] is given manually, and so this
    version of the tactic is able to unfold definitions.
    In other words, applies to a goal of the form
    [P1 \/ ... \/ PK \/ ... \/ PN] and leaves the goal [PK]. *)

Tactic Notation "branch" constr(K) "of" constr(N) :=
  let N := number_to_nat N in
  let K := number_to_nat K in
  branch_tactic K N.


(* ********************************************************************** *)
(** * Tactics to Invoke Automation *)


(* ---------------------------------------------------------------------- *)
(** ** [hint] to Add Hints Local to a Lemma *)

(** [hint E] adds [E] as an hypothesis so that automation can use it.
    Syntax [hint E1,..,EN] is available *)

Tactic Notation "hint" constr(E) :=
  let H := fresh "Hint" in lets H: E.
Tactic Notation "hint" constr(E1) "," constr(E2) :=
  hint E1; hint E2.
Tactic Notation "hint" constr(E1) "," constr(E2) "," constr(E3) :=
  hint E1; hint E2; hint(E3).
Tactic Notation "hint" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  hint E1; hint E2; hint(E3); hint(E4 ).


(* ---------------------------------------------------------------------- *)
(** ** [jauto], a New Automation Tactic *)

(** [jauto] is better at [intuition eauto] because it can open existentials
    from the context. In the same time, [jauto] can be faster than
    [intuition eauto] because it does not destruct disjunctions from the
    context. The strategy of [jauto] can be summarized as follows:
    - open all the existentials and conjunctions from the context
    - call esplit and split on the existentials and conjunctions in the goal
    - call eauto. *)

Tactic Notation "jauto" :=
  try solve [ jauto_set; eauto ].

Tactic Notation "jauto_fast" :=
  try solve [ auto | eauto | jauto ].

(** [iauto] is a shorthand for [intuition eauto] *)

Tactic Notation "iauto" := try solve [intuition eauto].


(* ---------------------------------------------------------------------- *)
(** ** Definitions of Automation Tactics *)

(** The two following tactics defined the default behaviour of
    "light automation" and "strong automation". These tactics
    may be redefined at any time using the syntax [Ltac .. ::= ..]. *)

(** [auto_tilde] is the tactic which will be called each time a symbol
    [~] is used after a tactic. *)

Ltac auto_tilde_default := auto.
Ltac auto_tilde := auto_tilde_default.

(** [auto_star] is the tactic which will be called each time a symbol
    [*] is used after a tactic. *)

Ltac auto_star_default := try solve [ auto | eauto | intuition eauto ].
  (* --TODO: should be jauto *)
Ltac auto_star := auto_star_default.


(** [autos~] is a notation for tactic [auto_tilde]. It may be followed
    by lemmas (or proofs terms) which auto will be able to use
    for solving the goal. *)
(** [autos] is an alias for [autos~] *)

Tactic Notation "autos" :=
  auto_tilde.
Tactic Notation "autos" "~" :=
  auto_tilde.
Tactic Notation "autos" "~" constr(E1) :=
  lets: E1; auto_tilde.
Tactic Notation "autos" "~" constr(E1) constr(E2) :=
  lets: E1; autos~ E2.
Tactic Notation "autos" "~" constr(E1) constr(E2) constr(E3) :=
  lets: E1; autos~ E2 E3.
Tactic Notation "autos" "~" constr(E1) constr(E2) constr(E3) constr(E4) :=
  lets: E1; autos~ E2 E3 E4.
Tactic Notation "autos" "~" constr(E1) constr(E2) constr(E3) constr(E4)
 constr(E5):=
  lets: E1; autos~ E2 E3 E4 E5.

(* New syntax using coma *)
Tactic Notation "autos" :=
  auto_tilde.
Tactic Notation "autos" "~" :=
  auto_tilde.
Tactic Notation "autos" "~" constr(E1) :=
  lets: E1; auto_tilde.
Tactic Notation "autos" "~" constr(E1) "," constr(E2) :=
  lets: E1; autos~ E2.
Tactic Notation "autos" "~" constr(E1) "," constr(E2) "," constr(E3) :=
  lets: E1; autos~ E2 E3.
Tactic Notation "autos" "~" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  lets: E1; autos~ E2 E3 E4.
Tactic Notation "autos" "~" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) ","
 constr(E5):=
  lets: E1; autos~ E2 E3 E4 E5.

(** [autos*] is a notation for tactic [auto_star]. It may be followed
    by lemmas (or proofs terms) which auto will be able to use
    for solving the goal. *)

Tactic Notation "autos" "*" :=
  auto_star.
Tactic Notation "autos" "*" constr(E1) :=
  lets: E1; auto_star.
Tactic Notation "autos" "*" constr(E1) constr(E2) :=
  lets: E1; autos* E2.
Tactic Notation "autos" "*" constr(E1) constr(E2) constr(E3) :=
  lets: E1; autos* E2 E3.
Tactic Notation "autos" "*" constr(E1) constr(E2) constr(E3) constr(E4) :=
  lets: E1; autos* E2 E3 E4.
Tactic Notation "autos" "*" constr(E1) constr(E2) constr(E3) constr(E4)
 constr(E5):=
  lets: E1; autos* E2 E3 E4 E5.

(* New syntax using coma *)

Tactic Notation "autos" "*" :=
  auto_star.
Tactic Notation "autos" "*" constr(E1) :=
  lets: E1; auto_star.
Tactic Notation "autos" "*" constr(E1) "," constr(E2) :=
  lets: E1; autos* E2.
Tactic Notation "autos" "*" constr(E1) "," constr(E2) "," constr(E3) :=
  lets: E1; autos* E2 E3.
Tactic Notation "autos" "*" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  lets: E1; autos* E2 E3 E4.
Tactic Notation "autos" "*" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) ","
 constr(E5):=
  lets: E1; autos* E2 E3 E4 E5.

(** [auto_false] is a version of [auto] able to spot some contradictions.
    There is an ad-hoc support for goals in [<->]: split is called first.
    [auto_false~] and [auto_false*] are also available. *)

Ltac auto_false_base cont :=
  try solve [
    intros_all; try match goal with |- _ <-> _ => split end;
    solve [ cont tt | intros_all; false; cont tt ] ].

Tactic Notation "auto_false" :=
   auto_false_base ltac:(fun tt => auto).
Tactic Notation "auto_false" "~" :=
   auto_false_base ltac:(fun tt => auto_tilde).
Tactic Notation "auto_false" "*" :=
   auto_false_base ltac:(fun tt => auto_star).

Tactic Notation "dauto" :=
  dintuition eauto.


(* ---------------------------------------------------------------------- *)
(** ** Parsing for Light Automation *)

(** Any tactic followed by the symbol [~] will have [auto_tilde] called
    on all of its subgoals. Three exceptions:
    - [cuts] and [asserts] only call [auto] on their first subgoal,
    - [apply~] relies on [sapply] rather than [apply],
    - [tryfalse~] is defined as [tryfalse by auto_tilde].

   Some builtin tactics are not defined using tactic notations
   and thus cannot be extended, e.g., [simpl] and [unfold].
   For these, notation such as [simpl~] will not be available. *)

(* Example: *)

Tactic Notation "applys" "~" constr(H) :=
  applys H; auto_tilde.

(* ---------------------------------------------------------------------- *)
(** ** Parsing for Strong Automation *)

(** Any tactic followed by the symbol [*] will have [auto*] called
    on all of its subgoals. The exceptions to these rules are the
    same as for light automation.

    Exception: use [subs*] instead of [subst*] if you
    import the library [Coq.Classes.Equivalence]. *)

(* Example: *)

Tactic Notation "applys" "*" constr(H) :=
  applys H; auto_star.

