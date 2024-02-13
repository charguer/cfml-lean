
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


(* ---------------------------------------------------------------------- *)
(** ** Heterogeneous lists of arguments *)

(** Any Coq value can be boxed into the type [Boxer]. This is
    useful to use Coq computations for implementing tactics. *)

Inductive Boxer : Type :=
  | boxer : forall (A:Type), A -> Boxer.

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
(** ** Instantiation *)

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

(** Auxiliary function to instantiate [t] whose first argument is
    a proposition of type [P], by creating a subgoal of type [P].
    Thereafter, [cont] denotes the continuation which handles
    the resulting partial instantiation. *)

Ltac app_assert t P cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ | cont(t H); clear H ].

(** Auxiliary function to instantiate [t] whose first argument is
    of type [A], by creating an evar of type [A]. *)

Ltac app_evar t A cont :=
  let x := fresh "TEMP" in
  evar (x:A);
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.

(** Auxiliary function to instantiate [t] whose first argument is
    of type [P], by applying it to a user-supplied value [v]. *)

Ltac app_arg t P v cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ apply v | cont(t H); try clear H ].

(** Auxiliary function to instantiate [t] whose first argument is
    of a typeclass, by applying it to a underscore, which triggers
    the generation of an evar, and scheduling a later typeclass
    resolution attempt for this evar
    (Coq is relatively underspecified on that matter). *)

Ltac app_typeclass t cont :=
  let t' := constr:(t _) in
  cont t'.

(** Auxiliary function to instantiate [t] on all its remaining
    visible arguments. Visible means with a [->] or [forall]. *)

Ltac build_app_alls t final :=
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

(** Auxiliary function to query the type of the next proper argument
    in a list of user-supplied arguments [vs]. This function is slightly
    complicated by the need to skip the [__] arguments, which are meant
    to indicate that we purposely want to not provide an argument that
    has the same type as the next provided argument. There are special
    cases if [__] is not followed by a proper argument, but only by
    others [__] and/or [___]. *)

Ltac boxerlist_next_type vs :=
  match vs with
  | nil => constr:(ltac_wild)
  | (boxer ltac_wild)::?vs' => boxerlist_next_type vs'
  | (boxer ltac_wilds)::_ => constr:(ltac_wild)
  | (@boxer ?T _)::_ => constr:(T)
  end.

(** Main recursive function, for building an instantiation of [t] on the list of
   arguments [vs]. [final] is the continuation applied to the resulting instantiation. *)
Ltac build_app_hnts t vs final :=
  let rec go t vs :=
    match vs with
    (* If there are no more arguments, we're done, we call the continuation *)
    | nil => first [ final t | fail 1 ]
    (* If we have a [___] argument (triple not double underscore), this means
       we need to instantiate all remaining arguments of [t] *)
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    (* Else we consider the first argument provided, [v] ---possibly a [__] *)
    | (boxer ?v)::?vs' =>
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      (* Because an argument is provided, we can [hnf] the term [t] to see
         whether it is a [->] or a [forall]. *)
      let T := type of t in
      let T := eval hnf in T in
      match v with
      (* If the argument [v] is a [__], we have to find the type of the next
         argument in the remaining list [vs'].  *)
      | ltac_wild =>
         first [ let U := boxerlist_next_type vs' in
          (* Corner case of the trailing [__] not followed by propert arguments;
             In this case, we just want to instantiate one more argument. *)
           match U with
           | ltac_wild =>
             match T with
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_typeclass t cont'
                                       | app_evar t A cont'
                                       | fail 3 ]
             end
           | _ =>
             (* Otherwise, let's assume we have a next proper argument of type [T].
                We want to keep instantiating arguments until we find at least one
                argument of [t] that admits the type [T]. This way, we can instantiate
                this argument with an evar/subgoal, and continue. *)
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
          (* Here we are in the regular case. *)
          match T with
          (* If the type of [t] is an arrow type, and we have a value [v] on which
             to instantiate it, we first attempt to instantiate [t] on [v]. If it
             works, good, else we generate [P] as subgoal, and try again with what
            remains of [t], still with [v] as first provided value. *)
           | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           (* If the [t] is a forall type, and we have a value [v] on which
             to instantiate it, we first attempt to instantiate [t] on [v]. If it
             works, good, else we generate an evar, and try again with what
             remains of [t], still with [v] as first provided value.
             There are special cases, however. If the first argument expected by [t]
             is of type [Type], we only want to attempt an instantiation of [t]
             on [v] if [v] is also of type [Type]. (This is because the type [Type]
             unifies with too many things in Coq. *)
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
             (* Another subtelty is if the user-provided argument [v] is of type [Prop],
                but [t] does not expect a proposition as argument.
                In this case, we don't try to instantiate [t] on [v] *)
             | Prop => first [ app_typeclass t cont
                              | app_evar t A cont
                              | fail 3 ]
             (* In the default case, we try to instantiate [t] on [v], else we try to
                instantiate [t] on [_], which works if the first argument is a typeclass,
                else we try to instantiate [t] on an evar. *)
             | _ => first [ cont' (t v)
                          | app_typeclass t cont
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.


(** Main function for building an instantiation of [t] on the list of
   arguments [vs], where [args] corresponds to [t :: vs].
   [final] is the continuation applied to the resulting instantiation. *)
Ltac build_app args final :=
  first [
    match args with (@boxer ?T ?t)::?vs =>
      let t := constr:(t:T) in
      build_app_hnts t vs final;
      rm_inside args
    end
  | fail 1 "Instantiation fails for:" args].


(* ---------------------------------------------------------------------- *)
(** ** Unfold tactics *)

(** The behavior of the instantiation tactic depend on the unfolding rule.
    For example, consider
[[
      Definition foo_def := forall x, x = 1 -> x <> 0.
      Lemma foo : foo_def.
]]
    What should [forwards H: foo.] do? Should it produce an hypothesis [H]
    of type [foo] is kind of silly---we could have used [lets H: foo] for
    this. Thus, it makes sense to unfold [foo_def] on the fly.
    However, unfolding should be limited. In the example:
[[
      Lemma bar : True -> foo_def.
]]
   the tactic [forwards H: bar] should produce [H] of type [foo_def],
   and a proof obligation for [True]. Only [forwards H: bar 2] should
   unfold the definition of [foo_def] on the fly.

   That said, for the robustness of certain tactics, it may be desirable
   to turn off the feature of unfolding head constants. The tactic
   [forwards_unfold], defined further, serves that purpose.

   The auxiliary tactics below are useful for unfolding certain kinds
   of head symbols. *)

Ltac unfold_head_until_product T :=
  eval hnf in T.

(** This tactic performs an unfolding of the head constant until
    seeing at list one forall quantifier. *)
Ltac args_unfold_head_if_not_product args :=
  match args with (@boxer ?T ?t)::?vs =>
    let T' := unfold_head_until_product T in
    constr:((@boxer T' t)::vs)
  end.

(** This tactic performs an unfolding of the head constant until
    seeing at list one forall quantifier, but only if at least
    one explicit argument is provided for the instantiation. *)
Ltac args_unfold_head_if_not_product_but_params args :=
  match args with
  | (boxer ?t)::(boxer ?v)::?vs =>
     args_unfold_head_if_not_product args
  | _ => constr:(args)
  end.

(* ---------------------------------------------------------------------- *)
(** ** [lets] *)

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
  build_app args ltac:(fun R => lets_base I R).

Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  lets I: (>> E0 A1).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets I: (>> E0 A1 A2).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets I: (>> E0 A1 A2 A3).

(* ---------------------------------------------------------------------- *)
(** ** [forwards] *)

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

Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  forwards I: (>> E0 A1).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: (>> E0 A1 A2).

(* ---------------------------------------------------------------------- *)
(** ** [forwards_nounfold] *)

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

(* ---------------------------------------------------------------------- *)
(** ** [applys] *)

Ltac applys_build Ei :=
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args ltac:(fun R =>
   first [ apply R | eapply R | rapply R ]).

Ltac applys_base E :=
  match type of E with
  | list Boxer => applys_build E
  | _ => first [ rapply E | applys_build E ]
  end; rm_inside E.

Tactic Notation "applys" constr(E) :=
  applys_base E.
Tactic Notation "applys" constr(E0) constr(A1) :=
  applys (>> E0 A1).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) :=
  applys (>> E0 A1 A2).

(* ---------------------------------------------------------------------- *)
(** ** [specializes] *)

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
  specializes_build H Ei; rm_inside Ei.

Tactic Notation "specializes" hyp(H) :=
  specializes_base H (___).
Tactic Notation "specializes" hyp(H) constr(A) :=
  specializes_base H A.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
  specializes H (>> A1 A2).