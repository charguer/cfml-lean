(* Representation of variables, and fresh name generator *)


Set Implicit Arguments.
From TLC Require LibListExec.
From TLC Require Export LibString LibList LibCore.
From CFML Require Import LibSepFmap LibSepTLCbuffer.
Module Fmap := LibSepFmap.
Open Scope string_scope.
Generalizable Variables A.


(* ********************************************************************** *)
(* * Variables *)

(** A variable is represented as a string.

    The boolean function [var_eq x y] compares two variables.

    The tactic [case_var] performs case analysis on expressions of the form
    [if var_eq x y then .. else ..] that appear in the goal.

*)

(* ---------------------------------------------------------------------- *)
(** Representation of variables *)

(** Variables are represented as strings *)

Definition var := string.

(** Variables can be compared via [var_eq s1 s2] *)

Definition eq_var_dec := String.string_dec.

Definition var_eq (s1:var) (s2:var) : bool :=
  if eq_var_dec s1 s2 then true else false.

Lemma var_eq_spec : forall s1 s2,
  var_eq s1 s2 = isTrue (s1 = s2).
Proof using.
  intros. unfold var_eq. case_if; rew_bool_eq~.
Qed.

Global Opaque var.

(** Tactic [var_neq] for proving two concrete variables distinct.
    Also registered as hint for [auto] *)

Ltac var_neq :=
  match goal with |- ?x <> ?y :> var =>
    solve [ let E := fresh in
            destruct (eq_var_dec x y) as [E|E];
              [ false | apply E ] ] end.

Hint Extern 1 (?x <> ?y) => var_neq.


(* ---------------------------------------------------------------------- *)
(** Tactic [case_var] *)

Tactic Notation "case_var" :=
  repeat rewrite var_eq_spec in *; repeat case_if.

Tactic Notation "case_var" "~" :=
  case_var; auto_tilde.

Tactic Notation "case_var" "*" :=
  case_var; auto_star.


(* ---------------------------------------------------------------------- *)
(** Distinct variables *)

(** [vars] is the type of a list of variables *)

Definition vars : Type := list var.

(** [var_fresh y xs] asserts that [y] does not belong to the list [xs] *)

Fixpoint var_fresh (y:var) (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => if var_eq x y then false else var_fresh y xs'
  end.

(** [var_distinct xs] asserts that [xs] consists of a list of distinct variables.
    --LATER: use [noduplicates] *)

Fixpoint var_distinct (xs:vars) : Prop :=
  match xs with
  | nil => True
  | x::xs' => var_fresh x xs' /\ var_distinct xs'
  end.

(** Computable version of [var_distinct] *)

Fixpoint var_distinct_exec (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => var_fresh x xs' && var_distinct_exec xs'
  end.

Lemma var_distinct_exec_eq : forall xs,
  var_distinct_exec xs = isTrue (var_distinct xs).
Proof using.
  intros. induction xs as [|x xs']; simpl; rew_isTrue.
  { auto. } { rewrite~ IHxs'. }
Qed.

(** Elimination lemma for [var_fresh] *)

Lemma var_fresh_mem_inv : forall y x xs,
  var_fresh x xs ->
  mem y xs ->
  x <> y.
Proof using.
  introv H M N. subst. induction xs as [|x xs'].
  { inverts M. }
  { simpls. case_var. inverts~ M. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** List of n fresh variables *)

(** [var_funs xs n] asserts that [xs] consists of [n] distinct variables,
    for [n > 0]. *)

Definition var_funs (xs:vars) (n:nat) : Prop :=
     var_distinct xs
  /\ length xs = n
  /\ xs <> nil.

(** Computable version of [var_funs] *)

Definition var_funs_exec (xs:vars) (n:nat) : bool :=
     LibNat.beq n (LibListExec.length xs)
  && LibListExec.is_not_nil xs
  && var_distinct_exec xs.

Lemma var_funs_exec_eq : forall (n:nat) xs,
  var_funs_exec xs n = isTrue (var_funs xs n).
Proof using.
  intros. unfold var_funs_exec, var_funs.
  rewrite LibNat.beq_eq.
  rewrite LibListExec.is_not_nil_eq.
  rewrite LibListExec.length_eq.
  rewrite var_distinct_exec_eq.
  extens. rew_istrue. iff*.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Generation of n variables *)

(** [nat_to_var n] converts [nat] values into distinct
    [name] values.
    Warning: the current implementation is inefficient. *)

Definition dummy_char := Ascii.ascii_of_nat 0%nat.

Fixpoint nat_to_var (n:nat) : var :=
  match n with
  | O => String.EmptyString
  | S n' => String.String dummy_char (nat_to_var n')
  end.

Lemma injective_nat_to_var : injective nat_to_var.
Proof using.
  intros n. induction n as [|n']; intros m E; destruct m as [|m']; tryfalse.
  { auto. }
  { inverts E. fequals~. }
Qed.

(** [var_seq i n] generates a list of variables [x1;x2;..;xn]
    with [x1=i] and [xn=i+n-1]. Such lists are useful for
    generic programming. *)

Fixpoint var_seq (start:nat) (nb:nat) : vars :=
  match nb with
  | O => nil
  | S nb' => (nat_to_var start) :: var_seq (S start) nb'
  end.

(** Properties of [var_seq] follow *)

Section Var_seq.
Implicit Types start nb : nat.

Lemma var_fresh_var_seq_lt : forall (x:nat) start nb,
  (x < start)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. case_var.
    { lets: injective_nat_to_var C. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_fresh_var_seq_ge : forall (x:nat) start nb,
  (x >= start+nb)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. case_var.
    { lets: injective_nat_to_var C. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_distinct_var_seq : forall start nb,
  var_distinct (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { simple~. }
  { split.
    { applys var_fresh_var_seq_lt. math. }
    { auto. } }
Qed.

Lemma length_var_seq : forall start nb,
  length (var_seq start nb) = nb.
Proof using.
  intros. gen start. induction nb; simpl; intros.
  { auto. } { rew_list. rewrite~ IHnb. }
Qed.

Lemma var_funs_var_seq : forall start nb,
  (nb > 0%nat)%nat ->
  var_funs (var_seq start nb) nb.
Proof using.
  introv E. splits.
  { applys var_distinct_var_seq. }
  { applys length_var_seq. }
  { destruct nb. { false. math. } { simpl. auto_false. } }
Qed.

End Var_seq.
