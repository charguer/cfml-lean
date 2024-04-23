import Lean
import Cfml.Init

namespace Cfml

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail : Result α
deriving Repr, BEq

open Result

instance Result_Inhabited (α : Type u) : Inhabited (Result α) :=
  Inhabited.mk fail

instance Result_Nonempty (α : Type u) : Nonempty (Result α) :=
  Nonempty.intro fail

/- HELPERS -/

def ok? {α: Type u} (r: Result α): Bool :=
  match r with
  | ok _ => true
  | fail => false

/- DO-DSL SUPPORT -/

def bind {α : Type u} {β : Type v} (x: Result α) (f: α → Result β) : Result β :=
  match x with
  | ok v  => f v
  | fail => fail

-- Allows using Result in do-blocks
instance : Bind Result where
  bind := bind

-- Allows using pure x in do-blocks
instance : Pure Result where
  pure := fun x => ok x

@[simp] theorem bind_ok (x : α) (f : α → Result β) : bind (.ok x) f = f x := by simp [bind]
@[simp] theorem bind_fail (f : α → Result β) : bind .fail f = .fail := by simp [bind]

/- CUSTOM-DSL SUPPORT -/

-- Let-binding the Result of a monadic operation is oftentimes not sufficient,
-- because we may need a hypothesis for equational reasoning in the scope. We
-- rely on subtype, and a custom let-binding operator, in effect recreating our
-- own variant of the do-dsl

def Result.attach {α: Type} (o : Result α): Result { x : α // o = ok x } :=
  match o with
  | ok x => ok ⟨x, rfl⟩
  | fail => fail

@[simp] theorem bind_tc_ok (x : α) (f : α → Result β) :
  (do let y ← .ok x; f y) = f x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_fail (x : Error) (f : α → Result β) :
  (do let y ← fail; f y) = fail := by simp [Bind.bind, bind]

@[simp] theorem bind_assoc_eq {a b c : Type u}
  (e : Result a) (g :  a → Result b) (h : b → Result c) :
  (Bind.bind (Bind.bind e g) h) =
  (Bind.bind e (λ x => Bind.bind (g x) h)) := by
  simp [Bind.bind]
  cases e <;> simp

def f (x : α) : Result α := do
  let x ← ok x
  ok x

def double (x : Int) : Result Int := do
  ok (x + x)

def quadruple (x : Int) : Result Int := do
  let y ← double x
  double y

def spec (r : Result α) (Q : α → Prop) : Prop :=
  match r with
  | ok v => Q v
  | fail => false

theorem spec_ok (v : α) (Q : α → Prop) (h : Q v) :
  spec (ok v) Q := by
  simp [spec, *]

#check spec_ok

theorem spec_ok_evar (v : α) :
  spec (ok v) (fun y => y = v) := by
  simp [spec, *]

theorem spec_let e Q1 Q :
  spec e Q1 →
  (∀ x, Q1 x → spec (k x) Q) →
  spec (bind e k) Q := by
  simp [spec, bind, *]
  cases e <;> simp
  sorry

theorem spec_let_ok_subst v Q :
  spec (k v) Q →
  spec (bind (ok v) k) Q := sorry

theorem spec_let_ok_nosubst v Q :
  (∀ x, x = v → spec (k x) Q) →
  spec (bind (ok v) k) Q := sorry

theorem spec_forall_eq_subst (k : α → Result β) v Q :
  spec (k v) Q →
  (∀ x, x = v → spec (k x) Q) := sorry

-- TODO: ==>
@[simp]
def entails (Q1 Q2 : α → Prop) : Prop :=
  ∀ x, Q1 x → Q2 x

theorem refl_entails : entails Q Q := sorry

theorem spec_weaken :
  spec e Q1 →
  entails Q1 Q2 →
  spec e Q2 := by sorry

-- TODO: notation =2*x
theorem spec_double (x : Int) :
  spec (double x) (λ y => y = 2 * x) :=
  sorry

theorem spec_quadruple (x : Int) :
  spec (quadruple x) (λ y => y = 4 * x) := by
  rw [quadruple]
  apply spec_let
  . apply spec_double
  . intro y Hy
    apply spec_weaken
    apply spec_double; simp 
    intro y Hy; simp_all
    sorry
  . apply spec_double
  sorry

theorem spec_quadruple1 (x : Int) :
  spec (quadruple x) (λ y => y = 4 * x) := by
  rw [quadruple]
  apply spec_let
  . apply spec_weaken
    apply spec_double
    apply refl_entails
  . intro y Hy
    apply spec_weaken
    apply spec_double; simp 
    intro y Hy; simp_all
    sorry
  . 
    apply spec_double
  sorry

-- xlet
-- xlet P
-- xlet_val
--syntax xletTac := ("as" " ⟨ " (ident <|> "_"),* " .."? " ⟩")?

--def evalProgress (args : TSyntax `Progress.progressArgs) : TacticM Unit := do
--  let args := args.raw

set_option trace.Xlet false
open Lean Elab Term Meta Tactic

#check Expr

#check LocalContext
#check ConstantInfo
#check Expr.const

def exprOfThm (name : Name) : MetaM Expr := do
  let env ← getEnv
  let thDecl := env.constants.find! name
  -- We have to introduce fresh meta-variables for the universes already
  let ul : List Level ←
    thDecl.levelParams.mapM (λ _ => do pure (← mkFreshLevelMVar))
  let th := Expr.const name ul
  trace[Xlet] "th: {th}"
  pure th

-- xlet
-- xlet P
-- xlet
def xletEval (cont1 : MVarId → TacticM (List MVarId))
             (cont2 : MVarId → Name → TacticM (List MVarId)) : TacticM Unit := do
  -- Focus on the current goal
  Tactic.focus do
  withMainContext do
  -- Retrieve the goal
  let mgoal ← Tactic.getMainGoal
  let goalTy ← mgoal.getType
  trace[Xlet] "goal: {goalTy}"
  -- Expected goal: spec (let x ← _; k) Q
  -- Retrieve: (let x ← _; k)
  goalTy.consumeMData.withApp fun _ args => do
  let e := args.get! 1 -- bind _ (fun x => k x)
  trace[Xlet] "e: {e}"
  e.consumeMData.withApp fun _bind bindArgs => do
  trace[Xlet] "bindArgs: {bindArgs}"
  let k := bindArgs.get! 5
  trace[Xlet] "k: {k}"
  -- Dive into the lambda
  lambdaTelescope k fun kArgs kBody => do
  trace[Xlet] "k: {kArgs}"
  -- Retrieve the first binder
  let x := kArgs.get! 0
  trace[Xlet] "x: {x}"
  let xId := x.fvarId!
  -- Lookup the name of the variable
  let ctx ← Lean.MonadLCtx.getLCtx
  let decl := ctx.get! xId
  let yName :=
    match decl with
    | .cdecl _index _ userName _ _ _ => userName
    | .ldecl _index _ userName _ _ _ _ => userName
  trace[Xlet] "yName: {yName}"
  -- Apply the theorem
  let th ← exprOfThm ``spec_let
  let ngoals ← mgoal.apply th
  setGoals ngoals
  -- intro y in the second goal
  match ngoals with
  | goal1 :: goal2 :: goals =>
    -- Apply continuations
    let ngoals1 ← cont1 goal1
    let ngoals2 ← cont2 goal2 yName
    setGoals (List.append ngoals1 (List.append ngoals2 goals))
    pure ()
  | _ =>
    -- Error
    panic "There should be at least 2 goals"

elab "xlet" : tactic => do
  let cont1 (goal : MVarId) : TacticM (List MVarId) := pure [goal]
  let cont2 goal yName := do
    let (_, ngoal) ← goal.intro yName
    pure [ngoal]
  xletEval cont1 cont2

def xletValEval : TacticM Unit := do
  withMainContext do
  -- Retrieve the goal
  let mgoal ← Tactic.getMainGoal
  let ngoals ← mgoal.apply (← exprOfThm ``spec_let_ok_subst)
  setGoals ngoals

elab "xlet_val" : tactic => do
  xletValEval

elab "xval" : tactic => do
  withMainContext do
  -- Retrieve the goal
  let mgoal ← Tactic.getMainGoal
  let ngoals ← mgoal.apply (← exprOfThm ``spec_ok)
  setGoals ngoals

/-syntax "xval" : tactic
macro_rules
  | `(tactic| xval) =>
    `(tactic|
      -- TODO: we should check wether the post is an evar or not
      apply ``spec_ok)-/

theorem entail_trivial :
  P a →
  entails (fun y => y = a) P := sorry

syntax "xapp_last" term : tactic
macro_rules
  | `(tactic| xapp_last $spec:term) =>
    `(tactic|
      apply spec_weaken <;>
      (try apply $spec) <;>
      (try intro res Hres; try simp only))

/-
-- TODO: use name given by lambda
syntax "xlet" : tactic
macro_rules
  | `(tactic| xlet) =>
    `(tactic|
      apply spec_let; [|intro])
-/

elab "xapp" e:term : tactic => do
  -- Resolve the id of the theorem
  withMainContext do
  let mut e ← instantiateMVars (← elabTermForApply e)
  let cont1 (goal : MVarId) : TacticM (List MVarId) := do
    let ngoals ← goal.apply e
    pure ngoals
  let cont2 goal yName := do
    let (_, ngoal) ← goal.intro yName
    pure [ngoal]
  xletEval cont1 cont2

elab "xapps" e:term : tactic => do
  -- Resolve the id of the theorem
  withMainContext do
  let mut e ← instantiateMVars (← elabTermForApply e)
  let cont1 (goal : MVarId) : TacticM (List MVarId) := do
    let ngoals ← goal.apply e
    pure ngoals
  let cont2 goal _yName := do
    goal.apply (← exprOfThm ``spec_forall_eq_subst)
  xletEval cont1 cont2

theorem spec_quadruple2 (x : Int) :
  spec (quadruple x) (λ y => y = 4 * x) := by
  rw [quadruple]
  xlet
  . apply spec_double
  . intro Hy
    sorry

theorem spec_2 :
  spec (do let x ← ok 2; pure 2) (λ y => y = 2) := by
  xlet_val
  sorry

example (x : Int) :
  spec (quadruple x) (λ y => y = 4 * x) := by
  xapp_last spec_quadruple2
  simp [*]

example (x : Int) :
  spec (double x) (λ y => y = 2 * x) := by
  rw [double] -- TODO: xstart
  xval
  sorry

example :
  spec (do let x ← ok 2; ok (x + x)) (λ y => y = 4) := by
  xlet_val
  xval
  simp

example :
  spec (do let x ← ok 2; ok (x + x)) (λ y => y = 4) := by
  xlet
  apply spec_ok_evar
  intro Hx
  xval
  simp [Hx]

example (x : Int) :
  spec (quadruple x) (λ y => y = 4 * x) := by
  rw [quadruple]
  xapp spec_double
  intro Hy
  xapp_last spec_double
  sorry

example (x : Int) :
  spec (quadruple x) (λ y => y = 4 * x) := by
  rw [quadruple]
  xapps spec_double
  xapp_last spec_double
  sorry

def half (n : Int) : Result Int :=
  ok (n / 2)

theorem spec_half :
  ∀ m n, n = 2 * m →
  spec (half n) (λ m' => m' = m) := by
  sorry

def quarter (x : Int) : Result Int := do
  let y ← half x
  half y

theorem spec_quarter :
  ∀ m n, n = 4 * m →
  spec (quarter n) (λ m' => m' = m) := by
  intro m n Heq
  unfold quarter
  -- TODO: xapp (spec_half 2 * m)
  -- TODO: xapp (>> 2 * m)
  xapps (spec_half (2 * m))
  sorry
  xapp_last (spec_half m) <;> simp [*]

end Cfml
