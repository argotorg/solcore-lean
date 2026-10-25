import Solcore.Frontend.RustHull.Semantics

/-! A property of external state survives an entire independent Hull execution
when each external operation preserves it. Local allocation and assignment,
recursive calls, loops and all fault paths are covered by the same induction. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.EffectProjectionPreservation
open Semantics

/-- The external specification preserves an observation of its state. -/
structure Preserves {σ τ : Type} (effects : ExternalSemantics σ) (project : σ → τ) : Prop where
  builtin : ∀ {name type arguments initial result final},
    effects.builtin name type arguments initial result final → project final = project initial
  assembly : ∀ {functions environment body initial control final},
    effects.assembly functions environment body initial control final →
      project final.external = project initial.external
  revert : ∀ {message initial control final},
    effects.revert message initial control final → project final = project initial

theorem write_external {σ : Type} {initial final : State σ} {location : Nat} {value : Value}
    (written : write? initial location value = some final) : final.external = initial.external := by
  unfold write? at written
  split at written
  · cases Option.some.inj written
    rfl
  · contradiction

theorem assign_external {σ : Type} {environment : Environment} {initial final : State σ}
    {lhs : Expr} {value : Value}
    (written : assignResult environment initial lhs value = .value final) :
    final.external = initial.external := by
  unfold assignResult at written
  repeat' (split at written <;> try contradiction)
  cases written
  exact write_external ‹write? initial _ _ = some _›

theorem bind_external {σ : Type} {arguments : List Arg} {values : List Value}
    {environment finalEnvironment : Environment} {initial final : State σ}
    (bound : bindArguments arguments values environment initial = some (finalEnvironment, final)) :
    final.external = initial.external := by
  induction arguments generalizing values environment initial with
  | nil =>
    cases values <;> simp_all [bindArguments]
  | cons argument arguments ih =>
    cases values with
    | nil => simp [bindArguments] at bound
    | cons value values => exact ih (initial := (allocate initial value).2) bound

/-- The conclusion includes successful results and faults, with no assumption
about termination of another execution or the absence of recursive calls. -/
theorem function_preserves {σ τ : Type} {effects : ExternalSemantics σ}
    {project : σ → τ} (preserved : Preserves effects project)
    {functions : List Function} {function : Function} {arguments : List Value}
    {initial final : State σ} {result : Result Value}
    (evaluated : EvalFunction functions effects function arguments initial result final) :
    project final.external = project initial.external := by
  refine EvalFunction.rec
    (motive_1 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_2 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_3 := fun _ _ _ initial _ final _ => project final.external = project initial.external)
    (motive_4 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_5 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_6 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_7 := fun _ _ _ _ initial _ final _ => project final.external = project initial.external)
    (motive_8 := fun _ _ _ _ initial _ final _ => project final.external = project initial.external)
    ?word ?bool ?unit ?var ?pair ?pairFault ?fst ?snd ?inl ?inr ?inK
    ?call ?callFault ?ifTrue ?ifFalse ?ifFault ?ifInvalid
    ?nil ?cons ?fault ?function ?primitive ?external ?body ?arity
    ?declare ?declareInvalid ?assign ?assignFault ?assignInvalid
    ?expression ?expressionFault ?returned ?returnFault ?block ?forInit ?forLoop
    ?breaking ?continuing ?matchStmt ?matchFault ?assembly ?revert ?comment
    ?nil_1 ?declare_1 ?declareInvalid_1 ?next ?stop
    ?done ?conditionFault ?conditionInvalid ?step ?bodyBreak ?bodyStop ?postBreak ?postStop
    ?nil_2 ?matched ?next_1 evaluated
  all_goals intros
  all_goals try (solve | simp_all only [allocate])
  case external => exact preserved.builtin ‹effects.builtin _ _ _ _ _ _›
  case body =>
    have bound := bind_external ‹bindArguments _ _ _ _ = some (_, _)›
    simp_all only
  case assign =>
    have written := assign_external ‹assignResult _ _ _ _ = .value _›
    simp_all only
  case assembly => exact preserved.assembly ‹effects.assembly _ _ _ _ _ _›
  case revert => exact preserved.revert ‹effects.revert _ _ _ _›

end Solcore.Frontend.RustHull.EffectProjectionPreservation
