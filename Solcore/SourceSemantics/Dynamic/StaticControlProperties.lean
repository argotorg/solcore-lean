import Solcore.SourceSemantics.Static
import Solcore.SourceSemantics.Dynamic.ControlProperties

/-!
Control realizability for summaries produced by source typing.

`ControlSummary` and `BodyFacts` remain forgeable data.  Static typing is the
boundary that rules out an empty summary with no ordinary or non-local
outcome.  Function-body preservation uses this fact when execution reaches the
tail of a statically complete sequence.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

private theorem mergeBodyControls_hasOutcome
    {facts : List BodyFacts} {fallback : Option BodyFacts}
    {summary : ControlSummary}
    (merged : mergeBodyControls facts fallback = some summary)
    (facts_outcome : ∀ fact, fact ∈ facts → fact.control.HasOutcome)
    (fallback_outcome : ∀ fact, fallback = some fact →
      fact.control.HasOutcome) :
    summary.HasOutcome := by
  induction facts with
  | nil =>
      cases fallback with
      | none => simp [mergeBodyControls] at merged
      | some fact =>
          simp only [mergeBodyControls, Option.some.injEq] at merged
          subst summary
          exact fallback_outcome fact rfl
  | cons head tail induction =>
      have head_outcome := facts_outcome head (by simp)
      cases tail_merged : mergeBodyControls tail fallback with
      | none =>
          simp only [mergeBodyControls, tail_merged, Option.some.injEq] at merged
          subst summary
          exact head_outcome
      | some tailSummary =>
          simp only [mergeBodyControls, tail_merged, Option.some.injEq] at merged
          subst summary
          exact head_outcome.branches_left

/-- Every statement sequence admitted by source typing denotes at least one
possible ordinary or non-local outcome.  The proof uses the generated mutual
recursor so nested blocks, conditionals, and match arms contribute their
induction hypotheses without imposing a non-structural proof recursion. -/
theorem StatementsHaveType.controlHasOutcome
    {source : Frontend.SourceInference.TypedSource}
    {control : ControlContext} {context finalContext : Context}
    {statements : List Frontend.SourceInference.StatementId}
    {facts : BodyFacts}
    (typing : StatementsHaveType source control context statements finalContext
      facts) :
    facts.control.HasOutcome := by
  apply StatementsHaveType.rec (source := source) (t := typing)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True)
    (motive_8 := fun _ _ _ _ facts _ => facts.control.HasOutcome)
    (motive_9 := fun _ _ _ _ facts _ => facts.control.HasOutcome)
    (motive_10 := fun _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ facts _ => facts.control.HasOutcome)
    (motive_13 := fun _ _ _ _ facts _ =>
      ∀ fact, fact ∈ facts → fact.control.HasOutcome)
  all_goals try { intros; exact True.intro }
  case letUninitialized =>
    intros
    exact ControlSummary.hasOutcome_ordinary .unit
  case letInitialized =>
    intros
    exact ControlSummary.hasOutcome_ordinary .unit
  case letInitializedGeneralized =>
    intros
    exact ControlSummary.hasOutcome_ordinary .unit
  case returnUnit =>
    intros
    exact ControlSummary.hasOutcome_returned
  case returnValue =>
    intros
    exact ControlSummary.hasOutcome_returned
  case expressionValue =>
    intros
    exact ControlSummary.hasOutcome_ordinary _
  case expressionDiscard =>
    intros
    exact ControlSummary.hasOutcome_ordinary .unit
  case assignValue =>
    intros
    exact ControlSummary.hasOutcome_ordinary .unit
  case assignBitNot =>
    intros
    exact ControlSummary.hasOutcome_ordinary .unit
  case ifWithoutElse =>
    intros
    exact (ControlSummary.hasOutcome_ordinary .unit).branches_right
  case ifWithElse =>
    intros
    apply ControlSummary.HasOutcome.branches_left
    assumption
  case block =>
    intros
    apply ControlSummary.HasOutcome.eraseValue
    assumption
  case matchWithoutDefault =>
    intros
    apply ControlSummary.HasOutcome.eraseValue
    apply mergeBodyControls_hasOutcome
    · assumption
    · assumption
    · intro fact impossible
      simp at impossible
  case matchWithDefault =>
    intros
    apply ControlSummary.HasOutcome.eraseValue
    apply mergeBodyControls_hasOutcome
    · assumption
    · assumption
    · intro fact equality
      injection equality with fact_eq
      subst fact
      assumption
  case forLoop =>
    intros
    exact ControlSummary.hasOutcome_loop _
  case whileLoop =>
    intros
    exact ControlSummary.hasOutcome_loop _
  case breakStmt =>
    intros
    exact ControlSummary.hasOutcome_breaking
  case continueStmt =>
    intros
    exact ControlSummary.hasOutcome_continuing
  case nil =>
    intros
    exact BodyFacts.empty_hasOutcome
  case singleton =>
    intros
    apply BodyFacts.singleton_hasOutcome
    assumption
  case cons =>
    intros
    apply BodyFacts.cons_hasOutcome <;> assumption
  case intro =>
    intros
    assumption
  case nil =>
    simp
  case cons =>
    intro control' context' scrutineeType matchCase cases headFacts tailFacts
      head tail head_outcome tail_outcome fact member
    simp only [List.mem_cons] at member
    rcases member with equality | member
    · subst fact
      exact head_outcome
    · exact tail_outcome fact member

end Solcore.SourceSemantics
