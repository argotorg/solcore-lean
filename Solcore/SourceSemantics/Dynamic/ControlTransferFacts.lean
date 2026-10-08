import Solcore.SourceSemantics.Dynamic.Control

/-! Pure control-summary adapters for the original Source preservation cores.
Returned values retain their existing typing contract. This sidecar records
ordinary completion and the two loop transfers; it does not classify runtime
faults or assign a fault token. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Dynamic
open Frontend SourceInference TypeSystem

namespace ControlOutcome

def NoEscapedControl (outcome : ControlOutcome) : Prop :=
  (∀ environment, outcome ≠ .breaking environment) ∧
  (∀ environment, outcome ≠ .continuing environment)

theorem NoEscapedControl.fallthrough (environment : Environment) :
    NoEscapedControl (.fallthrough environment) := by
  constructor <;> intro other equal <;> cases equal

theorem NoEscapedControl.returned (value : Value) :
    NoEscapedControl (.returned value) := by
  constructor <;> intro other equal <;> cases equal

theorem NoEscapedControl.restore {outcome : ControlOutcome}
    (closed : NoEscapedControl outcome) (outer : Environment) :
    NoEscapedControl (restoreControl outer outcome) := by
  cases outcome <;> simp_all [NoEscapedControl, restoreControl]

end ControlOutcome

namespace ControlSummary

def AllowsTransfers (summary : SourceSemantics.ControlSummary)
    (outcome : ControlOutcome) : Prop :=
  match outcome with
  | .fallthrough _ => summary.canFallthrough = true
  | .breaking _ => summary.mayBreak = true
  | .continuing _ => summary.mayContinue = true
  | .returned _ | .fault _ => True

theorem AllowsTransfers.canFallthrough
    {summary : SourceSemantics.ControlSummary} {outcome : ControlOutcome}
    (allowed : AllowsTransfers summary outcome)
    (falls : outcome.IsFallthrough) : summary.canFallthrough = true := by
  cases falls
  exact allowed

theorem AllowsTransfers.noEscape
    {summary : SourceSemantics.ControlSummary} {outcome : ControlOutcome}
    (allowed : AllowsTransfers summary outcome)
    (noBreak : summary.mayBreak = false)
    (noContinue : summary.mayContinue = false) :
    outcome.NoEscapedControl := by
  constructor
  · intro environment equal
    subst outcome
    simp [AllowsTransfers, noBreak] at allowed
  · intro environment equal
    subst outcome
    simp [AllowsTransfers, noContinue] at allowed

theorem AllowsTransfers.noEscape_of_complete
    {facts : BodyFacts} {expected : Ty} {outcome : ControlOutcome}
    (allowed : AllowsTransfers facts.control outcome)
    (complete : BodyCompletes expected facts) : outcome.NoEscapedControl :=
  allowed.noEscape complete.1 complete.2.1

theorem AllowsTransfers.noEscape_of_cons_complete
    {head : StatementFacts} {tail : BodyFacts} {expected : Ty}
    {outcome : ControlOutcome}
    (allowed : AllowsTransfers head.control outcome)
    (complete : BodyCompletes expected (.cons head tail)) :
    outcome.NoEscapedControl := by
  apply allowed.noEscape
  · exact (Bool.or_eq_false_iff.mp complete.1).1
  · exact (Bool.or_eq_false_iff.mp complete.2.1).1

theorem allows_of_noEscape {summary : SourceSemantics.ControlSummary}
    {outcome : ControlOutcome} (closed : outcome.NoEscapedControl)
    (falls : outcome.IsFallthrough → summary.canFallthrough = true) :
    AllowsTransfers summary outcome := by
  cases outcome with
  | fallthrough environment => exact falls (.intro environment)
  | returned | fault => exact True.intro
  | breaking environment => exact (closed.1 environment rfl).elim
  | continuing environment => exact (closed.2 environment rfl).elim

theorem AllowsTransfers.restore
    {summary : SourceSemantics.ControlSummary} {outcome : ControlOutcome}
    (allowed : AllowsTransfers summary outcome) (outer : Environment) :
    AllowsTransfers summary (restoreControl outer outcome) := by
  cases outcome <;> simp_all only [AllowsTransfers, restoreControl]

theorem AllowsTransfers.eraseValue
    {summary : SourceSemantics.ControlSummary} {outcome : ControlOutcome}
    (allowed : AllowsTransfers summary outcome) :
    AllowsTransfers summary.eraseValue outcome := by
  cases outcome with
  | fallthrough => exact ControlSummary.eraseValue_canFallthrough allowed
  | returned | fault => exact True.intro
  | breaking | continuing => exact allowed

theorem AllowsTransfers.branches_left
    {left right : SourceSemantics.ControlSummary} {outcome : ControlOutcome}
    (allowed : AllowsTransfers left outcome) :
    AllowsTransfers (left.branches right) outcome := by
  cases outcome with
  | fallthrough => exact ControlSummary.branches_canFallthrough_left allowed
  | returned | fault => exact True.intro
  | breaking => simp [AllowsTransfers, SourceSemantics.ControlSummary.branches,
      show left.mayBreak = true from allowed]
  | continuing => simp [AllowsTransfers, SourceSemantics.ControlSummary.branches,
      show left.mayContinue = true from allowed]

theorem AllowsTransfers.branches_right
    {left right : SourceSemantics.ControlSummary} {outcome : ControlOutcome}
    (allowed : AllowsTransfers right outcome) :
    AllowsTransfers (left.branches right) outcome := by
  cases outcome with
  | fallthrough => exact ControlSummary.branches_canFallthrough_right allowed
  | returned | fault => exact True.intro
  | breaking => simp [AllowsTransfers, SourceSemantics.ControlSummary.branches,
      show right.mayBreak = true from allowed]
  | continuing => simp [AllowsTransfers, SourceSemantics.ControlSummary.branches,
      show right.mayContinue = true from allowed]

theorem AllowsTransfers.sequence
    {head tail : SourceSemantics.ControlSummary} {outcome : ControlOutcome}
    (allowed : AllowsTransfers tail outcome)
    (headFalls : head.canFallthrough = true) :
    AllowsTransfers (head.sequence tail) outcome := by
  cases outcome with
  | fallthrough => exact ControlSummary.sequence_canFallthrough headFalls allowed
  | returned | fault => exact True.intro
  | breaking => simp [AllowsTransfers, SourceSemantics.ControlSummary.sequence,
      headFalls, show tail.mayBreak = true from allowed]
  | continuing => simp [AllowsTransfers, SourceSemantics.ControlSummary.sequence,
      headFalls, show tail.mayContinue = true from allowed]

theorem AllowsTransfers.sequence_terminal
    {head tail : SourceSemantics.ControlSummary} {outcome : ControlOutcome}
    (allowed : AllowsTransfers head outcome) (terminal : TerminalControl outcome) :
    AllowsTransfers (head.sequence tail) outcome := by
  cases terminal with
  | returned | fault => exact True.intro
  | breaking => simp [AllowsTransfers, SourceSemantics.ControlSummary.sequence,
      show head.mayBreak = true from allowed]
  | continuing => simp [AllowsTransfers, SourceSemantics.ControlSummary.sequence,
      show head.mayContinue = true from allowed]

end ControlSummary

namespace MergeBodyControls

theorem allows_of_mem
    {facts : List BodyFacts} {fallback : Option BodyFacts}
    {summary : SourceSemantics.ControlSummary} {selected : BodyFacts}
    {outcome : ControlOutcome}
    (merged : mergeBodyControls facts fallback = some summary)
    (member : selected ∈ facts)
    (allowed : ControlSummary.AllowsTransfers selected.control outcome) :
    ControlSummary.AllowsTransfers summary outcome := by
  induction facts generalizing summary with
  | nil => simp at member
  | cons head tail induction =>
    simp only [List.mem_cons] at member
    cases tailMerged : mergeBodyControls tail fallback with
    | none =>
      simp only [mergeBodyControls, tailMerged, Option.some.injEq] at merged
      subst summary
      rcases member with rfl | member
      · exact allowed
      · cases tail with
        | nil => simp at member
        | cons next rest =>
          cases restMerged : mergeBodyControls rest fallback <;>
            simp [mergeBodyControls, restMerged] at tailMerged
    | some tailSummary =>
      simp only [mergeBodyControls, tailMerged, Option.some.injEq] at merged
      subst summary
      rcases member with rfl | member
      · exact allowed.branches_left
      · exact (induction tailMerged member).branches_right

theorem allows_of_fallback
    {facts : List BodyFacts} {summary : SourceSemantics.ControlSummary}
    {fallback : BodyFacts} {outcome : ControlOutcome}
    (merged : mergeBodyControls facts (some fallback) = some summary)
    (allowed : ControlSummary.AllowsTransfers fallback.control outcome) :
    ControlSummary.AllowsTransfers summary outcome := by
  induction facts generalizing summary with
  | nil =>
    simp only [mergeBodyControls, Option.some.injEq] at merged
    subst summary
    exact allowed
  | cons head tail induction =>
    cases tailMerged : mergeBodyControls tail (some fallback) with
    | none =>
      cases tail with
      | nil => simp [mergeBodyControls] at tailMerged
      | cons next rest =>
        cases restMerged : mergeBodyControls rest (some fallback) <;>
          simp [mergeBodyControls, restMerged] at tailMerged
    | some tailSummary =>
      simp only [mergeBodyControls, tailMerged, Option.some.injEq] at merged
      subst summary
      exact (induction tailMerged).branches_right

end MergeBodyControls
end Solcore.SourceSemantics.Dynamic
