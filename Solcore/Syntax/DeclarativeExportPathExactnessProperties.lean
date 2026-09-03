import Solcore.Syntax.DeclarativeExportPathOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact maximal export-path components, covering spans, and rejection endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A maximal dotted export tail fixes every source-order identifier component. -/
theorem ExportPathTailParses.value_unique :
    ∀ {tokens : Array Token} {endIndex cursor : Nat}
      {left right : List Syntax.Identifier} {leftFinish rightFinish : Nat},
      ExportPathTailParses tokens endIndex cursor left leftFinish →
      ExportPathTailParses tokens endIndex cursor right rightFinish → left = right := by
  intro tokens endIndex cursor left right leftFinish rightFinish leftParsed
  induction leftParsed generalizing right rightFinish with
  | done cursor leftStopped =>
      intro rightParsed
      cases rightParsed with
      | done => rfl
      | next rightDotSpan rightDot rightComponent rightTail =>
          exact False.elim (leftStopped ⟨_, _, _, rightDot, rightComponent⟩)
  | @next cursor finish component components leftDotSpan leftDot leftComponent leftTail ih =>
      intro rightParsed
      cases rightParsed with
      | done cursor rightStopped =>
          exact False.elim (rightStopped ⟨_, _, _, leftDot, leftComponent⟩)
      | @next _ rightFinish rightComponent rightComponents _ _ rightToken rightTail =>
          have tokenEq := leftComponent.token_unique rightToken
          have componentEq : component = rightComponent := by
            cases component
            cases rightComponent
            simp_all
          cases componentEq
          cases ih rightTail
          rfl

/-- The first token and maximal tail fix the complete located export path. -/
theorem ExportPathParses.value_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportPathParses input left afterLeft)
    (rightParsed : ExportPathParses input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftTokens, leftEndIndex, leftFirst, leftTail, leftSpan⟩
  rcases rightParsed with ⟨rightTokens, rightEndIndex, rightFirst, rightTail, rightSpan⟩
  have firstEq := leftFirst.token_unique rightFirst
  have tailEq := leftTail.value_unique rightTail
  rcases left with ⟨leftSpan, ⟨⟨leftHead, leftRest⟩⟩⟩
  rcases right with ⟨rightSpan, ⟨⟨rightHead, rightRest⟩⟩⟩
  cases leftHead
  cases rightHead
  simp_all

/-- An export path fixes its complete AST and final declarative remainder. -/
theorem ExportPathParses.result_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportPathParses input left afterLeft)
    (rightParsed : ExportPathParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- First-identifier rejection fixes the complete export-path failure endpoint. -/
theorem ExportPathRejects.output_unique {input left right : Remainder}
    (leftRejected : ExportPathRejects input left)
    (rightRejected : ExportPathRejects input right) : left = right := by
  cases leftRejected with
  | firstRejected leftIdentifier =>
      cases rightRejected with
      | firstRejected rightIdentifier => exact leftIdentifier.output_unique rightIdentifier

/-- Export paths have exact located components and rejecting endpoints. -/
theorem exportPathExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExportPathOrdinaryParses ExportPathRejects where
  toDeterministicOutcomeSpec := exportPathDeterministicOutcomeSpec
  successValueUnique := ExportPathParses.value_unique
  rejectOutputUnique := ExportPathRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
