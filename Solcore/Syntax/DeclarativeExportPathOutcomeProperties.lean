import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeExportPathOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for maximal export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A maximal dotted export-path tail has one final cursor. -/
theorem ExportPathTailParses.output_unique :
    ∀ {tokens : Array Token} {endIndex cursor : Nat}
      {leftComponents rightComponents : List Syntax.Identifier}
      {leftFinish rightFinish : Nat},
      ExportPathTailParses tokens endIndex cursor leftComponents leftFinish →
      ExportPathTailParses tokens endIndex cursor rightComponents rightFinish →
      leftFinish = rightFinish := by
  intro tokens endIndex cursor leftComponents rightComponents leftFinish
    rightFinish leftParsed
  induction leftParsed generalizing rightComponents rightFinish with
  | done cursor stopped =>
      intro rightParsed
      cases rightParsed with
      | done => rfl
      | next dotSpan dotToken componentToken tail =>
          exact False.elim (stopped ⟨dotSpan, _, _, dotToken,
            componentToken⟩)
  | next dotSpan dotToken componentToken tail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | done cursor stopped =>
          exact False.elim (stopped ⟨dotSpan, _, _, dotToken,
            componentToken⟩)
      | next rightDotSpan rightDotToken rightComponentToken rightTail =>
          exact inductionHypothesis rightTail

/-- Maximal export paths have one final remainder. -/
theorem ExportPathParses.output_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportPathParses input left afterLeft)
    (rightParsed : ExportPathParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftTokens, leftEndIndex, leftFirst, leftTail, leftSpan⟩
  rcases rightParsed with
    ⟨rightTokens, rightEndIndex, rightFirst, rightTail, rightSpan⟩
  have cursorEq := ExportPathTailParses.output_unique leftTail rightTail
  cases input
  cases afterLeft
  cases afterRight
  simp_all

/-- First-identifier rejection excludes every maximal export-path success. -/
theorem ExportPathRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ExportPathRejects input rejected) :
    ¬ ∃ path output, ExportPathOrdinaryParses input path output := by
  rintro ⟨path, output, parsed⟩
  cases rejection with
  | firstRejected identifierRejected =>
      unfold ExportPathOrdinaryParses ExportPathParses at parsed
      have firstParsed : IdentifierParses input path.value.components.head
          { input with cursor := input.cursor + 1 } :=
        ⟨parsed.2.2.1, rfl, rfl, rfl⟩
      exact identifierDeterministicOutcomeSpec.successRejectDisjoint
        identifierRejected ⟨_, _, firstParsed⟩

/-- Maximal export paths have deterministic and exclusive broad outcomes. -/
theorem exportPathDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExportPathOrdinaryParses ExportPathRejects where
  successOutputUnique := ExportPathParses.output_unique
  successRejectDisjoint := ExportPathRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
