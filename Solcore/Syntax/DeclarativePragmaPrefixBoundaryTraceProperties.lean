import Solcore.Syntax.DeclarativePragmaPrefixBoundaryTraceGrammar
import Solcore.Syntax.DeclarativePragmaSequenceTraceProperties
import Solcore.Syntax.DeclarativePragmaRejectionTraceProperties

/-! Exact prefix order, stopping position, and protected pre-failure events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The stopping boundary stays inside the original carrier and active window. -/
theorem PragmaPrefixBoundaryTraceParses.carrier_stop
    {source : SourceId} {endByte : Nat} {input stopped : Remainder}
    {declarations : List Syntax.PragmaDecl} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses source endByte input
      declarations stopped diagnostic trace) :
    stopped.tokens = input.tokens ∧ stopped.endIndex = input.endIndex ∧
      input.cursor ≤ stopped.cursor ∧ stopped.cursor < input.endIndex := by
  induction parsed with
  | stopped marker recognized rejected =>
      exact ⟨rfl, rfl, Nat.le_refl _, recognized.1.1⟩
  | cons head tail ih =>
      have shape := head.1.carrier_progress
      exact ⟨ih.1.trans shape.1, ih.2.1.trans shape.2.1,
        by have advance := shape.2.2.1; have monotone := ih.2.2.1; omega,
        by simpa only [shape.2.1] using ih.2.2.2⟩

/-- Every successful prefix item consumes tokens, and the final recognized
marker requires another remaining token even when its declaration rejects. -/
theorem PragmaPrefixBoundaryTraceParses.length_lt_remaining
    {source : SourceId} {endByte : Nat} {input stopped : Remainder}
    {declarations : List Syntax.PragmaDecl} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses source endByte input
      declarations stopped diagnostic trace) :
    declarations.length < input.endIndex - input.cursor := by
  induction parsed with
  | stopped marker recognized rejected =>
      have inside := recognized.1.1
      simp only [List.length_nil]
      omega
  | cons head tail ih =>
      have shape := head.1.carrier_progress
      simp only [List.length_cons]
      omega

/-- Input and report context uniquely determine the complete successful
prefix, rewound stopping position, uncommitted report, and preceding events. -/
theorem PragmaPrefixBoundaryTraceParses.result_unique
    {source : SourceId} {endByte : Nat} {input leftStop rightStop : Remainder}
    {left right : List Syntax.PragmaDecl} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaPrefixBoundaryTraceParses source endByte input
      left leftStop leftReport leftTrace)
    (rightParsed : PragmaPrefixBoundaryTraceParses source endByte input
      right rightStop rightReport rightTrace) :
    left = right ∧ leftStop = rightStop ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightStop rightReport rightTrace with
  | stopped marker recognized rejected =>
      cases rightParsed with
      | stopped rightMarker rightRecognized rightRejected =>
          rcases rejected.result_unique rightRejected with ⟨_, report, events⟩
          exact ⟨rfl, rfl, report, events⟩
      | cons head tail =>
          exact False.elim (pragmaDeclExactOutcomeSpec.successRejectDisjoint
            rejected.ordinary ⟨_, _, head.1⟩)
  | cons head tail ih =>
      cases rightParsed with
      | stopped marker recognized rejected =>
          exact False.elim (pragmaDeclExactOutcomeSpec.successRejectDisjoint
            rejected.ordinary ⟨_, _, head.1⟩)
      | cons rightHead rightTail =>
          rcases head.result_unique rightHead with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every event preceding the final report is protected from lexical cascade
filtering; this deliberately makes no such claim about the report itself. -/
theorem PragmaPrefixBoundaryTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input stopped : Remainder}
    {declarations : List Syntax.PragmaDecl} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses source endByte input
      declarations stopped diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | stopped marker recognized rejected => exact rejected.cascadeFilters text lexical
  | cons head tail ih => exact (head.cascadeFilters text lexical).append ih

end Solcore.Syntax.DeclarativeGrammar
