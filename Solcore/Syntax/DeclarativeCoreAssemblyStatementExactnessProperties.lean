import Solcore.Syntax.DeclarativeCoreAssemblyStatementOutcomeProperties
import Solcore.Syntax.DeclarativeYulBodyExactnessProperties

/-! Exact Core assembly statements from unconditional inline-Yul body outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An assembly marker and Yul body fix the full embedded Core statement. -/
theorem AssemblyStatementOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssemblyStatementOrdinaryParses input left afterLeft)
    (rightParsed : AssemblyStatementOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases leftBody.result_unique rightBody with ⟨spanEq, bodyEq, outputEq⟩
          subst spanEq
          subst bodyEq
          rfl

/-- Ordinary assembly success fixes its complete AST and final remainder. -/
theorem AssemblyStatementOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssemblyStatementOrdinaryParses input left afterLeft)
    (rightParsed : AssemblyStatementOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Assembly rejection fixes the missing-marker or first Yul-body failure endpoint. -/
theorem AssemblyStatementRejects.output_unique
    {input left right : Remainder}
    (leftRejected : AssemblyStatementRejects input left)
    (rightRejected : AssemblyStatementRejects input right) : left = right := by
  cases leftRejected with
  | markerMissing leftAbsent =>
      cases rightRejected with
      | markerMissing => rfl
      | bodyRejected rightSpan rightMarker rightBody =>
          exact False.elim (leftAbsent ⟨_, rightMarker.1⟩)
  | bodyRejected leftSpan leftMarker leftBody =>
      cases rightRejected with
      | markerMissing rightAbsent =>
          exact False.elim (rightAbsent ⟨_, leftMarker.1⟩)
      | bodyRejected rightSpan rightMarker rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          exact leftBody.output_unique rightBody

/-- Independent Yul recursion discharges every Core assembly exactness premise. -/
theorem assemblyStatementExactOutcomeSpec :
    ExactDeterministicOutcomeSpec AssemblyStatementOrdinaryParses
      AssemblyStatementRejects where
  toDeterministicOutcomeSpec := assemblyStatementDeterministicOutcomeSpec
  successValueUnique := AssemblyStatementOrdinaryParses.value_unique
  rejectOutputUnique := AssemblyStatementRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
