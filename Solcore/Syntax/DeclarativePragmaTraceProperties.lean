import Solcore.Syntax.DeclarativePragmaTraceGrammar
import Solcore.Syntax.DeclarativeIdentifierTraceProperties
import Solcore.Syntax.DeclarativePragmaExactnessProperties
import Solcore.Syntax.DeclarativePragmaItemsExactnessProperties

/-! Exact event order and functional successful pragma traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every written identifier list determines a complete event sequence. -/
theorem identifierListDiagnosticTrace_total (names : List Syntax.Identifier) :
    ∃ trace, IdentifierListDiagnosticTrace names trace := by
  induction names with
  | nil => exact ⟨[], .nil⟩
  | cons name names ih =>
      rcases identifierDiagnosticTrace_total name with ⟨head, headTrace⟩
      rcases ih with ⟨tail, tailTrace⟩
      exact ⟨head ++ tail, .cons headTrace tailTrace⟩

/-- Ordered per-name emission fixes the complete trace including duplicates. -/
theorem IdentifierListDiagnosticTrace.trace_unique
    {names : List Syntax.Identifier} {left right : List ParseDiagnostic}
    (leftTrace : IdentifierListDiagnosticTrace names left)
    (rightTrace : IdentifierListDiagnosticTrace names right) : left = right := by
  induction leftTrace generalizing right with
  | nil => cases rightTrace; rfl
  | cons leftHead leftTail ih =>
      cases rightTrace with
      | cons rightHead rightTail =>
          rw [leftHead.trace_unique rightHead, ih rightTail]

/-- Joining two written name sequences appends their event sequences. -/
theorem IdentifierListDiagnosticTrace.append
    {leftNames rightNames : List Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : IdentifierListDiagnosticTrace leftNames leftTrace)
    (right : IdentifierListDiagnosticTrace rightNames rightTrace) :
    IdentifierListDiagnosticTrace (leftNames ++ rightNames) (leftTrace ++ rightTrace) := by
  induction left with
  | nil => exact right
  | cons head tail ih =>
      simpa only [List.cons_append, List.append_assoc] using
        IdentifierListDiagnosticTrace.cons head ih

/-- The exact tail grammar fixes its full suffix, endpoint, and added trace. -/
theorem PragmaItemsTailTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaItemsTailTraceParses input left afterLeft leftTrace)
    (rightParsed : PragmaItemsTailTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases pragmaItemsTailExactOutcomeSpec.successResultUnique leftParsed.1
    rightParsed.1 with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, leftParsed.2.trace_unique rightParsed.2⟩

/-- The complete item grammar fixes all names and their diagnostic order. -/
theorem PragmaItemsTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaItemsTraceParses input left afterLeft leftTrace)
    (rightParsed : PragmaItemsTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases pragmaItemsExactOutcomeSpec.successResultUnique leftParsed.1
    rightParsed.1 with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, leftParsed.2.trace_unique rightParsed.2⟩

/-- A pragma's exact AST fixes only its checked-item diagnostic sequence. -/
theorem PragmaDeclTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.PragmaDecl}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaDeclTraceParses input left afterLeft leftTrace)
    (rightParsed : PragmaDeclTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases pragmaDeclExactOutcomeSpec.successResultUnique leftParsed.1
    rightParsed.1 with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, leftParsed.2.trace_unique rightParsed.2⟩

end Solcore.Syntax.DeclarativeGrammar
