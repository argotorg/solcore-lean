import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties

/-! Independent observation and exact uncommitted-diagnostic consumers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPrimitiveRejectionDiagnosticProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @currentInputAt_total
example := @CurrentInputAt.result_unique
example := @rejectAtReports_total
example := @RejectAtReports.diagnostic_unique
example := @currentInputAt_currentSpan_peekKind
example := @currentInputAt_iff_currentSpan_peekKind
example := @rejectAt_reject_reports
example := @rawIdentifier_eq_rejectAt_of_identifierAbsent
example := @identifier_eq_rejectAt_of_identifierAbsent

example (source : SourceId) (endByte : Nat) (input : Remainder)
    (atEnd : input.endIndex ≤ input.cursor) :
    CurrentInputAt source endByte input
      { source, startByte := endByte, endByte } none :=
  .windowEnd atEnd

example (source : SourceId) (endByte : Nat) (input : Remainder)
    (inside : input.cursor < input.endIndex)
    (missing : input.tokens[input.cursor]? = none) :
    CurrentInputAt source endByte input
      { source, startByte := endByte, endByte } none :=
  .missingToken inside missing

example {alpha : Type} {input : State}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    {diagnostic : ParseDiagnostic}
    (reported : RejectAtReports input.file.id input.window.endByte
      expected context input.declarativeRemainder diagnostic) :
    ∃ failure, rejectAt (α := alpha) input expected context =
      .reject failure input ∧ failure.toDiagnostic = diagnostic :=
  rejectAt_reports_iff.mp reported

example {alpha : Type} {input : State} {failure : Failure}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    {diagnostic : ParseDiagnostic}
    (result : rejectAt (α := alpha) input expected context = .reject failure input)
    (reportEq : failure.toDiagnostic = diagnostic) :
    RejectAtReports input.file.id input.window.endByte expected context
      input.declarativeRemainder diagnostic :=
  (rejectAt_reports_iff (alpha := alpha)).mpr ⟨failure, result, reportEq⟩

example (context : ParseContext) {input : State} {span : SourceSpan}
    {found : Option TokenKind}
    (absent : IdentifierAbsentAt input.declarativeRemainder)
    (observed : CurrentInputAt input.file.id input.window.endByte
      input.declarativeRemainder span found) :
    rawIdentifier context input = .reject {
      span, found, expected := { head := .identifier, tail := [] }, context
    } input := by
  rcases (rawIdentifier_reject_reports_iff context).mp
      ⟨absent, .reported observed⟩ with ⟨failure, result, reportEq⟩
  have payload : failure = {
      span, found, expected := { head := .identifier, tail := [] }, context
    } := Failure.toDiagnostic_injective reportEq
  simpa only [payload] using result

example (context : ParseContext) {input : State} {failure : Failure}
    {diagnostic : ParseDiagnostic}
    (result : rawIdentifier context input = .reject failure input)
    (reportEq : failure.toDiagnostic = diagnostic) :
    IdentifierAbsentAt input.declarativeRemainder ∧
      RejectAtReports input.file.id input.window.endByte
        { head := .identifier, tail := [] } context
        input.declarativeRemainder diagnostic :=
  (rawIdentifier_reject_reports_iff context).mpr ⟨failure, result, reportEq⟩

example (context : ParseContext) {input : State} {diagnostic : ParseDiagnostic}
    (absent : IdentifierAbsentAt input.declarativeRemainder)
    (reported : RejectAtReports input.file.id input.window.endByte
      { head := .identifier, tail := [] } context input.declarativeRemainder diagnostic) :
    ∃ failure, identifier context input = .reject failure input ∧
      failure.toDiagnostic = diagnostic :=
  (identifier_reject_reports_iff context).mp ⟨absent, reported⟩

example (context : ParseContext) {input : State} {failure : Failure}
    {diagnostic : ParseDiagnostic}
    (result : identifier context input = .reject failure input)
    (reportEq : failure.toDiagnostic = diagnostic) :
    IdentifierAbsentAt input.declarativeRemainder ∧
      RejectAtReports input.file.id input.window.endByte
        { head := .identifier, tail := [] } context
        input.declarativeRemainder diagnostic :=
  (identifier_reject_reports_iff context).mpr ⟨failure, result, reportEq⟩

example (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  rawIdentifier_reject_diagnostics_eq context result

example (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  identifier_reject_diagnostics_eq context result

end Solcore.Test.SyntaxParserPrimitiveRejectionDiagnosticProperties
