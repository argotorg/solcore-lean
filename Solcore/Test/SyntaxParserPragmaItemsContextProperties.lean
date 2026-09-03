import Solcore.Syntax.Parser.PragmaItemsContextProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Context-frame consumers include invalid windows, arbitrary accumulated
diagnostics, emitted hyphen events, and reports after ordinary rejection. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaItemsContextProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PragmaInternals
open Solcore.Syntax.DeclarativeGrammar

example := @identifier_success_context_eq
example := @identifier_reject_context_eq
example := @pragmaItemsTail_success_context_eq
example := @pragmaItemsTail_reject_context_eq
example := @pragmaItems_success_context_eq
example := @pragmaItems_reject_context_eq

/-- A later semicolon rejection can report under the original source/end-byte
context after any successful item scan. -/
theorem successfulItems_transport_report
    {input output : State} {items : List Identifier} {remainder : Remainder}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    {diagnostic : ParseDiagnostic}
    (result : pragmaItems input = .ok items output)
    (report : RejectAtReports output.file.id output.window.endByte
      expected context remainder diagnostic) :
    RejectAtReports input.file.id input.window.endByte
      expected context remainder diagnostic := by
  rcases pragmaItems_success_context_eq result with ⟨fileEq, windowEq⟩
  simpa only [fileEq, windowEq] using report

/-- A rejected suffix transports its uncommitted payload under the same
original source context, for arbitrary fuel and existing reverse items. -/
theorem rejectedTail_transport_report (fuel : Nat) (itemsRev : List Identifier)
    {input rejected : State} {failure : Failure} {diagnostic : ParseDiagnostic}
    (result : pragmaItemsTail fuel itemsRev input = .reject failure rejected)
    (report : RejectAtReports rejected.file.id rejected.window.endByte
      { head := .identifier, tail := [] } .pragmaDecl
      rejected.declarativeRemainder diagnostic) :
    RejectAtReports input.file.id input.window.endByte
      { head := .identifier, tail := [] } .pragmaDecl
      rejected.declarativeRemainder diagnostic := by
  rcases pragmaItemsTail_reject_context_eq fuel itemsRev result with ⟨fileEq, windowEq⟩
  simpa only [fileEq, windowEq] using report

private def exampleFile : SourceFile := {
  id := { origin := .main, path := "pragma-context-frame.sol" }, content := ""
}

private def exampleSpan (startByte endByte : Nat) : SourceSpan := {
  source := exampleFile.id, startByte, endByte
}

private def hyphenName : Identifier := { span := exampleSpan 0 3, value := "a-b" }

private def hyphenEvent : ParseDiagnostic := {
  span := hyphenName.span, kind := .invalidIdentifierHyphen hyphenName.value
}

private def exampleInput (last : Symbol) (priorRev : List ParseDiagnostic) : State := {
  file := exampleFile
  tokens := #[{ span := hyphenName.span, value := .identifier hyphenName.value },
    { span := exampleSpan 3 4, value := .symbol .comma },
    { span := exampleSpan 4 5, value := .symbol last }]
  cursor := 0
  window := { endIndex := 3, endByte := 999 }
  diagnosticsRev := priorRev
}

/-- This fixture really is invalid: context preservation does not silently
depend on validated source bounds or earlier diagnostic provenance. -/
theorem exampleFrame_invalid (last : Symbol) (priorRev : List ParseDiagnostic) :
    ¬ (exampleInput last priorRev).ValidFor := by
  intro valid
  have bound := valid.endByte_le_source
  change 999 ≤ 0 at bound
  omega

/-- A trailing comma succeeds after emitting a hyphen diagnostic while
retaining even the deliberately invalid full file/window context. -/
theorem success_keeps_invalid_frame (priorRev : List ParseDiagnostic) :
    ∃ output, pragmaItems (exampleInput .semicolon priorRev) = .ok [hyphenName] output ∧
      output.file = exampleFile ∧ output.window = { endIndex := 3, endByte := 999 } ∧
      output.diagnostics = priorRev.reverse ++ [hyphenEvent] := by
  let output : State := { (exampleInput .semicolon priorRev).emit hyphenEvent with cursor := 2 }
  have result : pragmaItems (exampleInput .semicolon priorRev) = .ok [hyphenName] output := rfl
  rcases pragmaItems_success_context_eq result with ⟨fileEq, windowEq⟩
  refine ⟨output, result, fileEq, windowEq, ?_⟩
  simp only [output, State.diagnostics, State.emit, exampleInput, List.reverse_cons]

/-- A later missing item rejects after the same emission and retains the
original context, including the unvalidated end byte and complete source file. -/
theorem rejection_keeps_invalid_frame (priorRev : List ParseDiagnostic) :
    ∃ rejected, pragmaItems (exampleInput .plus priorRev) = .reject {
        span := exampleSpan 4 5
        found := some (.symbol .plus)
        expected := { head := .identifier, tail := [] }
        context := .pragmaDecl
      } rejected ∧
      rejected.file = exampleFile ∧ rejected.window = { endIndex := 3, endByte := 999 } ∧
      rejected.diagnostics = priorRev.reverse ++ [hyphenEvent] := by
  let rejected : State := { (exampleInput .plus priorRev).emit hyphenEvent with cursor := 2 }
  have result : pragmaItems (exampleInput .plus priorRev) = .reject {
      span := exampleSpan 4 5, found := some (.symbol .plus),
      expected := { head := .identifier, tail := [] }, context := .pragmaDecl
    } rejected := rfl
  rcases pragmaItems_reject_context_eq result with ⟨fileEq, windowEq⟩
  refine ⟨rejected, result, fileEq, windowEq, ?_⟩
  simp only [rejected, State.diagnostics, State.emit, exampleInput, List.reverse_cons]

end Solcore.Test.SyntaxParserPragmaItemsContextProperties
