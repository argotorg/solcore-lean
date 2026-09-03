import Solcore.Syntax.Parser.PragmaNameRejectionTraceProperties

/-! Independent missing-name witnesses, including window-end, wrong-token,
and unavailable-carrier branches, determine exact silent pragma rejection. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaNameRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar

example := @PragmaNameMissingAt.rejects
example := @peekKind_eq_pragma_of_exactTokenParses
example := @pragmaKeyword_eq_ok_of_exactTokenParses
example := @atTopItemStart_eq_true_of_pragmaToken
example := @plainTopItem_eq_pragma_of_exactTokenParses
example := @topItem_eq_pragma_of_exactTokenParses
example := @pragmaDecl_nameMissing_exact
example := @pragmaDecl_nameMissingAt_exact
example := @plainTopItem_pragmaNameMissing_exact
example := @topItem_pragmaNameMissing_exact
example := @parseItemsItem_pragmaNameMissing_exact
example := @parseItemsItem_pragmaNameMissingAt_exact

private def pragmaFile : SourceFile := {
  id := { origin := .main, path := "missing-pragma-name.sol" }
  content := "pragma"
}

private def markerSpan : SourceSpan := SourceSpan.fullFile pragmaFile

private def endSpan : SourceSpan := {
  source := pragmaFile.id, startByte := 6, endByte := 6
}

private def eofInput (priorRev : List ParseDiagnostic) : State := {
  file := pragmaFile
  tokens := #[{ span := markerSpan, value := .keyword .pragmaKw }]
  cursor := 0
  window := { endIndex := 1, endByte := 6 }
  diagnosticsRev := priorRev
}

private theorem eofMissing (priorRev : List ParseDiagnostic) :
    PragmaNameMissingAt pragmaFile.id 6 (eofInput priorRev).declarativeRemainder
      { (eofInput priorRev).declarativeRemainder with cursor := 1 } endSpan none := by
  apply PragmaNameMissingAt.missing (marker := markerSpan)
  · simp [ExactTokenParses, TokenAt, State.declarativeRemainder, eofInput]
  · simp [IdentifierAbsentAt, TokenAt, State.declarativeRemainder, eofInput]
  · exact .windowEnd (by simp [State.declarativeRemainder, eofInput])

/-- End-of-window uses the supplied end byte, retains only the marker step,
and does not commit its unexpected report into the raw diagnostic sequence. -/
theorem eof_exact (priorRev : List ParseDiagnostic) :
    parseItemsItem (eofInput priorRev) = .reject {
        span := endSpan, found := none,
        expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { eofInput priorRev with cursor := 1 } ∧
      ({ eofInput priorRev with cursor := 1 } : State).diagnostics = priorRev.reverse := by
  have result := parseItemsItem_pragmaNameMissingAt_exact (input := eofInput priorRev)
    (eofMissing priorRev)
  exact ⟨result.1, result.2.2⟩

private def wrongSpan : SourceSpan := {
  source := pragmaFile.id, startByte := 7, endByte := 8
}

private def wrongInput (priorRev : List ParseDiagnostic) : State := {
  eofInput priorRev with
  file := { pragmaFile with content := "pragma ;" }
  tokens := #[{ span := markerSpan, value := .keyword .pragmaKw },
    { span := wrongSpan, value := .symbol .semicolon }]
  window := { endIndex := 2, endByte := 8 }
}

private theorem wrongMissing (priorRev : List ParseDiagnostic) :
    PragmaNameMissingAt pragmaFile.id 8 (wrongInput priorRev).declarativeRemainder
      { (wrongInput priorRev).declarativeRemainder with cursor := 1 }
      wrongSpan (some (.symbol .semicolon)) := by
  apply PragmaNameMissingAt.missing (marker := markerSpan)
  · simp [ExactTokenParses, TokenAt, State.declarativeRemainder, wrongInput, eofInput]
  · simp [IdentifierAbsentAt, TokenAt, State.declarativeRemainder, wrongInput, eofInput]
  · apply CurrentInputAt.token (current := { span := wrongSpan, value := .symbol .semicolon })
    simp [TokenAt, State.declarativeRemainder, wrongInput, eofInput]

/-- A present non-identifier keeps its own exact span and found kind; it is
not replaced by the enclosing source's end-of-input report. -/
theorem semicolon_exact (priorRev : List ParseDiagnostic) :
    pragmaDecl (wrongInput priorRev) = .reject {
        span := wrongSpan, found := some (.symbol .semicolon),
        expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { wrongInput priorRev with cursor := 1 } ∧
      ({ wrongInput priorRev with cursor := 1 } : State).diagnostics = priorRev.reverse := by
  have result := pragmaDecl_nameMissingAt_exact (input := wrongInput priorRev)
    (wrongMissing priorRev)
  exact ⟨result.1, result.2.2⟩

private def unavailableInput (priorRev : List ParseDiagnostic) : State := {
  eofInput priorRev with window := { endIndex := 2, endByte := 6 }
}

private theorem unavailableMissing (priorRev : List ParseDiagnostic) :
    PragmaNameMissingAt pragmaFile.id 6 (unavailableInput priorRev).declarativeRemainder
      { (unavailableInput priorRev).declarativeRemainder with cursor := 1 }
      endSpan none := by
  apply PragmaNameMissingAt.missing (marker := markerSpan)
  · simp [ExactTokenParses, TokenAt, State.declarativeRemainder, unavailableInput, eofInput]
  · simp [IdentifierAbsentAt, TokenAt, State.declarativeRemainder, unavailableInput, eofInput]
  · apply CurrentInputAt.missingToken
    · simp [State.declarativeRemainder, unavailableInput, eofInput]
    · simp [State.declarativeRemainder, unavailableInput, eofInput]

/-- No validity assumption is silently introduced: an unavailable carrier
inside the supplied window has the exact same empty end-byte observation. -/
theorem unavailableCarrier_exact (priorRev : List ParseDiagnostic) :
    parseItemsItem (unavailableInput priorRev) = .reject {
        span := endSpan, found := none,
        expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { unavailableInput priorRev with cursor := 1 } ∧
      ({ unavailableInput priorRev with cursor := 1 } : State).diagnostics = priorRev.reverse := by
  have result := parseItemsItem_pragmaNameMissingAt_exact (input := unavailableInput priorRev)
    (unavailableMissing priorRev)
  exact ⟨result.1, result.2.2⟩

end Solcore.Test.SyntaxParserPragmaNameRejectionTraceProperties
