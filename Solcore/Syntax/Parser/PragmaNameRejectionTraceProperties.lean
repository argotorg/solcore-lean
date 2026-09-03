import Solcore.Syntax.DeclarativePragmaNameRejectionGrammar
import Solcore.Syntax.Parser.PragmaKeywordExecutionProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties

/-! An independently observed missing pragma name fixes the complete
uncommitted failure and preserves the existing raw diagnostic sequence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- After the exact pragma marker, an unavailable raw name fails at the
independently observed span/token. Only the marker cursor step is retained. -/
theorem pragmaDecl_nameMissing_exact
    {input : State} {marker span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after)
    (nameAbsent : DeclarativeGrammar.IdentifierAbsentAt after)
    (current : DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      after span found) :
    pragmaDecl input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  let advanced : State := { input with cursor := input.cursor + 1 }
  have advancedEq : advanced.declarativeRemainder = after := keywordParsed.2.symm
  have absent : DeclarativeGrammar.IdentifierAbsentAt advanced.declarativeRemainder := by
    simpa only [advancedEq] using nameAbsent
  have observed : DeclarativeGrammar.CurrentInputAt advanced.file.id advanced.window.endByte
      advanced.declarativeRemainder span found := by
    simpa only [advancedEq] using current
  rcases currentInputAt_iff_currentSpan_peekKind.mp observed with ⟨spanEq, foundEq⟩
  have nameResult := rawIdentifier_eq_rejectAt_of_identifierAbsent .pragmaDecl absent
  simp only [rejectAt, spanEq, foundEq] at nameResult
  refine ⟨?_, advancedEq, rfl⟩
  simp only [pragmaDecl, bind, pragmaKeyword_eq_ok_of_exactTokenParses keywordParsed]
  rw [nameResult]

/-- The packaged independent missing-name judgment yields the same exact
failure without any executable success or rejection premise. -/
theorem pragmaDecl_nameMissingAt_exact
    {input : State} {span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (missing : DeclarativeGrammar.PragmaNameMissingAt input.file.id input.window.endByte
      input.declarativeRemainder after span found) :
    pragmaDecl input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  cases missing with
  | missing keywordParsed nameAbsent current =>
      exact pragmaDecl_nameMissing_exact keywordParsed nameAbsent current

namespace FileInternals

/-- Attribute-free pragma dispatch preserves the exact leaf failure and its
silent raw diagnostic trace. -/
theorem plainTopItem_pragmaNameMissing_exact
    {input : State} {marker span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after)
    (nameAbsent : DeclarativeGrammar.IdentifierAbsentAt after)
    (current : DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      after span found) :
    plainTopItem input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  rcases pragmaDecl_nameMissing_exact keywordParsed nameAbsent current with
    ⟨rejected, afterEq, diagnosticsEq⟩
  refine ⟨?_, afterEq, diagnosticsEq⟩
  rw [plainTopItem_eq_pragma_of_exactTokenParses keywordParsed]
  simp only [mapTopItem, rejected]

/-- A leading pragma cannot enter derive parsing; its exact name failure is
returned unchanged through the derive-aware dispatcher. -/
theorem topItem_pragmaNameMissing_exact
    {input : State} {marker span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after)
    (nameAbsent : DeclarativeGrammar.IdentifierAbsentAt after)
    (current : DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      after span found) :
    topItem input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  rcases pragmaDecl_nameMissing_exact keywordParsed nameAbsent current with
    ⟨rejected, afterEq, diagnosticsEq⟩
  refine ⟨?_, afterEq, diagnosticsEq⟩
  rw [topItem_eq_pragma_of_exactTokenParses keywordParsed]
  simp only [mapTopItem, rejected]

/-- The file-loop item boundary has the identical failure and no emitted event. -/
theorem parseItemsItem_pragmaNameMissing_exact
    {input : State} {marker span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after)
    (nameAbsent : DeclarativeGrammar.IdentifierAbsentAt after)
    (current : DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      after span found) :
    parseItemsItem input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics :=
  topItem_pragmaNameMissing_exact keywordParsed nameAbsent current

/-- The packaged independent report also crosses the loop-item boundary. -/
theorem parseItemsItem_pragmaNameMissingAt_exact
    {input : State} {span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (missing : DeclarativeGrammar.PragmaNameMissingAt input.file.id input.window.endByte
      input.declarativeRemainder after span found) :
    parseItemsItem input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  cases missing with
  | missing keywordParsed nameAbsent current =>
      exact parseItemsItem_pragmaNameMissing_exact keywordParsed nameAbsent current

end FileInternals
end Solcore.Syntax.Parser
