import Solcore.Syntax.DeclarativeCoreSourceFileOrdinaryGrammar
import Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTermFuelDiagnosticReflectionProperties
import Solcore.Syntax.Parser.SourceFileSoundnessProperties

/-! Concrete ordinary soundness for complete canonical Core source files. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every diagnostic-free complete-file success follows the concrete ordinary
Core grammar with public expression and isolated-body outcomes. -/
theorem sourceFile_success_coreOrdinary_sound
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsedFile next.declarativeRemainder := by
  exact sourceFile_success_sound
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
    (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
    expression_reflectsDiagnosticFreeOnSuccess
    (fun _ expressionResult =>
      expression_success_ordinary_sound expressionResult)
    (isolatedPublicCoreBlock_reflectsDiagnosticFreeOnSuccess .allow)
    (fun _ bodyResult =>
      isolatedCoreBlockPublic_success_ordinary_sound .allow bodyResult)
    (isolatedPublicCoreBlock_reflectsDiagnosticFreeOnSuccess .require)
    (fun _ bodyResult =>
      isolatedCoreBlockPublic_success_ordinary_sound .require bodyResult)
    diagnosticFree result

/-- Every valid diagnostic-free complete-file success reaches the canonical
terminal remainder of its preserved token window. -/
theorem sourceFile_success_coreOrdinary_sound_toEnd
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile} (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsedFile {
        tokens := input.tokens
        endIndex := input.window.endIndex
        cursor := input.window.endIndex
      } := by
  have parsed := sourceFile_success_coreOrdinary_sound diagnosticFree result
  have outputValid := sourceFile_complete_reply_validFor inputValid commentsValid
  rw [result] at outputValid
  have outputShape := sourceFile_complete_preservesTokenWindow comments input
  rw [result] at outputShape
  have cursorEq : next.cursor = input.window.endIndex := by
    apply Nat.le_antisymm
    · simpa [outputShape.2] using outputValid.2.1.cursor_le_endIndex
    · simpa [State.declarativeRemainder, outputShape.2] using
        parsed.output_atEnd
  simpa [State.declarativeRemainder, outputShape.1, outputShape.2, cursorEq]
    using parsed

/-- Concrete complete-file ordinary soundness paired with canonical source
validity. -/
theorem sourceFile_success_coreOrdinary_sound_and_validFor
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile} (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParses input.file comments
        input.declarativeRemainder parsedFile next.declarativeRemainder ∧
      ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor input.file
        parsedFile := by
  exact sourceFile_success_sound_and_validFor
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
    (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
    expression_reflectsDiagnosticFreeOnSuccess
    (fun _ expressionResult =>
      expression_success_ordinary_sound expressionResult)
    (isolatedPublicCoreBlock_reflectsDiagnosticFreeOnSuccess .allow)
    (fun _ bodyResult =>
      isolatedCoreBlockPublic_success_ordinary_sound .allow bodyResult)
    (isolatedPublicCoreBlock_reflectsDiagnosticFreeOnSuccess .require)
    (fun _ bodyResult =>
      isolatedCoreBlockPublic_success_ordinary_sound .require bodyResult)
    inputValid commentsValid diagnosticFree result

end Solcore.Syntax.Parser.FileInternals
