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
