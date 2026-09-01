import Solcore.Syntax.Parser.ContractDeclSoundnessProperties
import Solcore.Syntax.Parser.DeclarationLeafDiagnosticReflectionProperties
import Solcore.Syntax.Parser.ExportDiagnosticReflectionProperties
import Solcore.Syntax.Parser.File
import Solcore.Syntax.Parser.FunctionDeclSoundnessProperties
import Solcore.Syntax.Parser.ImplDeclSoundnessProperties
import Solcore.Syntax.Parser.ImportDiagnosticReflectionProperties
import Solcore.Syntax.Parser.PragmaDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TraitDeclSoundnessProperties

/-! Diagnostic-freedom reflection through attribute-free top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem mapTopItem_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    {parser : Parser alpha} {wrap : alpha → TopItem}
    (parserReflects : Parser.ReflectsDiagnosticFreeOnSuccess parser) :
    Parser.ReflectsDiagnosticFreeOnSuccess (mapTopItem parser wrap) := by
  intro input item next result diagnosticFree
  unfold mapTopItem at result
  cases parserResult : parser input with
  | invariant error => simp [parserResult] at result
  | reject failure rejected => simp [parserResult] at result
  | ok value afterValue =>
      simp only [parserResult] at result
      cases result
      exact parserReflects input value next parserResult diagnosticFree

/-- Plain top-item parsing cannot erase an incoming diagnostic. -/
theorem plainTopItem_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess plainTopItem := by
  intro input item next result diagnosticFree
  unfold plainTopItem at result
  split at result
  · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
      importDecl_reflectsDiagnosticFreeOnSuccess input item next result
        diagnosticFree
  · split at result
    · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
        exportDecl_reflectsDiagnosticFreeOnSuccess input item next result
          diagnosticFree
    · split at result
      · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
          pragmaDecl_reflectsDiagnosticFreeOnSuccess input item next result
            diagnosticFree
      · split at result
        · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
            typeAlias_reflectsDiagnosticFreeOnSuccess input item next result
              diagnosticFree
        · split at result
          · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
              (functionDecl_reflectsDiagnosticFreeOnSuccess .module
                allowBodyReflects) input item next result diagnosticFree
          · split at result
            · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
                (enumDecl_reflectsDiagnosticFreeOnSuccess none) input item next
                  result diagnosticFree
            · split at result
              · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
                  traitDecl_reflectsDiagnosticFreeOnSuccess input item next
                    result diagnosticFree
              · split at result
                · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
                    (implDecl_reflectsDiagnosticFreeOnSuccess allowBodyReflects)
                      input item next result diagnosticFree
                · split at result
                  · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
                      (ContractInternals.contractDecl_reflectsDiagnosticFreeOnSuccess
                        expressionReflects allowBodyReflects
                          requiredBodyReflects)
                      input item next result diagnosticFree
                  · simp [rejectAt] at result

end Solcore.Syntax.Parser.FileInternals
