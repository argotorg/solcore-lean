import Solcore.Syntax.Parser.PlainImportSoundnessProperties
import Solcore.Syntax.Parser.NamespaceImportSoundnessProperties
import Solcore.Syntax.Parser.WildcardImportSoundnessProperties
import Solcore.Syntax.Parser.SelectiveImportSoundnessProperties

/-! Aggregate diagnostic-free soundness of all canonical import forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free successful import follows its declarative grammar. -/
theorem importDecl_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.ImportDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder := by
  cases shape : declaration.value with
  | plain path =>
      exact .ofPlain (importDecl_plain_success_sound diagnosticFree
        ⟨path, shape⟩ result)
  | «namespace» path alias =>
      exact .ofNamespace (importDecl_namespace_success_sound diagnosticFree
        ⟨path, alias, shape⟩ result)
  | wildcard path hidden =>
      exact .ofWildcard (importDecl_wildcard_success_sound diagnosticFree
        ⟨path, hidden, shape⟩ result)
  | selected selection path hidden =>
      exact .ofSelected (importDecl_selected_success_sound diagnosticFree
        ⟨selection, path, hidden, shape⟩ result)

/-- Aggregate import soundness composes with source-provenance validity. -/
theorem importDecl_success_sound_and_validFor {input next : State}
    {declaration : ImportDecl} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.ImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨importDecl_success_sound diagnosticFree result, ?_⟩
  have valid := importDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
