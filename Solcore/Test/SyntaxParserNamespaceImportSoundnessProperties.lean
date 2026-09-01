import Solcore.Syntax.Parser.NamespaceImportSoundnessProperties

/-! External consumers for diagnostic-free namespace-import soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserNamespaceImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NamespaceImportTailParses
example := @NamespaceImportDeclParses
example := @contextual_ok_tokenAt
example := @importBind_success_components
example := @finishImport_success_value
example := @plainImport_success_value
example := @namespaceImport_success_value
example := @wildcardImport_success_value
example := @selectiveImport_success_value
example := @namespaceImport_success_sound_of_diagnosticFree
example := @importDecl_namespace_success_sound
example := @importDecl_namespace_success_sound_and_validFor

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl} (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.namespaceImport start input =
      .ok declaration next) :
    NamespaceImportTailParses start input.declarativeRemainder declaration
      next.declarativeRemainder :=
  namespaceImport_success_sound_of_diagnosticFree start diagnosticFree result

example {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (namespaceShape :
      ∃ path alias, declaration.value = .namespace path alias)
    (result : importDecl input = .ok declaration next) :
    NamespaceImportDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  importDecl_namespace_success_sound diagnosticFree namespaceShape result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (namespaceShape :
      ∃ path alias, declaration.value = .namespace path alias)
    (result : importDecl input = .ok declaration next) :
    NamespaceImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_namespace_success_sound_and_validFor inputValid diagnosticFree
    namespaceShape result

end Solcore.Test.SyntaxParserNamespaceImportSoundnessProperties
