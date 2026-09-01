import Solcore.Syntax.Parser.WildcardImportNoHidingSoundnessProperties

/-! External consumers for wildcard-import no-hiding soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserWildcardImportNoHidingSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @WildcardImportNoHidingTailParses
example := @WildcardImportNoHidingDeclParses
example := @optionalHiding_none_success_state
example := @wildcardImport_noHiding_success_sound_of_diagnosticFree
example := @importDecl_wildcardNoHiding_success_sound
example := @importDecl_wildcardNoHiding_success_sound_and_validFor

example {input next : State}
    (result : ImportInternals.optionalHiding input = .ok none next) :
    next = input :=
  optionalHiding_none_success_state result

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl} (diagnosticFree : next.diagnosticsRev = [])
    (noHidingShape :
      ∃ path, declaration.value = .wildcard path none)
    (result : ImportInternals.wildcardImport start input =
      .ok declaration next) :
    WildcardImportNoHidingTailParses start input.declarativeRemainder
      declaration next.declarativeRemainder :=
  wildcardImport_noHiding_success_sound_of_diagnosticFree start
    diagnosticFree noHidingShape result

example {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (noHidingShape :
      ∃ path, declaration.value = .wildcard path none)
    (result : importDecl input = .ok declaration next) :
    WildcardImportNoHidingDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  importDecl_wildcardNoHiding_success_sound diagnosticFree noHidingShape
    result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (noHidingShape :
      ∃ path, declaration.value = .wildcard path none)
    (result : importDecl input = .ok declaration next) :
    WildcardImportNoHidingDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_wildcardNoHiding_success_sound_and_validFor inputValid
    diagnosticFree noHidingShape result

end Solcore.Test.SyntaxParserWildcardImportNoHidingSoundnessProperties
