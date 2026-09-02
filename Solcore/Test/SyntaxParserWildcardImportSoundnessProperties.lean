import Solcore.Syntax.Parser.WildcardImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.WildcardImportSoundnessProperties

/-! External consumers for complete wildcard-import grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserWildcardImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @WildcardImportTailParses
example := @WildcardImportDeclParses
example := @WildcardImportOrdinaryParses
example := @WildcardImportRejects
example := @wildcardImportDeterministicOutcomeSpec
example := @wildcardImport_success_sound_of_diagnosticFree
example := @importDecl_wildcard_success_sound
example := @importDecl_wildcardWithHiding_success_sound
example := @importDecl_wildcard_success_sound_and_validFor
example := @importDecl_wildcardWithHiding_success_sound_and_validFor
example := @wildcardImport_success_ordinaryOutcome_sound
example := @wildcardImport_reject_ordinaryOutcome_sound
example := @wildcardImport_ordinaryOutcome_sound
example := @wildcardImport_ordinaryOutcomeSpec

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl}
    (result : ImportInternals.wildcardImport start input =
      .ok declaration next) :
    WildcardImportOrdinaryParses start input.declarativeRemainder declaration
      next.declarativeRemainder :=
  wildcardImport_success_ordinaryOutcome_sound start result

example (start : SourceSpan) {input rejected : State} {failure : Failure}
    (result : ImportInternals.wildcardImport start input =
      .reject failure rejected) :
    WildcardImportRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  wildcardImport_reject_ordinaryOutcome_sound start result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (wildcardShape : ∃ path hidden,
      declaration.value = .wildcard path hidden)
    (result : importDecl input = .ok declaration next) :
    WildcardImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_wildcard_success_sound_and_validFor inputValid diagnosticFree
    wildcardShape result

example {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (withHidingShape : ∃ path clause,
      declaration.value = .wildcard path (some clause))
    (result : importDecl input = .ok declaration next) :
    WildcardImportDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  importDecl_wildcardWithHiding_success_sound diagnosticFree withHidingShape
    result

end Solcore.Test.SyntaxParserWildcardImportSoundnessProperties
