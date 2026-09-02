import Solcore.Syntax.Parser.TraitDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TraitDeclSoundnessProperties

/-! External consumers for diagnostic-free trait grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTraitSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TraitMethodParses
example := @TraitMethodTailParses
example := @TraitBodyParses
example := @TraitDeclParses
example := @TraitMethodOrdinaryParses
example := @TraitMethodRejects
example := @traitMethodDeterministicOutcomeSpec
example := @TraitMethodStartAt
example := @TraitMethodTailOrdinaryParses
example := @TraitMethodTailOrdinaryOutcomeParses
example := @TraitMethodTailRejects
example := @traitMethodTailDeterministicOutcomeSpec
example := @TraitBodyOrdinaryParses
example := @TraitBodyOrdinaryOutcomeParses
example := @TraitBodyRejects
example := @traitBodyDeterministicOutcomeSpec
example := @TraitDeclOrdinaryParses
example := @TraitDeclRejects
example := @traitDeclDeterministicOutcomeSpec

example := @TraitInternals.traitMethod_reflectsDiagnosticFreeOnSuccess
example := @TraitInternals.traitMethod_success_sound
example := @TraitInternals.traitMethod_success_sound_and_validFor

example := @TraitInternals.traitBody_reflectsDiagnosticFreeOnSuccess
example := @TraitInternals.traitBody_success_sound
example := @TraitInternals.traitBody_success_sound_and_validFor

example := @traitDecl_reflectsDiagnosticFreeOnSuccess
example := @traitDecl_success_sound
example := @traitDecl_success_sound_and_validFor
example := @TraitInternals.traitMethod_success_ordinaryOutcome_sound
example := @TraitInternals.traitMethod_reject_ordinaryOutcome_sound
example := @TraitInternals.traitMethod_ordinaryOutcome_sound
example := @TraitInternals.traitMethod_ordinaryOutcomeSpec
example := @traitMethodExactOutcomeSpec
example := @TraitInternals.traitMethod_exactOutcomeSpec
example := @TraitInternals.traitMethod_success_result_unique
example := @TraitInternals.traitMethod_reject_output_unique
example := @TraitInternals.traitBody_success_ordinaryOutcome_sound
example := @TraitInternals.traitBody_reject_ordinaryOutcome_sound
example := @TraitInternals.traitBody_ordinaryOutcome_sound
example := @TraitInternals.traitBody_ordinaryOutcomeSpec
example := @traitDecl_success_ordinaryOutcome_sound
example := @traitDecl_reject_ordinaryOutcome_sound
example := @traitDecl_ordinaryOutcome_sound
example := @traitDecl_ordinaryOutcomeSpec

example {input next : State} {method : TraitMethod}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : TraitInternals.traitMethod input = .ok method next) :
    TraitMethodParses input.declarativeRemainder method
      next.declarativeRemainder :=
  TraitInternals.traitMethod_success_sound diagnosticFree result

example {input next : State} {body : TraitInternals.TraitBody}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : TraitInternals.traitBody input = .ok body next) :
    TraitBodyParses input.declarativeRemainder body.span body.methods
          next.declarativeRemainder ∧
      TraitInternals.TraitBody.ValidFor input.file body :=
  TraitInternals.traitBody_success_sound_and_validFor inputValid
    diagnosticFree result

example {input next : State} {declaration : TraitDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitDecl input = .ok declaration next) :
    TraitDeclParses input.declarativeRemainder declaration
          next.declarativeRemainder ∧
      TraitDecl.ValidFor input.file declaration :=
  traitDecl_success_sound_and_validFor inputValid diagnosticFree result

example {input rejected : State} {failure : Failure}
    (result : traitDecl input = .reject failure rejected) :
    TraitDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  traitDecl_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserTraitSoundnessProperties
