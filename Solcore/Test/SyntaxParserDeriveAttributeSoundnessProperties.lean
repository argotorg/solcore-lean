import Solcore.Syntax.Parser.DeriveAttributeValidOrdinaryOutcomeSoundnessProperties

/-! External consumers for derive-attribute grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveAttributeSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @DeriveAttributeParses
example := @DeriveAttributeValidRejects
example := @deriveAttributeValidDeterministicOutcomeSpec
example := @deriveAttributeValid_success_sound
example := @DeriveAttributeInternals.valid_reject_ordinaryOutcome_sound
example := @deriveAttributeValid_success_ordinaryOutcome_sound
example := @deriveAttributeValid_reject_ordinaryOutcome_sound
example := @deriveAttributeValid_ordinaryOutcome_sound
example := @deriveAttributeValid_ordinaryOutcomeSpec
example := @deriveAttribute_success_sound
example := @deriveAttribute_success_sound_and_validFor

example {input next : State} {value : DeriveAttribute}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeriveAttributeParses input.declarativeRemainder value
      next.declarativeRemainder :=
  deriveAttribute_success_sound diagnosticFree result

example {input next : State} {value : DeriveAttribute}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeriveAttributeParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      value.ValidFor input.file :=
  deriveAttribute_success_sound_and_validFor inputValid diagnosticFree result

example {input rejected : State} {failure : Failure}
    (result : DeriveAttributeInternals.valid input =
      .reject failure rejected) :
    DeriveAttributeValidRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveAttributeValid_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserDeriveAttributeSoundnessProperties
