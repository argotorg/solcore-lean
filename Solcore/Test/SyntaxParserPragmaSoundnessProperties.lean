import Solcore.Syntax.Parser.PragmaDeclarationOrdinaryOutcomeSoundnessProperties

/-! External consumers for canonical pragma success soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TokenAt
example := @PragmaItemsTailParses
example := @PragmaItemsParses
example := @PragmaDeclParses
example := @PragmaItemsTokenPresentAt
example := @PragmaItemsTailOrdinaryParses
example := @PragmaItemsTailRejects
example := @pragmaItemsTailDeterministicOutcomeSpec
example := @PragmaItemsOrdinaryParses
example := @PragmaItemsRejects
example := @pragmaItemsDeterministicOutcomeSpec
example := @PragmaDeclOrdinaryParses
example := @PragmaDeclRejects
example := @pragmaDeclDeterministicOutcomeSpec
example := @State.declarativeRemainder
example := @rawIdentifier_success_ordinaryOutcome_sound
example := @rawIdentifier_reject_ordinaryOutcome_sound
example := @rawIdentifier_ordinaryOutcome_sound
example := @rawIdentifier_ordinaryOutcomeSpec
example := @PragmaInternals.pragmaItemsTail_production_ordinaryOutcome_sound
example := @PragmaInternals.pragmaItems_ordinaryOutcome_sound
example := @PragmaInternals.pragmaItemsTail_ordinaryOutcomeSpec
example := @PragmaInternals.pragmaItems_ordinaryOutcomeSpec
example := @pragmaDecl_success_ordinaryOutcome_sound
example := @pragmaDecl_reject_ordinaryOutcome_sound
example := @pragmaDecl_ordinaryOutcome_sound
example := @pragmaDecl_ordinaryOutcomeSpec
example := @pragmaDecl_success_sound
example := @pragmaDecl_success_sound_and_validFor

example {input next : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration next) :
    PragmaDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  pragmaDecl_success_sound result

example {input next : State} {declaration : PragmaDecl}
    (inputValid : input.ValidFor)
    (result : pragmaDecl input = .ok declaration next) :
    PragmaDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  pragmaDecl_success_sound_and_validFor inputValid result

example {input next : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration next) :
    PragmaDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  pragmaDecl_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : pragmaDecl input = .reject failure rejected) :
    PragmaDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  pragmaDecl_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserPragmaSoundnessProperties
