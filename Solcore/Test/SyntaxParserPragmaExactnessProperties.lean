import Solcore.Syntax.Parser.PragmaDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PragmaItemsOrdinaryOutcomeSoundnessProperties

/-! External consumers of exact pragma items and complete declarations. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.PragmaItemsTailOrdinaryParses
    DeclarativeGrammar.PragmaItemsTailRejects :=
  PragmaInternals.pragmaItemsTail_exactOutcomeSpec

-- The executable reverse prefix is shared; the grammar retains a forward suffix.
example (itemsRev : List Identifier)
    {input output : State} {actual suffix : List Identifier}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : PragmaInternals.pragmaItemsTail (input.remainingCount + 1)
      itemsRev input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PragmaItemsTailOrdinaryParses
      input.declarativeRemainder suffix afterExpected) :
    actual = itemsRev.reverse ++ suffix ∧
      output.declarativeRemainder = afterExpected := by
  rcases PragmaInternals.pragmaItemsTail_production_success_ordinaryOutcome_sound
    itemsRev result with ⟨actualSuffix, actualEq, actualParsed⟩
  rcases PragmaInternals.pragmaItemsTail_exactOutcomeSpec.successResultUnique
    actualParsed expectedParsed with ⟨suffixEq, afterEq⟩
  exact ⟨actualEq.trans (congrArg (itemsRev.reverse ++ ·) suffixEq), afterEq⟩

example (itemsRev : List Identifier)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : PragmaInternals.pragmaItemsTail (input.remainingCount + 1)
      itemsRev input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.PragmaItemsTailRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  PragmaInternals.pragmaItemsTail_exactOutcomeSpec.rejectOutputUnique
    (PragmaInternals.pragmaItemsTail_production_reject_ordinaryOutcome_sound
      itemsRev result) expectedRejected

example := @PragmaInternals.pragmaItemsTail_production_success_result_unique
example := @PragmaInternals.pragmaItemsTail_production_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.PragmaItemsOrdinaryParses
    DeclarativeGrammar.PragmaItemsRejects :=
  PragmaInternals.pragmaItems_exactOutcomeSpec

example {input output : State} {actual expected : List Identifier}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : PragmaInternals.pragmaItems input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PragmaItemsOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  PragmaInternals.pragmaItems_exactOutcomeSpec.successResultUnique
    (PragmaInternals.pragmaItems_success_ordinaryOutcome_sound result)
    expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : PragmaInternals.pragmaItems input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.PragmaItemsRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  PragmaInternals.pragmaItems_exactOutcomeSpec.rejectOutputUnique
    (PragmaInternals.pragmaItems_reject_ordinaryOutcome_sound result)
    expectedRejected

example := @PragmaInternals.pragmaItems_success_result_unique
example := @PragmaInternals.pragmaItems_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.PragmaDeclOrdinaryParses
    DeclarativeGrammar.PragmaDeclRejects :=
  pragmaDecl_exactOutcomeSpec

example {input output : State} {actual expected : PragmaDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : pragmaDecl input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PragmaDeclOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  pragmaDecl_exactOutcomeSpec.successResultUnique
    (pragmaDecl_success_ordinaryOutcome_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : pragmaDecl input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.PragmaDeclRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  pragmaDecl_exactOutcomeSpec.rejectOutputUnique
    (pragmaDecl_reject_ordinaryOutcome_sound result) expectedRejected

example := @pragmaDecl_success_result_unique
example := @pragmaDecl_reject_output_unique

end Solcore.Test.SyntaxParserPragmaExactnessProperties
