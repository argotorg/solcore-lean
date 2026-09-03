import Solcore.Syntax.Parser.TopItemRecoveryOrdinaryOutcomeSoundnessProperties

/-! Standalone consumers of exact top-item recovery, without clean-input premises. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTopItemRecoveryExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @DeclarativeGrammar.TopItemRecoveryScanParses.result_unique
example := @recoverTopItem_success_result_unique
example := @recoverTopItem_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.TopItemRecoveryParses DeclarativeGrammar.TopItemRecoveryRejects :=
  recoverTopItem_exactOutcomeSpec

example {input output : State} {actual expected : TopItem}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : recoverTopItem input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  recoverTopItem_exactOutcomeSpec.successResultUnique
    (recoverTopItem_success_ordinaryOutcome_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : recoverTopItem input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.TopItemRecoveryRejects
      input.declarativeRemainder expected) : output.declarativeRemainder = expected :=
  recoverTopItem_exactOutcomeSpec.rejectOutputUnique
    (recoverTopItem_reject_ordinaryOutcome_sound result) expectedRejected

end Solcore.Test.SyntaxParserTopItemRecoveryExactnessProperties
