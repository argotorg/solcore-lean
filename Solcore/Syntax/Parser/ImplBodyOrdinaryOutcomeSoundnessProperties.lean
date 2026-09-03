import Solcore.Syntax.DeclarativeImplBodyExactnessProperties
import Solcore.Syntax.Parser.ImplBodyOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImplBodyOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for implementation bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- Package executable implementation-body success and exact rejection. -/
theorem implBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : ImplBody},
      implBody input = .ok body output →
        DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
          input.declarativeRemainder (body.span, body.methods)
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implBody input = .reject failure rejected →
        DeclarativeGrammar.ImplBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨implBody_success_ordinaryOutcome_sound,
    implBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive implementation-body outcomes. -/
theorem implBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyDeterministicOutcomeSpec

/-- Re-export exact implementation-body outcomes from exact method
outcomes. -/
theorem implBody_exactOutcomeSpec_of_method
    (methodOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyExactOutcomeSpecOfMethod methodOutcomes

/-- Re-export exact implementation-body outcomes from an exact isolated
method body. -/
theorem implBody_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyExactOutcomeSpecOfBody bodyOutcomes

/-- Fixed-fuel Core statement exactness discharges the executable
implementation-body contract. -/
theorem implBody_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyExactOutcomeSpecOfStatementFuel
    statementOutcomes

/-- Exact method outcomes make two successful executable implementation
bodies agree on their parser value and final declarative remainder. -/
theorem implBody_success_result_unique_of_method
    (methodOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects)
    {input leftOutput rightOutput : State} {left right : ImplBody}
    (leftResult : implBody input = .ok left leftOutput)
    (rightResult : implBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases (implBody_exactOutcomeSpec_of_method methodOutcomes)
      |>.successResultUnique
        (implBody_success_ordinaryOutcome_sound leftResult)
        (implBody_success_ordinaryOutcome_sound rightResult) with
    ⟨bodyEq, outputEq⟩
  constructor
  · cases left
    cases right
    cases bodyEq
    rfl
  · exact outputEq

/-- Exact method outcomes make two executable implementation-body
rejections agree on their declarative endpoint. -/
theorem implBody_reject_output_unique_of_method
    (methodOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implBody input = .reject leftFailure leftOutput)
    (rightResult : implBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (implBody_exactOutcomeSpec_of_method methodOutcomes).rejectOutputUnique
    (implBody_reject_ordinaryOutcome_sound leftResult)
    (implBody_reject_ordinaryOutcome_sound rightResult)

/-- An exact isolated method body makes two successful executable
implementation bodies agree. -/
theorem implBody_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State} {left right : ImplBody}
    (leftResult : implBody input = .ok left leftOutput)
    (rightResult : implBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_success_result_unique_of_method
    (DeclarativeGrammar.implMethodExactOutcomeSpecOfBody bodyOutcomes)
    leftResult rightResult

/-- An exact isolated method body makes two executable implementation-body
rejections agree. -/
theorem implBody_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implBody input = .reject leftFailure leftOutput)
    (rightResult : implBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_reject_output_unique_of_method
    (DeclarativeGrammar.implMethodExactOutcomeSpecOfBody bodyOutcomes)
    leftResult rightResult

/-- Fixed-fuel Core statement exactness makes two successful executable
implementation bodies agree. -/
theorem implBody_success_result_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    {input leftOutput rightOutput : State} {left right : ImplBody}
    (leftResult : implBody input = .ok left leftOutput)
    (rightResult : implBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_success_result_unique_of_method
    (DeclarativeGrammar.implMethodExactOutcomeSpecOfStatementFuel
      statementOutcomes)
    leftResult rightResult

/-- Fixed-fuel Core statement exactness makes two executable
implementation-body rejections agree. -/
theorem implBody_reject_output_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implBody input = .reject leftFailure leftOutput)
    (rightResult : implBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_reject_output_unique_of_method
    (DeclarativeGrammar.implMethodExactOutcomeSpecOfStatementFuel
      statementOutcomes)
    leftResult rightResult

end Solcore.Syntax.Parser.ImplInternals
