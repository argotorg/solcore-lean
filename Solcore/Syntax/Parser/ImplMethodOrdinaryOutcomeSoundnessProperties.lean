import Solcore.Syntax.DeclarativeImplMethodExactnessProperties
import Solcore.Syntax.Parser.FunctionDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Impl

/-! Executable ordinary outcomes for one implementation method wrapper. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ImplInternals

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Every successful method is an ordinary module-position function wrapped
with its exact span and empty parser-time leading comments. -/
theorem implMethod_success_ordinaryOutcome_sound
    {input output : State} {method : ImplMethod}
    (result : implMethod input = .ok method output) :
    DeclarativeGrammar.ImplMethodOrdinaryParses
      input.declarativeRemainder method output.declarativeRemainder := by
  unfold implMethod at result
  rcases bind_ok_components result with
    ⟨declaration, afterDeclaration, declarationResult, finished⟩
  cases finished
  exact .parsed
    (functionDecl_success_ordinaryOutcome_sound .module declarationResult)

/-- Every method rejection is exactly its nested module-position function
declaration rejection; the pure wrapper cannot reject. -/
theorem implMethod_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : implMethod input = .reject failure rejected) :
    DeclarativeGrammar.ImplMethodRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold implMethod at result
  cases declarationResult : functionDecl .module input with
  | invariant error => simp [bind, declarationResult] at result
  | ok declaration afterDeclaration =>
      simp [bind, declarationResult, pure] at result
  | reject declarationFailure declarationRejected =>
      simp only [bind, declarationResult] at result
      cases result
      exact .declarationRejected
        (functionDecl_reject_ordinaryOutcome_sound .module declarationResult)

/-- Package exact executable implementation-method success and rejection. -/
theorem implMethod_ordinaryOutcome_sound :
    (∀ {input output : State} {method : ImplMethod},
      implMethod input = .ok method output →
        DeclarativeGrammar.ImplMethodOrdinaryParses
          input.declarativeRemainder method output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implMethod input = .reject failure rejected →
        DeclarativeGrammar.ImplMethodRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨implMethod_success_ordinaryOutcome_sound,
    implMethod_reject_ordinaryOutcome_sound⟩

/-- Re-export the deterministic parser-independent method contract. -/
theorem implMethod_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects :=
  DeclarativeGrammar.implMethodDeterministicOutcomeSpec

/-- Re-export exact implementation-method outcomes from an exact isolated
function body. -/
theorem implMethod_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects :=
  DeclarativeGrammar.implMethodExactOutcomeSpecOfBody bodyOutcomes

/-- Fixed-fuel Core statement exactness discharges the executable
implementation-method contract. -/
theorem implMethod_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects :=
  DeclarativeGrammar.implMethodExactOutcomeSpecOfStatementFuel
    statementOutcomes

/-- With an exact isolated body, two executable implementation methods have
the same AST and final declarative remainder. -/
theorem implMethod_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State} {left right : ImplMethod}
    (leftResult : implMethod input = .ok left leftOutput)
    (rightResult : implMethod input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplMethodOrdinaryParses.result_unique_of_exact_body
    bodyOutcomes (implMethod_success_ordinaryOutcome_sound leftResult)
    (implMethod_success_ordinaryOutcome_sound rightResult)

/-- With an exact isolated body, two implementation-method rejections have
the same declarative endpoint. -/
theorem implMethod_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implMethod input = .reject leftFailure leftOutput)
    (rightResult : implMethod input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplMethodRejects.output_unique_of_exact_body
    bodyOutcomes (implMethod_reject_ordinaryOutcome_sound leftResult)
    (implMethod_reject_ordinaryOutcome_sound rightResult)

end ImplInternals
end Solcore.Syntax.Parser
