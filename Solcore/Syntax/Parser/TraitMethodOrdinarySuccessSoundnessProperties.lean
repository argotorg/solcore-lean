import Solcore.Syntax.DeclarativeTraitMethodOutcomeGrammar
import Solcore.Syntax.Parser.FunctionSignatureOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.Trait

/-! Broad ordinary-success soundness for signature-only trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

namespace TraitInternals

/-- Every executable trait-method success records its broad module-location
signature, exact semicolon, AST cover span, empty trivia, and remainder. -/
theorem traitMethod_success_ordinaryOutcome_sound
    {input output : State} {method : TraitMethod}
    (result : traitMethod input = .ok method output) :
    DeclarativeGrammar.TraitMethodOrdinaryParses
      input.declarativeRemainder method output.declarativeRemainder := by
  unfold traitMethod at result
  rcases bind_ok_components result with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases bind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed semicolon.span
    (functionSignature_success_ordinaryOutcome_sound .module signatureResult)
    (symbol_success_exactTokenParses .semicolon .topItem semicolonResult)

end TraitInternals
end Solcore.Syntax.Parser
