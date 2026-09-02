import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasParametersOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasValueOrdinaryOutcomeSoundnessProperties

/-! Executable ordinary success for complete transparent type aliases. -/

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

/-- Every executable type-alias success records its exact keyword, name,
optional parameters, equals token, recovery-aware value, semicolon, AST,
covering span, and final remainder. -/
theorem typeAlias_success_ordinaryOutcome_sound
    {input output : State} {declaration : TypeAliasDecl}
    (result : typeAlias input = .ok declaration output) :
    DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold typeAlias at result
  rcases bind_ok_components result with
    ⟨typeKeyword, afterKeyword, keywordResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, parametersStage⟩
  rcases bind_ok_components parametersStage with
    ⟨parameters, afterParameters, parametersResult, equalStage⟩
  rcases bind_ok_components equalStage with
    ⟨equal, afterEqual, equalResult, valueStage⟩
  rcases bind_ok_components valueStage with
    ⟨value, afterValue, valueResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed typeKeyword.span equal.span semicolon.span
    (keyword_success_exactTokenParses .typeKw .typeAlias keywordResult)
    (identifier_success_sound .typeAlias nameResult)
    (parseTypeAliasParameters_success_ordinaryOutcome_sound parametersResult)
    (symbol_success_exactTokenParses .equal .typeAlias equalResult)
    (TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound
      valueResult)
    (symbol_success_exactTokenParses .semicolon .typeAlias semicolonResult)

end Solcore.Syntax.Parser
