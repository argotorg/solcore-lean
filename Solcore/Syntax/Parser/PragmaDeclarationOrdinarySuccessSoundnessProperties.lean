import Solcore.Syntax.DeclarativePragmaOutcomeGrammar
import Solcore.Syntax.Parser.PragmaItemsOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.RawIdentifierOrdinaryOutcomeSoundnessProperties

/-! Exact executable ordinary success for complete pragma declarations. -/

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

/-- Every executable pragma success records the exact keyword, raw name,
checked item scan, semicolon, AST cover, and final remainder. -/
theorem pragmaDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration output) :
    DeclarativeGrammar.PragmaDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold pragmaDecl at result
  rcases bind_ok_components result with
    ⟨pragmaKeyword, afterKeyword, keywordResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, itemsStage⟩
  rcases bind_ok_components itemsStage with
    ⟨items, afterItems, itemsResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed pragmaKeyword.span semicolon.span
    (keyword_success_exactTokenParses .pragmaKw .pragmaDecl keywordResult)
    (rawIdentifier_success_ordinaryOutcome_sound .pragmaDecl nameResult)
    (PragmaInternals.pragmaItems_success_ordinaryOutcome_sound itemsResult)
    (symbol_success_exactTokenParses .semicolon .pragmaDecl semicolonResult)

end Solcore.Syntax.Parser
