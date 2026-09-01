import Solcore.Syntax.Parser.TypeAliasParameterSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasProperties
import Solcore.Syntax.Parser.TypeAliasRecoveryDiagnosticProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-! Diagnostic-free success soundness for transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeAliasInternals

/-- A diagnostic-free alias RHS success came from the ordinary type parser. -/
theorem parseAliasValue_success_sound_of_diagnosticFree
    {input next : State} {value : TypeExpr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : parseAliasValue input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseAliasValue at result
  cases coreResult : typeExpr input with
  | ok parsed afterCore =>
      simp only [coreResult] at result
      cases result
      exact typeExpr_success_sound coreResult
  | invariant error =>
      simp [coreResult] at result
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := {
        failedState with
        cursor := input.cursor
      }
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          .reject failure rewound
        else recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)) = .ok value next at result
      split at result
      · contradiction
      · exact False.elim
          (recoverTypeAliasValue_diagnostics_ne_nil_onSuccess result
            diagnosticFree)

end TypeAliasInternals

private theorem typeAliasSoundBind_success_components {alpha beta : Type}
    {first : Parser alpha} {nextParser : alpha → Parser beta}
    {input final : State} {value : beta}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every diagnostic-free successful alias follows the exact declaration grammar. -/
theorem typeAlias_success_sound {input next : State}
    {declaration : TypeAliasDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    DeclarativeGrammar.TypeAliasDeclParses input.declarativeRemainder
      declaration next.declarativeRemainder := by
  unfold typeAlias at result
  rcases typeAliasSoundBind_success_components result with
    ⟨typeKeyword, afterKeyword, keywordResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨equal, afterEqual, equalResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨value, afterValue, valueResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have semicolonShape := symbol_ok_tokenAt .semicolon .typeAlias
    semicolonResult
  have valueDiagnosticFree : afterValue.diagnosticsRev = [] := by
    rw [semicolonShape.2] at diagnosticFree
    exact diagnosticFree
  exact .parsed typeKeyword.span equal.span semicolon.span
    (keyword_success_exactTokenParses .typeKw .typeAlias keywordResult)
    (identifier_success_sound .typeAlias nameResult)
    (parseTypeAliasParameters_success_sound parametersResult)
    (symbol_success_exactTokenParses .equal .typeAlias equalResult)
    (TypeAliasInternals.parseAliasValue_success_sound_of_diagnosticFree
      valueDiagnosticFree valueResult)
    (symbol_success_exactTokenParses .semicolon .typeAlias semicolonResult)

/-- Alias grammar soundness composes with source validity. -/
theorem typeAlias_success_sound_and_validFor {input next : State}
    {declaration : TypeAliasDecl} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    DeclarativeGrammar.TypeAliasDeclParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      TypeAliasDecl.ValidFor input.file declaration := by
  refine ⟨typeAlias_success_sound diagnosticFree result, ?_⟩
  have valid := typeAlias_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
