import Solcore.Syntax.DeclarativeGenericParametersOutcomeProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.GenericParametersSoundnessProperties

/-! Exact executable rejection reflection for canonical generic parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem lessPresent_of_isSymbol_eq_true {input : State}
    (present : isSymbol input .less = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .less } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .less .parameter present with
    ⟨opening, parsed⟩
  exact ⟨opening.span,
    (symbol_success_exactTokenParses .less .parameter parsed).1⟩

/-- Every executable generic-parameter rejection is the exact rejection of
its required nonempty, allow-trailing delimited list. -/
theorem genericParameters_reject_sound
    {input rejected : State} {failure : Failure}
    (result : genericParameters input = .reject failure rejected) :
    DeclarativeGrammar.GenericParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold genericParameters at result
  cases valuesResult : delimited .less .greater false
      (identifier .parameter) .parameter .topLevel input with
  | invariant error => simp [bind, valuesResult] at result
  | reject valuesFailure valuesRejected =>
      simp only [bind, valuesResult] at result
      cases result
      exact delimited_reject_sound .less .greater false
        (identifier .parameter) DeclarativeGrammar.IdentifierParses
        DeclarativeGrammar.IdentifierRejects .parameter .topLevel
        (identifier_success_sound .parameter)
        (identifier_reject_sound .parameter) valuesResult
  | ok values afterValues =>
      simp only [bind, valuesResult] at result
      unfold requireGenericParameters at result
      cases elements : values.elements with
      | nil => simp [elements] at result
      | cons head tail => simp [elements, pure] at result

/-- Package executable generic-parameter success and exact rejection. -/
theorem genericParameters_ordinaryOutcome_sound :
    (∀ {input next : State} {parameters : GenericParameters},
      genericParameters input = .ok parameters next →
        DeclarativeGrammar.GenericParametersParses
          input.declarativeRemainder parameters next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      genericParameters input = .reject failure rejected →
        DeclarativeGrammar.GenericParametersRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨genericParameters_success_sound, genericParameters_reject_sound⟩

/-- Every optional-generic rejection is the selected generic rejection from
the original positively guarded input. -/
theorem optionalGenericParameters_reject_sound
    {input rejected : State} {failure : Failure}
    (result : optionalGenericParameters input = .reject failure rejected) :
    DeclarativeGrammar.OptionalGenericParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold optionalGenericParameters getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .less
  · simp only [present, if_true] at result
    cases parametersResult : genericParameters input with
    | invariant error => simp [parametersResult] at result
    | ok parameters afterParameters =>
        simp [parametersResult, pure] at result
    | reject parametersFailure parametersRejected =>
        simp only [parametersResult] at result
        cases result
        exact .present (lessPresent_of_isSymbol_eq_true present)
          (genericParameters_reject_sound parametersResult)
  · have absent : isSymbol input .less = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package executable optional-generic success and exact rejection. -/
theorem optionalGenericParameters_ordinaryOutcome_sound :
    (∀ {input next : State} {parameters : Option GenericParameters},
      optionalGenericParameters input = .ok parameters next →
        DeclarativeGrammar.OptionalGenericParametersParses
          input.declarativeRemainder parameters next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalGenericParameters input = .reject failure rejected →
        DeclarativeGrammar.OptionalGenericParametersRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨optionalGenericParameters_success_sound,
    optionalGenericParameters_reject_sound⟩

end Solcore.Syntax.Parser
