import Solcore.Syntax.Parser.CoreTypeQualifiedNameRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.TypeNamedSoundnessProperties

/-! Exact ordinary-rejection reflection for named Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional named-type arguments reject only inside the selected nonempty
angle-list parser. -/
theorem parseNamedTypeArguments_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : parseNamedTypeArguments nested input =
      .reject failure rejected) :
    DeclarativeGrammar.NamedTypeArgumentsRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold parseNamedTypeArguments getState at result
  simp only [bind] at result
  split at result
  next argumentsPresent =>
    rcases symbol_eq_ok_of_isSymbol_eq_true .less .typeExpr argumentsPresent
      with ⟨opening, openingResult⟩
    cases valuesResult : delimited .less .greater false nested
        .typeExpr .typeExpr input with
    | invariant error => simp [valuesResult] at result
    | reject valuesFailure valuesRejected =>
        simp only [valuesResult] at result
        cases result
        exact .selected opening.span
          (symbol_success_exactTokenParses .less .typeExpr openingResult)
          (delimited_reject_sound .less .greater false nested
            DeclarativeGrammar.TypeExprParses nestedRejects .typeExpr .typeExpr
            nestedSuccessSound nestedRejectSound valuesResult)
    | ok values afterValues =>
        simp only [valuesResult] at result
        unfold requireNonempty at result
        cases elements : values.elements <;> simp [elements, pure] at result
  next argumentsAbsent =>
    simp [pure] at result

/-- A named-type rejection records either the missing qualified-name component
or the exact rejected generic-argument list.  Canonical-`mapping` spelling
diagnostics occur only after successful arguments and therefore remain
ordinary successes, not rejection constructors. -/
theorem parseNamedType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : parseNamedType nested input = .reject failure rejected) :
    DeclarativeGrammar.NamedTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold parseNamedType at result
  cases nameResult : qualifiedName .typeExpr .typeExpr input with
  | invariant error => simp [bind, nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [bind, nameResult] at result
      cases result
      exact .nameRejected
        (qualifiedName_reject_type_sound .typeExpr .typeExpr nameResult)
  | ok name afterName =>
      simp only [bind, nameResult] at result
      cases argumentsResult : parseNamedTypeArguments nested afterName with
      | invariant error => simp [argumentsResult] at result
      | reject argumentsFailure argumentsRejected =>
          simp only [argumentsResult] at result
          cases result
          exact .argumentsRejected
            (qualifiedName_success_sound .typeExpr .typeExpr nameResult)
            (parseNamedTypeArguments_reject_type_sound nested nestedRejects
              nestedSuccessSound nestedRejectSound argumentsResult)
      | ok arguments afterArguments =>
          simp only [argumentsResult] at result
          unfold finishNamedType emitDiagnostic modifyState at result
          simp only [bind] at result
          split at result <;> contradiction

end Solcore.Syntax.Parser
