import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.ContractEntryModifierSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.FunctionParametersOrdinaryOutcomeSoundnessProperties

/-!
Executable ordinary outcomes for recovery-aware contract-entry parameters and
fixed-order implicit-public modifiers.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractEntryInternals

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

/-- Contract-entry parameters are definitionally the public recovery-aware
function-parameter parser. -/
theorem entryParameters_success_ordinaryOutcome_sound
    {input output : State}
    {parameters : DelimitedList FunctionParameter}
    (result : entryParameters input = .ok parameters output) :
    DeclarativeGrammar.FunctionParametersOrdinaryParses
      input.declarativeRemainder parameters output.declarativeRemainder := by
  simpa only [entryParameters, functionParameters] using
    functionParameters_success_ordinaryOutcome_sound result

/-- Contract-entry parameter rejection preserves the exact public
function-parameter rejection endpoint. -/
theorem entryParameters_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : entryParameters input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  simpa only [entryParameters, functionParameters] using
    functionParameters_reject_ordinaryOutcome_sound result

/-- Every successful implicit-public modifier parse retains the optional
explicit `public` marker in its derivation and the optional `payable` marker
in its output.  Emitting the implicit-public diagnostic changes no
declarative remainder. -/
theorem implicitPublicModifiers_success_ordinaryOutcome_sound
    (declaration : HardKeyword) {input output : State}
    {payableMarker : Option SourceSpan}
    (result : implicitPublicModifiers declaration input =
      .ok payableMarker output) :
    DeclarativeGrammar.ContractEntryModifiersOrdinaryParses
      input.declarativeRemainder payableMarker
        output.declarativeRemainder := by
  unfold implicitPublicModifiers at result
  rcases bind_ok_components result with
    ⟨publicMarker, afterPublic, publicResult, rest⟩
  have publicParsed := optionalModifier_success_sound .publicKw publicResult
  cases publicMarker with
  | none =>
      exact .parsed publicParsed
        (optionalModifier_success_sound .payableKw rest)
  | some publicSpan =>
      rcases bind_ok_components rest with
        ⟨emitted, afterDiagnostic, diagnosticResult, payableResult⟩
      unfold emitDiagnostic modifyState at diagnosticResult
      cases diagnosticResult
      have payableParsed :=
        optionalModifier_success_sound .payableKw payableResult
      exact .parsed publicParsed (by
        simpa only [State.declarativeRemainder, State.emit] using
          payableParsed)

private theorem optionalModifier_ne_reject
    (modifier : HardKeyword) {input rejected : State} {failure : Failure}
    (result : optionalModifier modifier input = .reject failure rejected) :
    False := by
  unfold optionalModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input modifier
  · rcases keyword_eq_ok_of_isKeyword_eq_true modifier .contractMember
        present with ⟨token, markerResult⟩
    simp [present, markerResult, pure] at result
  · have absent : isKeyword input modifier = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Fixed-order implicit-public modifiers cannot reject.  A present explicit
`public` marker emits a diagnostic and continues to optional `payable`. -/
theorem implicitPublicModifiers_ne_reject
    (declaration : HardKeyword) {input rejected : State} {failure : Failure}
    (result : implicitPublicModifiers declaration input =
      .reject failure rejected) : False := by
  unfold implicitPublicModifiers at result
  cases publicResult : optionalModifier .publicKw input with
  | invariant error => simp [bind, publicResult] at result
  | reject publicFailure publicRejected =>
      exact optionalModifier_ne_reject .publicKw publicResult
  | ok publicMarker afterPublic =>
      simp only [bind, publicResult] at result
      cases publicMarker with
      | none =>
          exact optionalModifier_ne_reject .payableKw result
      | some publicSpan =>
          unfold emitDiagnostic modifyState at result
          exact optionalModifier_ne_reject .payableKw result

end ContractEntryInternals
end Solcore.Syntax.Parser
