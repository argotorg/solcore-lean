import Solcore.Syntax.Parser.Function
import Solcore.Syntax.CallableDeclarationValidity

/-! State and start-token contracts for complete function declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem functionBind_ok_components {α β : Type}
    {first : Parser α} {next : α → Parser β} {input final : State}
    {value : β} (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
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

/--
Function declarations retain valid inner syntax when the isolated body does;
only the outer cover-span law remains an explicit premise.
-/
theorem functionDecl_validFor_of_span
    (statementValid : SourceFile → Statement → Prop)
    (location : FunctionLocation)
    (bodyValid : (isolateBlock (block .allow)).ValidFor
      (Block.ValidFor statementValid))
    (spanValidOnSuccess : ∀ input declaration next,
      input.ValidFor → functionDecl location input = .ok declaration next →
      declaration.span.ValidFor input.file) :
    (functionDecl location).ValidFor
      (FunctionDecl.ValidFor statementValid) := by
  have weak : (functionDecl location).ValidFor (fun _ _ => True) := by
    unfold functionDecl
    apply Parser.bind_validFor (functionSignature_validFor location)
    intro signature
    apply Parser.bind_validFor bodyValid
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : functionDecl location input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok declaration final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold functionDecl at stages
      rcases functionBind_ok_components stages with
        ⟨signature, afterSignature, signatureResult, rest⟩
      rcases functionBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have signatureContract := functionSignature_validFor location input inputValid
      rw [signatureResult] at signatureContract
      have bodyContract := bodyValid afterSignature signatureContract.2.1
      rw [bodyResult] at bodyContract
      have signatureValidInput : FunctionSignature.ValidFor input.file signature := by
        simpa [signatureContract.2.2] using signatureContract.1
      have bodyValidInput : Block.ValidFor statementValid input.file body := by
        simpa [bodyContract.2.2, signatureContract.2.2] using bodyContract.1
      have outerValid := spanValidOnSuccess input declaration final inputValid parsed
      cases finished
      exact ⟨⟨outerValid, signatureValidInput, bodyValidInput.1,
        bodyValidInput.2⟩, weakResult.2.1, weakResult.2.2⟩

/-- Function declarations preserve token windows when block parsing does. -/
theorem functionDecl_preservesTokenWindow_of_block
    (location : FunctionLocation)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow (functionDecl location) := by
  unfold functionDecl
  apply Parser.bind_preservesTokenWindow
    (functionSignature_preservesTokenWindow location)
  intro signature
  apply Parser.bind_preservesTokenWindow
    (isolateBlock_preservesTokenWindow (block .allow) bodyWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Successful function parsing preserves the immutable token carrier. -/
theorem functionDecl_preservesTokensOnSuccess_of_block
    (location : FunctionLocation)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokensOnSuccess (functionDecl location) :=
  (functionDecl_preservesTokenWindow_of_block location bodyWindow
    ).preservesTokensOnSuccess

/-- Function declarations never rewind when block parsing is monotone. -/
theorem functionDecl_cursorMonotoneOnSuccess_of_block
    (location : FunctionLocation)
    (bodyCursor : Parser.CursorMonotoneOnSuccess (block .allow)) :
    Parser.CursorMonotoneOnSuccess (functionDecl location) := by
  unfold functionDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (functionSignature_cursorMonotoneOnSuccess location)
  intro signature
  apply Parser.bind_cursorMonotoneOnSuccess
    (isolateBlock_cursorMonotoneOnSuccess (block .allow) bodyCursor)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A function declaration starts at its signature's `function` keyword. -/
theorem functionDecl_startsAtCurrentTokenOnSuccess
    (location : FunctionLocation) :
    Parser.StartsAtCurrentTokenOnSuccess (functionDecl location) (·.span) := by
  unfold functionDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (functionSignature_startsAtCurrentTokenOnSuccess location)
  intro signature input declaration final parsed
  simp only [bind] at parsed
  cases bodyResult : isolateBlock (block .allow) input with
  | invariant error => simp [bodyResult] at parsed
  | reject failure rejected => simp [bodyResult] at parsed
  | ok body afterBody =>
      simp only [bodyResult] at parsed
      cases parsed
      rfl

end Solcore.Syntax.Parser
