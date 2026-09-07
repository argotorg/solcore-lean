import Solcore.Syntax.Parser.ExpressionCollectionRejectionContextProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchSelectionTraceProperties
import Solcore.Syntax.Parser.LiteralExpressionTraceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.Parser.LambdaExpressionRejectionTraceStateProperties

/-! Atom-core rejection keeps the file and an explicitly chosen window
observation. Both full-window and endByte-only specializations are provided.
Separate successful/rejected child context laws suffice: no token carrier,
block success frame, trace, validity, progress, or ordinary premise is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem literalExpression_reject_context {input rejected : State} {failure : Failure}
    (result : literalExpression input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have same := (coreLiteral_reject_trace_sound (literalExpression_reject_iff_coreLiteral.mp result)).2
  rw [same]
  exact ⟨rfl, rfl⟩

theorem identifierExpression_reject_context {input rejected : State} {failure : Failure}
    (result : identifierExpression input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  rw [(expressionName_reject_trace_sound (identifierExpression_reject_iff_expressionName.mp result)).2]
  exact ⟨rfl, rfl⟩

theorem proxyExpression_reject_context {input rejected : State} {failure : Failure}
    (result : proxyExpression input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  unfold proxyExpression at result
  cases markerResult : symbol .at .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject actual next =>
      simp only [bind, markerResult] at result
      cases result
      rw [symbol_reject_state_eq .at .expression markerResult]
      exact ⟨rfl, rfl⟩
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases typeResult : typeExpr afterMarker with
      | invariant error => simp [typeResult] at result
      | ok type next => simp [typeResult, pure] at result
      | reject actual next =>
          simp only [typeResult] at result
          cases result
          have window := typeExpr_preservesTokenWindow afterMarker
          rw [typeResult] at window
          have file := typeExpr_preservesFile.file_eq_of_reject typeResult
          have markerState := (symbol_ok_tokenAt .at .expression markerResult).2
          rw [markerState] at file window
          exact ⟨file, window.2⟩

theorem lambdaExpression_reject_context_of_windowProjection {β : Type} {view : TokenWindow → β}
    {block : Parser Block}
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure}
    (result : lambdaExpression block input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  unfold lambdaExpression at result
  cases markerResult : keyword .lamKw .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject actual next =>
      simp only [bind, markerResult] at result
      cases result
      have same := acceptToken_reject_state_shape (.keyword .lamKw) .expression
        (· == .keyword .lamKw) markerResult
      exact ⟨congrArg State.file same, congrArg (fun state => view state.window) same⟩
  | ok marker afterMarker =>
      have markerState := (keyword_ok_tokenAt .lamKw .expression markerResult).2
      subst afterMarker
      simp only [bind, markerResult] at result
      cases parametersResult : delimited .leftParen .rightParen true lambdaParameter .parameter .expression
          { input with cursor := input.cursor + 1 } with
      | invariant error => simp [parametersResult] at result
      | reject actual next =>
          simp only [parametersResult] at result
          cases result
          have frame := lambdaParameters_reject_context parametersResult
          exact ⟨frame.1, congrArg view frame.2⟩
      | ok parameters afterParameters =>
          simp only [parametersResult] at result
          have parameterFrame := lambdaParameters_success_context parametersResult
          cases returnResult : optionalLambdaReturnType afterParameters with
          | invariant error => simp [returnResult] at result
          | reject actual next =>
              simp only [returnResult] at result
              cases result
              have frame := optionalLambdaReturnType_reject_context returnResult
              exact ⟨frame.1.trans parameterFrame.1, congrArg view (frame.2.trans parameterFrame.2)⟩
          | ok returnType afterReturn =>
              simp only [returnResult] at result
              have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
              cases bodyResult : block afterReturn with
              | invariant error => simp [bodyResult] at result
              | ok body next => simp [bodyResult, pure] at result
              | reject actual next =>
                  simp only [bodyResult] at result
                  cases result
                  have frame := blockReject bodyResult
                  exact ⟨frame.1.trans (returnFrame.1.trans parameterFrame.1),
                    frame.2.trans (congrArg view (returnFrame.2.trans parameterFrame.2))⟩

theorem expressionAtomCore_reject_context_of_windowProjection
    {β : Type} {view : TokenWindow → β} {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ExpressionSuccessContext nested)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure}
    (result : expressionAtomCore nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  rw [ExpressionAtomDispatchTraceInternals.expressionAtomCore_eq_selected_raw] at result
  generalize chosen : ExpressionAtomDispatchTraceInternals.selectedBranch input = branch at result
  cases branch with
  | literal =>
      have frame := literalExpression_reject_context result
      exact ⟨frame.1, congrArg view frame.2⟩
  | name =>
      have frame := identifierExpression_reject_context result
      exact ⟨frame.1, congrArg view frame.2⟩
  | dotConstructor => exact dotConstructor_reject_context_of_windowProjection nestedSuccess nestedReject result
  | proxy =>
      have frame := proxyExpression_reject_context result
      exact ⟨frame.1, congrArg view frame.2⟩
  | parenthesized => exact parenthesized_reject_context_of_windowProjection nestedSuccess nestedReject result
  | array => exact arrayLiteral_reject_context_of_windowProjection nestedSuccess nestedReject result
  | lambda => exact lambdaExpression_reject_context_of_windowProjection blockReject result
  | final =>
      change Reply.reject _ input = Reply.reject failure rejected at result
      cases result
      exact ⟨rfl, rfl⟩

theorem expressionAtomCore_reject_context {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ExpressionSuccessContext nested)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input rejected : State} {failure : Failure}
    (result : expressionAtomCore nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window :=
  expressionAtomCore_reject_context_of_windowProjection (view := id) nestedSuccess nestedReject blockReject result

/-- Rejection may change both tokens and endIndex. Only its file and byte end
are needed to reconstruct a whole State from its exact traced remainder. -/
theorem expressionAtomCore_reject_source_endByte {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ExpressionSuccessContext nested)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input rejected : State} {failure : Failure}
    (result : expressionAtomCore nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte :=
  expressionAtomCore_reject_context_of_windowProjection (view := TokenWindow.endByte)
    nestedSuccess nestedReject blockReject result

end Solcore.Syntax.Parser.ExpressionAtomInternals
