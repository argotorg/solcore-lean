import Solcore.Syntax.Parser.CoreExpressionBinaryOperatorSoundnessProperties
import Solcore.Syntax.Parser.DiagnosticTraceContracts

/-! Left-associative execution retains source and an arbitrary window
observation under exactly the corresponding operand frames. Successful child
frames need not preserve the entire window. No token carrier, progress,
trace, ordinary-execution, or validity assumption is used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

variable {operand : Parser Expr} {β : Type} {view : TokenWindow → β}

theorem leftAssociativeTail_success_context_of_windowProjection
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (precedence : Nat) : ∀ fuel left {input output : State} {value : Expr},
      leftAssociativeTail operand precedence fuel left input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window := by
  intro fuel
  induction fuel with
  | zero => intro left input output value result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input output value result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp only [leftAssociativeTail, operatorResult] at result; cases result; exact ⟨rfl, rfl⟩
      | some operator =>
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + 1 } with
          | invariant error => simp [childResult] at result
          | reject failure rejected => simp [childResult] at result
          | ok right next =>
              simp only [childResult] at result
              have childFrame := successFrame childResult
              have tailFrame := ih (binaryNode left operator right) result
              exact ⟨tailFrame.1.trans childFrame.1, tailFrame.2.trans childFrame.2⟩

theorem leftAssociativeTail_reject_context_of_windowProjection
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (rejectFrame : ∀ {input rejected failure}, operand input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    (precedence : Nat) : ∀ fuel left {input rejected : State} {failure : Failure},
      leftAssociativeTail operand precedence fuel left input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window := by
  intro fuel
  induction fuel with
  | zero => intro left input rejected failure result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input rejected failure result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp [leftAssociativeTail, operatorResult] at result
      | some operator =>
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + 1 } with
          | invariant error => simp [childResult] at result
          | reject actual next =>
              simp only [childResult] at result; cases result
              exact rejectFrame (input := { input with cursor := input.cursor + 1 }) childResult
          | ok right next =>
              simp only [childResult] at result
              have childFrame := successFrame childResult
              have tailFrame := ih (binaryNode left operator right) result
              exact ⟨tailFrame.1.trans childFrame.1, tailFrame.2.trans childFrame.2⟩

theorem leftAssociative_success_context_of_windowProjection
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (precedence : Nat) {input output : State} {value : Expr}
    (result : leftAssociative operand precedence input = .ok value output) :
    output.file = input.file ∧ view output.window = view input.window := by
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok left next =>
      simp only [firstResult] at result
      have childFrame := successFrame firstResult
      have tailFrame := leftAssociativeTail_success_context_of_windowProjection successFrame
        precedence (next.remainingCount + 1) left result
      exact ⟨tailFrame.1.trans childFrame.1, tailFrame.2.trans childFrame.2⟩

theorem leftAssociative_reject_context_of_windowProjection
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (rejectFrame : ∀ {input rejected failure}, operand input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    (precedence : Nat) {input rejected : State} {failure : Failure}
    (result : leftAssociative operand precedence input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject actual next => simp only [firstResult] at result; cases result; exact rejectFrame firstResult
  | ok left next =>
      simp only [firstResult] at result
      have childFrame := successFrame firstResult
      have tailFrame := leftAssociativeTail_reject_context_of_windowProjection successFrame rejectFrame
        precedence (next.remainingCount + 1) left result
      exact ⟨tailFrame.1.trans childFrame.1, tailFrame.2.trans childFrame.2⟩

theorem leftAssociativeTail_success_context (successFrame : ParserSuccessContext operand)
    (precedence fuel : Nat) (left : Expr) : ParserSuccessContext (leftAssociativeTail operand precedence fuel left) := by
  intro input output value result
  exact leftAssociativeTail_success_context_of_windowProjection (view := id) successFrame precedence fuel left result

theorem leftAssociative_success_context (successFrame : ParserSuccessContext operand)
    (precedence : Nat) : ParserSuccessContext (leftAssociative operand precedence) := by
  intro input output value result
  exact leftAssociative_success_context_of_windowProjection (view := id) successFrame precedence result

end Solcore.Syntax.Parser.ExpressionInternals
