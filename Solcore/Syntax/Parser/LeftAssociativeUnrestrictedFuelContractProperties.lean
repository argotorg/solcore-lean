import Solcore.Syntax.Parser.ExpressionLeftAssociativeTotalityProperties
import Solcore.Syntax.Parser.UnrestrictedFuelElementContract
import Solcore.Syntax.Parser.DelimitedNumericWindowProperties

/-! Left-associative layers preserve unrestricted operand contracts at the
same fuel. A tail has one extra unit of operand allowance because its actual
recognized operator is consumed before the child. Successful numeric frames
hold at every fuel and on arbitrary States, independently of ordinary bounds.
No validity, source, token-carrier, or byte-end frame is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem leftAssociativeTail_endIndex_onSuccess
    (operand : Parser Expr)
    (operandSuccess : ∀ {input output value}, operand input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (precedence : Nat) : ∀ fuel left {input output : State} {value : Expr},
      leftAssociativeTail operand precedence fuel left input = .ok value output →
      output.window.endIndex = input.window.endIndex := by
  intro fuel
  induction fuel with
  | zero => intro left input output value result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input output value result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp only [leftAssociativeTail, operatorResult] at result; cases result; rfl
      | some operator =>
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + 1 } with
          | invariant error => simp [childResult] at result
          | reject failure rejected => simp [childResult] at result
          | ok right next =>
              simp only [childResult] at result
              have childFrame := operandSuccess childResult
              exact (ih (binaryNode left operator right) result).trans childFrame

theorem leftAssociative_endIndex_onSuccess
    (operand : Parser Expr)
    (operandSuccess : ∀ {input output value}, operand input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (precedence : Nat) {input output : State} {value : Expr}
    (result : leftAssociative operand precedence input = .ok value output) :
    output.window.endIndex = input.window.endIndex := by
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok left next =>
      simp only [firstResult] at result
      exact (leftAssociativeTail_endIndex_onSuccess operand operandSuccess precedence
        (next.remainingCount + 1) left result).trans (operandSuccess firstResult)

theorem leftAssociativeTail_preservesEndIndex
    (operand : Parser Expr) (operandFrame : Parser.PreservesEndIndex operand)
    (precedence : Nat) : ∀ fuel left,
      Parser.PreservesEndIndex (leftAssociativeTail operand precedence fuel left) := by
  intro fuel
  induction fuel with
  | zero => intro left input; trivial
  | succ fuel ih =>
      intro left input
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp only [leftAssociativeTail, operatorResult, Reply.PreservesEndIndex]
      | some operator =>
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape]
          cases childResult : operand { input with cursor := input.cursor + 1 } with
          | invariant error => trivial
          | reject failure rejected =>
              have childFrame := operandFrame.endIndex_eq_of_reject childResult
              exact childFrame
          | ok right next =>
              have childFrame := operandFrame.endIndex_eq_of_ok childResult
              exact (ih (binaryNode left operator right) next).trans childFrame

theorem leftAssociative_preservesEndIndex
    (operand : Parser Expr) (operandFrame : Parser.PreservesEndIndex operand) (precedence : Nat) :
    Parser.PreservesEndIndex (leftAssociative operand precedence) := by
  intro input
  unfold leftAssociative
  cases firstResult : operand input with
  | invariant error => trivial
  | reject failure rejected => exact operandFrame.endIndex_eq_of_reject firstResult
  | ok left next =>
      exact (leftAssociativeTail_preservesEndIndex operand operandFrame precedence
        (next.remainingCount + 1) left next).trans (operandFrame.endIndex_eq_of_ok firstResult)

/-- The recognized operator pays one unit before the operand is run. Child
successes cannot increase the numeric remainder, even on malformed States. -/
theorem leftAssociativeTail_ordinary_of_unrestrictedFuels
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel) :
    ∀ loopFuel left input, input.remainingCount < loopFuel →
      input.remainingCount < operandFuel + 1 →
      (∃ value output, leftAssociativeTail operand precedence loopFuel left input = .ok value output) ∨
      (∃ failure rejected, leftAssociativeTail operand precedence loopFuel left input = .reject failure rejected) := by
  intro loopFuel
  induction loopFuel with
  | zero => intro left input loopAdequate operandAdequate; omega
  | succ loopFuel ih =>
      intro left input loopAdequate operandAdequate
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => exact Or.inl ⟨left, input, by simp only [leftAssociativeTail, operatorResult]⟩
      | some operator =>
          rcases binaryAtPrecedence?_some_state_shape operatorResult with ⟨token, found, _, _⟩
          have beforeEnd := State.cursor_lt_endIndex_of_peek?_eq_some found
          let afterOperator := { input with cursor := input.cursor + 1 }
          have childAdequate : afterOperator.remainingCount < operandFuel := by
            simp only [afterOperator, State.remainingCount] at operandAdequate ⊢
            omega
          have afterOperatorLoop : afterOperator.remainingCount < loopFuel := by
            simp only [afterOperator, State.remainingCount] at loopAdequate ⊢
            omega
          rcases contract.ordinary afterOperator childAdequate with
            ⟨right, next, childResult⟩ | ⟨failure, rejected, childResult⟩
          · dsimp only [afterOperator] at childResult
            have nextLoop := contract.remainingCount_lt_of_success childResult afterOperatorLoop
            have nextChild := contract.remainingCount_lt_of_success childResult childAdequate
            rcases ih (binaryNode left operator right) next nextLoop (by omega) with
              ⟨value, output, tailResult⟩ | ⟨failure, rejected, tailResult⟩
            · exact Or.inl ⟨value, output, by
                simpa only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape,
                  childResult] using tailResult⟩
            · exact Or.inr ⟨failure, rejected, by
                simpa only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape,
                  childResult] using tailResult⟩
          · dsimp only [afterOperator] at childResult
            exact Or.inr ⟨failure, rejected, by
              simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape, childResult]⟩

theorem leftAssociativeTail_ne_invariant_of_unrestrictedFuels
    (operand : Parser Expr) (operandFuel precedence loopFuel : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel)
    (left : Expr) (input : State) (loopAdequate : input.remainingCount < loopFuel)
    (operandAdequate : input.remainingCount < operandFuel + 1) (error : ParserInvariantError) :
    leftAssociativeTail operand precedence loopFuel left input ≠ .invariant error := by
  intro failed
  rcases leftAssociativeTail_ordinary_of_unrestrictedFuels operand operandFuel precedence contract
      loopFuel left input loopAdequate operandAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

theorem leftAssociative_ordinary_of_unrestrictedElementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel)
    (input : State) (adequate : input.remainingCount < operandFuel) :
    (∃ value output, leftAssociative operand precedence input = .ok value output) ∨
    (∃ failure rejected, leftAssociative operand precedence input = .reject failure rejected) := by
  rcases contract.ordinary input adequate with
    ⟨left, next, firstResult⟩ | ⟨failure, rejected, firstResult⟩
  · have nextAdequate := contract.remainingCount_lt_of_success firstResult adequate
    rcases leftAssociativeTail_ordinary_of_unrestrictedFuels operand operandFuel precedence contract
        (next.remainingCount + 1) left next (by omega) (by omega) with
      ⟨value, output, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨value, output, by simpa only [leftAssociative, firstResult] using tailResult⟩
    · exact Or.inr ⟨failure, rejected, by simpa only [leftAssociative, firstResult] using tailResult⟩
  · exact Or.inr ⟨failure, rejected, by simp only [leftAssociative, firstResult]⟩

theorem leftAssociative_ne_invariant_of_unrestrictedElementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel)
    (input : State) (adequate : input.remainingCount < operandFuel) (error : ParserInvariantError) :
    leftAssociative operand precedence input ≠ .invariant error := by
  intro failed
  rcases leftAssociative_ordinary_of_unrestrictedElementFuel operand operandFuel precedence
      contract input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

/-- Whole-layer success laws remain unrestricted; only ordinary execution
inherits the first operand's same-fuel input bound. -/
theorem leftAssociative_unrestrictedElementContract
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel) :
    UnrestrictedFuelElementContract (leftAssociative operand precedence) operandFuel where
  endIndexOnSuccess := leftAssociative_endIndex_onSuccess operand contract.endIndexOnSuccess precedence
  cursorLtOnSuccess := leftAssociative_cursor_lt_onSuccess operand contract.cursorLtOnSuccess precedence
  ordinary := leftAssociative_ordinary_of_unrestrictedElementFuel operand operandFuel precedence contract

end Solcore.Syntax.Parser.ExpressionInternals
