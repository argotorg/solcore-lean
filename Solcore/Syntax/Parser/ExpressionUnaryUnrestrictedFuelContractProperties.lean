import Solcore.Syntax.Parser.UnaryOperatorsTraceProperties
import Solcore.Syntax.Parser.ExpressionPostfixUnrestrictedChildContractProperties

/-! Actual unary layers inherit an unrestricted contract at the same budget
as their postfix parser. Prefix scanning cannot increase the remaining count,
but the empty prefix pays no extra fuel. Successful numeric frames and progress
hold on every State; only ordinary execution is restricted by the fuel bound.
No source, token-carrier, byte-end, or validity assumptions are needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem expressionUnary_endIndex_onSuccess
    (nested : Parser Expr) (block : Parser Block)
    (postfixSuccess : ∀ {input output value},
      expressionPostfix nested block input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    {input output : State} {value : Expr}
    (result : expressionUnary nested block input = .ok value output) :
    output.window.endIndex = input.window.endIndex := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, middle, prefixResult⟩
  have prefixFrame := congrArg TokenWindow.endIndex
    (unaryOperators_success_context (input.remainingCount + 1) [] prefixResult).2
  simp only [expressionUnary, prefixResult] at result
  cases postfixResult : expressionPostfix nested block middle with
  | invariant error => simp [postfixResult] at result
  | reject failure rejected => simp [postfixResult] at result
  | ok base next =>
      simp only [postfixResult] at result
      cases result
      exact (postfixSuccess postfixResult).trans prefixFrame

/-- A rejected postfix carrier is passed through unchanged, so the all-reply
numeric frame requires its rejection frame as well as its success frame. -/
theorem expressionUnary_preservesEndIndex
    (nested : Parser Expr) (block : Parser Block)
    (postfixFrame : Parser.PreservesEndIndex (expressionPostfix nested block)) :
    Parser.PreservesEndIndex (expressionUnary nested block) := by
  intro input
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, middle, prefixResult⟩
  have prefixFrame := congrArg TokenWindow.endIndex
    (unaryOperators_success_context (input.remainingCount + 1) [] prefixResult).2
  simp only [expressionUnary, prefixResult]
  cases postfixResult : expressionPostfix nested block middle with
  | invariant error => trivial
  | reject failure rejected =>
      exact (postfixFrame.endIndex_eq_of_reject postfixResult).trans prefixFrame
  | ok base next =>
      exact (postfixFrame.endIndex_eq_of_ok postfixResult).trans prefixFrame

theorem expressionUnary_ordinary_of_unrestrictedPostfixFuel
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (postfixContract : UnrestrictedFuelElementContract (expressionPostfix nested block) fuel)
    (input : State) (adequate : input.remainingCount < fuel) :
    (∃ value output, expressionUnary nested block input = .ok value output) ∨
    (∃ failure rejected, expressionUnary nested block input = .reject failure rejected) := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, middle, prefixResult⟩
  have prefixFrame := congrArg TokenWindow.endIndex
    (unaryOperators_success_context (input.remainingCount + 1) [] prefixResult).2
  have prefixCursor := unaryOperators_cursorMonotoneOnSuccess
    (input.remainingCount + 1) [] input operators middle prefixResult
  have middleAdequate := remainingCount_lt_of_endIndex_eq prefixFrame prefixCursor adequate
  rcases postfixContract.ordinary middle middleAdequate with
    ⟨base, output, postfixResult⟩ | ⟨failure, rejected, postfixResult⟩
  · exact Or.inl ⟨applyUnaryOperators operators base, output, by
      simp only [expressionUnary, prefixResult, postfixResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [expressionUnary, prefixResult, postfixResult]⟩

theorem expressionUnary_ne_invariant_of_unrestrictedPostfixFuel
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (postfixContract : UnrestrictedFuelElementContract (expressionPostfix nested block) fuel)
    (input : State) (adequate : input.remainingCount < fuel) (error : ParserInvariantError) :
    expressionUnary nested block input ≠ .invariant error := by
  intro failed
  rcases expressionUnary_ordinary_of_unrestrictedPostfixFuel nested block fuel
      postfixContract input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- This is a same-fuel lift: the maximal unary prefix is allowed to be empty. -/
theorem expressionUnary_unrestrictedPostfixContract
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (postfixContract : UnrestrictedFuelElementContract (expressionPostfix nested block) fuel) :
    UnrestrictedFuelElementContract (expressionUnary nested block) fuel where
  endIndexOnSuccess := expressionUnary_endIndex_onSuccess nested block postfixContract.endIndexOnSuccess
  cursorLtOnSuccess := expressionUnary_cursor_lt_onSuccess nested block postfixContract.cursorLtOnSuccess
  ordinary := expressionUnary_ordinary_of_unrestrictedPostfixFuel nested block fuel postfixContract

/-- The actual postfix contract is constructed from the supplied children.
Neither that construction nor this unary lift asserts recursive closure. -/
theorem expressionUnary_unrestrictedChildContract
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel unaryFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (nestedBound : unaryFuel ≤ nestedFuel + 1) (bodyBound : unaryFuel ≤ bodyFuel + 1) :
    UnrestrictedFuelElementContract (expressionUnary nested block) unaryFuel :=
  expressionUnary_unrestrictedPostfixContract nested block unaryFuel
    (expressionPostfix_unrestrictedChildContract nested block nestedFuel bodyFuel unaryFuel
      nestedContract bodyContract nestedReject bodyReject nestedBound bodyBound)

theorem expressionUnary_unrestrictedChildContract_succ
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested fuel)
    (bodyContract : UnrestrictedFuelElementContract block fuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex) :
    UnrestrictedFuelElementContract (expressionUnary nested block) (fuel + 1) :=
  expressionUnary_unrestrictedChildContract nested block fuel fuel (fuel + 1)
    nestedContract bodyContract nestedReject bodyReject (Nat.le_refl _) (Nat.le_refl _)

end Solcore.Syntax.Parser.ExpressionInternals
