import Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeProperties
import Solcore.Syntax.Parser.CoreAssignmentTailSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-!
Executable ordinary-success and exact RHS-rejection bridges for Core
assignment suffixes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
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

@[simp] private theorem valueAssignOp?_symbol (operator : ValueAssignOp) :
    valueAssignOp? (.symbol operator.symbol) = some operator := by
  cases operator <;> rfl

private theorem valueAssignOperatorAbsentAt_of_lookahead_false
    {input : State}
    (absent : (input.peekKind?.bind valueAssignOp?).isSome = false) :
    DeclarativeGrammar.ValueAssignOperatorAbsentAt
      input.declarativeRemainder := by
  rintro ⟨span, operator, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := .symbol operator.symbol } at token
  unfold State.peekKind? State.peek? at absent
  simp only [token.1, ↓reduceIte, token.2, Option.map_some,
    valueAssignOp?_symbol, Option.bind_some, Option.isSome_some] at absent
  contradiction

private theorem assignmentTailAbsentAt_of_start_false {input : State}
    (absent : (isSymbol input .tildeEqual ||
      (input.peekKind?.bind valueAssignOp?).isSome) = false) :
    DeclarativeGrammar.AssignmentTailAbsentAt
      input.declarativeRemainder := by
  rcases Bool.or_eq_false_iff.mp absent with ⟨tildeAbsent, valueAbsent⟩
  exact ⟨symbolAbsentAt_of_isSymbol_eq_false .tildeEqual tildeAbsent,
    valueAssignOperatorAbsentAt_of_lookahead_false valueAbsent⟩

private theorem valueAssignOperator_eq_ok_of_selected {input : State}
    {selected : ValueAssignOp}
    (selection : input.peekKind?.bind valueAssignOp? = some selected) :
    ∃ operator output,
      valueAssignOperator input = .ok operator output := by
  unfold State.peekKind? at selection
  cases found : input.peek? with
  | none => simp [found] at selection
  | some token =>
      simp only [found, Option.map_some] at selection
      cases decoded : valueAssignOp? token.value with
      | none => simp [decoded] at selection
      | some value =>
          simp only [decoded, Option.bind_some] at selection
          cases selection
          refine ⟨{ span := token.span, value := selected },
            { input with cursor := input.cursor + 1 }, ?_⟩
          unfold valueAssignOperator
          simp only [found, decoded]

/-- Every executable assignment-tail success follows the ordinary prioritized
tail grammar, independently of diagnostics. -/
theorem assignmentTail_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {tail : AssignmentTail}
    (result : assignmentTail expression input = .ok tail output) :
    DeclarativeGrammar.AssignmentTailParses expressionOrdinary
      input.declarativeRemainder tail.declarative
        output.declarativeRemainder := by
  unfold assignmentTail at result
  by_cases bitNot : isSymbol input .tildeEqual
  · simp only [bitNot, if_true] at result
    rcases bind_ok_components result with
      ⟨operator, afterOperator, operatorResult, finished⟩
    cases finished
    exact .bitNot operator.span
      (symbol_success_exactTokenParses .tildeEqual .statement operatorResult)
  · have bitNotFalse : isSymbol input .tildeEqual = false :=
      Bool.eq_false_iff.mpr bitNot
    simp only [bitNotFalse, Bool.false_eq_true, if_false] at result
    cases decoded : input.peekKind?.bind valueAssignOp? with
    | none => rw [decoded] at result; unfold rejectAt at result; contradiction
    | some operator =>
        rw [decoded] at result
        rcases bind_ok_components result with
          ⟨located, afterOperator, operatorResult, rest⟩
        rcases bind_ok_components rest with
          ⟨right, afterRight, rightResult, finished⟩
        cases finished
        exact .value
          (symbolAbsentAt_of_isSymbol_eq_false .tildeEqual bitNotFalse)
          (valueAssignOperator_success_sound operatorResult)
          (expressionSuccessSound rightResult)

/-- Every executable optional-tail success retains exact maximal absence or
the ordinary committed assignment suffix. -/
theorem optionalAssignmentTail_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {tail : Option AssignmentTail}
    (result : optionalAssignmentTail expression input = .ok tail output) :
    DeclarativeGrammar.OptionalAssignmentTailParses expressionOrdinary
      input.declarativeRemainder (tail.map AssignmentTail.declarative)
        output.declarativeRemainder := by
  unfold optionalAssignmentTail at result
  by_cases starts : (isSymbol input .tildeEqual ||
      (input.peekKind?.bind valueAssignOp?).isSome) = true
  · simp only [starts, if_true] at result
    rcases bind_ok_components result with
      ⟨value, afterTail, tailResult, finished⟩
    cases finished
    exact .present (assignmentTail_success_ordinary_sound expression
      expressionOrdinary expressionSuccessSound tailResult)
  · have startsFalse : (isSymbol input .tildeEqual ||
        (input.peekKind?.bind valueAssignOp?).isSome) = false :=
      Bool.eq_false_iff.mpr starts
    simp only [startsFalse, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (assignmentTailAbsentAt_of_start_false startsFalse)

/-- An executable optional-tail rejection can only be the right expression
of a committed value-assignment operator. -/
theorem optionalAssignmentTail_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalAssignmentTail expression input =
      .reject failure rejected) :
    ∃ afterOperator operator,
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
          input.cursor (.symbol .tildeEqual) ∧
        DeclarativeGrammar.ValueAssignOperatorParses
          input.declarativeRemainder operator afterOperator ∧
        expressionRejects afterOperator rejected.declarativeRemainder := by
  unfold optionalAssignmentTail at result
  by_cases starts : (isSymbol input .tildeEqual ||
      (input.peekKind?.bind valueAssignOp?).isSome) = true
  · simp only [starts, if_true, bind] at result
    unfold assignmentTail at result
    by_cases bitNot : isSymbol input .tildeEqual
    · simp only [bitNot, if_true] at result
      rcases symbol_eq_ok_of_isSymbol_eq_true .tildeEqual .statement
          bitNot with ⟨operator, operatorResult⟩
      simp only [bind, operatorResult, pure] at result
      contradiction
    · have bitNotFalse : isSymbol input .tildeEqual = false :=
        Bool.eq_false_iff.mpr bitNot
      simp only [bitNotFalse, Bool.false_eq_true, if_false] at result
      cases selected : input.peekKind?.bind valueAssignOp? with
      | none => simp [bitNotFalse, selected] at starts
      | some selectedOperator =>
          simp only [selected] at result
          rcases valueAssignOperator_eq_ok_of_selected selected with
            ⟨operator, afterOperator, operatorResult⟩
          simp only [bind, operatorResult] at result
          cases rightResult : expression afterOperator with
          | invariant error => simp [rightResult] at result
          | ok right afterRight => simp [rightResult, pure] at result
          | reject rightFailure rightRejected =>
              simp only [rightResult] at result
              cases result
              exact ⟨afterOperator.declarativeRemainder, operator,
                symbolAbsentAt_of_isSymbol_eq_false .tildeEqual bitNotFalse,
                valueAssignOperator_success_sound operatorResult,
                expressionRejectSound rightResult⟩
  · have startsFalse : (isSymbol input .tildeEqual ||
        (input.peekKind?.bind valueAssignOp?).isSome) = false :=
      Bool.eq_false_iff.mpr starts
    simp [startsFalse] at result

end Solcore.Syntax.Parser.StatementSimpleInternals
