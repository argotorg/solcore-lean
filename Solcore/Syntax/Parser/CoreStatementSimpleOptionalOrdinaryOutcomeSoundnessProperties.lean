import Solcore.Syntax.DeclarativeCoreStatementSimpleOutcomeProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Statement.Simple

/-! Ordinary executable outcomes for optional Core statement components. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Optional return-value success preserves the semicolon-first priority. -/
theorem optionalReturnValue_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {value : Option Expr}
    (result : optionalReturnValue expression input = .ok value output) :
    DeclarativeGrammar.OptionalReturnValueOrdinaryParses expressionOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold optionalReturnValue getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon = true
  · simp only [present, if_true, pure] at result
    cases result
    rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .statement present with
      ⟨semicolon, semicolonResult⟩
    exact .absent semicolon.span
      (symbol_ok_tokenAt .semicolon .statement semicolonResult).1
  · have absent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false] at result
    rcases bind_ok_components result with
      ⟨expressionValue, afterExpression, expressionResult, finished⟩
    cases finished
    exact .present
      (symbolAbsentAt_of_isSymbol_eq_false .semicolon absent)
      (expressionSuccessSound expressionResult)

/-- Optional return-value rejection is exactly expression rejection after a
failed semicolon guard. -/
theorem optionalReturnValue_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalReturnValue expression input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalReturnValueRejects expressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold optionalReturnValue getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon = true
  · simp [present, pure] at result
  · have absent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false] at result
    cases expressionResult : expression input with
    | invariant error => simp [expressionResult] at result
    | ok value afterExpression => simp [expressionResult, pure] at result
    | reject expressionFailure expressionRejected =>
        simp only [expressionResult] at result
        cases result
        exact .expressionRejected
          (symbolAbsentAt_of_isSymbol_eq_false .semicolon absent)
          (expressionRejectSound expressionResult)

/-- Optional let-type success uses the public ordinary Core-type outcome. -/
theorem optionalLetType_success_ordinary_sound
    {input output : State} {value : Option TypeExpr}
    (result : optionalLetType input = .ok value output) :
    DeclarativeGrammar.OptionalLetTypeParses input.declarativeRemainder value
      output.declarativeRemainder := by
  unfold optionalLetType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .colon = true
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨colon, afterColon, colonResult, typeStage⟩
    rcases bind_ok_components typeStage with
      ⟨type, afterType, typeResult, finished⟩
    cases finished
    exact .present colon.span
      (symbol_success_exactTokenParses .colon .statement colonResult)
      (typeExpr_ordinaryOutcome_sound.1 typeResult)
  · have absent : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .colon absent)

/-- Optional let-type rejection is a committed type rejection after its
exact colon. -/
theorem optionalLetType_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : optionalLetType input = .reject failure rejected) :
    DeclarativeGrammar.OptionalLetTypeRejects
      DeclarativeGrammar.TypeExprRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalLetType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .colon = true
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .colon .statement present with
      ⟨colon, colonResult⟩
    simp only [colonResult] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | ok type afterType => simp [typeResult, pure] at result
    | reject typeFailure typeRejected =>
        simp only [typeResult] at result
        cases result
        exact .typeRejected colon.span
          (symbol_success_exactTokenParses .colon .statement colonResult)
          (typeExpr_ordinaryOutcome_sound.2 typeResult)
  · have absent : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Optional let-initializer success preserves its equal guard and ordinary
expression output. -/
theorem optionalLetInitializer_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {value : Option Expr}
    (result : optionalLetInitializer expression input = .ok value output) :
    DeclarativeGrammar.OptionalLetInitializerOrdinaryParses
      expressionOrdinary input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold optionalLetInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal = true
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨equal, afterEqual, equalResult, expressionStage⟩
    rcases bind_ok_components expressionStage with
      ⟨expressionValue, afterExpression, expressionResult, finished⟩
    cases finished
    exact .present equal.span
      (symbol_success_exactTokenParses .equal .statement equalResult)
      (expressionSuccessSound expressionResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .equal absent)

/-- Optional let-initializer rejection is a committed expression rejection
after its exact equal marker. -/
theorem optionalLetInitializer_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalLetInitializer expression input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalLetInitializerRejects expressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold optionalLetInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal = true
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .equal .statement present with
      ⟨equal, equalResult⟩
    simp only [equalResult] at result
    cases expressionResult : expression
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [expressionResult] at result
    | ok value afterExpression =>
        simp [expressionResult, pure] at result
    | reject expressionFailure expressionRejected =>
        simp only [expressionResult] at result
        cases result
        exact .expressionRejected equal.span
          (symbol_success_exactTokenParses .equal .statement equalResult)
          (expressionRejectSound expressionResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end Solcore.Syntax.Parser.StatementSimpleInternals
