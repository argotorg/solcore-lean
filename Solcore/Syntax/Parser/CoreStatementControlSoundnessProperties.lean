import Solcore.Syntax.DeclarativeCoreStatementControlGrammar
import Solcore.Syntax.Parser.CoreStatementControlDiagnosticReflectionProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-!
Exact parser-independent soundness for basic Core control statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

namespace ControlInternals

theorem optionalElseBody_success_sound
    (statement : Parser Statement)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Option Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalElseBody statement input = .ok value next) :
    DeclarativeGrammar.OptionalElseBodyParses
      (DeclarativeGrammar.CoreBlockParses statementParses .require)
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold optionalElseBody getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .elseKw
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases bind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact .present marker.span
      (keyword_success_exactTokenParses .elseKw .statement markerResult)
      (coreBlock_success_sound statementParses statement .require
        statementReflects statementSound diagnosticFree bodyResult)
  · have absent : isKeyword input .elseKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (keywordAbsentAt_of_isKeyword_eq_false .elseKw absent)

theorem terminatedControl_success_sound
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input next : State} {value : Statement}
    (result : terminatedControl keywordValue statementValue input =
      .ok value next) :
    DeclarativeGrammar.TerminatedControlStatementParses keywordValue
      statementValue input.declarativeRemainder value
        next.declarativeRemainder := by
  unfold terminatedControl at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed marker.span semicolon.span
    (keyword_success_exactTokenParses keywordValue .statement markerResult)
    (symbol_success_exactTokenParses .semicolon .statement semicolonResult)

end ControlInternals

theorem blockStatement_success_sound
    (statement : Parser Statement)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : blockStatement statement input = .ok value next) :
    DeclarativeGrammar.BlockStatementParses
      (DeclarativeGrammar.CoreBlockParses statementParses .require)
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold blockStatement at result
  rcases bind_ok_components result with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed (coreBlock_success_sound statementParses statement .require
    statementReflects statementSound diagnosticFree bodyResult)

theorem whileStatement_success_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : whileStatement statement expression input = .ok value next) :
    DeclarativeGrammar.WhileStatementParses expressionParses
      (DeclarativeGrammar.CoreBlockParses statementParses .require)
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold whileStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, openingStage⟩
  rcases bind_ok_components openingStage with
    ⟨opening, afterOpening, openingResult, conditionStage⟩
  rcases bind_ok_components conditionStage with
    ⟨condition, afterCondition, conditionResult, closingStage⟩
  rcases bind_ok_components closingStage with
    ⟨closing, afterClosing, closingResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterClosingFree := coreBlock_reflectsDiagnosticFreeOnSuccess
    statement .require statementReflects afterClosing body next bodyResult
      diagnosticFree
  have afterConditionFree := symbol_reflectsDiagnosticFreeOnSuccess
    .rightParen .statement afterCondition closing afterClosing closingResult
      afterClosingFree
  exact .parsed marker.span opening.span closing.span
    (contextual_success_exactTokenParses .while .statement markerResult)
    (symbol_success_exactTokenParses .leftParen .statement openingResult)
    (expressionSound afterConditionFree conditionResult)
    (symbol_success_exactTokenParses .rightParen .statement closingResult)
    (coreBlock_success_sound statementParses statement .require
      statementReflects statementSound diagnosticFree bodyResult)

theorem ifStatement_success_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ifStatement statement expression input = .ok value next) :
    DeclarativeGrammar.IfStatementParses expressionParses
      (DeclarativeGrammar.CoreBlockParses statementParses .require)
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold ifStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, openingStage⟩
  rcases bind_ok_components openingStage with
    ⟨opening, afterOpening, openingResult, conditionStage⟩
  rcases bind_ok_components conditionStage with
    ⟨condition, afterCondition, conditionResult, closingStage⟩
  rcases bind_ok_components closingStage with
    ⟨closing, afterClosing, closingResult, thenStage⟩
  rcases bind_ok_components thenStage with
    ⟨thenBody, afterThen, thenResult, elseStage⟩
  rcases bind_ok_components elseStage with
    ⟨elseBody, afterElse, elseResult, finished⟩
  cases finished
  have afterThenFree :=
    ControlInternals.optionalElseBody_reflectsDiagnosticFreeOnSuccess
      statement statementReflects afterThen elseBody next elseResult
        diagnosticFree
  have afterClosingFree := coreBlock_reflectsDiagnosticFreeOnSuccess
    statement .require statementReflects afterClosing thenBody afterThen
      thenResult afterThenFree
  have afterConditionFree := symbol_reflectsDiagnosticFreeOnSuccess
    .rightParen .statement afterCondition closing afterClosing closingResult
      afterClosingFree
  exact .parsed marker.span opening.span closing.span
    (keyword_success_exactTokenParses .ifKw .statement markerResult)
    (symbol_success_exactTokenParses .leftParen .statement openingResult)
    (expressionSound afterConditionFree conditionResult)
    (symbol_success_exactTokenParses .rightParen .statement closingResult)
    (coreBlock_success_sound statementParses statement .require
      statementReflects statementSound afterThenFree thenResult)
    (ControlInternals.optionalElseBody_success_sound statement statementParses
      statementReflects statementSound diagnosticFree elseResult)

theorem breakStatement_success_sound {input next : State}
    {value : Statement} (result : breakStatement input = .ok value next) :
    DeclarativeGrammar.TerminatedControlStatementParses .breakKw .breakStmt
      input.declarativeRemainder value next.declarativeRemainder :=
  ControlInternals.terminatedControl_success_sound .breakKw .breakStmt result

theorem continueStatement_success_sound {input next : State}
    {value : Statement} (result : continueStatement input = .ok value next) :
    DeclarativeGrammar.TerminatedControlStatementParses .continueKw
      .continueStmt input.declarativeRemainder value
        next.declarativeRemainder :=
  ControlInternals.terminatedControl_success_sound .continueKw .continueStmt
    result

end Solcore.Syntax.Parser
