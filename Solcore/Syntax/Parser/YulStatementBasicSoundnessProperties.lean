import Solcore.Syntax.DeclarativeYulStatementBasicGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedAllowEmptyDiagnosticFreeSoundnessProperties
import Solcore.Syntax.Parser.Yul.ExpressionProperties
import Solcore.Syntax.Parser.YulNamesSoundnessProperties
import Solcore.Syntax.Parser.YulStatementBasicDiagnosticReflectionProperties

/-!
Exact diagnostic-free soundness for the basic inline-Yul statement forms.
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

/-- Every optional Yul `let` initializer success follows the exact `:=`
priority and the supplied public-expression relation. -/
theorem yulLetInitializer_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {initializer : Option YulExpr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulLetInitializer input = .ok initializer next) :
    DeclarativeGrammar.YulLetInitializerParses expressionParses
      input.declarativeRemainder initializer next.declarativeRemainder := by
  unfold yulLetInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .colonEqual
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨operator, afterOperator, operatorResult, valueStage⟩
    rcases bind_ok_components valueStage with
      ⟨value, afterValue, valueResult, finished⟩
    cases finished
    exact .present operator.span
      (symbol_success_exactTokenParses .colonEqual .yulStatement
        operatorResult)
      (expressionSound diagnosticFree valueResult)
  · have absent : isSymbol input .colonEqual = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .colonEqual absent)

/-- Every diagnostic-free inline-Yul `let` success retains its exact names,
initializer priority, span, AST, and remainder. -/
theorem yulLetStatement_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {statement : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulLetStatement input = .ok statement next) :
    DeclarativeGrammar.YulLetStatementParses expressionParses
      input.declarativeRemainder statement next.declarativeRemainder := by
  unfold yulLetStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, namesStage⟩
  rcases bind_ok_components namesStage with
    ⟨names, afterNames, namesResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, finished⟩
  cases finished
  have afterNamesFree := yulLetInitializer_reflectsDiagnosticFreeOnSuccess
    afterNames initializer next initializerResult diagnosticFree
  exact .parsed marker.span names.span
    (keyword_success_exactTokenParses .letKw .yulStatement markerResult)
    (yulNames_success_sound afterNamesFree namesResult)
    (yulLetInitializer_success_sound expressionParses expressionSound
      diagnosticFree initializerResult)

/-- Every diagnostic-free inline-Yul assignment success retains the forward
target order, exact `:=`, value, covering span, and remainder. -/
theorem yulAssignment_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {statement : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulAssignment input = .ok statement next) :
    DeclarativeGrammar.YulAssignmentParses expressionParses
      input.declarativeRemainder statement next.declarativeRemainder := by
  unfold yulAssignment at result
  rcases bind_ok_components result with
    ⟨names, afterNames, namesResult, operatorStage⟩
  rcases bind_ok_components operatorStage with
    ⟨operator, afterOperator, operatorResult, valueStage⟩
  rcases bind_ok_components valueStage with
    ⟨value, afterValue, valueResult, finished⟩
  cases finished
  have afterOperatorFree := yulExpression_reflectsDiagnosticFreeOnSuccess
    afterOperator value next valueResult diagnosticFree
  have afterNamesFree := symbol_reflectsDiagnosticFreeOnSuccess .colonEqual
    .yulStatement afterNames operator afterOperator operatorResult
      afterOperatorFree
  exact .parsed names.span operator.span
    (yulNames_success_sound afterNamesFree namesResult)
    (symbol_success_exactTokenParses .colonEqual .yulStatement operatorResult)
    (expressionSound diagnosticFree valueResult)

/-- Every diagnostic-free expression-statement success is the exact lift of
the supplied public-expression relation. -/
theorem yulExpressionStatement_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {statement : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulExpressionStatement input = .ok statement next) :
    DeclarativeGrammar.YulExpressionStatementParses expressionParses
      input.declarativeRemainder statement next.declarativeRemainder := by
  unfold yulExpressionStatement at result
  rcases bind_ok_components result with
    ⟨expression, afterExpression, expressionResult, finished⟩
  cases finished
  exact .parsed (expressionSound diagnosticFree expressionResult)

/-- Every diagnostic-free source-level `return(...)` success is the exact
synthesized call, including allow-empty/trailing arguments and delimiters. -/
theorem yulReturnBuiltin_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {statement : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulReturnBuiltin input = .ok statement next) :
    DeclarativeGrammar.YulReturnBuiltinParses expressionParses
      input.declarativeRemainder statement next.declarativeRemainder := by
  unfold yulReturnBuiltin at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, argumentsStage⟩
  rcases bind_ok_components argumentsStage with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .returnKw .yulStatement markerResult)
    (delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
      .leftParen .rightParen yulExpression expressionParses .yulExpression
      .yul expressionSound yulExpression_reflectsDiagnosticFreeOnSuccess
      yulExpression_preservesTokenWindow diagnosticFree argumentsResult)

end Solcore.Syntax.Parser
