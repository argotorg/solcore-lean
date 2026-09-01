import Solcore.Syntax.DeclarativeYulStatementControlGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.YulBlockSoundnessProperties
import Solcore.Syntax.Parser.YulStatementControlDiagnosticReflectionProperties

/-!
Exact diagnostic-free soundness for Yul block, `if`, and `for` statements.
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

theorem yulBlockStatement_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulBlockStatement statement input = .ok value next) :
    DeclarativeGrammar.YulBlockStatementParses statementParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulBlockStatement at result
  rcases bind_ok_components result with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed (yulBlock_success_sound statement statementParses
    statementReflects statementSound diagnosticFree bodyResult)

theorem yulIfStatement_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulIfStatement statement input = .ok value next) :
    DeclarativeGrammar.YulIfStatementParses statementParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulIfStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, conditionStage⟩
  rcases bind_ok_components conditionStage with
    ⟨condition, afterCondition, conditionResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterConditionFree := yulBlock_reflectsDiagnosticFreeOnSuccess
    statement statementReflects afterCondition body next bodyResult
      diagnosticFree
  exact .parsed marker.span
    (keyword_success_exactTokenParses .ifKw .yulStatement markerResult)
    (expressionSound afterConditionFree conditionResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound diagnosticFree bodyResult)

theorem yulForStatement_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulForStatement statement input = .ok value next) :
    DeclarativeGrammar.YulForStatementParses statementParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulForStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, conditionStage⟩
  rcases bind_ok_components conditionStage with
    ⟨condition, afterCondition, conditionResult, postStage⟩
  rcases bind_ok_components postStage with
    ⟨post, afterPost, postResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterPostFree := yulBlock_reflectsDiagnosticFreeOnSuccess statement
    statementReflects afterPost body next bodyResult diagnosticFree
  have afterConditionFree := yulBlock_reflectsDiagnosticFreeOnSuccess
    statement statementReflects afterCondition post afterPost postResult
      afterPostFree
  have afterInitializerFree :=
    yulExpression_reflectsDiagnosticFreeOnSuccess afterInitializer condition
      afterCondition conditionResult afterConditionFree
  exact .parsed marker.span
    (keyword_success_exactTokenParses .forKw .yulStatement markerResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound afterInitializerFree initializerResult)
    (expressionSound afterConditionFree conditionResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound afterPostFree postResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound diagnosticFree bodyResult)

end Solcore.Syntax.Parser
