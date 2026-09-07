import Solcore.Syntax.DeclarativeLambdaExpressionTraceGrammar
import Solcore.Syntax.DeclarativeParameterListTraceProperties
import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceExactnessProperties
import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceProtectionProperties
import Solcore.Syntax.DeclarativeTypeExprTraceOutcomeProperties
import Solcore.Syntax.DeclarativeTypeExprTraceStructuralProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Raw lambda exactness assumes only exact outcomes for the supplied body
relations. Parameters and optional return types already have concrete exactness.
No body carrier/progress law or atom-selection guard is added. Parameter and
body events are filtered explicitly; only return-type events are protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem returnsExactOutcomeSpec :
    TraceExactOutcomeSpec (OptionalLambdaReturnTypeTraceParses TypeExprTraceParses)
      (OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects) source endByte :=
  optionalLambdaReturnTypeTraceExactOutcomeSpec typeExprTraceExactOutcomeSpec

theorem LambdaExpressionTraceParses.result_unique
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : LambdaExpressionTraceParses blockTrace source endByte input left afterLeft leftTrace)
    (rightParsed : LambdaExpressionTraceParses blockTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed _ leftMarker leftParameters leftReturn leftBody =>
      cases rightParsed with
      | parsed _ rightMarker rightParameters rightReturn rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨rfl, rfl⟩
          rcases lambdaParametersTraceExactOutcomeSpec.successResultUnique leftParameters rightParameters with ⟨rfl, rfl, rfl⟩
          rcases returnsExactOutcomeSpec.successResultUnique leftReturn rightReturn with ⟨rfl, rfl, rfl⟩
          rcases blocks.successResultUnique leftBody rightBody with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

private theorem marker_absent_conflicts {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .lamKw))
    (marker : ExactTokenParses (.keyword .lamKw) input span output) : False := absent ⟨span, marker.1⟩

theorem LambdaExpressionTraceRejects.result_unique
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : LambdaExpressionTraceRejects blockRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : LambdaExpressionTraceRejects blockRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  have parameters := @lambdaParametersTraceExactOutcomeSpec source endByte
  have parameterUnique := @parameters.successResultUnique
  have parameterRejectUnique := @parameters.rejectResultUnique
  have parameterDisjoint := @parameters.successRejectDisjoint
  have returns := @returnsExactOutcomeSpec source endByte
  have returnUnique := @returns.successResultUnique
  have returnRejectUnique := @returns.rejectResultUnique
  have returnDisjoint := @returns.successRejectDisjoint
  have bodyUnique := @blocks.rejectResultUnique
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 16) only [ExactTokenParses.result_unique, marker_absent_conflicts,
      RejectAtReports.diagnostic_unique]

theorem LambdaExpressionTraceRejects.disjoint_success
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaExpressionTraceRejects blockRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, LambdaExpressionTraceParses blockTrace source endByte input value output events := by
  have parameters := @lambdaParametersTraceExactOutcomeSpec source endByte
  have parameterUnique := @parameters.successResultUnique
  have parameterDisjoint := @parameters.successRejectDisjoint
  have returns := @returnsExactOutcomeSpec source endByte
  have returnUnique := @returns.successResultUnique
  have returnDisjoint := @returns.successRejectDisjoint
  have bodyDisjoint := @blocks.successRejectDisjoint
  rintro ⟨value, output, events, parsed⟩
  cases parsed
  cases rejection <;>
    grind (ematch := 16) only [ExactTokenParses.result_unique, marker_absent_conflicts]

theorem lambdaExpressionTraceExactOutcomeSpec
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte) :
    TraceExactOutcomeSpec (LambdaExpressionTraceParses blockTrace)
      (LambdaExpressionTraceRejects blockRejects) source endByte where
  successResultUnique := LambdaExpressionTraceParses.result_unique blocks
  rejectResultUnique := LambdaExpressionTraceRejects.result_unique blocks
  successRejectDisjoint := LambdaExpressionTraceRejects.disjoint_success blocks

/-- Successful return annotations retain their protected events between two
explicitly filtered, possibly recovering component traces. -/
theorem lambdaExpressionTrace_cascadeFilters
    {input output : Remainder} {returnType : Option Syntax.TypeExpr}
    {parameterEvents returnEvents bodyEvents keptParameters keptBody : List ParseDiagnostic}
    (returnParsed : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses source endByte
      input returnType output returnEvents)
    (text : String) (lexical : List SourceSpan)
    (parametersFiltered : ParseDiagnosticCascadeFilters text lexical parameterEvents keptParameters)
    (bodyFiltered : ParseDiagnosticCascadeFilters text lexical bodyEvents keptBody) :
    ParseDiagnosticCascadeFilters text lexical ((parameterEvents ++ returnEvents) ++ bodyEvents)
      ((keptParameters ++ returnEvents) ++ keptBody) :=
  (parametersFiltered.append (returnParsed.cascadeFilters (fun parsed => parsed.cascadeFilters text lexical))).append
    bodyFiltered

/-- A rejected annotation retains prior parameter events through their explicit
filter and protects only its own preceding type events, not its terminal report. -/
theorem lambdaExpressionReturnRejectionTrace_cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic}
    {parameterEvents returnEvents keptParameters : List ParseDiagnostic}
    (returnRejected : OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects source endByte
      input rejected report returnEvents)
    (text : String) (lexical : List SourceSpan)
    (parametersFiltered : ParseDiagnosticCascadeFilters text lexical parameterEvents keptParameters) :
    ParseDiagnosticCascadeFilters text lexical (parameterEvents ++ returnEvents) (keptParameters ++ returnEvents) :=
  parametersFiltered.append (returnRejected.cascadeFilters (fun rejection => rejection.cascadeFilters text lexical))

end Solcore.Syntax.DeclarativeGrammar
