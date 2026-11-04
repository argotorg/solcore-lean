import Solcore.Syntax.Internal.ParameterTrace
import Solcore.Syntax.Internal.ExpressionTrace
import Solcore.Syntax.Internal.TypeTrace
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.DelimitedTrace
import Solcore.Syntax.Internal.NameTrace
import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Internal.TraceBasics
import Solcore.Syntax.Grammar.Types

/-!
Exact diagnostic traces of leading-dot constructors, postfix tails and lambda expressions:
trace grammars, unique outcomes and protection of earlier events.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaExpressionTraceGrammar
/-! Raw lambda expressions retain their marker, complete parameter list,
optional return annotation, and body. Parameter recovery events are committed
before return and body events. Every first failure has a separate terminal
report; these judgments impose no atom-dispatch guard or body frame. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def lambdaExpressionTraceValue (marker : SourceSpan)
    (parameters : Syntax.DelimitedList Syntax.LambdaParameter)
    (returnType : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr := {
  span := SourceSpan.cover marker body.span
  value := .lambda marker parameters returnType body
}

inductive LambdaExpressionTraceParses
    (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterParameters afterReturn output : Remainder}
      {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {returnType : Option Syntax.TypeExpr}
      {body : Syntax.Block} {parameterEvents returnEvents bodyEvents : List ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword .lamKw) input markerSpan afterMarker)
      (parameterList : LambdaParametersTraceParses source endByte afterMarker parameters afterParameters parameterEvents)
      (returnParsed : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses source endByte
        afterParameters returnType afterReturn returnEvents)
      (bodyParsed : blockTrace source endByte afterReturn body output bodyEvents) :
      LambdaExpressionTraceParses blockTrace source endByte input
        (lambdaExpressionTraceValue markerSpan parameters returnType body) output
        ((parameterEvents ++ returnEvents) ++ bodyEvents)

inductive LambdaExpressionTraceRejects
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .lamKw))
      (reported : RejectAtReports source endByte { head := .keyword .lamKw, tail := [] } .expression input report) :
      LambdaExpressionTraceRejects blockRejects source endByte input input report []
  | parametersRejected {input afterMarker rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword .lamKw) input markerSpan afterMarker)
      (parameters : LambdaParametersTraceRejects source endByte afterMarker rejected report trace) :
      LambdaExpressionTraceRejects blockRejects source endByte input rejected report trace
  | returnTypeRejected {input afterMarker afterParameters rejected : Remainder}
      {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {report : ParseDiagnostic}
      {parameterEvents returnEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword .lamKw) input markerSpan afterMarker)
      (parameterList : LambdaParametersTraceParses source endByte afterMarker parameters afterParameters parameterEvents)
      (returnRejected : OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects source endByte
        afterParameters rejected report returnEvents) :
      LambdaExpressionTraceRejects blockRejects source endByte input rejected report (parameterEvents ++ returnEvents)
  | bodyRejected {input afterMarker afterParameters afterReturn rejected : Remainder}
      {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {returnType : Option Syntax.TypeExpr}
      {report : ParseDiagnostic} {parameterEvents returnEvents bodyEvents : List ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword .lamKw) input markerSpan afterMarker)
      (parameterList : LambdaParametersTraceParses source endByte afterMarker parameters afterParameters parameterEvents)
      (returnParsed : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses source endByte
        afterParameters returnType afterReturn returnEvents)
      (bodyRejected : blockRejects source endByte afterReturn rejected report bodyEvents) :
      LambdaExpressionTraceRejects blockRejects source endByte input rejected report
        ((parameterEvents ++ returnEvents) ++ bodyEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaExpressionTraceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDotConstructorTraceGrammar
/-! Independent leading-dot constructor success traces. Names are Boolean
first and checked spelling events precede argument events. Optional argument
absence is silent and leaves the remainder unchanged. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OptionalDotConstructorArgumentsTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option (DelimitedList Syntax.Expr) → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen)) :
      OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input none input []
  | present {input output : Remainder} {arguments : DelimitedList Syntax.Expr}
      {trace : List ParseDiagnostic}
      (parsed : NoTrailingDelimitedListTraceParses .leftParen .rightParen true elementTrace source endByte
        input arguments output trace) :
      OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input (some arguments) output trace

inductive DotConstructorTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterDot afterName output : Remainder} {name : Syntax.Identifier}
      {arguments : Option (DelimitedList Syntax.Expr)} {nameEvents argumentEvents : List ParseDiagnostic}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : ExpressionNameTraceParses source endByte afterDot name afterName nameEvents)
      (argumentsParsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte
        afterName arguments output argumentEvents) :
      DotConstructorTraceParses elementTrace source endByte input {
        span := SourceSpan.cover dotSpan (arguments.map (fun values => values.span) |>.getD name.span)
        value := .dotConstructor dotSpan name arguments
      } output (nameEvents ++ argumentEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDotConstructorRejectionTraceGrammar
/-! Exact raw leading-dot rejection traces. A missing dot is represented even
outside dispatcher selection. Optional arguments commit only on a left parenthesis;
successful name events precede argument rejection events and the report is uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OptionalDotConstructorArgumentsTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | present {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan, value := .symbol .leftParen })
      (argumentsRejected : NoTrailingDelimitedListTraceRejects .leftParen .rightParen true .expression
        elementTrace elementRejects source endByte input rejected diagnostic trace) :
      OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
        input rejected diagnostic trace

inductive DotConstructorTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | dotMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (reported : RejectAtReports source endByte { head := .symbol .dot, tail := [] }
        .expression input diagnostic) :
      DotConstructorTraceRejects elementTrace elementRejects source endByte input input diagnostic []
  | nameRejected {input afterDot rejected : Remainder} {diagnostic : ParseDiagnostic}
      {trace : List ParseDiagnostic} (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameRejected : ExpressionNameTraceRejects source endByte afterDot rejected diagnostic trace) :
      DotConstructorTraceRejects elementTrace elementRejects source endByte input rejected diagnostic trace
  | argumentsRejected {input afterDot afterName rejected : Remainder} {name : Syntax.Identifier}
      {diagnostic : ParseDiagnostic} {nameEvents argumentEvents : List ParseDiagnostic} (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : ExpressionNameTraceParses source endByte afterDot name afterName nameEvents)
      (argumentsRejected : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects
        source endByte afterName rejected diagnostic argumentEvents) :
      DotConstructorTraceRejects elementTrace elementRejects source endByte
        input rejected diagnostic (nameEvents ++ argumentEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDotConstructorRejectionTraceProperties
/-! Independent rejection erasure, functionality, and exclusion. The older
ordinary dot relation is dispatcher-selected, so raw-dot erasure explicitly
separates missing-dot rejection instead of silently strengthening that relation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryParses : Remainder → Syntax.Expr → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem OptionalDotConstructorArgumentsTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
      input rejected diagnostic trace) :
    OptionalDotConstructorArgumentsRejects ordinaryParses ordinaryRejects input rejected := by
  cases rejection with
  | present span opening arguments => exact .present span opening (arguments.ordinary successErases rejectErases)

theorem DotConstructorTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DotConstructorTraceRejects elementTrace elementRejects source endByte input rejected diagnostic trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot) ∧ rejected = input) ∨
      DotConstructorRejects ordinaryParses ordinaryRejects input rejected := by
  cases rejection with
  | dotMissing absent reported => exact .inl ⟨absent, rfl⟩
  | nameRejected span dot name => exact .inr (.nameRejected span dot name.ordinary)
  | argumentsRejected span dot name arguments =>
      exact .inr (.argumentsRejected span dot name.ordinary (arguments.ordinary successErases rejectErases))

theorem DotConstructorTraceRejects.ordinary_of_dot_present
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .dot })
    (rejection : DotConstructorTraceRejects elementTrace elementRejects source endByte input rejected diagnostic trace) :
    DotConstructorRejects ordinaryParses ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases with missing | ordinary
  · exact False.elim (missing.1 selected)
  · exact ordinary

variable
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    elementTrace source endByte input left afterLeft leftTrace →
    elementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    elementRejects source endByte input afterLeft leftReport leftTrace →
    elementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected diagnostic trace},
    elementRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, elementTrace source endByte input value output events)

include successUnique rejectUnique disjoint in
theorem OptionalDotConstructorArgumentsTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | present _ _ left =>
      cases right with
      | present _ _ right => exact left.result_unique successUnique rejectUnique disjoint right

include successUnique rejectUnique disjoint in
theorem DotConstructorTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : DotConstructorTraceRejects elementTrace elementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : DotConstructorTraceRejects elementTrace elementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | dotMissing absent reported =>
      cases right with
      | dotMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | nameRejected span dot _ | argumentsRejected span dot _ _ => exact False.elim (absent ⟨span, dot.1⟩)
  | nameRejected span dot name =>
      cases right with
      | dotMissing absent _ => exact False.elim (absent ⟨span, dot.1⟩)
      | nameRejected _ otherDot otherName =>
          cases dot.output_unique otherDot
          exact name.result_unique otherName
      | argumentsRejected _ otherDot otherName _ =>
          cases dot.output_unique otherDot
          exact False.elim (name.disjoint_success otherName)
  | argumentsRejected span dot name arguments =>
      cases right with
      | dotMissing absent _ => exact False.elim (absent ⟨span, dot.1⟩)
      | nameRejected _ otherDot otherName =>
          cases dot.output_unique otherDot
          exact False.elim (otherName.disjoint_success name)
      | argumentsRejected _ otherDot otherName otherArguments =>
          cases dot.output_unique otherDot
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases arguments.result_unique successUnique rejectUnique disjoint otherArguments with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique disjoint in
theorem OptionalDotConstructorArgumentsTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {trace events : List ParseDiagnostic}
    {arguments : Option (DelimitedList Syntax.Expr)}
    (rejection : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
      input rejected diagnostic trace)
    (success : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments after events) : False := by
  cases rejection with
  | present span opening rejected =>
      cases success with
      | absent absent => exact absent ⟨span, opening⟩
      | present parsed => exact rejected.disjoint_success successUnique disjoint ⟨_, _, _, parsed⟩

include successUnique disjoint in
theorem DotConstructorTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {trace events : List ParseDiagnostic}
    {value : Syntax.Expr}
    (rejection : DotConstructorTraceRejects elementTrace elementRejects source endByte input rejected diagnostic trace)
    (success : DotConstructorTraceParses elementTrace source endByte input value after events) : False := by
  cases success with
  | parsed _ dot name arguments =>
      cases rejection with
      | dotMissing absent reported => exact absent ⟨_, dot.1⟩
      | nameRejected _ otherDot rejectedName =>
          cases dot.output_unique otherDot
          exact rejectedName.disjoint_success name
      | argumentsRejected _ otherDot otherName rejectedArguments =>
          cases dot.output_unique otherDot
          cases (name.result_unique otherName).2.1
          exact rejectedArguments.disjoint_success successUnique disjoint arguments

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDotConstructorRejectionTraceProtectionProperties
/-! A checked constructor name remains protected when its argument list
later rejects. Protected child events follow it in order, while the separate
uncommitted failure report is not included in this preservation claim. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalDotConstructorArgumentsTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | present _ _ arguments => exact arguments.cascadeFilters successProtected rejectProtected

theorem DotConstructorTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DotConstructorTraceRejects elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | dotMissing => exact .nil
  | nameRejected _ _ name => exact name.cascadeFilters text lexical
  | argumentsRejected _ _ name arguments =>
      exact (name.cascadeFilters text lexical).append
        (arguments.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionAtomDispatchTraceGrammar
/-! One prioritized expression-atom layer over supplied expression and block
trace relations. Literal/name leaves and proxy types are concrete; recovering
lambda parameters and return types are also concrete. Final rejection emits no
event. These judgments do not claim recursive expression or block existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionAtomDispatchFinalTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | rejected {input : Remainder} {report : ParseDiagnostic}
      (reported : RejectAtReports source endByte { head := .expression, tail := [] } .expression input report) :
      ExpressionAtomDispatchFinalTraceRejects source endByte input input report []

def ExpressionAtomDispatchRawTraceParses
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
    (branch : ExpressionAtomDispatchBranch) :
    SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop :=
  match branch with
  | .literal => LiteralExpressionTraceParses
  | .name => IdentifierExpressionTraceParses
  | .dotConstructor => DotConstructorTraceParses nestedTrace
  | .proxy => ProxyExpressionTraceParses TypeExprTraceParses
  | .parenthesized => ParenthesizedExpressionTraceParses nestedTrace
  | .array => ArrayLiteralTraceParses nestedTrace
  | .lambda => LambdaExpressionTraceParses blockTrace
  | .final => fun _ _ _ _ _ _ => False

def ExpressionAtomDispatchRawTraceRejects
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (branch : ExpressionAtomDispatchBranch) :
    SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop :=
  match branch with
  | .literal => LiteralExpressionTraceRejects
  | .name => IdentifierExpressionTraceRejects
  | .dotConstructor => DotConstructorTraceRejects nestedTrace nestedRejects
  | .proxy => ProxyExpressionTraceRejects TypeExprTraceRejects
  | .parenthesized => ParenthesizedExpressionTraceRejects nestedTrace nestedRejects
  | .array => ArrayLiteralTraceRejects nestedTrace nestedRejects
  | .lambda => LambdaExpressionTraceRejects blockRejects
  | .final => ExpressionAtomDispatchFinalTraceRejects

inductive ExpressionAtomDispatchTraceParses
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | selected {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
      (branch : ExpressionAtomDispatchBranch)
      (selection : ExpressionAtomDispatchSelects input branch)
      (parsed : ExpressionAtomDispatchRawTraceParses nestedTrace blockTrace branch source endByte input value output trace) :
      ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input value output trace

inductive ExpressionAtomDispatchTraceRejects
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | selected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (branch : ExpressionAtomDispatchBranch)
      (selection : ExpressionAtomDispatchSelects input branch)
      (rejection : ExpressionAtomDispatchRawTraceRejects nestedTrace nestedRejects blockRejects branch
        source endByte input rejected report trace) :
      ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDotConstructorTraceProtectionProperties
/-! Checked name events are intrinsically protected; protected argument
events follow them without reordering, dropping metadata, or deduplication. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalDotConstructorArgumentsTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {arguments : Option (DelimitedList Syntax.Expr)} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present args => exact args.cascadeFilters elementProtected

theorem DotConstructorTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed span dot name args =>
      exact (name.cascadeFilters text lexical).append (args.cascadeFilters elementProtected)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDotConstructorTraceProperties
/-! Ordinary erasure, progress, and exact structure. The older whole-list
grammar needs child carrier/end-index preservation, supplied separately here. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {elementParses : Remainder → Syntax.Expr → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalDotConstructorArgumentsTraceParses.present_token
    {input output : Remainder} {arguments : DelimitedList Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte
      input (some arguments) output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen } := by
  cases parsed with
  | present arguments =>
      cases arguments with
      | empty span _ _ opening _ | nonempty span _ opening _ _ _ _ => exact ⟨span, opening.1⟩

theorem OptionalDotConstructorArgumentsTraceParses.ordinary
    (erases : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {arguments : Option (DelimitedList Syntax.Expr)} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    OptionalDotConstructorArgumentsParses elementParses input arguments output := by
  cases parsed with
  | absent absent => exact .absent absent
  | present arguments => exact .present (arguments.ordinary erases elementWindow)

theorem DotConstructorTraceParses.ordinary
    (erases : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses elementTrace source endByte input value output trace) :
    DotConstructorParses elementParses input value output := by
  cases parsed with
  | parsed span dot name args => exact .parsed span dot name.ordinary (args.ordinary erases elementWindow)

theorem OptionalDotConstructorArgumentsTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {arguments : Option (DelimitedList Syntax.Expr)} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present args => exact args.output_window elementWindow

theorem DotConstructorTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed span dot name args =>
      have frame := args.output_window elementWindow
      simpa only [name.output_eq, dot.2] using frame

theorem OptionalDotConstructorArgumentsTraceParses.cursor_le
    {input output : Remainder} {arguments : Option (DelimitedList Syntax.Expr)} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    input.cursor ≤ output.cursor := by
  cases parsed with
  | absent => exact Nat.le_refl _
  | present args =>
      cases args with
      | empty _ _ _ opening closing =>
          rw [closing.2, opening.2]
          exact Nat.le_add_right _ 2
      | nonempty _ _ opening _ _ progress tail =>
          have finalProgress := tail.progress
          rw [opening.2] at progress
          exact Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_lt progress))
            (Nat.le_of_lt finalProgress)

theorem DotConstructorTraceParses.cursor_lt
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed span dot name args =>
      have progress := args.cursor_le
      rw [name.output_eq, dot.2] at progress
      exact Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)) progress

theorem OptionalDotConstructorArgumentsTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option (DelimitedList Syntax.Expr)}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent absent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present args => exact False.elim (absent (OptionalDotConstructorArgumentsTraceParses.present args).present_token)
  | present args =>
      cases rightParsed with
      | absent absent => exact False.elim (absent (OptionalDotConstructorArgumentsTraceParses.present args).present_token)
      | present other =>
          rcases args.result_unique unique other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem DotConstructorTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : DotConstructorTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : DotConstructorTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed span dot name args =>
      cases rightParsed with
      | parsed _ otherDot otherName otherArgs =>
          rcases dot.result_unique otherDot with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases args.result_unique unique otherArgs with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDotConstructorTraceOutcomeProperties
/-! Independent joint exactness for optional arguments and raw leading-dot
constructors. Child laws determine values, endpoints, reports, and whole event
sequences; neither existence nor general recursive expression execution is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem optionalDotConstructorArgumentsTraceExactOutcomeSpec
    (elements : ExpressionTraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (OptionalDotConstructorArgumentsTraceParses elementTrace)
      (OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := OptionalDotConstructorArgumentsTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := OptionalDotConstructorArgumentsTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := by
    rintro input rejected diagnostic trace rejection ⟨arguments, output, events, success⟩
    exact rejection.disjoint_success elements.successResultUnique elements.successRejectDisjoint success

theorem dotConstructorTraceExactOutcomeSpec
    (elements : ExpressionTraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    ExpressionTraceExactOutcomeSpec (DotConstructorTraceParses elementTrace)
      (DotConstructorTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := DotConstructorTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := DotConstructorTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := by
    rintro input rejected diagnostic trace rejection ⟨value, output, events, success⟩
    exact rejection.disjoint_success elements.successResultUnique elements.successRejectDisjoint success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePostfixTailTraceGrammar
/-! Independent maximal postfix traces. Index, call, and checked-identifier
field suffixes retain their ordered lookahead guards and exact AST spans.
Only call arguments enforce the existing delimited-list child progress rule;
index expressions do not acquire a new progress or carrier restriction. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def postfixIndexTraceValue (base index : Syntax.Expr)
    (openingSpan closingSpan : SourceSpan) : Syntax.Expr := {
  span := SourceSpan.cover base.span closingSpan
  value := .index base (SourceSpan.cover openingSpan closingSpan) index
}

def postfixCallTraceValue (base : Syntax.Expr)
    (arguments : DelimitedList Syntax.Expr) : Syntax.Expr := {
  span := SourceSpan.cover base.span arguments.span
  value := .call base arguments
}

def postfixFieldTraceValue (base : Syntax.Expr) (dotSpan : SourceSpan)
    (name : Syntax.Identifier) : Syntax.Expr := {
  span := SourceSpan.cover base.span name.span
  value := .field base dotSpan name
}

inductive PostfixTailTraceParses
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | done {input : Remainder} {base : Syntax.Expr}
      (absent : PostfixSuffixAbsentAt input) :
      PostfixTailTraceParses nestedTrace source endByte input base base input []
  | index {input afterOpening afterIndex afterClosing output : Remainder}
      {base index expression : Syntax.Expr} {indexEvents tailEvents : List ParseDiagnostic}
      (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input openingSpan afterOpening)
      (indexParsed : nestedTrace source endByte afterOpening index afterIndex indexEvents)
      (closingToken : ExactTokenParses (.symbol .rightBracket) afterIndex closingSpan afterClosing)
      (tail : PostfixTailTraceParses nestedTrace source endByte afterClosing
        (postfixIndexTraceValue base index openingSpan closingSpan) expression output tailEvents) :
      PostfixTailTraceParses nestedTrace source endByte input base expression output (indexEvents ++ tailEvents)
  | call {input afterArguments output : Remainder}
      {base expression : Syntax.Expr} {arguments : DelimitedList Syntax.Expr}
      {argumentEvents tailEvents : List ParseDiagnostic}
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (argumentsParsed : NoTrailingDelimitedListTraceParses .leftParen .rightParen true
        nestedTrace source endByte input arguments afterArguments argumentEvents)
      (tail : PostfixTailTraceParses nestedTrace source endByte afterArguments
        (postfixCallTraceValue base arguments) expression output tailEvents) :
      PostfixTailTraceParses nestedTrace source endByte input base expression output (argumentEvents ++ tailEvents)
  | field {input afterDot afterName output : Remainder}
      {base expression : Syntax.Expr} {name : Syntax.Identifier}
      {nameEvents tailEvents : List ParseDiagnostic} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : IdentifierTraceParses afterDot name afterName nameEvents)
      (tail : PostfixTailTraceParses nestedTrace source endByte afterName
        (postfixFieldTraceValue base dotSpan name) expression output tailEvents) :
      PostfixTailTraceParses nestedTrace source endByte input base expression output (nameEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePostfixTailRejectionTraceGrammar
/-! Independent exact postfix rejections. Selected opening markers cannot
fail; failures occur in the nested index, its closing bracket, call arguments,
the checked field identifier, or a later suffix. Earlier emitted events remain
ordered, and the terminal report is never appended as an emitted event. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive PostfixTailTraceRejects
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | indexNestedRejected {input afterOpening rejected : Remainder}
      {base : Syntax.Expr} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input openingSpan afterOpening)
      (nestedRejected : nestedRejects source endByte afterOpening rejected report trace) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report trace
  | indexClosingMissing {input afterOpening afterIndex : Remainder}
      {base index : Syntax.Expr} {report : ParseDiagnostic} {indexEvents : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input openingSpan afterOpening)
      (indexParsed : nestedTrace source endByte afterOpening index afterIndex indexEvents)
      (closingAbsent : TokenKindAbsentAt afterIndex.tokens afterIndex.endIndex afterIndex.cursor (.symbol .rightBracket))
      (reported : RejectAtReports source endByte { head := .symbol .rightBracket, tail := [] }
        .expression afterIndex report) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base afterIndex report indexEvents
  | indexLaterRejected {input afterOpening afterIndex afterClosing rejected : Remainder}
      {base index : Syntax.Expr} {report : ParseDiagnostic}
      {indexEvents tailEvents : List ParseDiagnostic} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input openingSpan afterOpening)
      (indexParsed : nestedTrace source endByte afterOpening index afterIndex indexEvents)
      (closingToken : ExactTokenParses (.symbol .rightBracket) afterIndex closingSpan afterClosing)
      (tailRejected : PostfixTailTraceRejects nestedTrace nestedRejects source endByte afterClosing
        (postfixIndexTraceValue base index openingSpan closingSpan) rejected report tailEvents) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report (indexEvents ++ tailEvents)
  | callArgumentsRejected {input rejected : Remainder}
      {base : Syntax.Expr} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (openingToken : TokenAt input.tokens input.endIndex input.cursor { span := openingSpan, value := .symbol .leftParen })
      (argumentsRejected : NoTrailingDelimitedListTraceRejects .leftParen .rightParen true .expression
        nestedTrace nestedRejects source endByte input rejected report trace) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report trace
  | callLaterRejected {input afterArguments rejected : Remainder}
      {base : Syntax.Expr} {arguments : DelimitedList Syntax.Expr} {report : ParseDiagnostic}
      {argumentEvents tailEvents : List ParseDiagnostic}
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (argumentsParsed : NoTrailingDelimitedListTraceParses .leftParen .rightParen true
        nestedTrace source endByte input arguments afterArguments argumentEvents)
      (tailRejected : PostfixTailTraceRejects nestedTrace nestedRejects source endByte afterArguments
        (postfixCallTraceValue base arguments) rejected report tailEvents) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report (argumentEvents ++ tailEvents)
  | fieldNameRejected {input afterDot : Remainder}
      {base : Syntax.Expr} {report : ParseDiagnostic} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameAbsent : IdentifierAbsentAt afterDot)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] }
        .expression afterDot report) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base afterDot report []
  | fieldLaterRejected {input afterDot afterName rejected : Remainder}
      {base : Syntax.Expr} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : IdentifierTraceParses afterDot name afterName nameEvents)
      (tailRejected : PostfixTailTraceRejects nestedTrace nestedRejects source endByte afterName
        (postfixFieldTraceValue base dotSpan name) rejected report tailEvents) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report (nameEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionPostfixTraceGrammar
/-! Independent atom-plus-maximal-postfix traces. Atom events precede every
suffix event. The first rejecting report is retained separately, never appended
as an emitted event by this composition. No parser state or fuel occurs here. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionPostfixTraceParses
    (atomTrace nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterAtom output : Remainder} {base value : Syntax.Expr}
      {atomEvents tailEvents : List ParseDiagnostic}
      (atomParsed : atomTrace source endByte input base afterAtom atomEvents)
      (tailParsed : PostfixTailTraceParses nestedTrace source endByte afterAtom base value output tailEvents) :
      ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input value output (atomEvents ++ tailEvents)

inductive ExpressionPostfixTraceRejects
    (atomTrace nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | atomRejected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (atomRejected : atomRejects source endByte input rejected report trace) :
      ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
        input rejected report trace
  | tailRejected {input afterAtom rejected : Remainder} {base : Syntax.Expr} {report : ParseDiagnostic}
      {atomEvents tailEvents : List ParseDiagnostic}
      (atomParsed : atomTrace source endByte input base afterAtom atomEvents)
      (tailRejected : PostfixTailTraceRejects nestedTrace nestedRejects source endByte
        afterAtom base rejected report tailEvents) :
      ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
        input rejected report (atomEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePostfixTailTraceProperties
/-! Fixed-base postfix success functionality follows from independent child
functionality. No child carrier, progress, parser, or existence law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem NoTrailingDelimitedListTraceParses.opening_present
    {α : Type} {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    {opening closing : Symbol} {allowEmpty : Bool} {input output : Remainder}
    {values : DelimitedList α} {events : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      source endByte input values output events) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol opening } := by
  cases parsed with
  | empty span _ _ token _ | nonempty span _ token _ _ _ _ => exact ⟨span, token.1⟩

private theorem absent_conflicts_exact {kind : TokenKind} {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False := absent ⟨span, parsed.1⟩

private theorem absent_conflicts_token {kind : TokenKind} {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

theorem PostfixTailTraceParses.result_unique
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input afterLeft afterRight : Remainder} {base left right : Syntax.Expr}
    {leftEvents rightEvents : List ParseDiagnostic}
    (leftParsed : PostfixTailTraceParses nestedTrace source endByte input base left afterLeft leftEvents)
    (rightParsed : PostfixTailTraceParses nestedTrace source endByte input base right afterRight rightEvents) :
    left = right ∧ afterLeft = afterRight ∧ leftEvents = rightEvents := by
  have arguments := noTrailingDelimitedListTraceExactOutcomeSpec .leftParen .rightParen true .expression nested
  induction leftParsed generalizing right afterRight rightEvents <;> cases rightParsed <;>
    grind (ematch := 20) [PostfixSuffixAbsentAt, absent_conflicts_exact, absent_conflicts_token,
      ExactTokenParses.result_unique, nested.successResultUnique,
      NoTrailingDelimitedListTraceParses.opening_present,
      arguments.successResultUnique, IdentifierTraceParses.result_unique]

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePostfixTailRejectionTraceProperties
/-! Exact postfix failures and success/rejection disjointness use independent
nested outcome laws only. Earlier events are retained in order; no existence,
recursive parser closure, progress, or carrier law follows from this bundle. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem identifier_absent_conflicts_trace {input output : Remainder}
    {name : Syntax.Identifier} {events : List ParseDiagnostic}
    (absent : IdentifierAbsentAt input) (parsed : IdentifierTraceParses input name output events) : False := by
  cases parsed with
  | parsed ordinary _ => exact absent ⟨name.span, name.value, ordinary.1⟩

/-- Rejection functionality is independent even of the accumulated base AST. -/
theorem PostfixTailTraceRejects.result_unique
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftBase rightBase : Syntax.Expr}
    {leftReport rightReport : ParseDiagnostic} {leftEvents rightEvents : List ParseDiagnostic}
    (left : PostfixTailTraceRejects nestedTrace nestedRejects source endByte
      input leftBase afterLeft leftReport leftEvents)
    (right : PostfixTailTraceRejects nestedTrace nestedRejects source endByte
      input rightBase afterRight rightReport rightEvents) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftEvents = rightEvents := by
  have arguments := noTrailingDelimitedListTraceExactOutcomeSpec .leftParen .rightParen true .expression nested
  induction left generalizing rightBase afterRight rightReport rightEvents <;> cases right <;>
    grind (ematch := 20) [absent_conflicts_exact, absent_conflicts_token,
      identifier_absent_conflicts_trace, ExactTokenParses.result_unique,
      nested.successResultUnique, nested.rejectResultUnique, nested.successRejectDisjoint,
      NoTrailingDelimitedListTraceParses.opening_present, arguments.successResultUnique,
      arguments.rejectResultUnique, arguments.successRejectDisjoint,
      IdentifierTraceParses.result_unique, RejectAtReports.diagnostic_unique]

/-- The rejected base need not equal the successful base: selection and child
outcomes already exclude every success at this same starting remainder. -/
theorem PostfixTailTraceRejects.disjoint_success
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input rejected : Remainder} {base : Syntax.Expr} {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (rejection : PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report events) :
    ¬ ∃ otherBase value after trace, PostfixTailTraceParses nestedTrace source endByte input otherBase value after trace := by
  have arguments := noTrailingDelimitedListTraceExactOutcomeSpec .leftParen .rightParen true .expression nested
  induction rejection <;> rintro ⟨otherBase, value, after, trace, parsed⟩ <;> cases parsed <;>
    grind (ematch := 20) [PostfixSuffixAbsentAt, absent_conflicts_exact, absent_conflicts_token,
      identifier_absent_conflicts_trace, ExactTokenParses.result_unique,
      nested.successResultUnique, nested.successRejectDisjoint,
      NoTrailingDelimitedListTraceParses.opening_present, arguments.successResultUnique,
      arguments.successRejectDisjoint, IdentifierTraceParses.result_unique]

theorem postfixTailTraceExactOutcomeSpec
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte) (base : Syntax.Expr) :
    TraceExactOutcomeSpec
      (fun source endByte input value after trace => PostfixTailTraceParses nestedTrace source endByte input base value after trace)
      (fun source endByte input after report trace => PostfixTailTraceRejects nestedTrace nestedRejects source endByte
        input base after report trace) source endByte where
  successResultUnique := PostfixTailTraceParses.result_unique nested
  rejectResultUnique := PostfixTailTraceRejects.result_unique nested
  successRejectDisjoint := by
    intro input rejected report trace rejection
    rintro ⟨value, after, events, parsed⟩
    exact rejection.disjoint_success nested ⟨base, value, after, events, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionPostfixTraceProperties
/-! Exact independent atom and nested outcomes determine the complete postfix
AST, endpoint, first terminal report, and ordered event sequence. This joint
bundle states uniqueness and disjointness, not existence or parser totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {atomTrace nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ExpressionPostfixTraceParses.result_unique
    (atoms : TraceExactOutcomeSpec atomTrace atomRejects source endByte)
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftEvents rightEvents : List ParseDiagnostic}
    (leftParsed : ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input left afterLeft leftEvents)
    (rightParsed : ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input right afterRight rightEvents) :
    left = right ∧ afterLeft = afterRight ∧ leftEvents = rightEvents := by
  cases leftParsed with
  | parsed leftAtom leftTail =>
      cases rightParsed with
      | parsed rightAtom rightTail =>
          rcases atoms.successResultUnique leftAtom rightAtom with ⟨rfl, rfl, rfl⟩
          rcases leftTail.result_unique nested rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionPostfixTraceRejects.result_unique
    (atoms : TraceExactOutcomeSpec atomTrace atomRejects source endByte)
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftEvents rightEvents : List ParseDiagnostic}
    (left : ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
      input afterLeft leftReport leftEvents)
    (right : ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
      input afterRight rightReport rightEvents) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftEvents = rightEvents := by
  cases left with
  | atomRejected leftAtom =>
      cases right with
      | atomRejected rightAtom => exact atoms.rejectResultUnique leftAtom rightAtom
      | tailRejected rightAtom rightTail => exact False.elim (atoms.successRejectDisjoint leftAtom ⟨_, _, _, rightAtom⟩)
  | tailRejected leftAtom leftTail =>
      cases right with
      | atomRejected rightAtom => exact False.elim (atoms.successRejectDisjoint rightAtom ⟨_, _, _, leftAtom⟩)
      | tailRejected rightAtom rightTail =>
          rcases atoms.successResultUnique leftAtom rightAtom with ⟨rfl, rfl, rfl⟩
          rcases leftTail.result_unique nested rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionPostfixTraceRejects.disjoint_success
    (atoms : TraceExactOutcomeSpec atomTrace atomRejects source endByte)
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
      input rejected report trace) :
    ¬ ∃ value after events, ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input value after events := by
  rintro ⟨value, after, events, parsed⟩
  cases parsed with
  | parsed atom tail =>
      cases rejection with
      | atomRejected rejectedAtom => exact atoms.successRejectDisjoint rejectedAtom ⟨_, _, _, atom⟩
      | tailRejected otherAtom rejectedTail =>
          rcases atoms.successResultUnique atom otherAtom with ⟨rfl, rfl, rfl⟩
          exact rejectedTail.disjoint_success nested ⟨_, _, _, _, tail⟩

theorem expressionPostfixTraceExactOutcomeSpec
    (atoms : TraceExactOutcomeSpec atomTrace atomRejects source endByte)
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte) :
    TraceExactOutcomeSpec
      (ExpressionPostfixTraceParses atomTrace nestedTrace)
      (ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects) source endByte where
  successResultUnique := ExpressionPostfixTraceParses.result_unique atoms nested
  rejectResultUnique := ExpressionPostfixTraceRejects.result_unique atoms nested
  successRejectDisjoint := ExpressionPostfixTraceRejects.disjoint_success atoms nested

end Solcore.Syntax.DeclarativeGrammar
end
