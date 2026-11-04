import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Grammar.Patterns
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Internal.TraceBasics
import Solcore.Syntax.Internal.DelimitedTrace

/-!
Exact diagnostic traces of parenthesized forms, array literals, operators and expression
atoms: trace grammars, unique outcomes and protection of earlier events.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeLiteralDiagnosticTraceGrammar
/-! Exact independent silent traces for Core literals and Boolean builtins.
Literal spellings and Boolean identifier-shaped ASTs remain unchanged. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def CoreLiteralTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (literal : Syntax.CoreLiteral) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  CoreLiteralParses input literal output ∧ trace = []

def BooleanIdentifierTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (name : Syntax.Identifier) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  BooleanIdentifierParses input name output ∧ trace = []

/-- Literal rejection retains its ordinary relation and full uncommitted
`coreLiteral` expectation in expression context, with no added event. -/
def CoreLiteralTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  CoreLiteralRejects input rejected ∧
    RejectAtReports source endByte { head := .coreLiteral, tail := [] }
      .expression rejected diagnostic ∧ trace = []

/-- Boolean absence reuses the existing true/false absence predicate. Its
failure expects an expression, not a Core literal or ordinary identifier. -/
def BooleanIdentifierTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  BooleanPatternAbsentAt input ∧ rejected = input ∧
    RejectAtReports source endByte { head := .expression, tail := [] }
      .expression input diagnostic ∧ trace = []

def LiteralExpressionTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : Syntax.Expr) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  LiteralExpressionParses input value output ∧ trace = []

abbrev LiteralExpressionTraceRejects := CoreLiteralTraceRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLiteralDiagnosticTraceProperties
/-! Independent total, disjoint, and exact literal/Boolean diagnostic outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem CoreLiteralTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.CoreLiteral}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : CoreLiteralTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : CoreLiteralTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace :=
  ⟨(leftParsed.1.result_unique rightParsed.1).1,
    (leftParsed.1.result_unique rightParsed.1).2, leftParsed.2.trans rightParsed.2.symm⟩

theorem BooleanIdentifierTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : BooleanIdentifierTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : BooleanIdentifierTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  refine ⟨leftParsed.1.value_unique rightParsed.1, ?_, leftParsed.2.trans rightParsed.2.symm⟩
  cases leftParsed.1 <;> cases rightParsed.1 <;> rfl

theorem LiteralExpressionTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : LiteralExpressionTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : LiteralExpressionTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace :=
  ⟨LiteralExpressionOrdinaryParses.value_unique leftParsed.1 rightParsed.1,
    LiteralExpressionOrdinaryParses.output_unique leftParsed.1 rightParsed.1,
    leftParsed.2.trans rightParsed.2.symm⟩

theorem CoreLiteralTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : CoreLiteralTraceRejects source endByte input afterLeft left leftTrace)
    (rightRejected : CoreLiteralTraceRejects source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  rcases leftRejected with ⟨leftOrdinary, leftReport, leftEvents⟩
  rcases rightRejected with ⟨rightOrdinary, rightReport, rightEvents⟩
  cases leftOrdinary
  cases rightOrdinary
  exact ⟨rfl, leftReport.diagnostic_unique rightReport, leftEvents.trans rightEvents.symm⟩

theorem BooleanIdentifierTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : BooleanIdentifierTraceRejects source endByte input afterLeft left leftTrace)
    (rightRejected : BooleanIdentifierTraceRejects source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace :=
  ⟨leftRejected.2.1.trans rightRejected.2.1.symm,
    leftRejected.2.2.1.diagnostic_unique rightRejected.2.2.1,
    leftRejected.2.2.2.trans rightRejected.2.2.2.symm⟩

theorem CoreLiteralTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {literal : Syntax.CoreLiteral}
    {rejectTrace successTrace : List ParseDiagnostic}
    (rejectedTrace : CoreLiteralTraceRejects source endByte input rejected diagnostic rejectTrace)
    (successful : CoreLiteralTraceParses source endByte input literal after successTrace) : False :=
  rejectedTrace.1.disjointOrdinary ⟨literal, after, successful.1⟩

theorem BooleanIdentifierTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {name : Syntax.Identifier}
    {rejectTrace successTrace : List ParseDiagnostic}
    (rejectedTrace : BooleanIdentifierTraceRejects source endByte input rejected diagnostic rejectTrace)
    (successful : BooleanIdentifierTraceParses source endByte input name after successTrace) : False := by
  cases successful.1 with
  | trueKeyword token => exact rejectedTrace.1.1 ⟨_, token⟩
  | falseKeyword token => exact rejectedTrace.1.2 ⟨_, token⟩

/-- Every carrier has one literal success or silent first-failure report,
independently of all parser states, executable fuel, and input validity. -/
theorem coreLiteralTrace_outcome_total (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ literal after trace, CoreLiteralTraceParses source endByte input literal after trace) ∨
    ∃ rejected diagnostic trace, CoreLiteralTraceRejects source endByte input rejected diagnostic trace := by
  classical
  by_cases success : ∃ literal after, CoreLiteralParses input literal after
  · rcases success with ⟨literal, after, parsed⟩
    exact Or.inl ⟨literal, after, [], parsed, rfl⟩
  · have absent : CoreLiteralAbsentAt input := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨span, spelling, token⟩; exact success ⟨_, _, .decimal token⟩
      · rintro ⟨span, spelling, token⟩; exact success ⟨_, _, .hexadecimal token⟩
      · rintro ⟨span, spelling, token⟩; exact success ⟨_, _, .string token⟩
    rcases rejectAtReports_total source endByte { head := .coreLiteral, tail := [] }
      .expression input with ⟨diagnostic, reported⟩
    exact Or.inr ⟨input, diagnostic, [], .absent absent, reported, rfl⟩

theorem booleanIdentifierTrace_outcome_total (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ name after trace, BooleanIdentifierTraceParses source endByte input name after trace) ∨
    ∃ rejected diagnostic trace,
      BooleanIdentifierTraceRejects source endByte input rejected diagnostic trace := by
  classical
  by_cases success : ∃ name after, BooleanIdentifierParses input name after
  · rcases success with ⟨name, after, parsed⟩
    exact Or.inl ⟨name, after, [], parsed, rfl⟩
  · have absent : BooleanPatternAbsentAt input := by
      constructor
      · rintro ⟨span, token⟩; exact success ⟨_, _, .trueKeyword token⟩
      · rintro ⟨span, token⟩; exact success ⟨_, _, .falseKeyword token⟩
    rcases rejectAtReports_total source endByte { head := .expression, tail := [] }
      .expression input with ⟨diagnostic, reported⟩
    exact Or.inr ⟨input, diagnostic, [], absent, rfl, reported, rfl⟩

theorem LiteralExpressionTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {value : Syntax.Expr}
    {rejectTrace successTrace : List ParseDiagnostic}
    (rejectedTrace : LiteralExpressionTraceRejects source endByte input rejected diagnostic rejectTrace)
    (successful : LiteralExpressionTraceParses source endByte input value after successTrace) : False := by
  cases successful.1 with
  | parsed literalParsed => exact rejectedTrace.1.disjointOrdinary ⟨_, after, literalParsed⟩

theorem literalExpressionTrace_outcome_total (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value after trace, LiteralExpressionTraceParses source endByte input value after trace) ∨
    ∃ rejected diagnostic trace,
      LiteralExpressionTraceRejects source endByte input rejected diagnostic trace := by
  rcases coreLiteralTrace_outcome_total source endByte input with successful | rejected
  · rcases successful with ⟨literal, after, trace, literalParsed, events⟩
    exact Or.inl ⟨_, after, trace, .parsed literalParsed, events⟩
  · exact Or.inr rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeProxyExpressionTraceGrammar
/-! Independent proxy traces retain the exact marker and nested type AST.
Only the nested type contributes events; no silence or carrier law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ProxyExpressionTraceParses
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker output : Remainder} {type : Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.symbol .at) input markerSpan afterMarker)
      (typed : typeTrace source endByte afterMarker type output trace) :
      ProxyExpressionTraceParses typeTrace source endByte input {
        span := SourceSpan.cover markerSpan type.span
        value := .proxy markerSpan type
      } output trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeProxyExpressionTraceProperties
/-! Structure, exactness, and protected-event composition are separate laws.
Ordinary erasure needs no token law; progress and carrier preservation explicitly
depend on the corresponding child laws, not on a validity assumption. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ProxyExpressionTraceParses.marker_present
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at } := by
  cases parsed with
  | parsed span marker _ => exact ⟨span, marker.1⟩

theorem ProxyExpressionTraceParses.ordinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (erases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → typeOrdinary input value output)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    ProxyExpressionOrdinaryParses typeOrdinary input value output := by
  cases parsed with
  | parsed span marker typed => exact .parsed span marker (erases typed)

theorem ProxyExpressionTraceParses.output_window
    (childWindow : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed span marker typed => simpa only [marker.2] using childWindow typed

theorem ProxyExpressionTraceParses.cursor_lt
    (childProgress : ∀ {input value output trace},
      typeTrace source endByte input value output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed span marker typed =>
      have progress := childProgress typed
      rw [marker.2] at progress
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) progress

theorem ProxyExpressionTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ProxyExpressionTraceParses typeTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ProxyExpressionTraceParses typeTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed span marker typed =>
      cases rightParsed with
      | parsed otherSpan otherMarker otherTyped =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases unique typed otherTyped with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ProxyExpressionTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ typed => exact childProtected typed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeProxyExpressionRejectionTraceGrammar
/-! Raw proxy rejection distinguishes a missing marker from a nested type
failure. The exact final report stays separate from the child's ordered events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ProxyExpressionTraceRejects
    (typeRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (reported : RejectAtReports source endByte { head := .symbol .at, tail := [] } .expression input report) :
      ProxyExpressionTraceRejects typeRejects source endByte input input report []
  | typeRejected {input afterMarker rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.symbol .at) input markerSpan afterMarker)
      (typed : typeRejects source endByte afterMarker rejected report trace) :
      ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeProxyExpressionRejectionTraceProperties
/-! Independent raw rejection erasure, exactness, and event protection. The
older selected relation needs a marker guard; the outcome bundle proves only
uniqueness and disjointness, never type-parser totality or silent diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ProxyExpressionTraceRejects.ordinary_cases
    {ordinaryRejects : Remainder → Remainder → Prop}
    (erases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at) ∧ rejected = input) ∨
      ProxyExpressionRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent _ => exact .inl ⟨absent, rfl⟩
  | typeRejected span marker typed => exact .inr (.typeRejected span marker (erases typed))

theorem ProxyExpressionTraceRejects.ordinary_of_marker_present
    {ordinaryRejects : Remainder → Remainder → Prop}
    (erases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at })
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    ProxyExpressionRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases erases with missing | ordinary
  · exact False.elim (missing.1 selected)
  · exact ordinary

theorem ProxyExpressionTraceRejects.result_unique
    (unique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
      typeRejects source endByte input afterLeft leftReport leftTrace →
      typeRejects source endByte input afterRight rightReport rightTrace →
        afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ProxyExpressionTraceRejects typeRejects source endByte input afterLeft leftReport leftTrace)
    (right : ProxyExpressionTraceRejects typeRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | markerMissing absent reported =>
      cases right with
      | markerMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | typeRejected span marker _ => exact False.elim (absent ⟨span, marker.1⟩)
  | typeRejected span marker typed =>
      cases right with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | typeRejected _ otherMarker other =>
          cases marker.output_unique otherMarker
          exact unique typed other

theorem ProxyExpressionTraceRejects.disjoint_success
    (disjoint : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ¬ ∃ value output events, typeTrace source endByte input value output events)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ProxyExpressionTraceParses typeTrace source endByte input value output events := by
  rintro ⟨_, _, _, success⟩
  cases success with
  | parsed span marker typed =>
      cases rejection with
      | markerMissing absent _ => exact absent ⟨span, marker.1⟩
      | typeRejected _ otherMarker rejectedType =>
          cases marker.output_unique otherMarker
          exact disjoint rejectedType ⟨_, _, _, typed⟩

theorem ProxyExpressionTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing => exact .nil
  | typeRejected _ _ typed => exact childProtected typed

theorem proxyExpressionTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec typeTrace typeRejects source endByte) :
    ExpressionTraceExactOutcomeSpec (ProxyExpressionTraceParses typeTrace)
      (ProxyExpressionTraceRejects typeRejects) source endByte where
  successResultUnique := ProxyExpressionTraceParses.result_unique types.successResultUnique
  rejectResultUnique := ProxyExpressionTraceRejects.result_unique types.rejectResultUnique
  successRejectDisjoint := ProxyExpressionTraceRejects.disjoint_success types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceGrammar
/-! Independent exact traces for optional lambda return annotations. An absent
arrow is silent; a present arrow contributes no event before the supplied type
outcome. The final rejection report remains separate from committed events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OptionalLambdaReturnTypeTraceParses
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .arrow)) :
      OptionalLambdaReturnTypeTraceParses typeTrace source endByte input none input []
  | present {input afterArrow output : Remainder} {type : Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan afterArrow)
      (typeParsed : typeTrace source endByte afterArrow type output trace) :
      OptionalLambdaReturnTypeTraceParses typeTrace source endByte input (some type) output trace

inductive OptionalLambdaReturnTypeTraceRejects
    (typeRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | typeRejected {input afterArrow rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan afterArrow)
      (typeRejected : typeRejects source endByte afterArrow rejected diagnostic trace) :
      OptionalLambdaReturnTypeTraceRejects typeRejects source endByte input rejected diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceProtectionProperties
/-! Only supplied protected type events are preserved. The separate final
rejection report has no implied protection property. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalLambdaReturnTypeTraceParses.cascadeFilters
    (typeProtected : ∀ {input type output trace},
      typeTrace source endByte input type output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {type : Option Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present _ _ type => exact typeProtected type

theorem OptionalLambdaReturnTypeTraceRejects.cascadeFilters
    (typeProtected : ∀ {input rejected diagnostic trace},
      typeRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | typeRejected _ _ type => exact typeProtected type

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceProperties
/-! Ordinary erasure and separately supplied carrier/progress laws. No such
law, and no diagnostic silence of the type relation, is part of the grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalLambdaReturnTypeTraceParses.ordinary
    (erases : ∀ {input type output trace},
      typeTrace source endByte input type output trace → typeOrdinary input type output)
    {input output : Remainder} {type : Option Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output trace) :
    OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input type output := by
  cases parsed with
  | absent absent => exact .absent absent
  | present span arrow type => exact .present span arrow (erases type)

theorem OptionalLambdaReturnTypeTraceRejects.ordinary
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (erases : ∀ {input rejected diagnostic trace},
      typeRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input rejected diagnostic trace) :
    OptionalLambdaReturnTypeRejects typeOrdinary ordinaryRejects input rejected := by
  cases rejection with
  | typeRejected span arrow type => exact .typeRejected span arrow (erases type)

theorem OptionalLambdaReturnTypeTraceParses.output_window
    (typeWindow : ∀ {input type output trace},
      typeTrace source endByte input type output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {type : Option Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present span arrow type => simpa only [arrow.2] using typeWindow type

theorem OptionalLambdaReturnTypeTraceParses.cursor_le
    (typeProgress : ∀ {input type output trace},
      typeTrace source endByte input type output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {type : Option Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output trace) :
    input.cursor ≤ output.cursor := by
  cases parsed with
  | absent => exact Nat.le_refl _
  | present span arrow type =>
      have progress := typeProgress type
      rw [arrow.2] at progress
      exact Nat.le_trans (Nat.le_succ _) progress

theorem OptionalLambdaReturnTypeTraceParses.present_cursor_lt
    (typeProgress : ∀ {input type output trace},
      typeTrace source endByte input type output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {type : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input (some type) output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | present span arrow type =>
      have progress := typeProgress type
      rw [arrow.2] at progress
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) progress

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceExactnessProperties
/-! Conditional uniqueness and disjointness of the optional annotation. This
bundle does not assert that the supplied type relation has an outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalLambdaReturnTypeTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input left afterLeft leftTrace)
    (rightParsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent absent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present span arrow _ => exact False.elim (absent ⟨span, arrow.1⟩)
  | present span arrow type =>
      cases rightParsed with
      | absent absent => exact False.elim (absent ⟨span, arrow.1⟩)
      | present _ otherArrow other =>
          rcases arrow.result_unique otherArrow with ⟨rfl, rfl⟩
          rcases unique type other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem OptionalLambdaReturnTypeTraceRejects.result_unique
    (unique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
      typeRejects source endByte input afterLeft leftReport leftTrace →
      typeRejects source endByte input afterRight rightReport rightTrace →
        afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input afterLeft leftReport leftTrace)
    (rightRejected : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | typeRejected span arrow type =>
      cases rightRejected with
      | typeRejected _ otherArrow other =>
          rcases arrow.result_unique otherArrow with ⟨rfl, rfl⟩
          exact unique type other

theorem OptionalLambdaReturnTypeTraceRejects.disjoint_success
    (disjoint : ∀ {input rejected diagnostic trace},
      typeRejects source endByte input rejected diagnostic trace →
        ¬ ∃ type output events, typeTrace source endByte input type output events)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ type output events, OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output events := by
  rintro ⟨type, output, events, parsed⟩
  cases rejection with
  | typeRejected span arrow rejected =>
      cases parsed with
      | absent absent => exact absent ⟨span, arrow.1⟩
      | present _ otherArrow parsed =>
          rcases arrow.result_unique otherArrow with ⟨rfl, rfl⟩
          exact disjoint rejected ⟨_, _, _, parsed⟩

theorem optionalLambdaReturnTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec typeTrace typeRejects source endByte) :
    TraceExactOutcomeSpec (OptionalLambdaReturnTypeTraceParses typeTrace)
      (OptionalLambdaReturnTypeTraceRejects typeRejects) source endByte where
  successResultUnique := OptionalLambdaReturnTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := OptionalLambdaReturnTypeTraceRejects.result_unique types.rejectResultUnique
  successRejectDisjoint := OptionalLambdaReturnTypeTraceRejects.disjoint_success types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLeftAssociativeTraceGrammar
/-! Independent maximal left-associative traces at one binary precedence.
Selected operators are consumed silently; only supplied operand events are
concatenated in source order. The exact terminal report remains uncommitted.
Operand success has no added progress, token-carrier, or numeric-window rule. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive LeftAssociativeTailTraceParses
    (operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (precedence : Nat) (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | done {input : Remainder} {left : Syntax.Expr}
      (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input) :
      LeftAssociativeTailTraceParses operandTrace precedence source endByte input left left input []
  | next {input afterOperator afterRight output : Remainder}
      {left right expression : Syntax.Expr} {operator : Located BinaryOp}
      {rightEvents tailEvents : List ParseDiagnostic}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input operator afterOperator)
      (rightParsed : operandTrace source endByte afterOperator right afterRight rightEvents)
      (tail : LeftAssociativeTailTraceParses operandTrace precedence source endByte afterRight
        (binaryNode left operator right) expression output tailEvents) :
      LeftAssociativeTailTraceParses operandTrace precedence source endByte input left expression output
        (rightEvents ++ tailEvents)

inductive LeftAssociativeTailTraceRejects
    (operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (precedence : Nat) (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | rightRejected {input afterOperator rejected : Remainder}
      {left : Syntax.Expr} {operator : Located BinaryOp} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input operator afterOperator)
      (rightRejected : operandRejects source endByte afterOperator rejected report trace) :
      LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte input left rejected report trace
  | laterRejected {input afterOperator afterRight rejected : Remainder}
      {left right : Syntax.Expr} {operator : Located BinaryOp} {report : ParseDiagnostic}
      {rightEvents tailEvents : List ParseDiagnostic}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input operator afterOperator)
      (rightParsed : operandTrace source endByte afterOperator right afterRight rightEvents)
      (tailRejected : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
        afterRight (binaryNode left operator right) rejected report tailEvents) :
      LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte input left rejected report
        (rightEvents ++ tailEvents)

inductive LeftAssociativeTraceParses
    (operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (precedence : Nat) (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterLeft output : Remainder} {left expression : Syntax.Expr}
      {leftEvents tailEvents : List ParseDiagnostic}
      (leftParsed : operandTrace source endByte input left afterLeft leftEvents)
      (tailParsed : LeftAssociativeTailTraceParses operandTrace precedence source endByte
        afterLeft left expression output tailEvents) :
      LeftAssociativeTraceParses operandTrace precedence source endByte input expression output (leftEvents ++ tailEvents)

inductive LeftAssociativeTraceRejects
    (operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (precedence : Nat) (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | firstRejected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (firstRejected : operandRejects source endByte input rejected report trace) :
      LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte input rejected report trace
  | tailRejected {input afterLeft rejected : Remainder} {left : Syntax.Expr} {report : ParseDiagnostic}
      {leftEvents tailEvents : List ParseDiagnostic}
      (leftParsed : operandTrace source endByte input left afterLeft leftEvents)
      (tailRejected : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
        afterLeft left rejected report tailEvents) :
      LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte input rejected report
        (leftEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLeftAssociativeTraceProperties
/-! Independent operand exactness fixes every maximal left-associated trace.
Successful AST uniqueness is at a fixed accumulated base, while rejection
uniqueness and disjointness hold even across different bases. Neither fuel,
progress, window preservation, nor outcome existence is introduced. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte precedence : Nat}

theorem LeftAssociativeTailTraceParses.result_unique
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input afterLeft afterRight : Remainder} {base left right : Syntax.Expr}
    {leftEvents rightEvents : List ParseDiagnostic}
    (leftParsed : LeftAssociativeTailTraceParses operandTrace precedence source endByte input base left afterLeft leftEvents)
    (rightParsed : LeftAssociativeTailTraceParses operandTrace precedence source endByte input base right afterRight rightEvents) :
    left = right ∧ afterLeft = afterRight ∧ leftEvents = rightEvents := by
  induction leftParsed generalizing right afterRight rightEvents with
  | done absent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl, rfl⟩
      | next operatorParsed _ _ => exact False.elim (absent.not_parses operatorParsed)
  | next leftOperator leftOperand leftTail ih =>
      cases rightParsed with
      | done absent => exact False.elim (absent.not_parses leftOperator)
      | next rightOperator rightOperand rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          rcases outcomes.successResultUnique leftOperand rightOperand with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LeftAssociativeTailTraceRejects.result_unique
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftBase rightBase : Syntax.Expr}
    {leftReport rightReport : ParseDiagnostic} {leftEvents rightEvents : List ParseDiagnostic}
    (left : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
      input leftBase afterLeft leftReport leftEvents)
    (right : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
      input rightBase afterRight rightReport rightEvents) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftEvents = rightEvents := by
  induction left generalizing rightBase afterRight rightReport rightEvents with
  | rightRejected leftOperator leftRejected =>
      cases right with
      | rightRejected rightOperator rightRejected =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          exact outcomes.rejectResultUnique leftRejected rightRejected
      | laterRejected rightOperator rightParsed rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          exact False.elim (outcomes.successRejectDisjoint leftRejected ⟨_, _, _, rightParsed⟩)
  | laterRejected leftOperator leftParsed leftTail ih =>
      cases right with
      | rightRejected rightOperator rightRejected =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          exact False.elim (outcomes.successRejectDisjoint rightRejected ⟨_, _, _, leftParsed⟩)
      | laterRejected rightOperator rightParsed rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          rcases outcomes.successResultUnique leftParsed rightParsed with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LeftAssociativeTailTraceRejects.disjoint_success
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input rejected : Remainder} {base : Syntax.Expr} {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (rejection : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
      input base rejected report events) :
    ¬ ∃ otherBase value after trace,
      LeftAssociativeTailTraceParses operandTrace precedence source endByte input otherBase value after trace := by
  induction rejection with
  | rightRejected rejectedOperator rejectedOperand =>
      rintro ⟨otherBase, value, after, trace, parsed⟩
      cases parsed with
      | done absent => exact absent.not_parses rejectedOperator
      | next parsedOperator parsedOperand parsedTail =>
          rcases rejectedOperator.result_unique parsedOperator with ⟨rfl, rfl⟩
          exact outcomes.successRejectDisjoint rejectedOperand ⟨_, _, _, parsedOperand⟩
  | laterRejected rejectedOperator parsedOperand rejectedTail ih =>
      rintro ⟨otherBase, value, after, trace, parsed⟩
      cases parsed with
      | done absent => exact absent.not_parses rejectedOperator
      | next parsedOperator otherOperand parsedTail =>
          rcases rejectedOperator.result_unique parsedOperator with ⟨rfl, rfl⟩
          rcases outcomes.successResultUnique parsedOperand otherOperand with ⟨rfl, rfl, rfl⟩
          exact ih ⟨_, _, _, _, parsedTail⟩

theorem leftAssociativeTailTraceExactOutcomeSpec
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte) (precedence : Nat) (base : Syntax.Expr) :
    TraceExactOutcomeSpec
      (fun source endByte input value after trace =>
        LeftAssociativeTailTraceParses operandTrace precedence source endByte input base value after trace)
      (fun source endByte input after report trace =>
        LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte input base after report trace)
      source endByte where
  successResultUnique := LeftAssociativeTailTraceParses.result_unique outcomes
  rejectResultUnique := LeftAssociativeTailTraceRejects.result_unique outcomes
  successRejectDisjoint := by
    intro input rejected report trace rejection
    rintro ⟨value, after, events, parsed⟩
    exact rejection.disjoint_success outcomes ⟨base, value, after, events, parsed⟩

theorem LeftAssociativeTraceParses.result_unique
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftEvents rightEvents : List ParseDiagnostic}
    (leftParsed : LeftAssociativeTraceParses operandTrace precedence source endByte input left afterLeft leftEvents)
    (rightParsed : LeftAssociativeTraceParses operandTrace precedence source endByte input right afterRight rightEvents) :
    left = right ∧ afterLeft = afterRight ∧ leftEvents = rightEvents := by
  cases leftParsed with
  | parsed leftOperand leftTail =>
      cases rightParsed with
      | parsed rightOperand rightTail =>
          rcases outcomes.successResultUnique leftOperand rightOperand with ⟨rfl, rfl, rfl⟩
          rcases leftTail.result_unique outcomes rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LeftAssociativeTraceRejects.result_unique
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftEvents rightEvents : List ParseDiagnostic}
    (left : LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte
      input afterLeft leftReport leftEvents)
    (right : LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte
      input afterRight rightReport rightEvents) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftEvents = rightEvents := by
  cases left with
  | firstRejected leftRejected =>
      cases right with
      | firstRejected rightRejected => exact outcomes.rejectResultUnique leftRejected rightRejected
      | tailRejected rightParsed rightTail => exact False.elim (outcomes.successRejectDisjoint leftRejected ⟨_, _, _, rightParsed⟩)
  | tailRejected leftParsed leftTail =>
      cases right with
      | firstRejected rightRejected => exact False.elim (outcomes.successRejectDisjoint rightRejected ⟨_, _, _, leftParsed⟩)
      | tailRejected rightParsed rightTail =>
          rcases outcomes.successResultUnique leftParsed rightParsed with ⟨rfl, rfl, rfl⟩
          rcases leftTail.result_unique outcomes rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LeftAssociativeTraceRejects.disjoint_success
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (rejection : LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte input rejected report events) :
    ¬ ∃ value after trace, LeftAssociativeTraceParses operandTrace precedence source endByte input value after trace := by
  rintro ⟨value, after, trace, parsed⟩
  cases parsed with
  | parsed parsedOperand parsedTail =>
      cases rejection with
      | firstRejected rejectedOperand => exact outcomes.successRejectDisjoint rejectedOperand ⟨_, _, _, parsedOperand⟩
      | tailRejected otherOperand rejectedTail =>
          rcases outcomes.successResultUnique parsedOperand otherOperand with ⟨rfl, rfl, rfl⟩
          exact rejectedTail.disjoint_success outcomes ⟨_, _, _, _, parsedTail⟩

theorem leftAssociativeTraceExactOutcomeSpec
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte) (precedence : Nat) :
    TraceExactOutcomeSpec (LeftAssociativeTraceParses operandTrace precedence)
      (LeftAssociativeTraceRejects operandTrace operandRejects precedence) source endByte where
  successResultUnique := LeftAssociativeTraceParses.result_unique outcomes
  rejectResultUnique := LeftAssociativeTraceRejects.result_unique outcomes
  successRejectDisjoint := LeftAssociativeTraceRejects.disjoint_success outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionUnaryTraceGrammar
/-! Independent exact unary traces reuse the maximal source-ordered prefix
grammar. Canonical unary tokens are silent; all emitted events and any terminal
report come from the supplied postfix outcome after that complete prefix. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionUnaryTraceParses
    (postfixTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterOperators output : Remainder}
      {operators : List (Located UnaryOp)} {base : Syntax.Expr} {trace : List ParseDiagnostic}
      (operatorsParsed : UnaryOperatorsParses input operators afterOperators)
      (postfixParsed : postfixTrace source endByte afterOperators base output trace) :
      ExpressionUnaryTraceParses postfixTrace source endByte input
        (applyUnaryOperators operators base) output trace

inductive ExpressionUnaryTraceRejects
    (postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | postfixRejected {input afterOperators rejected : Remainder}
      {operators : List (Located UnaryOp)} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (operatorsParsed : UnaryOperatorsParses input operators afterOperators)
      (postfixRejected : postfixRejects source endByte afterOperators rejected report trace) :
      ExpressionUnaryTraceRejects postfixRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionUnaryTraceProperties
/-! Maximal unary-prefix determinism and independent postfix exactness fix
the complete wrapped AST, remainder, ordered events, and terminal report.
The joint bundle states only uniqueness/disjointness, never existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {postfixTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ExpressionUnaryTraceParses.result_unique
    (outcomes : TraceExactOutcomeSpec postfixTrace postfixRejects source endByte)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionUnaryTraceParses postfixTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionUnaryTraceParses postfixTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftPrefix leftPostfix =>
      cases rightParsed with
      | parsed rightPrefix rightPostfix =>
          rcases leftPrefix.result_unique rightPrefix with ⟨rfl, rfl⟩
          rcases outcomes.successResultUnique leftPostfix rightPostfix with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionUnaryTraceRejects.result_unique
    (outcomes : TraceExactOutcomeSpec postfixTrace postfixRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ExpressionUnaryTraceRejects postfixRejects source endByte input afterLeft leftReport leftTrace)
    (right : ExpressionUnaryTraceRejects postfixRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | postfixRejected leftPrefix leftPostfix =>
      cases right with
      | postfixRejected rightPrefix rightPostfix =>
          have same := leftPrefix.output_unique rightPrefix
          cases same
          exact outcomes.rejectResultUnique leftPostfix rightPostfix

theorem ExpressionUnaryTraceRejects.disjoint_success
    (outcomes : TraceExactOutcomeSpec postfixTrace postfixRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionUnaryTraceRejects postfixRejects source endByte input rejected report trace) :
    ¬ ∃ value after events, ExpressionUnaryTraceParses postfixTrace source endByte input value after events := by
  rintro ⟨value, after, events, parsed⟩
  cases rejection with
  | postfixRejected rejectedPrefix rejectedPostfix =>
      cases parsed with
      | parsed parsedPrefix parsedPostfix =>
          have same := rejectedPrefix.output_unique parsedPrefix
          cases same
          exact outcomes.successRejectDisjoint rejectedPostfix ⟨_, _, _, parsedPostfix⟩

theorem expressionUnaryTraceExactOutcomeSpec
    (outcomes : TraceExactOutcomeSpec postfixTrace postfixRejects source endByte) :
    TraceExactOutcomeSpec (ExpressionUnaryTraceParses postfixTrace)
      (ExpressionUnaryTraceRejects postfixRejects) source endByte where
  successResultUnique := ExpressionUnaryTraceParses.result_unique outcomes
  rejectResultUnique := ExpressionUnaryTraceRejects.result_unique outcomes
  successRejectDisjoint := ExpressionUnaryTraceRejects.disjoint_success outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedTraceGrammar
/-! Independent prioritized parenthesized success traces. Tail results contain
only newly read forward elements, their closing span, and ordered child events.
Fuel and the already-accumulated reverse prefix are deliberately absent. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ParenthesizedTupleTailTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → List Syntax.Expr → SourceSpan → Remainder → List ParseDiagnostic → Prop where
  | trailing {input afterComma output : Remainder} (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterComma closingSpan output) :
      ParenthesizedTupleTailTraceParses elementTrace source endByte input [] closingSpan output []
  | final {input afterComma afterElement output : Remainder} {element : Syntax.Expr}
      {events : List ParseDiagnostic} (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : elementTrace source endByte afterComma element afterElement events)
      (progress : afterComma.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterElement closingSpan output) :
      ParenthesizedTupleTailTraceParses elementTrace source endByte input [element] closingSpan output events
  | next {input afterComma afterElement output : Remainder} {element : Syntax.Expr} {elements : List Syntax.Expr}
      {headEvents tailEvents : List ParseDiagnostic} (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : elementTrace source endByte afterComma element afterElement headEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (tail : ParenthesizedTupleTailTraceParses elementTrace source endByte afterElement elements closingSpan output tailEvents) :
      ParenthesizedTupleTailTraceParses elementTrace source endByte input (element :: elements) closingSpan output
        (headEvents ++ tailEvents)

inductive ParenthesizedExpressionTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | empty {input afterOpening output : Remainder} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterOpening closingSpan output) :
      ParenthesizedExpressionTraceParses elementTrace source endByte input
        (closeParenthesizedExpression openingSpan closingSpan []) output []
  | group {input afterOpening afterElement output : Remainder} {element : Syntax.Expr}
      {events : List ParseDiagnostic} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (elementParsed : elementTrace source endByte afterOpening element afterElement events)
      (progress : afterOpening.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterElement closingSpan output) :
      ParenthesizedExpressionTraceParses elementTrace source endByte input
        (closeParenthesizedExpression openingSpan closingSpan [element]) output events
  | tuple {input afterOpening afterFirst output : Remainder} {first : Syntax.Expr} {rest : List Syntax.Expr}
      {headEvents tailEvents : List ParseDiagnostic} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : elementTrace source endByte afterOpening first afterFirst headEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tail : ParenthesizedTupleTailTraceParses elementTrace source endByte afterFirst rest closingSpan output tailEvents) :
      ParenthesizedExpressionTraceParses elementTrace source endByte input
        (closeParenthesizedExpression openingSpan closingSpan (first :: rest)) output (headEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedTraceProperties
/-! Parenthesized trace erasure and structural laws. Unlike generic delimited
whole-list erasure, these older grammars impose no child carrier condition.
Carrier/end-index preservation remains a separate conditional structural law. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {elementParses : Remainder → Syntax.Expr → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem ParenthesizedTupleTailTraceParses.comma_present
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .comma } := by
  cases parsed with
  | trailing span _ comma _ | final span _ comma _ _ _ _ _ | next span _ comma _ _ _ _ => exact ⟨span, comma.1⟩

theorem ParenthesizedTupleTailTraceParses.comma_conflicts_absent
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma)) : False :=
  absent parsed.comma_present

theorem ParenthesizedTupleTailTraceParses.ordinary
    (erases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      elementParses input value output)
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    ParenthesizedTupleTailParses elementParses input values closingSpan output := by
  induction parsed with
  | trailing span closing comma finish => exact .trailing span closing comma finish
  | final span closing comma absent child progress noComma finish =>
      exact .final span closing comma absent (erases child) progress noComma finish
  | next span closing comma absent child progress tail ih =>
      exact .next span closing comma absent (erases child) progress ih

theorem ParenthesizedExpressionTraceParses.ordinary
    (erases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      elementParses input value output)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses elementTrace source endByte input value output trace) :
    ParenthesizedExpressionParses elementParses input value output := by
  cases parsed with
  | empty span closing opening finish => exact .empty span closing opening finish
  | group span closing opening absent child progress noComma finish =>
      exact .group span closing opening absent (erases child) progress noComma finish
  | tuple span closing opening absent child progress tail =>
      exact .tuple span closing opening absent (erases child) progress (tail.ordinary erases)

theorem ParenthesizedTupleTailTraceParses.output_window
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | trailing span closing comma finish => rw [finish.2, comma.2]; exact ⟨rfl, rfl⟩
  | final span closing comma absent child progress noComma finish =>
      rw [finish.2]
      simpa only [comma.2] using elementWindow child
  | next span closing comma absent child progress tail ih =>
      have frame := elementWindow child
      simpa only [comma.2] using And.intro (ih.1.trans frame.1) (ih.2.trans frame.2)

theorem ParenthesizedExpressionTraceParses.output_window
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | empty span closing opening finish => rw [finish.2, opening.2]; exact ⟨rfl, rfl⟩
  | group span closing opening absent child progress noComma finish =>
      rw [finish.2]
      simpa only [opening.2] using elementWindow child
  | tuple span closing opening absent child progress tail =>
      have headFrame := elementWindow child
      have tailFrame := tail.output_window elementWindow
      simpa only [opening.2] using And.intro (tailFrame.1.trans headFrame.1) (tailFrame.2.trans headFrame.2)

theorem ParenthesizedTupleTailTraceParses.cursor_lt
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    input.cursor < output.cursor := by
  induction parsed with
  | trailing span closing comma finish => rw [finish.2, comma.2]; exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  | final span closing comma absent child progress noComma finish =>
      rw [comma.2] at progress
      rw [finish.2]
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) (Nat.lt_succ_self _)
  | next span closing comma absent child progress tail ih =>
      rw [comma.2] at progress
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) ih

theorem ParenthesizedTupleTailTraceParses.output_cursor_le_endIndex
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    output.cursor ≤ output.endIndex := by
  induction parsed with
  | trailing _ _ _ finish | final _ _ _ _ _ _ _ finish => rw [finish.2]; exact finish.1.1
  | next _ _ _ _ _ _ _ ih => exact ih

theorem ParenthesizedExpressionTraceParses.cursor_lt
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | empty span closing opening finish => rw [finish.2, opening.2]; exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  | group span closing opening absent child progress noComma finish =>
      rw [opening.2] at progress
      rw [finish.2]
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) (Nat.lt_succ_self _)
  | tuple span closing opening absent child progress tail =>
      rw [opening.2] at progress
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) tail.cursor_lt

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedTraceExactnessProperties
/-! Exact child outcomes determine every forward element, close, remainder,
and diagnostic occurrence. Cover need not be injective in either endpoint. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem absent_conflicts_exact {kind : TokenKind} {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False := absent ⟨span, parsed.1⟩

theorem ParenthesizedTupleTailTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Expr}
    {leftClosing rightClosing : SourceSpan} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input left leftClosing afterLeft leftTrace)
    (rightParsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input right rightClosing afterRight rightTrace) :
    left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightClosing afterRight rightTrace with
  | trailing commaSpan closingSpan comma closing =>
      cases rightParsed <;> grind [ExactTokenParses.result_unique, absent_conflicts_exact]
  | final commaSpan closingSpan comma closingAbsent child progress commaAbsent closing =>
      cases rightParsed <;> grind [ExactTokenParses.result_unique,
        absent_conflicts_exact, ParenthesizedTupleTailTraceParses.comma_conflicts_absent]
  | next commaSpan closingSpan comma closingAbsent child progress tail ih =>
      cases rightParsed <;> grind [ExactTokenParses.result_unique,
        absent_conflicts_exact, ParenthesizedTupleTailTraceParses.comma_conflicts_absent]

theorem ParenthesizedExpressionTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ParenthesizedExpressionTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ParenthesizedExpressionTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ExactTokenParses.result_unique, ParenthesizedTupleTailTraceParses.result_unique unique,
      absent_conflicts_exact, ParenthesizedTupleTailTraceParses.comma_conflicts_absent]

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedRejectionTraceGrammar
/-! Raw tuple-tail and parenthesized rejection traces. Marker failures are
included even outside dispatcher-selected entry points. The final report is
not an event. Recursive tails require a selected comma explicitly. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ParenthesizedTupleTailTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | commaMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma))
      (reported : RejectAtReports source endByte { head := .symbol .comma, tail := [] } .expression input report) :
      ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input input report []
  | elementRejected {input afterComma rejected : Remainder} {report : ParseDiagnostic}
      {events : List ParseDiagnostic} (commaSpan : SourceSpan)
      (comma : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (child : elementRejects source endByte afterComma rejected report events) :
      ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report events
  | closingMissing {input afterComma afterElement : Remainder} {element : Syntax.Expr}
      {events : List ParseDiagnostic} {report : ParseDiagnostic} (commaSpan : SourceSpan)
      (comma : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (child : elementTrace source endByte afterComma element afterElement events)
      (progress : afterComma.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .comma))
      (lastClosingAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .rightParen))
      (reported : RejectAtReports source endByte { head := .symbol .rightParen, tail := [] } .expression afterElement report) :
      ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input afterElement report events
  | laterRejected {input afterComma afterElement rejected : Remainder} {element : Syntax.Expr}
      {headEvents tailEvents : List ParseDiagnostic} {report : ParseDiagnostic} (commaSpan nextCommaSpan : SourceSpan)
      (comma : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (child : elementTrace source endByte afterComma element afterElement headEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (nextComma : TokenAt afterElement.tokens afterElement.endIndex afterElement.cursor
        { span := nextCommaSpan, value := .symbol .comma })
      (tail : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte
        afterElement rejected report tailEvents) :
      ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report
        (headEvents ++ tailEvents)

inductive ParenthesizedExpressionTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | openingMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (reported : RejectAtReports source endByte { head := .symbol .leftParen, tail := [] } .expression input report) :
      ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input input report []
  | firstRejected {input afterOpening rejected : Remainder} {report : ParseDiagnostic}
      {events : List ParseDiagnostic} (openingSpan : SourceSpan)
      (opening : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (child : elementRejects source endByte afterOpening rejected report events) :
      ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report events
  | closingMissing {input afterOpening afterElement : Remainder} {element : Syntax.Expr}
      {events : List ParseDiagnostic} {report : ParseDiagnostic} (openingSpan : SourceSpan)
      (opening : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (child : elementTrace source endByte afterOpening element afterElement events)
      (progress : afterOpening.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .comma))
      (lastClosingAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .rightParen))
      (reported : RejectAtReports source endByte { head := .symbol .rightParen, tail := [] } .expression afterElement report) :
      ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input afterElement report events
  | tailRejected {input afterOpening afterFirst rejected : Remainder} {first : Syntax.Expr}
      {headEvents tailEvents : List ParseDiagnostic} {report : ParseDiagnostic} (openingSpan commaSpan : SourceSpan)
      (opening : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (child : elementTrace source endByte afterOpening first afterFirst headEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (comma : TokenAt afterFirst.tokens afterFirst.endIndex afterFirst.cursor
        { span := commaSpan, value := .symbol .comma })
      (tail : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte
        afterFirst rejected report tailEvents) :
      ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report
        (headEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedRejectionTraceProperties
/-! Erasure separates raw marker failures from the older selected grammars. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinary : Remainder → Syntax.Expr → Remainder → Prop}
  {rejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem ParenthesizedTupleTailTraceRejects.ordinary_of_comma_present
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinary input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      rejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report trace)
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .comma }) :
    ParenthesizedTupleTailRejects ordinary rejects input rejected := by
  induction rejection with
  | commaMissing absent reported => exact False.elim (absent selected)
  | elementRejected span comma absent child => exact .elementRejected span comma absent (rejectErases child)
  | closingMissing span comma absent child progress commaAbsent closingAbsent reported =>
      exact .closingMissing span comma absent (successErases child) progress commaAbsent closingAbsent
  | laterRejected span nextSpan comma absent child progress nextComma tail ih =>
      exact .laterRejected span comma absent (successErases child) progress (ih ⟨nextSpan, nextComma⟩)

theorem ParenthesizedTupleTailTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinary input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      rejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma) ∧ rejected = input) ∨
      ParenthesizedTupleTailRejects ordinary rejects input rejected := by
  cases rejection with
  | commaMissing absent reported => exact .inl ⟨absent, rfl⟩
  | elementRejected span comma absent child => exact .inr (.elementRejected span comma absent (rejectErases child))
  | closingMissing span comma absent child progress commaAbsent closingAbsent reported =>
      exact .inr (.closingMissing span comma absent (successErases child) progress commaAbsent closingAbsent)
  | laterRejected span nextSpan comma absent child progress nextComma tail =>
      exact .inr (.laterRejected span comma absent (successErases child) progress
        (tail.ordinary_of_comma_present successErases rejectErases ⟨nextSpan, nextComma⟩))

theorem ParenthesizedExpressionTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinary input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      rejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen) ∧ rejected = input) ∨
      ParenthesizedExpressionRejects ordinary rejects input rejected := by
  cases rejection with
  | openingMissing absent reported => exact .inl ⟨absent, rfl⟩
  | firstRejected span opening absent child => exact .inr (.firstRejected span opening absent (rejectErases child))
  | closingMissing span opening absent child progress commaAbsent closingAbsent reported =>
      exact .inr (.closingMissing span opening absent (successErases child) progress commaAbsent closingAbsent)
  | tailRejected span commaSpan opening absent child progress comma tail =>
      exact .inr (.tailRejected span opening absent (successErases child) progress
        (tail.ordinary_of_comma_present successErases rejectErases ⟨commaSpan, comma⟩))

theorem ParenthesizedExpressionTraceRejects.ordinary_of_opening_present
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinary input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      rejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report trace)
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen }) :
    ParenthesizedExpressionRejects ordinary rejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases with ⟨absent, _⟩ | ordinary
  · exact False.elim (absent selected)
  · exact ordinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedRejectionTraceExactnessProperties
/-! Full rejection functionality from independent child functionality. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    elementTrace source endByte input left afterLeft leftTrace →
    elementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    elementRejects source endByte input afterLeft leftReport leftTrace →
    elementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected report trace},
    elementRejects source endByte input rejected report trace →
      ¬ ∃ value output events, elementTrace source endByte input value output events)

include successUnique rejectUnique disjoint in
theorem ParenthesizedTupleTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  induction left generalizing afterRight rightReport rightTrace with
  | commaMissing absent reported =>
      cases right with
      | commaMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | elementRejected span token _ _
      | closingMissing span token _ _ _ _ _ _
      | laterRejected span _ token _ _ _ _ _ => exact False.elim (absent ⟨span, token.1⟩)
  | elementRejected span token absent child =>
      cases right with
      | commaMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | elementRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact rejectUnique child other
      | closingMissing _ otherToken _ other _ _ _ _
      | laterRejected _ _ otherToken _ other _ _ _ =>
          cases token.output_unique otherToken
          exact False.elim (disjoint child ⟨_, _, _, other⟩)
  | closingMissing span token absent child progress commaAbsent closingAbsent reported =>
      cases right with
      | commaMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | elementRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | closingMissing _ otherToken _ other _ _ _ otherReport =>
          cases token.output_unique otherToken
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩
      | laterRejected _ nextSpan otherToken _ other _ nextComma _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact False.elim (commaAbsent ⟨nextSpan, nextComma⟩)
  | laterRejected span nextSpan token absent child progress nextComma tail ih =>
      cases right with
      | commaMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | elementRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | closingMissing _ otherToken _ other _ commaAbsent _ _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact False.elim (commaAbsent ⟨nextSpan, nextComma⟩)
      | laterRejected _ _ otherToken _ other _ _ otherTail =>
          cases token.output_unique otherToken
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique rejectUnique disjoint in
theorem ParenthesizedExpressionTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | openingMissing absent reported =>
      cases right with
      | openingMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | firstRejected span token _ _
      | closingMissing span token _ _ _ _ _ _
      | tailRejected span _ token _ _ _ _ _ => exact False.elim (absent ⟨span, token.1⟩)
  | firstRejected span token absent child =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | firstRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact rejectUnique child other
      | closingMissing _ otherToken _ other _ _ _ _
      | tailRejected _ _ otherToken _ other _ _ _ =>
          cases token.output_unique otherToken
          exact False.elim (disjoint child ⟨_, _, _, other⟩)
  | closingMissing span token absent child progress commaAbsent closingAbsent reported =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | firstRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | closingMissing _ otherToken _ other _ _ _ otherReport =>
          cases token.output_unique otherToken
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩
      | tailRejected _ nextSpan otherToken _ other _ nextComma _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact False.elim (commaAbsent ⟨nextSpan, nextComma⟩)
  | tailRejected span nextSpan token absent child progress nextComma tail  =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | firstRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | closingMissing _ otherToken _ other _ commaAbsent _ _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact False.elim (commaAbsent ⟨nextSpan, nextComma⟩)
      | tailRejected _ _ otherToken _ other _ _ otherTail =>
          cases token.output_unique otherToken
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique successUnique rejectUnique disjoint otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedTraceDisjointnessProperties
/-! Prioritized rejection and success are disjoint without parser execution. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    elementTrace source endByte input left afterLeft leftTrace →
    elementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    elementRejects source endByte input afterLeft leftReport leftTrace →
    elementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected report trace},
    elementRejects source endByte input rejected report trace →
      ¬ ∃ value output events, elementTrace source endByte input value output events)

private theorem tail_comma_present
    {input output : Remainder} {values : List Syntax.Expr} {span : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values span output trace) :
    ∃ commaSpan, TokenAt input.tokens input.endIndex input.cursor { span := commaSpan, value := .symbol .comma } := by
  cases parsed with
  | trailing commaSpan _ comma _
  | final commaSpan _ comma _ _ _ _ _
  | next commaSpan _ comma _ _ _ _ => exact ⟨commaSpan, comma.1⟩

include successUnique disjoint in
theorem ParenthesizedTupleTailTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ values closingSpan output events,
      ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output events := by
  induction rejection with
  | commaMissing absent reported =>
      rintro ⟨_, _, _, _, parsed⟩
      exact absent (tail_comma_present parsed)
  | elementRejected span token absent child =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | trailing _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | final _ _ otherToken _ other _ _ _
      | next _ _ otherToken _ other _ _ =>
          cases token.output_unique otherToken
          exact disjoint child ⟨_, _, _, other⟩
  | closingMissing span token absent child progress commaAbsent closingAbsent reported =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | trailing _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | final _ _ otherToken _ other _ _ closing =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact closingAbsent ⟨_, closing.1⟩
      | next _ _ otherToken _ other _ tail =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact commaAbsent (tail_comma_present tail)
  | laterRejected span nextSpan token absent child progress nextComma tail ih =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | trailing _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | final _ _ otherToken _ other _ commaAbsent _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact commaAbsent ⟨nextSpan, nextComma⟩
      | next _ _ otherToken _ other _ otherTail =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact ih ⟨_, _, _, _, otherTail⟩

include successUnique disjoint in
theorem ParenthesizedExpressionTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ParenthesizedExpressionTraceParses elementTrace source endByte input value output events := by
  rintro ⟨_, _, _, parsed⟩
  cases rejection with
  | openingMissing absent reported =>
      cases parsed with
      | empty span _ token _
      | group span _ token _ _ _ _ _
      | tuple span _ token _ _ _ _ => exact absent ⟨span, token.1⟩
  | firstRejected span token absent child =>
      cases parsed with
      | empty _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | group _ _ otherToken _ other _ _ _
      | tuple _ _ otherToken _ other _ _ =>
          cases token.output_unique otherToken
          exact disjoint child ⟨_, _, _, other⟩
  | closingMissing span token absent child progress commaAbsent closingAbsent reported =>
      cases parsed with
      | empty _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | group _ _ otherToken _ other _ _ closing =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact closingAbsent ⟨_, closing.1⟩
      | tuple _ _ otherToken _ other _ tail =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact commaAbsent (tail_comma_present tail)
  | tailRejected span nextSpan token absent child progress nextComma tail =>
      cases parsed with
      | empty _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | group _ _ otherToken _ other _ commaAbsent _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact commaAbsent ⟨nextSpan, nextComma⟩
      | tuple _ _ otherToken _ other _ otherTail =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact tail.disjoint_success successUnique disjoint ⟨_, _, _, _, otherTail⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedTraceOutcomeProperties
/-! Independent exact parenthesized outcomes lift child uniqueness and
disjointness. This includes raw opening rejection without asserting existence,
concrete recursive execution, or a parser-state equality beyond the traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem parenthesizedTraceExactOutcomeSpec
    {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (elements : ExpressionTraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    ExpressionTraceExactOutcomeSpec (ParenthesizedExpressionTraceParses elementTrace)
      (ParenthesizedExpressionTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := ParenthesizedExpressionTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := ParenthesizedExpressionTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := ParenthesizedExpressionTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedRejectionTraceProtectionProperties
/-! Protected child events survive later tuple-tail or parenthesized
rejection. Marker/closing failures emit nothing, and their uncommitted report
is separate from the complete protected diagnostic suffix. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem ParenthesizedTupleTailTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedTupleTailTraceRejects elementTrace elementRejects
      source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | commaMissing => exact .nil
  | elementRejected _ _ _ child => exact rejectProtected child
  | closingMissing _ _ _ child _ _ _ _ => exact successProtected child
  | laterRejected _ _ _ _ child _ _ _ ih => exact (successProtected child).append ih

theorem ParenthesizedExpressionTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects elementTrace elementRejects
      source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | openingMissing => exact .nil
  | firstRejected _ _ _ child => exact rejectProtected child
  | closingMissing _ _ _ child _ _ _ _ => exact successProtected child
  | tailRejected _ _ _ _ child _ _ tail =>
      exact (successProtected child).append (tail.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParenthesizedTraceProtectionProperties
/-! Parenthesis and comma tokens emit no events. Protected child traces keep
their source order and every duplicate through all successful branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem ParenthesizedTupleTailTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | trailing => exact .nil
  | final _ _ _ _ child _ _ _ => exact elementProtected child
  | next _ _ _ _ child _ _ ih => exact (elementProtected child).append ih

theorem ParenthesizedExpressionTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | empty => exact .nil
  | group _ _ _ _ child _ _ _ => exact elementProtected child
  | tuple _ _ _ _ child _ tail => exact (elementProtected child).append (tail.cascadeFilters elementProtected)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionAtomRecoveryTraceGrammar
/-! Standalone atom recovery consumes its mandatory first token, then uses the
existing boundary-prioritized scan. Exactly one recovered expression-atom
event is emitted at the error span. Missing backing during a scan is a stop;
an unavailable first token instead rejects with a separate expression report.
Any earlier committed caller report is outside these judgments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def expressionAtomRecoveryTraceEvent (span : SourceSpan) : ParseDiagnostic :=
  { span, kind := .recovered .expressionAtom }

def ExpressionAtomRecoveryTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : Syntax.Expr) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  ExpressionAtomRecoveryParses input value output ∧ trace = [expressionAtomRecoveryTraceEvent value.span]

def ExpressionAtomRecoveryTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  ExpressionAtomRecoveryRejects input rejected ∧
    RejectAtReports source endByte { head := .expression, tail := [] } .expression input report ∧ trace = []

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionAtomTraceGrammar
/-! Public atom outcomes over arbitrary core traces. Rewind preserves the
failed carrier and end index and restores only the original cursor. Boundary
rejection leaves the original report uncommitted; otherwise it is committed
once before standalone recovery. A recovery failure is a separate terminal
report. Unlike ordinary public atom outcomes, no core carrier law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def expressionAtomTraceRewind (input failed : Remainder) : Remainder :=
  { failed with cursor := input.cursor }

inductive ExpressionAtomTraceParses
    (coreTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | core {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
      (parsed : coreTrace source endByte input value output trace) :
      ExpressionAtomTraceParses coreTrace coreRejects source endByte input value output trace
  | recovered {input failed output : Remainder} {value : Syntax.Expr}
      {coreReport : ParseDiagnostic} {coreTraceEvents recoveryTrace : List ParseDiagnostic}
      (coreRejected : coreRejects source endByte input failed coreReport coreTraceEvents)
      (continues : ¬ ExpressionAtomBoundaryStops (expressionAtomTraceRewind input failed))
      (recovered : ExpressionAtomRecoveryTraceParses source endByte
        (expressionAtomTraceRewind input failed) value output recoveryTrace) :
      ExpressionAtomTraceParses coreTrace coreRejects source endByte input value output
        ((coreTraceEvents ++ [coreReport]) ++ recoveryTrace)

inductive ExpressionAtomTraceRejects
    (coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | boundary {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
      (coreRejected : coreRejects source endByte input failed coreReport coreTrace)
      (stops : ExpressionAtomBoundaryStops (expressionAtomTraceRewind input failed)) :
      ExpressionAtomTraceRejects coreRejects source endByte input
        (expressionAtomTraceRewind input failed) coreReport coreTrace
  | recovery {input failed rejected : Remainder} {coreReport report : ParseDiagnostic}
      {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : coreRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ ExpressionAtomBoundaryStops (expressionAtomTraceRewind input failed))
      (recoveryRejected : ExpressionAtomRecoveryTraceRejects source endByte
        (expressionAtomTraceRewind input failed) rejected report recoveryTrace) :
      ExpressionAtomTraceRejects coreRejects source endByte input rejected report
        ((coreTrace ++ [coreReport]) ++ recoveryTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionAtomRecoveryTraceProperties
/-! Exact standalone recovery keeps its complete error AST, token remainder,
and singleton event distinct from the terminal report. The recovered event is
only conditionally kept or dropped by lexical cascade filtering. Independent
outcome exactness is not an existence claim about complete expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

private theorem scan_fields {first last : SourceSpan} {input output : Remainder} {value : Syntax.Expr}
    (parsed : ExpressionAtomRecoveryScanParses first last input value output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor ≤ output.cursor ∧ value.value = .error := by
  induction parsed with
  | stop => exact ⟨rfl, rfl, Nat.le_refl _, rfl⟩
  | next _ _ _ ih => exact ⟨ih.1, ih.2.1, Nat.le_trans (Nat.le_succ _) ih.2.2.1, ih.2.2.2⟩

theorem ExpressionAtomRecoveryTraceParses.ordinary
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    ExpressionAtomRecoveryParses input value output := parsed.1

theorem ExpressionAtomRecoveryTraceParses.error_value
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    value.value = .error := by
  cases parsed.1 with
  | recovered _ scan => exact (scan_fields scan).2.2.2

theorem ExpressionAtomRecoveryTraceParses.output_window
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed.1 with
  | recovered _ scan => exact ⟨(scan_fields scan).1, (scan_fields scan).2.1⟩

theorem ExpressionAtomRecoveryTraceParses.cursor_lt
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed.1 with
  | recovered _ scan => have progress := (scan_fields scan).2.2.1; exact progress

theorem ExpressionAtomRecoveryTraceParses.trace_eq
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    trace = [expressionAtomRecoveryTraceEvent value.span] := parsed.2

theorem ExpressionAtomRecoveryTraceRejects.ordinary
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) :
    ExpressionAtomRecoveryRejects input rejected := rejection.1

theorem ExpressionAtomRecoveryTraceRejects.output_eq
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) :
    rejected = input := rejection.1.output_eq

theorem ExpressionAtomRecoveryTraceRejects.trace_eq
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) : trace = [] :=
  rejection.2.2

theorem ExpressionAtomRecoveryTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionAtomRecoveryTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionAtomRecoveryTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  have sameValue := leftParsed.1.value_unique rightParsed.1
  have sameOutput := leftParsed.1.output_unique rightParsed.1
  cases sameValue
  exact ⟨rfl, sameOutput, leftParsed.2.trans rightParsed.2.symm⟩

theorem ExpressionAtomRecoveryTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ExpressionAtomRecoveryTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ExpressionAtomRecoveryTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  ⟨leftRejected.1.output_eq.trans rightRejected.1.output_eq.symm,
    leftRejected.2.1.diagnostic_unique rightRejected.2.1, leftRejected.2.2.trans rightRejected.2.2.symm⟩

theorem ExpressionAtomRecoveryTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ExpressionAtomRecoveryTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  exact rejection.1.disjointParses ⟨value, output, parsed.1⟩

theorem ExpressionAtomRecoveryTraceParses.cascade_kept
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [parsed.2]
  exact .keep (fun suppressed => retained suppressed.2) .nil

theorem ExpressionAtomRecoveryTraceParses.cascade_dropped
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace [] := by
  rw [parsed.2]
  exact .drop ⟨by trivial, suppressed⟩ .nil

theorem ExpressionAtomRecoveryTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [rejection.2.2]
  exact .nil

theorem expressionAtomRecoveryTraceExactOutcomeSpec :
    TraceExactOutcomeSpec ExpressionAtomRecoveryTraceParses ExpressionAtomRecoveryTraceRejects source endByte where
  successResultUnique := ExpressionAtomRecoveryTraceParses.result_unique
  rejectResultUnique := ExpressionAtomRecoveryTraceRejects.result_unique
  successRejectDisjoint := ExpressionAtomRecoveryTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionAtomTraceProperties
/-! Conditional exactness first compares arbitrary core outcomes, then the
boundary or standalone recovery. Rewind never replaces a failed carrier with
the input carrier. Exactness gives uniqueness and disjointness, not existence.
All mixed trace components have explicit filtering premises: arbitrary core
events, committed reports, and recovery events are not uniformly protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {coreTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem expressionAtomTraceRewind_fields (input failed : Remainder) :
    (expressionAtomTraceRewind input failed).tokens = failed.tokens ∧
    (expressionAtomTraceRewind input failed).endIndex = failed.endIndex ∧
    (expressionAtomTraceRewind input failed).cursor = input.cursor := ⟨rfl, rfl, rfl⟩

theorem expressionAtomTraceRewind_eq_input_of_carrier {input failed : Remainder}
    (tokens : failed.tokens = input.tokens) (endIndex : failed.endIndex = input.endIndex) :
    expressionAtomTraceRewind input failed = input := by
  cases input
  simp only [expressionAtomTraceRewind, tokens, endIndex]

theorem ExpressionAtomTraceParses.result_unique
    (core : TraceExactOutcomeSpec coreTrace coreRejects source endByte)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionAtomTraceParses coreTrace coreRejects source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionAtomTraceParses coreTrace coreRejects source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact core.successResultUnique leftCore rightCore
      | recovered rejected _ _ => exact False.elim (core.successRejectDisjoint rejected ⟨_, _, _, leftCore⟩)
  | recovered leftCore _ leftRecovery =>
      cases rightParsed with
      | core rightCore => exact False.elim (core.successRejectDisjoint leftCore ⟨_, _, _, rightCore⟩)
      | recovered rightCore _ rightRecovery =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionAtomTraceRejects.result_unique
    (core : TraceExactOutcomeSpec coreTrace coreRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ExpressionAtomTraceRejects coreRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ExpressionAtomTraceRejects coreRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | boundary leftCore stops =>
      cases rightRejected with
      | boundary rightCore _ =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | recovery rightCore continues _ =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
  | recovery leftCore continues leftRecovery =>
      cases rightRejected with
      | boundary rightCore stops =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
      | recovery rightCore _ rightRecovery =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionAtomTraceRejects.disjoint_success
    (core : TraceExactOutcomeSpec coreTrace coreRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomTraceRejects coreRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ExpressionAtomTraceParses coreTrace coreRejects source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | boundary rejectedCore stops =>
      cases parsed with
      | core parsedCore => exact core.successRejectDisjoint rejectedCore ⟨_, _, _, parsedCore⟩
      | recovered otherCore continues _ =>
          rcases core.rejectResultUnique rejectedCore otherCore with ⟨rfl, rfl, rfl⟩
          exact continues stops
  | recovery rejectedCore _ rejectedRecovery =>
      cases parsed with
      | core parsedCore => exact core.successRejectDisjoint rejectedCore ⟨_, _, _, parsedCore⟩
      | recovered otherCore _ parsedRecovery =>
          rcases core.rejectResultUnique rejectedCore otherCore with ⟨rfl, rfl, rfl⟩
          exact rejectedRecovery.disjoint_success ⟨_, _, _, parsedRecovery⟩

theorem expressionAtomTraceExactOutcomeSpec
    (core : TraceExactOutcomeSpec coreTrace coreRejects source endByte) :
    TraceExactOutcomeSpec (ExpressionAtomTraceParses coreTrace coreRejects)
      (ExpressionAtomTraceRejects coreRejects) source endByte where
  successResultUnique := ExpressionAtomTraceParses.result_unique core
  rejectResultUnique := ExpressionAtomTraceRejects.result_unique core
  successRejectDisjoint := ExpressionAtomTraceRejects.disjoint_success core

/-- An unavailable mandatory token inside the public non-boundary branch is a
missing backing slot, never merely a window end. Its report is still terminal. -/
theorem expressionAtomRecoveryTraceRejects_missingToken_of_nonboundary
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (continues : ¬ ExpressionAtomBoundaryStops input)
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) :
    rejected = input ∧ input.cursor < input.endIndex ∧ input.tokens[input.cursor]? = none ∧ trace = [] := by
  rcases rejection with ⟨recovery, _, traceEq⟩
  cases recovery with
  | windowEnd ended => exact False.elim (continues (.windowEnd ended))
  | missingToken inside missing => exact ⟨rfl, inside, missing, traceEq⟩

theorem expressionAtomRecoveryTrace_cascadeFilters
    (text : String) (lexical : List SourceSpan)
    {coreTrace recoveryTrace keptCore keptReport keptRecovery : List ParseDiagnostic} {coreReport : ParseDiagnostic}
    (coreFiltered : ParseDiagnosticCascadeFilters text lexical coreTrace keptCore)
    (reportFiltered : ParseDiagnosticCascadeFilters text lexical [coreReport] keptReport)
    (recoveryFiltered : ParseDiagnosticCascadeFilters text lexical recoveryTrace keptRecovery) :
    ParseDiagnosticCascadeFilters text lexical ((coreTrace ++ [coreReport]) ++ recoveryTrace)
      ((keptCore ++ keptReport) ++ keptRecovery) :=
  (coreFiltered.append reportFiltered).append recoveryFiltered

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeArrayLiteralTraceGrammar
/-! Independent array-literal traces wrap an allow-empty no-trailing bracketed
list. The wrapper changes only the AST: remainder, reports, and events are
unchanged. This relation is not restricted to a dispatch-selected opening. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ArrayLiteralTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {values : DelimitedList Syntax.Expr}
      {trace : List ParseDiagnostic}
      (valuesParsed : NoTrailingDelimitedListTraceParses .leftBracket .rightBracket true
        elementTrace source endByte input values output trace) :
      ArrayLiteralTraceParses elementTrace source endByte input
        { span := values.span, value := .array values } output trace

abbrev ArrayLiteralTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop) :=
  NoTrailingDelimitedListTraceRejects .leftBracket .rightBracket true .expression
    elementTrace elementRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeArrayLiteralTraceProperties
/-! Array mapping retains the list's exact structure and protected event
suffix. Ordinary erasure requires a child carrier law separately; the trace
grammar itself imposes neither that law nor a recursive expression claim. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ArrayLiteralTraceParses.ordinary
    {elementParses : Remainder → Syntax.Expr → Remainder → Prop}
    (erases : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ArrayLiteralTraceParses elementTrace source endByte input value output trace) :
    ArrayLiteralExpressionParses elementParses input value output := by
  cases parsed with
  | parsed values => exact .parsed (values.ordinary erases elementWindow)

theorem ArrayLiteralTraceParses.cursor_lt
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ArrayLiteralTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed values =>
      cases values with
      | empty _ _ _ opening closing =>
          rw [closing.2, opening.2]
          exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
      | nonempty _ _ opening _ _ progress tail =>
          rw [opening.2] at progress
          exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) tail.progress

theorem ArrayLiteralTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ArrayLiteralTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed values => exact values.output_window elementWindow

theorem ArrayLiteralTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ArrayLiteralTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed values => exact values.cascadeFilters elementProtected

theorem ArrayLiteralTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ArrayLiteralTraceRejects elementTrace elementRejects source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace :=
  NoTrailingDelimitedListTraceRejects.cascadeFilters successProtected rejectProtected rejection

theorem ArrayLiteralTraceParses.result_unique
    (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ArrayLiteralTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ArrayLiteralTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftValues =>
      cases rightParsed with
      | parsed rightValues =>
          rcases leftValues.result_unique successUnique rightValues with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ArrayLiteralTraceRejects.result_unique
    (elements : ExpressionTraceExactOutcomeSpec elementTrace elementRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ArrayLiteralTraceRejects elementTrace elementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : ArrayLiteralTraceRejects elementTrace elementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  (noTrailingDelimitedListTraceExactOutcomeSpec .leftBracket .rightBracket true .expression
    elements.toTraceExactOutcomeSpec).rejectResultUnique left right

theorem ArrayLiteralTraceRejects.disjoint_success
    (elements : ExpressionTraceExactOutcomeSpec elementTrace elementRejects source endByte)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ArrayLiteralTraceRejects elementTrace elementRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ value output events, ArrayLiteralTraceParses elementTrace source endByte input value output events := by
  rintro ⟨_, _, _, parsed⟩
  cases parsed with
  | parsed values =>
      exact (noTrailingDelimitedListTraceExactOutcomeSpec .leftBracket .rightBracket true .expression
        elements.toTraceExactOutcomeSpec).successRejectDisjoint rejection ⟨_, _, _, values⟩

/-- Exactness fixes ASTs, remainders, reports, and complete event sequences.
It is a uniqueness/disjointness bundle, not an assertion of outcome existence. -/
theorem arrayLiteralTraceExactOutcomeSpec
    (elements : ExpressionTraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    ExpressionTraceExactOutcomeSpec (ArrayLiteralTraceParses elementTrace)
      (ArrayLiteralTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := ArrayLiteralTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := ArrayLiteralTraceRejects.result_unique elements
  successRejectDisjoint := ArrayLiteralTraceRejects.disjoint_success elements

end Solcore.Syntax.DeclarativeGrammar
end
