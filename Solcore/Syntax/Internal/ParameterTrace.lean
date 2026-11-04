import Solcore.Syntax.Internal.NameTrace
import Solcore.Syntax.Grammar.Signatures
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.ParameterOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.TraceBasics
import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Internal.TypeTrace
import Solcore.Syntax.Internal.DelimitedTrace

/-!
Exact diagnostic traces of function and lambda parameters: raw, core and
public layers, tails, recovery, and whole parameter lists.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeParameterNameFinishingTraceProperties
/-! Independent finishing events for an ordinary parameter name. This check
follows the checked-identifier events and precedes the parameter tail. It does
not apply to the name following a selected contextual comptime marker. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ParameterNameFinishingTrace (name : Syntax.Identifier) : List ParseDiagnostic → Prop where
  | ordinary (spelling : name.value ≠ ContextualKeyword.comptime.spelling) :
      ParameterNameFinishingTrace name []
  | comptime (spelling : name.value = ContextualKeyword.comptime.spelling) :
      ParameterNameFinishingTrace name [{
        span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName
      }]

theorem parameterNameFinishingTrace_exists (name : Syntax.Identifier) :
    ∃ trace, ParameterNameFinishingTrace name trace := by
  by_cases spelling : name.value = ContextualKeyword.comptime.spelling
  · exact ⟨_, .comptime spelling⟩
  · exact ⟨[], .ordinary spelling⟩

theorem ParameterNameFinishingTrace.trace_unique {name : Syntax.Identifier}
    {left right : List ParseDiagnostic}
    (leftTrace : ParameterNameFinishingTrace name left)
    (rightTrace : ParameterNameFinishingTrace name right) : left = right := by
  cases leftTrace <;> cases rightTrace <;> first | rfl | contradiction

theorem ParameterNameFinishingTrace.nil_iff {name : Syntax.Identifier} :
    ParameterNameFinishingTrace name [] ↔ name.value ≠ ContextualKeyword.comptime.spelling := by
  constructor
  · intro trace; cases trace with | ordinary spelling => exact spelling
  · exact .ordinary

theorem ParameterNameFinishingTrace.comptime_iff {name : Syntax.Identifier} :
    ParameterNameFinishingTrace name [{
      span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName
    }] ↔ name.value = ContextualKeyword.comptime.spelling := by
  constructor
  · intro trace; cases trace with | comptime spelling => exact spelling
  · exact .comptime

theorem ParameterNameFinishingTrace.cascadeFilters {name : Syntax.Identifier}
    {trace : List ParseDiagnostic} (events : ParameterNameFinishingTrace name trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases events with
  | ordinary => exact .nil
  | comptime => exact parseDiagnosticCascadeFilters_protected_cons (by simp [LexicalCascadeCandidate]) .nil

/-- Checked identifier events first, then the ordinary-name spelling check.
This prefix relation makes no comptime-pair selection or tail claim. -/
inductive CheckedParameterNameTraceParses :
    Remainder → Syntax.Identifier → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier}
      {identifierTrace finishingTrace : List ParseDiagnostic}
      (identifier : IdentifierTraceParses input name output identifierTrace)
      (finishing : ParameterNameFinishingTrace name finishingTrace) :
      CheckedParameterNameTraceParses input name output (identifierTrace ++ finishingTrace)

theorem CheckedParameterNameTraceParses.ordinary
    {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : CheckedParameterNameTraceParses input name output trace) : IdentifierParses input name output := by
  cases parsed with
  | parsed identifier _ => exact (identifierTraceParses_iff.mp identifier).1

theorem checkedParameterNameTraceParses_exists
    {input output : Remainder} {name : Syntax.Identifier}
    (ordinary : IdentifierParses input name output) :
    ∃ trace, CheckedParameterNameTraceParses input name output trace := by
  rcases identifierDiagnosticTrace_total name with ⟨identifierTrace, identifier⟩
  rcases parameterNameFinishingTrace_exists name with ⟨finishingTrace, finishing⟩
  exact ⟨_, .parsed (.parsed ordinary identifier) finishing⟩

theorem CheckedParameterNameTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : CheckedParameterNameTraceParses input left afterLeft leftTrace)
    (rightParsed : CheckedParameterNameTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftIdentifier leftFinishing =>
      cases rightParsed with
      | parsed rightIdentifier rightFinishing =>
          rcases leftIdentifier.result_unique rightIdentifier with ⟨rfl, rfl, rfl⟩
          cases leftFinishing.trace_unique rightFinishing
          exact ⟨rfl, rfl, rfl⟩

theorem CheckedParameterNameTraceParses.cascadeFilters
    {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : CheckedParameterNameTraceParses input name output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed identifier finishing =>
      exact ((identifierTraceParses_iff.mp identifier).2.cascadeFilters text lexical).append
        (finishing.cascadeFilters text lexical)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParameterRecoveryTraceGrammar
/-! Standalone parameter recovery retains the existing exact scan and emits
one recovered event at its final error-node span. A missing mandatory first
token rejects without events; its terminal report is separate from the trace.
These judgments do not include the caller's earlier failure commitment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def parameterRecoveryTraceEvent (span : SourceSpan) : ParseDiagnostic :=
  { span, kind := .recovered .functionParameter }

def FunctionParameterRecoveryTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : Syntax.FunctionParameter) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  FunctionParameterRecoveryParses input value output ∧ trace = [parameterRecoveryTraceEvent value.span]

def FunctionParameterRecoveryTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  FunctionParameterRecoveryRejects input rejected ∧
    RejectAtReports source endByte { head := .identifier, tail := [] } .parameter input report ∧ trace = []

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterRecoveryTraceGrammar
/-! Standalone lambda recovery reuses the independent function recovery scan,
retagging its recovered span as a lambda error. The event and terminal report
are unchanged; a caller's earlier failure commitment is outside this grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive LambdaParameterRecoveryTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | recovered {input output : Remainder} {parameter : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (parsed : FunctionParameterRecoveryTraceParses source endByte input parameter output trace) :
      LambdaParameterRecoveryTraceParses source endByte input { span := parameter.span, value := .error } output trace

abbrev LambdaParameterRecoveryTraceRejects := FunctionParameterRecoveryTraceRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParameterRecoveryTraceProperties
/-! Exact standalone recovery values, remainders, reports, and event suffixes.
Earlier committed reports belong to the caller, not to this one-event scan.
The joint specification asserts uniqueness and disjointness, not existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem FunctionParameterRecoveryTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : FunctionParameterRecoveryTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : FunctionParameterRecoveryTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases leftParsed.1.result_unique rightParsed.1 with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, leftParsed.2.trans rightParsed.2.symm⟩

theorem FunctionParameterRecoveryTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : FunctionParameterRecoveryTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : FunctionParameterRecoveryTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  ⟨leftRejected.1.output_unique rightRejected.1,
    leftRejected.2.1.diagnostic_unique rightRejected.2.1, leftRejected.2.2.trans rightRejected.2.2.symm⟩

theorem FunctionParameterRecoveryTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionParameterRecoveryTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, FunctionParameterRecoveryTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  exact rejection.1.disjointParses ⟨value, output, parsed.1⟩

theorem FunctionParameterRecoveryTraceParses.cascade_kept
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : FunctionParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [parsed.2]
  exact .keep (fun suppressed => retained suppressed.2) .nil

theorem FunctionParameterRecoveryTraceParses.cascade_dropped
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : FunctionParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace [] := by
  rw [parsed.2]
  exact .drop ⟨by trivial, suppressed⟩ .nil

theorem FunctionParameterRecoveryTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionParameterRecoveryTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [rejection.2.2]
  exact .nil

theorem functionParameterRecoveryTraceExactOutcomeSpec :
    TraceExactOutcomeSpec FunctionParameterRecoveryTraceParses FunctionParameterRecoveryTraceRejects source endByte where
  successResultUnique := FunctionParameterRecoveryTraceParses.result_unique
  rejectResultUnique := FunctionParameterRecoveryTraceRejects.result_unique
  successRejectDisjoint := FunctionParameterRecoveryTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterRecoveryTraceProperties
/-! Standalone lambda recovery has exact error values, remainders, reports,
and event suffixes. Its recovered event is conditionally retained or dropped,
not unconditionally protected against lexical cascade suppression. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem LambdaParameterRecoveryTraceParses.ordinary
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace) :
    LambdaParameterRecoveryParses input value output := by
  cases parsed with
  | recovered recovery => exact .recovered recovery.1

theorem LambdaParameterRecoveryTraceParses.error_value
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace) :
    value.value = .error := by cases parsed; rfl

theorem LambdaParameterRecoveryTraceParses.trace_eq
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace) :
    trace = [parameterRecoveryTraceEvent value.span] := by
  cases parsed with
  | recovered recovery => exact recovery.2

theorem LambdaParameterRecoveryTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : LambdaParameterRecoveryTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : LambdaParameterRecoveryTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | recovered leftRecovery =>
      cases rightParsed with
      | recovered rightRecovery =>
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LambdaParameterRecoveryTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : LambdaParameterRecoveryTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : LambdaParameterRecoveryTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  FunctionParameterRecoveryTraceRejects.result_unique leftRejected rightRejected

theorem LambdaParameterRecoveryTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterRecoveryTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, LambdaParameterRecoveryTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | recovered recovery => exact FunctionParameterRecoveryTraceRejects.disjoint_success rejection ⟨_, _, _, recovery⟩

theorem LambdaParameterRecoveryTraceParses.cascade_kept
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | recovered recovery => exact recovery.cascade_kept text lexical retained

theorem LambdaParameterRecoveryTraceParses.cascade_dropped
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace [] := by
  cases parsed with
  | recovered recovery => exact recovery.cascade_dropped text lexical suppressed

theorem LambdaParameterRecoveryTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterRecoveryTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace :=
  FunctionParameterRecoveryTraceRejects.cascadeFilters rejection text lexical

theorem lambdaParameterRecoveryTraceExactOutcomeSpec :
    TraceExactOutcomeSpec LambdaParameterRecoveryTraceParses LambdaParameterRecoveryTraceRejects source endByte where
  successResultUnique := LambdaParameterRecoveryTraceParses.result_unique
  rejectResultUnique := LambdaParameterRecoveryTraceRejects.result_unique
  successRejectDisjoint := LambdaParameterRecoveryTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypedParameterFinishingTraceGrammar
/-! Independent parameter-finishing events and exact constructed values.
The already parsed type is retained, but its own events are not replayed.
Only an outer comptime type contributes the parameter-specific diagnostic. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def typedParameterTraceValue (start : SourceSpan) (marker : Option SourceSpan)
    (name : Syntax.Identifier) (type : Syntax.TypeExpr) : Syntax.FunctionParameter := {
  span := SourceSpan.cover start type.span, value := .typed marker name type
}

inductive TypedParameterFinishingTrace (type : Syntax.TypeExpr) : List ParseDiagnostic → Prop where
  | ordinary (allowed : ParameterTypeAllowed type) : TypedParameterFinishingTrace type []
  | comptime (forbidden : ¬ ParameterTypeAllowed type) :
      TypedParameterFinishingTrace type [{
        span := type.span, kind := .constraintViolation .comptimeTypeInParameter
      }]

def errorParameterTraceValue (span : SourceSpan) : Syntax.FunctionParameter :=
  { span, value := .error }

inductive ErrorParameterFinishingTrace (span : SourceSpan) (constraint : ParseConstraint) :
    List ParseDiagnostic → Prop where
  | emitted : ErrorParameterFinishingTrace span constraint [{ span, kind := .constraintViolation constraint }]

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedParameterTailTraceGrammar
/-! Independent named-parameter tails use the complete recursive type trace.
Colon absence is an error-valued success with its own constraint event; colon
presence parses the type and then appends only its finishing events. A rejected
type retains its complete trace and separate, uncommitted terminal report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedParameterTailTraceParses
    (start : SourceSpan) (marker : Option SourceSpan) (name : Syntax.Identifier) (errorSpan : SourceSpan)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | typed {input afterColon output : Remainder} {type : Syntax.TypeExpr}
      {typeEvents finishingEvents : List ParseDiagnostic} (colonSpan : SourceSpan)
      (colon : ExactTokenParses (.symbol .colon) input colonSpan afterColon)
      (typeParsed : TypeExprTraceParses source endByte afterColon type output typeEvents)
      (finished : TypedParameterFinishingTrace type finishingEvents) :
      NamedParameterTailTraceParses start marker name errorSpan source endByte input
        (typedParameterTraceValue start marker name type) output (typeEvents ++ finishingEvents)
  | typeMissing {input : Remainder} {events : List ParseDiagnostic}
      (colonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .colon))
      (finished : ErrorParameterFinishingTrace errorSpan .namedParameterRequiresType events) :
      NamedParameterTailTraceParses start marker name errorSpan source endByte input
        (errorParameterTraceValue errorSpan) input events

inductive NamedParameterTailTraceRejects
    (start : SourceSpan) (marker : Option SourceSpan) (name : Syntax.Identifier) (errorSpan : SourceSpan)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | typeRejected {input afterColon rejected : Remainder} {report : ParseDiagnostic}
      {trace : List ParseDiagnostic} (colonSpan : SourceSpan)
      (colon : ExactTokenParses (.symbol .colon) input colonSpan afterColon)
      (typeRejected : TypeExprTraceRejects source endByte afterColon rejected report trace) :
      NamedParameterTailTraceRejects start marker name errorSpan source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterTailTraceGrammar
/-! Lambda-tail outcomes before name dispatch or recovery. The retagging is
pure data. A typed branch requires a present colon; without one an ordinary
name is inferred, while a comptime name emits its distinct missing-type event. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def lambdaParameterTraceValue (parameter : Syntax.FunctionParameter) : Syntax.LambdaParameter := {
  span := parameter.span
  value := match parameter.value with
    | .typed marker name type => .typed marker name type
    | .error => .error
}

inductive OrdinaryLambdaParameterTailTraceParses (name : Syntax.Identifier)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | typed {input output : Remainder} {parameter : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .colon })
      (parsed : NamedParameterTailTraceParses name.span none name name.span source endByte
        input parameter output trace) :
      OrdinaryLambdaParameterTailTraceParses name source endByte input (lambdaParameterTraceValue parameter) output trace
  | inferred {input : Remainder}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .colon)) :
      OrdinaryLambdaParameterTailTraceParses name source endByte input { span := name.span, value := .inferred name } input []

abbrev OrdinaryLambdaParameterTailTraceRejects (name : Syntax.Identifier) :=
  NamedParameterTailTraceRejects name.span none name name.span

inductive ComptimeLambdaParameterTailTraceParses (marker : SourceSpan) (name : Syntax.Identifier)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | typed {input output : Remainder} {parameter : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .colon })
      (parsed : NamedParameterTailTraceParses marker (some marker) name (SourceSpan.cover marker name.span)
        source endByte input parameter output trace) :
      ComptimeLambdaParameterTailTraceParses marker name source endByte input (lambdaParameterTraceValue parameter) output trace
  | typeMissing {input : Remainder} {trace : List ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .colon))
      (finished : ErrorParameterFinishingTrace (SourceSpan.cover marker name.span) .comptimeParameterRequiresType trace) :
      ComptimeLambdaParameterTailTraceParses marker name source endByte input
        (lambdaParameterTraceValue (errorParameterTraceValue (SourceSpan.cover marker name.span))) input trace

abbrev ComptimeLambdaParameterTailTraceRejects (marker : SourceSpan) (name : Syntax.Identifier) :=
  NamedParameterTailTraceRejects marker (some marker) name (SourceSpan.cover marker name.span)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterRawTraceGrammar
/-! Raw lambda-parameter outcomes before pair selection or public recovery.
Ordinary names include their parameter-name finishing events. A comptime marker
is silent and its following name receives only identifier checking. Each first
failure retains its complete separate report and all earlier ordered events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OrdinaryLambdaParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterName output : Remainder} {name : Syntax.Identifier} {value : Syntax.LambdaParameter}
      {nameEvents tailEvents : List ParseDiagnostic}
      (nameParsed : CheckedParameterNameTraceParses input name afterName nameEvents)
      (tail : OrdinaryLambdaParameterTailTraceParses name source endByte afterName value output tailEvents) :
      OrdinaryLambdaParameterTraceParses source endByte input value output (nameEvents ++ tailEvents)

inductive OrdinaryLambdaParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | nameRejected {input : Remainder} {report : ParseDiagnostic}
      (absent : IdentifierAbsentAt input)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] } .parameter input report) :
      OrdinaryLambdaParameterTraceRejects source endByte input input report []
  | tailRejected {input afterName rejected : Remainder} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic}
      (nameParsed : CheckedParameterNameTraceParses input name afterName nameEvents)
      (tail : OrdinaryLambdaParameterTailTraceRejects name source endByte afterName rejected report tailEvents) :
      OrdinaryLambdaParameterTraceRejects source endByte input rejected report (nameEvents ++ tailEvents)

inductive ComptimeLambdaParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterName output : Remainder} {name : Syntax.Identifier} {value : Syntax.LambdaParameter}
      {nameEvents tailEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
      (tail : ComptimeLambdaParameterTailTraceParses markerSpan name source endByte afterName value output tailEvents) :
      ComptimeLambdaParameterTraceParses source endByte input value output (nameEvents ++ tailEvents)

inductive ComptimeLambdaParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.identifier ContextualKeyword.comptime.spelling))
      (reported : RejectAtReports source endByte { head := .contextual .comptime, tail := [] } .parameter input report) :
      ComptimeLambdaParameterTraceRejects source endByte input input report []
  | nameRejected {input afterMarker : Remainder} {report : ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (absent : IdentifierAbsentAt afterMarker)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] } .parameter afterMarker report) :
      ComptimeLambdaParameterTraceRejects source endByte input afterMarker report []
  | tailRejected {input afterMarker afterName rejected : Remainder} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
      (tail : ComptimeLambdaParameterTailTraceRejects markerSpan name source endByte afterName rejected report tailEvents) :
      ComptimeLambdaParameterTraceRejects source endByte input rejected report (nameEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterCoreTraceGrammar
/-! Exact pair-selected lambda-parameter outcomes before public recovery.
Both success and rejection retain the same explicit lookahead choice. A raw
comptime failure is never admitted through an absent contextual-name pair. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive LambdaParameterCoreTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | ordinary {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
      (absent : ComptimeParameterPrefixAbsentAt input)
      (parsed : OrdinaryLambdaParameterTraceParses source endByte input value output trace) :
      LambdaParameterCoreTraceParses source endByte input value output trace
  | comptime {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
      (present : ComptimeLambdaParameterStartsAt input)
      (parsed : ComptimeLambdaParameterTraceParses source endByte input value output trace) :
      LambdaParameterCoreTraceParses source endByte input value output trace

inductive LambdaParameterCoreTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | ordinary {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (absent : ComptimeParameterPrefixAbsentAt input)
      (rejection : OrdinaryLambdaParameterTraceRejects source endByte input rejected report trace) :
      LambdaParameterCoreTraceRejects source endByte input rejected report trace
  | comptime {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (present : ComptimeLambdaParameterStartsAt input)
      (rejection : ComptimeLambdaParameterTraceRejects source endByte input rejected report trace) :
      LambdaParameterCoreTraceRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedParameterRawTraceGrammar
/-! Raw ordinary and comptime parameter outcomes, before pair selection or
public recovery. Ordinary names include their spelling-finishing check; names
after a comptime marker receive only checked-identifier events. Every rejection
stops at the first failing stage and retains its separate complete report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OrdinaryNamedParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterName output : Remainder} {name : Syntax.Identifier} {value : Syntax.FunctionParameter}
      {nameEvents tailEvents : List ParseDiagnostic}
      (nameParsed : CheckedParameterNameTraceParses input name afterName nameEvents)
      (tail : NamedParameterTailTraceParses name.span none name name.span source endByte afterName value output tailEvents) :
      OrdinaryNamedParameterTraceParses source endByte input value output (nameEvents ++ tailEvents)

inductive OrdinaryNamedParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | nameRejected {input : Remainder} {report : ParseDiagnostic}
      (absent : IdentifierAbsentAt input)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] } .parameter input report) :
      OrdinaryNamedParameterTraceRejects source endByte input input report []
  | tailRejected {input afterName rejected : Remainder} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic}
      (nameParsed : CheckedParameterNameTraceParses input name afterName nameEvents)
      (tail : NamedParameterTailTraceRejects name.span none name name.span source endByte afterName rejected report tailEvents) :
      OrdinaryNamedParameterTraceRejects source endByte input rejected report (nameEvents ++ tailEvents)

inductive ComptimeNamedParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterName output : Remainder} {name : Syntax.Identifier} {value : Syntax.FunctionParameter}
      {nameEvents tailEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
      (tail : NamedParameterTailTraceParses markerSpan (some markerSpan) name (SourceSpan.cover markerSpan name.span)
        source endByte afterName value output tailEvents) :
      ComptimeNamedParameterTraceParses source endByte input value output (nameEvents ++ tailEvents)

inductive ComptimeNamedParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.identifier ContextualKeyword.comptime.spelling))
      (reported : RejectAtReports source endByte { head := .contextual .comptime, tail := [] } .parameter input report) :
      ComptimeNamedParameterTraceRejects source endByte input input report []
  | nameRejected {input afterMarker : Remainder} {report : ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (absent : IdentifierAbsentAt afterMarker)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] } .parameter afterMarker report) :
      ComptimeNamedParameterTraceRejects source endByte input afterMarker report []
  | tailRejected {input afterMarker afterName rejected : Remainder} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
      (tail : NamedParameterTailTraceRejects markerSpan (some markerSpan) name (SourceSpan.cover markerSpan name.span)
        source endByte afterName rejected report tailEvents) :
      ComptimeNamedParameterTraceRejects source endByte input rejected report (nameEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedParameterCoreTraceGrammar
/-! Exact pair-selected function-parameter outcomes before public recovery.
Both success and rejection retain the same explicit lookahead choice. A raw
comptime failure is never admitted through an absent contextual-name pair. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedParameterCoreTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | ordinary {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (absent : ComptimeParameterPrefixAbsentAt input)
      (parsed : OrdinaryNamedParameterTraceParses source endByte input value output trace) :
      NamedParameterCoreTraceParses source endByte input value output trace
  | comptime {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (present : ComptimeLambdaParameterStartsAt input)
      (parsed : ComptimeNamedParameterTraceParses source endByte input value output trace) :
      NamedParameterCoreTraceParses source endByte input value output trace

inductive NamedParameterCoreTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | ordinary {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (absent : ComptimeParameterPrefixAbsentAt input)
      (rejection : OrdinaryNamedParameterTraceRejects source endByte input rejected report trace) :
      NamedParameterCoreTraceRejects source endByte input rejected report trace
  | comptime {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (present : ComptimeLambdaParameterStartsAt input)
      (rejection : ComptimeNamedParameterTraceRejects source endByte input rejected report trace) :
      NamedParameterCoreTraceRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedParameterTraceGrammar
/-! Public named-parameter outcomes preserve the failed carrier and end index
while rewinding only its cursor. Boundary rejection commits no terminal report;
otherwise the original report is committed once before standalone recovery.
A later recovery failure is a new, separate uncommitted terminal report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def parameterTraceRewind (input failed : Remainder) : Remainder :=
  { failed with cursor := input.cursor }

inductive NamedParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | core {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (parsed : NamedParameterCoreTraceParses source endByte input value output trace) :
      NamedParameterTraceParses source endByte input value output trace
  | recovered {input failed output : Remainder} {value : Syntax.FunctionParameter}
      {coreReport : ParseDiagnostic} {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : NamedParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ FunctionParameterBoundaryStops (parameterTraceRewind input failed))
      (recovered : FunctionParameterRecoveryTraceParses source endByte
        (parameterTraceRewind input failed) value output recoveryTrace) :
      NamedParameterTraceParses source endByte input value output ((coreTrace ++ [coreReport]) ++ recoveryTrace)

inductive NamedParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | boundary {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
      (coreRejected : NamedParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (stops : FunctionParameterBoundaryStops (parameterTraceRewind input failed)) :
      NamedParameterTraceRejects source endByte input (parameterTraceRewind input failed) coreReport coreTrace
  | recovery {input failed rejected : Remainder} {coreReport report : ParseDiagnostic}
      {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : NamedParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ FunctionParameterBoundaryStops (parameterTraceRewind input failed))
      (recoveryRejected : FunctionParameterRecoveryTraceRejects source endByte
        (parameterTraceRewind input failed) rejected report recoveryTrace) :
      NamedParameterTraceRejects source endByte input rejected report ((coreTrace ++ [coreReport]) ++ recoveryTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterTraceGrammar
/-! Public lambda parameters reuse the exact cursor-only rewind and boundary
policy. Core events survive rewind; only a non-boundary path commits the core
report before lambda recovery. A recovery rejection has its own uncommitted
terminal report, even when its payload equals the already committed report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive LambdaParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | core {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
      (parsed : LambdaParameterCoreTraceParses source endByte input value output trace) :
      LambdaParameterTraceParses source endByte input value output trace
  | recovered {input failed output : Remainder} {value : Syntax.LambdaParameter}
      {coreReport : ParseDiagnostic} {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : LambdaParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ FunctionParameterBoundaryStops (parameterTraceRewind input failed))
      (recovered : LambdaParameterRecoveryTraceParses source endByte
        (parameterTraceRewind input failed) value output recoveryTrace) :
      LambdaParameterTraceParses source endByte input value output ((coreTrace ++ [coreReport]) ++ recoveryTrace)

inductive LambdaParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | boundary {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
      (coreRejected : LambdaParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (stops : FunctionParameterBoundaryStops (parameterTraceRewind input failed)) :
      LambdaParameterTraceRejects source endByte input (parameterTraceRewind input failed) coreReport coreTrace
  | recovery {input failed rejected : Remainder} {coreReport report : ParseDiagnostic}
      {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : LambdaParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ FunctionParameterBoundaryStops (parameterTraceRewind input failed))
      (recoveryRejected : LambdaParameterRecoveryTraceRejects source endByte
        (parameterTraceRewind input failed) rejected report recoveryTrace) :
      LambdaParameterTraceRejects source endByte input rejected report ((coreTrace ++ [coreReport]) ++ recoveryTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParameterListTraceGrammar
/-! Parenthesized parameter lists allow empty lists and a trailing comma.
Their child traces include public parameter recovery and any committed reports.
These aliases describe the lists only, not signatures or lambda expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev FunctionParametersTraceParses :=
  TrailingDelimitedListTraceParses .leftParen .rightParen true NamedParameterTraceParses

abbrev FunctionParametersTraceRejects :=
  TrailingDelimitedListTraceRejects .leftParen .rightParen true .parameter
    NamedParameterTraceParses NamedParameterTraceRejects

abbrev LambdaParametersTraceParses :=
  TrailingDelimitedListTraceParses .leftParen .rightParen true LambdaParameterTraceParses

abbrev LambdaParametersTraceRejects :=
  TrailingDelimitedListTraceRejects .leftParen .rightParen true .parameter
    LambdaParameterTraceParses LambdaParameterTraceRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypedParameterFinishingTraceProperties
/-! Parameter finishing always has exactly one complete trace, including the
empty trace on allowed types. Constraint events are protected independently
of source validity and lexical errors at the same locations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem typedParameterFinishingTrace_exists (type : Syntax.TypeExpr) :
    ∃ trace, TypedParameterFinishingTrace type trace := by
  by_cases allowed : ParameterTypeAllowed type
  · exact ⟨[], .ordinary allowed⟩
  · exact ⟨_, .comptime allowed⟩

theorem TypedParameterFinishingTrace.trace_unique {type : Syntax.TypeExpr}
    {left right : List ParseDiagnostic}
    (leftTrace : TypedParameterFinishingTrace type left)
    (rightTrace : TypedParameterFinishingTrace type right) : left = right := by
  cases leftTrace <;> cases rightTrace <;> first | rfl | contradiction

theorem TypedParameterFinishingTrace.nil_iff {type : Syntax.TypeExpr} :
    TypedParameterFinishingTrace type [] ↔ ParameterTypeAllowed type := by
  constructor
  · intro trace; cases trace with | ordinary allowed => exact allowed
  · exact .ordinary

theorem TypedParameterFinishingTrace.comptime_iff {type : Syntax.TypeExpr} :
    TypedParameterFinishingTrace type [{
      span := type.span, kind := .constraintViolation .comptimeTypeInParameter
    }] ↔ ¬ ParameterTypeAllowed type := by
  constructor
  · intro trace; cases trace with | comptime forbidden => exact forbidden
  · exact .comptime

theorem TypedParameterFinishingTrace.cascadeFilters {type : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (events : TypedParameterFinishingTrace type trace) (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases events with
  | ordinary => exact .nil
  | comptime => exact parseDiagnosticCascadeFilters_protected_cons (by simp [LexicalCascadeCandidate]) .nil

theorem errorParameterFinishingTrace_exists (span : SourceSpan) (constraint : ParseConstraint) :
    ∃ trace, ErrorParameterFinishingTrace span constraint trace := ⟨_, .emitted⟩

theorem ErrorParameterFinishingTrace.trace_eq {span : SourceSpan} {constraint : ParseConstraint}
    {trace : List ParseDiagnostic} (events : ErrorParameterFinishingTrace span constraint trace) :
    trace = [{ span, kind := .constraintViolation constraint }] := by cases events; rfl

theorem ErrorParameterFinishingTrace.trace_unique {span : SourceSpan} {constraint : ParseConstraint}
    {left right : List ParseDiagnostic}
    (leftTrace : ErrorParameterFinishingTrace span constraint left)
    (rightTrace : ErrorParameterFinishingTrace span constraint right) : left = right :=
  leftTrace.trace_eq.trans rightTrace.trace_eq.symm

theorem ErrorParameterFinishingTrace.cascadeFilters {span : SourceSpan} {constraint : ParseConstraint}
    {trace : List ParseDiagnostic} (events : ErrorParameterFinishingTrace span constraint trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases events
  exact parseDiagnosticCascadeFilters_protected_cons (by simp [LexicalCascadeCandidate]) .nil

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedParameterTailTraceProperties
/-! Named-parameter tail traces have exact outcomes and protected ordered
events. Complete recursive type laws discharge child premises unconditionally;
colon guards distinguish the error-valued success from typed success/failure.
The joint bundle is exactness, not a separate outcome-existence assertion. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {start errorSpan : SourceSpan} {marker : Option SourceSpan} {name : Syntax.Identifier}
  {source : SourceId} {endByte : Nat}

theorem NamedParameterTailTraceParses.output_window
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : NamedParameterTailTraceParses start marker name errorSpan source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | typed _ colon typed _ =>
      rcases colon with ⟨_, rfl⟩
      exact typed.output_window
  | typeMissing => exact ⟨rfl, rfl⟩

theorem NamedParameterTailTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedParameterTailTraceParses start marker name errorSpan source endByte input left afterLeft leftTrace)
    (rightParsed : NamedParameterTailTraceParses start marker name errorSpan source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | typed span colon typed finished =>
      cases rightParsed with
      | typeMissing absent _ => exact False.elim (absent ⟨span, colon.1⟩)
      | typed _ otherColon otherTyped otherFinished =>
          rcases colon.result_unique otherColon with ⟨rfl, rfl⟩
          rcases typed.result_unique otherTyped with ⟨rfl, rfl, rfl⟩
          cases finished.trace_unique otherFinished
          exact ⟨rfl, rfl, rfl⟩
  | typeMissing absent finished =>
      cases rightParsed with
      | typed span colon _ _ => exact False.elim (absent ⟨span, colon.1⟩)
      | typeMissing _ otherFinished => exact ⟨rfl, rfl, finished.trace_unique otherFinished⟩

theorem NamedParameterTailTraceRejects.colon_present
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTailTraceRejects start marker name errorSpan source endByte input rejected report trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .colon } := by
  cases rejection with
  | typeRejected span colon _ => exact ⟨span, colon.1⟩

theorem NamedParameterTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : NamedParameterTailTraceRejects start marker name errorSpan source endByte
      input afterLeft leftReport leftTrace)
    (rightRejected : NamedParameterTailTraceRejects start marker name errorSpan source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | typeRejected _ colon rejected =>
      cases rightRejected with
      | typeRejected _ otherColon otherRejected =>
          rcases colon.result_unique otherColon with ⟨rfl, rfl⟩
          exact rejected.result_unique otherRejected

theorem NamedParameterTailTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTailTraceRejects start marker name errorSpan source endByte input rejected report trace) :
    ¬ ∃ value output events, NamedParameterTailTraceParses start marker name errorSpan source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | typeRejected span colon rejected =>
      cases parsed with
      | typeMissing absent _ => exact absent ⟨span, colon.1⟩
      | typed _ otherColon typed _ =>
          rcases colon.result_unique otherColon with ⟨rfl, rfl⟩
          exact rejected.disjoint_success ⟨_, _, _, typed⟩

theorem NamedParameterTailTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : NamedParameterTailTraceParses start marker name errorSpan source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | typed _ _ typed finished => exact (typed.cascadeFilters text lexical).append (finished.cascadeFilters text lexical)
  | typeMissing _ finished => exact finished.cascadeFilters text lexical

theorem NamedParameterTailTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTailTraceRejects start marker name errorSpan source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | typeRejected _ _ rejected => exact rejected.cascadeFilters text lexical

theorem namedParameterTailTraceExactOutcomeSpec (start : SourceSpan) (marker : Option SourceSpan)
    (name : Syntax.Identifier) (errorSpan : SourceSpan) {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec (NamedParameterTailTraceParses start marker name errorSpan)
      (NamedParameterTailTraceRejects start marker name errorSpan) source endByte where
  successResultUnique := NamedParameterTailTraceParses.result_unique
  rejectResultUnique := NamedParameterTailTraceRejects.result_unique
  successRejectDisjoint := NamedParameterTailTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterTailTraceProperties
/-! Exact lambda-tail outcomes retain the named-tail carrier and ordered
protected events. Colon guards separate inference/missing-type success from
typed success or rejection, independently of executable state or validity. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat} {name : Syntax.Identifier} {marker : SourceSpan}

theorem OrdinaryLambdaParameterTailTraceParses.output_window
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : OrdinaryLambdaParameterTailTraceParses name source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | typed _ tail => exact tail.output_window
  | inferred => exact ⟨rfl, rfl⟩

theorem OrdinaryLambdaParameterTailTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OrdinaryLambdaParameterTailTraceParses name source endByte input left afterLeft leftTrace)
    (rightParsed : OrdinaryLambdaParameterTailTraceParses name source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | typed present tail =>
      cases rightParsed with
      | inferred absent => exact False.elim (absent present)
      | typed _ otherTail =>
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
  | inferred absent =>
      cases rightParsed with
      | typed present _ => exact False.elim (absent present)
      | inferred => exact ⟨rfl, rfl, rfl⟩

theorem OrdinaryLambdaParameterTailTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : OrdinaryLambdaParameterTailTraceParses name source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | typed _ tail => exact tail.cascadeFilters text lexical
  | inferred => exact .nil

theorem OrdinaryLambdaParameterTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : OrdinaryLambdaParameterTailTraceRejects name source endByte input afterLeft leftReport leftTrace)
    (rightRejected : OrdinaryLambdaParameterTailTraceRejects name source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  NamedParameterTailTraceRejects.result_unique leftRejected rightRejected

theorem OrdinaryLambdaParameterTailTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryLambdaParameterTailTraceRejects name source endByte input rejected report trace) :
    ¬ ∃ value output events, OrdinaryLambdaParameterTailTraceParses name source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | typed _ tail => exact NamedParameterTailTraceRejects.disjoint_success rejection ⟨_, _, _, tail⟩
  | inferred absent => exact absent rejection.colon_present

theorem OrdinaryLambdaParameterTailTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryLambdaParameterTailTraceRejects name source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace :=
  NamedParameterTailTraceRejects.cascadeFilters rejection text lexical

theorem ordinaryLambdaParameterTailTraceExactOutcomeSpec (name : Syntax.Identifier) :
    TraceExactOutcomeSpec (OrdinaryLambdaParameterTailTraceParses name)
      (OrdinaryLambdaParameterTailTraceRejects name) source endByte where
  successResultUnique := OrdinaryLambdaParameterTailTraceParses.result_unique
  rejectResultUnique := OrdinaryLambdaParameterTailTraceRejects.result_unique
  successRejectDisjoint := OrdinaryLambdaParameterTailTraceRejects.disjoint_success

theorem ComptimeLambdaParameterTailTraceParses.output_window
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeLambdaParameterTailTraceParses marker name source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | typed _ tail => exact tail.output_window
  | typeMissing => exact ⟨rfl, rfl⟩

theorem ComptimeLambdaParameterTailTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ComptimeLambdaParameterTailTraceParses marker name source endByte input left afterLeft leftTrace)
    (rightParsed : ComptimeLambdaParameterTailTraceParses marker name source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | typed present tail =>
      cases rightParsed with
      | typeMissing absent _ => exact False.elim (absent present)
      | typed _ otherTail =>
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
  | typeMissing absent finished =>
      cases rightParsed with
      | typed present _ => exact False.elim (absent present)
      | typeMissing _ otherFinished => exact ⟨rfl, rfl, finished.trace_unique otherFinished⟩

theorem ComptimeLambdaParameterTailTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeLambdaParameterTailTraceParses marker name source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | typed _ tail => exact tail.cascadeFilters text lexical
  | typeMissing _ finished => exact finished.cascadeFilters text lexical

theorem ComptimeLambdaParameterTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ComptimeLambdaParameterTailTraceRejects marker name source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ComptimeLambdaParameterTailTraceRejects marker name source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  NamedParameterTailTraceRejects.result_unique leftRejected rightRejected

theorem ComptimeLambdaParameterTailTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeLambdaParameterTailTraceRejects marker name source endByte input rejected report trace) :
    ¬ ∃ value output events, ComptimeLambdaParameterTailTraceParses marker name source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | typed _ tail => exact NamedParameterTailTraceRejects.disjoint_success rejection ⟨_, _, _, tail⟩
  | typeMissing absent _ => exact absent rejection.colon_present

theorem ComptimeLambdaParameterTailTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeLambdaParameterTailTraceRejects marker name source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace :=
  NamedParameterTailTraceRejects.cascadeFilters rejection text lexical

theorem comptimeLambdaParameterTailTraceExactOutcomeSpec (marker : SourceSpan) (name : Syntax.Identifier) :
    TraceExactOutcomeSpec (ComptimeLambdaParameterTailTraceParses marker name)
      (ComptimeLambdaParameterTailTraceRejects marker name) source endByte where
  successResultUnique := ComptimeLambdaParameterTailTraceParses.result_unique
  rejectResultUnique := ComptimeLambdaParameterTailTraceRejects.result_unique
  successRejectDisjoint := ComptimeLambdaParameterTailTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterRawTraceProperties
/-! Raw lambda-parameter successes retain their carrier, exact value, and
complete ordered events. Comptime marker names do not undergo the ordinary
parameter-name finishing check. Pair selection and recovery remain separate. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem OrdinaryLambdaParameterTraceParses.output_window
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : OrdinaryLambdaParameterTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed name tail =>
      exact ⟨tail.output_window.1.trans name.ordinary.2.1,
        tail.output_window.2.trans name.ordinary.2.2.1⟩

theorem OrdinaryLambdaParameterTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OrdinaryLambdaParameterTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : OrdinaryLambdaParameterTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed name tail =>
      cases rightParsed with
      | parsed otherName otherTail =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem OrdinaryLambdaParameterTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : OrdinaryLambdaParameterTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed name tail => exact (name.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem ComptimeLambdaParameterTraceParses.output_window
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeLambdaParameterTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed _ marker name tail =>
      rcases marker with ⟨_, rfl⟩
      have ordinary := (identifierTraceParses_iff.mp name).1
      exact ⟨tail.output_window.1.trans ordinary.2.1, tail.output_window.2.trans ordinary.2.2.1⟩

theorem ComptimeLambdaParameterTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ComptimeLambdaParameterTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : ComptimeLambdaParameterTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed _ marker name tail =>
      cases rightParsed with
      | parsed _ otherMarker otherName otherTail =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ComptimeLambdaParameterTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeLambdaParameterTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ name tail =>
      exact ((identifierTraceParses_iff.mp name).2.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterRawRejectionTraceProperties
/-! First-failure exactness for the two raw lambda-parameter forms. A marker failure
is raw comptime rejection, not a selected-core judgment. Name/tail events are
preserved in order, and terminal reports are not part of the emitted trace. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

private theorem checked_name_absent_conflict {input output : Remainder}
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (absent : IdentifierAbsentAt input) (parsed : CheckedParameterNameTraceParses input name output trace) : False :=
  absent ⟨name.span, name.value, parsed.ordinary.1⟩

private theorem identifier_absent_conflict {input output : Remainder}
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (absent : IdentifierAbsentAt input) (parsed : IdentifierTraceParses input name output trace) : False :=
  absent ⟨name.span, name.value, (identifierTraceParses_iff.mp parsed).1.1⟩

theorem OrdinaryLambdaParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : OrdinaryLambdaParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : OrdinaryLambdaParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | nameRejected absent reported =>
      cases rightRejected with
      | nameRejected _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | tailRejected name _ => exact False.elim (checked_name_absent_conflict absent name)
  | tailRejected name tail =>
      cases rightRejected with
      | nameRejected absent _ => exact False.elim (checked_name_absent_conflict absent name)
      | tailRejected otherName otherTail =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem OrdinaryLambdaParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryLambdaParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, OrdinaryLambdaParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed name tail =>
      cases rejection with
      | nameRejected absent _ => exact checked_name_absent_conflict absent name
      | tailRejected otherName otherTail =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          exact OrdinaryLambdaParameterTailTraceRejects.disjoint_success otherTail ⟨_, _, _, tail⟩

theorem OrdinaryLambdaParameterTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryLambdaParameterTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | nameRejected => exact .nil
  | tailRejected name tail => exact (name.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem ordinaryLambdaParameterTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec OrdinaryLambdaParameterTraceParses OrdinaryLambdaParameterTraceRejects source endByte where
  successResultUnique := OrdinaryLambdaParameterTraceParses.result_unique
  rejectResultUnique := OrdinaryLambdaParameterTraceRejects.result_unique
  successRejectDisjoint := OrdinaryLambdaParameterTraceRejects.disjoint_success

theorem ComptimeLambdaParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ComptimeLambdaParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ComptimeLambdaParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | markerMissing absent reported =>
      cases rightRejected with
      | markerMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | nameRejected span marker _ _ | tailRejected span marker _ _ => exact False.elim (absent ⟨span, marker.1⟩)
  | nameRejected span marker absent reported =>
      cases rightRejected with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | nameRejected _ otherMarker _ other =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | tailRejected _ otherMarker name _ =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact False.elim (identifier_absent_conflict absent name)
  | tailRejected span marker name tail =>
      cases rightRejected with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | nameRejected _ otherMarker absent _ =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact False.elim (identifier_absent_conflict absent name)
      | tailRejected _ otherMarker otherName otherTail =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ComptimeLambdaParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeLambdaParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ComptimeLambdaParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed span marker name tail =>
      cases rejection with
      | markerMissing absent _ => exact absent ⟨span, marker.1⟩
      | nameRejected _ otherMarker absent _ =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact identifier_absent_conflict absent name
      | tailRejected _ otherMarker otherName otherTail =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          exact ComptimeLambdaParameterTailTraceRejects.disjoint_success otherTail ⟨_, _, _, tail⟩

theorem ComptimeLambdaParameterTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeLambdaParameterTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing | nameRejected => exact .nil
  | tailRejected _ _ name tail =>
      exact ((identifierTraceParses_iff.mp name).2.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem comptimeLambdaParameterTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec ComptimeLambdaParameterTraceParses ComptimeLambdaParameterTraceRejects source endByte where
  successResultUnique := ComptimeLambdaParameterTraceParses.result_unique
  rejectResultUnique := ComptimeLambdaParameterTraceRejects.result_unique
  successRejectDisjoint := ComptimeLambdaParameterTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterCoreTraceProperties
/-! Pair selection preserves exact raw outcomes and protected event order.
Opposite branches cannot compete on one input. The joint specification states
uniqueness and disjointness, not existence of an execution or derivation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem LambdaParameterCoreTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : LambdaParameterCoreTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : LambdaParameterCoreTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | ordinary absent leftRaw =>
      cases rightParsed with
      | ordinary _ rightRaw => exact ordinaryLambdaParameterTraceExactOutcomeSpec.successResultUnique leftRaw rightRaw
      | comptime present _ => exact False.elim (absent present)
  | comptime present leftRaw =>
      cases rightParsed with
      | ordinary absent _ => exact False.elim (absent present)
      | comptime _ rightRaw => exact comptimeLambdaParameterTraceExactOutcomeSpec.successResultUnique leftRaw rightRaw

theorem LambdaParameterCoreTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : LambdaParameterCoreTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : LambdaParameterCoreTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | ordinary absent leftRaw =>
      cases rightRejected with
      | ordinary _ rightRaw => exact ordinaryLambdaParameterTraceExactOutcomeSpec.rejectResultUnique leftRaw rightRaw
      | comptime present _ => exact False.elim (absent present)
  | comptime present leftRaw =>
      cases rightRejected with
      | ordinary absent _ => exact False.elim (absent present)
      | comptime _ rightRaw => exact comptimeLambdaParameterTraceExactOutcomeSpec.rejectResultUnique leftRaw rightRaw

theorem LambdaParameterCoreTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterCoreTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, LambdaParameterCoreTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | ordinary absent rawRejected =>
      cases parsed with
      | ordinary _ rawParsed =>
          exact ordinaryLambdaParameterTraceExactOutcomeSpec.successRejectDisjoint rawRejected ⟨_, _, _, rawParsed⟩
      | comptime present _ => exact absent present
  | comptime present rawRejected =>
      cases parsed with
      | ordinary absent _ => exact absent present
      | comptime _ rawParsed =>
          exact comptimeLambdaParameterTraceExactOutcomeSpec.successRejectDisjoint rawRejected ⟨_, _, _, rawParsed⟩

theorem LambdaParameterCoreTraceParses.output_window
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterCoreTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | ordinary _ raw => exact raw.output_window
  | comptime _ raw => exact raw.output_window

theorem LambdaParameterCoreTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterCoreTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | ordinary _ raw => exact raw.cascadeFilters text lexical
  | comptime _ raw => exact raw.cascadeFilters text lexical

theorem LambdaParameterCoreTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterCoreTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | ordinary _ raw => exact raw.cascadeFilters text lexical
  | comptime _ raw => exact raw.cascadeFilters text lexical

theorem lambdaParameterCoreTraceExactOutcomeSpec :
    TraceExactOutcomeSpec LambdaParameterCoreTraceParses LambdaParameterCoreTraceRejects source endByte where
  successResultUnique := LambdaParameterCoreTraceParses.result_unique
  rejectResultUnique := LambdaParameterCoreTraceRejects.result_unique
  successRejectDisjoint := LambdaParameterCoreTraceRejects.disjoint_success

/-- A selected comptime rejection cannot fail at the marker or following name. -/
theorem ComptimeLambdaParameterTraceRejects.tail_of_prefix
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (present : ComptimeLambdaParameterStartsAt input)
    (rejection : ComptimeLambdaParameterTraceRejects source endByte input rejected report trace) :
    ∃ markerSpan afterMarker afterName name nameEvents tailEvents,
      ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker ∧
      IdentifierTraceParses afterMarker name afterName nameEvents ∧
      ComptimeLambdaParameterTailTraceRejects markerSpan name
        source endByte afterName rejected report tailEvents ∧ trace = nameEvents ++ tailEvents := by
  rcases present with ⟨selectedMarker, selectedName, spelling, markerToken, nameToken⟩
  cases rejection with
  | markerMissing absent _ => exact False.elim (absent ⟨selectedMarker, markerToken⟩)
  | nameRejected markerSpan marker absent _ =>
      rcases marker with ⟨_, rfl⟩
      exact False.elim (absent ⟨selectedName, spelling, nameToken⟩)
  | tailRejected markerSpan marker nameParsed tail => exact ⟨_, _, _, _, _, _, marker, nameParsed, tail, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLambdaParameterTraceProperties
/-! Public lambda exactness compares the selected core and then the actual
rewound recovery remainder. Carrier preservation is not substituted implicitly.
The joint specification is uniqueness/disjointness, not existence. Core events
are protected, while committed reports and recovery events are filtered explicitly. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem LambdaParameterTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : LambdaParameterTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : LambdaParameterTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact leftCore.result_unique rightCore
      | recovered rejected _ _ => exact False.elim (rejected.disjoint_success ⟨_, _, _, leftCore⟩)
  | recovered leftCore _ leftRecovery =>
      cases rightParsed with
      | core rightCore => exact False.elim (leftCore.disjoint_success ⟨_, _, _, rightCore⟩)
      | recovered rightCore _ rightRecovery =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LambdaParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : LambdaParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : LambdaParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | boundary leftCore stops =>
      cases rightRejected with
      | boundary rightCore _ =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | recovery rightCore continues _ =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
  | recovery leftCore continues leftRecovery =>
      cases rightRejected with
      | boundary rightCore stops =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
      | recovery rightCore _ rightRecovery =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          rcases LambdaParameterRecoveryTraceRejects.result_unique leftRecovery rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LambdaParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, LambdaParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | boundary rejectedCore stops =>
      cases parsed with
      | core parsedCore => exact rejectedCore.disjoint_success ⟨_, _, _, parsedCore⟩
      | recovered otherCore continues _ =>
          rcases rejectedCore.result_unique otherCore with ⟨rfl, rfl, rfl⟩
          exact continues stops
  | recovery rejectedCore _ rejectedRecovery =>
      cases parsed with
      | core parsedCore => exact rejectedCore.disjoint_success ⟨_, _, _, parsedCore⟩
      | recovered otherCore _ parsedRecovery =>
          rcases rejectedCore.result_unique otherCore with ⟨rfl, rfl, rfl⟩
          exact LambdaParameterRecoveryTraceRejects.disjoint_success rejectedRecovery ⟨_, _, _, parsedRecovery⟩

theorem lambdaParameterTraceExactOutcomeSpec :
    TraceExactOutcomeSpec LambdaParameterTraceParses LambdaParameterTraceRejects source endByte where
  successResultUnique := LambdaParameterTraceParses.result_unique
  rejectResultUnique := LambdaParameterTraceRejects.result_unique
  successRejectDisjoint := LambdaParameterTraceRejects.disjoint_success

/-- The protected core prefix is preserved, but both cascade-candidate suffixes
need their own explicit filters. Their order and multiplicity are unchanged. -/
theorem lambdaParameterRecoveryTrace_cascadeFilters
    {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
    (coreRejected : LambdaParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
    (text : String) (lexical : List SourceSpan)
    {recoveryTrace keptReport keptRecovery : List ParseDiagnostic}
    (reportFiltered : ParseDiagnosticCascadeFilters text lexical [coreReport] keptReport)
    (recoveryFiltered : ParseDiagnosticCascadeFilters text lexical recoveryTrace keptRecovery) :
    ParseDiagnosticCascadeFilters text lexical ((coreTrace ++ [coreReport]) ++ recoveryTrace)
      ((coreTrace ++ keptReport) ++ keptRecovery) :=
  ((coreRejected.cascadeFilters text lexical).append reportFiltered).append recoveryFiltered

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedParameterRawTraceProperties
/-! Raw named-parameter successes retain their carrier, exact value, and
complete ordered events. Comptime marker names do not undergo the ordinary
parameter-name finishing check. Pair selection and recovery remain separate. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem OrdinaryNamedParameterTraceParses.output_window
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : OrdinaryNamedParameterTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed name tail =>
      exact ⟨tail.output_window.1.trans name.ordinary.2.1,
        tail.output_window.2.trans name.ordinary.2.2.1⟩

theorem OrdinaryNamedParameterTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OrdinaryNamedParameterTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : OrdinaryNamedParameterTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed name tail =>
      cases rightParsed with
      | parsed otherName otherTail =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem OrdinaryNamedParameterTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : OrdinaryNamedParameterTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed name tail => exact (name.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem ComptimeNamedParameterTraceParses.output_window
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeNamedParameterTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed _ marker name tail =>
      rcases marker with ⟨_, rfl⟩
      have ordinary := (identifierTraceParses_iff.mp name).1
      exact ⟨tail.output_window.1.trans ordinary.2.1, tail.output_window.2.trans ordinary.2.2.1⟩

theorem ComptimeNamedParameterTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ComptimeNamedParameterTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : ComptimeNamedParameterTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed _ marker name tail =>
      cases rightParsed with
      | parsed _ otherMarker otherName otherTail =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ComptimeNamedParameterTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeNamedParameterTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ name tail =>
      exact ((identifierTraceParses_iff.mp name).2.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedParameterRawRejectionTraceProperties
/-! First-failure exactness for the two raw parameter forms. A marker failure
is raw comptime rejection, not a selected-core judgment. Name/tail events are
preserved in order, and terminal reports are not part of the emitted trace. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem OrdinaryNamedParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : OrdinaryNamedParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : OrdinaryNamedParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | nameRejected absent reported =>
      cases rightRejected with
      | nameRejected _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | tailRejected name _ => exact False.elim (checked_name_absent_conflict absent name)
  | tailRejected name tail =>
      cases rightRejected with
      | nameRejected absent _ => exact False.elim (checked_name_absent_conflict absent name)
      | tailRejected otherName otherTail =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem OrdinaryNamedParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryNamedParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, OrdinaryNamedParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed name tail =>
      cases rejection with
      | nameRejected absent _ => exact checked_name_absent_conflict absent name
      | tailRejected otherName otherTail =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          exact otherTail.disjoint_success ⟨_, _, _, tail⟩

theorem OrdinaryNamedParameterTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryNamedParameterTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | nameRejected => exact .nil
  | tailRejected name tail => exact (name.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem ordinaryNamedParameterTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec OrdinaryNamedParameterTraceParses OrdinaryNamedParameterTraceRejects source endByte where
  successResultUnique := OrdinaryNamedParameterTraceParses.result_unique
  rejectResultUnique := OrdinaryNamedParameterTraceRejects.result_unique
  successRejectDisjoint := OrdinaryNamedParameterTraceRejects.disjoint_success

theorem ComptimeNamedParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ComptimeNamedParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ComptimeNamedParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | markerMissing absent reported =>
      cases rightRejected with
      | markerMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | nameRejected span marker _ _ | tailRejected span marker _ _ => exact False.elim (absent ⟨span, marker.1⟩)
  | nameRejected span marker absent reported =>
      cases rightRejected with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | nameRejected _ otherMarker _ other =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | tailRejected _ otherMarker name _ =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact False.elim (identifier_absent_conflict absent name)
  | tailRejected span marker name tail =>
      cases rightRejected with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | nameRejected _ otherMarker absent _ =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact False.elim (identifier_absent_conflict absent name)
      | tailRejected _ otherMarker otherName otherTail =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ComptimeNamedParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeNamedParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ComptimeNamedParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed span marker name tail =>
      cases rejection with
      | markerMissing absent _ => exact absent ⟨span, marker.1⟩
      | nameRejected _ otherMarker absent _ =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact identifier_absent_conflict absent name
      | tailRejected _ otherMarker otherName otherTail =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          exact otherTail.disjoint_success ⟨_, _, _, tail⟩

theorem ComptimeNamedParameterTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeNamedParameterTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing | nameRejected => exact .nil
  | tailRejected _ _ name tail =>
      exact ((identifierTraceParses_iff.mp name).2.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem comptimeNamedParameterTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec ComptimeNamedParameterTraceParses ComptimeNamedParameterTraceRejects source endByte where
  successResultUnique := ComptimeNamedParameterTraceParses.result_unique
  rejectResultUnique := ComptimeNamedParameterTraceRejects.result_unique
  successRejectDisjoint := ComptimeNamedParameterTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedParameterCoreTraceProperties
/-! Pair selection preserves exact raw outcomes and protected event order.
Opposite branches cannot compete on one input. The joint specification states
uniqueness and disjointness, not existence of an execution or derivation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem NamedParameterCoreTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedParameterCoreTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : NamedParameterCoreTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | ordinary absent leftRaw =>
      cases rightParsed with
      | ordinary _ rightRaw => exact ordinaryNamedParameterTraceExactOutcomeSpec.successResultUnique leftRaw rightRaw
      | comptime present _ => exact False.elim (absent present)
  | comptime present leftRaw =>
      cases rightParsed with
      | ordinary absent _ => exact False.elim (absent present)
      | comptime _ rightRaw => exact comptimeNamedParameterTraceExactOutcomeSpec.successResultUnique leftRaw rightRaw

theorem NamedParameterCoreTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : NamedParameterCoreTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : NamedParameterCoreTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | ordinary absent leftRaw =>
      cases rightRejected with
      | ordinary _ rightRaw => exact ordinaryNamedParameterTraceExactOutcomeSpec.rejectResultUnique leftRaw rightRaw
      | comptime present _ => exact False.elim (absent present)
  | comptime present leftRaw =>
      cases rightRejected with
      | ordinary absent _ => exact False.elim (absent present)
      | comptime _ rightRaw => exact comptimeNamedParameterTraceExactOutcomeSpec.rejectResultUnique leftRaw rightRaw

theorem NamedParameterCoreTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterCoreTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, NamedParameterCoreTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | ordinary absent rawRejected =>
      cases parsed with
      | ordinary _ rawParsed =>
          exact ordinaryNamedParameterTraceExactOutcomeSpec.successRejectDisjoint rawRejected ⟨_, _, _, rawParsed⟩
      | comptime present _ => exact absent present
  | comptime present rawRejected =>
      cases parsed with
      | ordinary absent _ => exact absent present
      | comptime _ rawParsed =>
          exact comptimeNamedParameterTraceExactOutcomeSpec.successRejectDisjoint rawRejected ⟨_, _, _, rawParsed⟩

theorem NamedParameterCoreTraceParses.output_window
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : NamedParameterCoreTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | ordinary _ raw => exact raw.output_window
  | comptime _ raw => exact raw.output_window

theorem NamedParameterCoreTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : NamedParameterCoreTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | ordinary _ raw => exact raw.cascadeFilters text lexical
  | comptime _ raw => exact raw.cascadeFilters text lexical

theorem NamedParameterCoreTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterCoreTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | ordinary _ raw => exact raw.cascadeFilters text lexical
  | comptime _ raw => exact raw.cascadeFilters text lexical

theorem namedParameterCoreTraceExactOutcomeSpec :
    TraceExactOutcomeSpec NamedParameterCoreTraceParses NamedParameterCoreTraceRejects source endByte where
  successResultUnique := NamedParameterCoreTraceParses.result_unique
  rejectResultUnique := NamedParameterCoreTraceRejects.result_unique
  successRejectDisjoint := NamedParameterCoreTraceRejects.disjoint_success

/-- A selected comptime rejection cannot fail at the marker or following name. -/
theorem ComptimeNamedParameterTraceRejects.tail_of_prefix
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (present : ComptimeLambdaParameterStartsAt input)
    (rejection : ComptimeNamedParameterTraceRejects source endByte input rejected report trace) :
    ∃ markerSpan afterMarker afterName name nameEvents tailEvents,
      ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker ∧
      IdentifierTraceParses afterMarker name afterName nameEvents ∧
      NamedParameterTailTraceRejects markerSpan (some markerSpan) name (SourceSpan.cover markerSpan name.span)
        source endByte afterName rejected report tailEvents ∧ trace = nameEvents ++ tailEvents := by
  rcases present with ⟨selectedMarker, selectedName, spelling, markerToken, nameToken⟩
  cases rejection with
  | markerMissing absent _ => exact False.elim (absent ⟨selectedMarker, markerToken⟩)
  | nameRejected markerSpan marker absent _ =>
      rcases marker with ⟨_, rfl⟩
      exact False.elim (absent ⟨selectedName, spelling, nameToken⟩)
  | tailRejected markerSpan marker nameParsed tail => exact ⟨_, _, _, _, _, _, marker, nameParsed, tail, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedParameterTraceProperties
/-! Public exactness compares the core first, then the boundary or standalone
recovery. No carrier frame is silently substituted for the actual rewind.
Committed unexpected reports and recovered events may be cascade-suppressed,
so only explicit component filtering is composed for mixed recovery traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem parameterTraceRewind_fields (input failed : Remainder) :
    (parameterTraceRewind input failed).tokens = failed.tokens ∧
    (parameterTraceRewind input failed).endIndex = failed.endIndex ∧
    (parameterTraceRewind input failed).cursor = input.cursor := ⟨rfl, rfl, rfl⟩

theorem parameterTraceRewind_eq_input_of_carrier {input failed : Remainder}
    (tokens : failed.tokens = input.tokens) (endIndex : failed.endIndex = input.endIndex) :
    parameterTraceRewind input failed = input := by
  cases input
  simp only [parameterTraceRewind, tokens, endIndex]

theorem NamedParameterTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedParameterTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : NamedParameterTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact leftCore.result_unique rightCore
      | recovered rejected _ _ => exact False.elim (rejected.disjoint_success ⟨_, _, _, leftCore⟩)
  | recovered leftCore _ leftRecovery =>
      cases rightParsed with
      | core rightCore => exact False.elim (leftCore.disjoint_success ⟨_, _, _, rightCore⟩)
      | recovered rightCore _ rightRecovery =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem NamedParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : NamedParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : NamedParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | boundary leftCore stops =>
      cases rightRejected with
      | boundary rightCore _ =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | recovery rightCore continues _ =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
  | recovery leftCore continues leftRecovery =>
      cases rightRejected with
      | boundary rightCore stops =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
      | recovery rightCore _ rightRecovery =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem NamedParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, NamedParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | boundary rejectedCore stops =>
      cases parsed with
      | core parsedCore => exact rejectedCore.disjoint_success ⟨_, _, _, parsedCore⟩
      | recovered otherCore continues _ =>
          rcases rejectedCore.result_unique otherCore with ⟨rfl, rfl, rfl⟩
          exact continues stops
  | recovery rejectedCore _ rejectedRecovery =>
      cases parsed with
      | core parsedCore => exact rejectedCore.disjoint_success ⟨_, _, _, parsedCore⟩
      | recovered otherCore _ parsedRecovery =>
          rcases rejectedCore.result_unique otherCore with ⟨rfl, rfl, rfl⟩
          exact rejectedRecovery.disjoint_success ⟨_, _, _, parsedRecovery⟩

theorem namedParameterTraceExactOutcomeSpec :
    TraceExactOutcomeSpec NamedParameterTraceParses NamedParameterTraceRejects source endByte where
  successResultUnique := NamedParameterTraceParses.result_unique
  rejectResultUnique := NamedParameterTraceRejects.result_unique
  successRejectDisjoint := NamedParameterTraceRejects.disjoint_success

/-- Inside the non-boundary branch, a failed mandatory recovery token is
necessarily absent from the backing carrier. The new report is not emitted. -/
theorem functionParameterRecoveryTraceRejects_missingToken_of_nonboundary
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (continues : ¬ FunctionParameterBoundaryStops input)
    (rejection : FunctionParameterRecoveryTraceRejects source endByte input rejected report trace) :
    rejected = input ∧ input.cursor < input.endIndex ∧ input.tokens[input.cursor]? = none ∧ trace = [] := by
  rcases rejection with ⟨recovery, _, traceEq⟩
  cases recovery with
  | windowEnd ended => exact False.elim (continues (.windowEnd ended))
  | missingToken inside missing => exact ⟨rfl, inside, missing, traceEq⟩

/-- The core suffix is protected, but the committed report and subsequent
recovery events are filtered explicitly, preserving order and multiplicity. -/
theorem namedParameterRecoveryTrace_cascadeFilters
    {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
    (coreRejected : NamedParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
    (text : String) (lexical : List SourceSpan)
    {recoveryTrace keptReport keptRecovery : List ParseDiagnostic}
    (reportFiltered : ParseDiagnosticCascadeFilters text lexical [coreReport] keptReport)
    (recoveryFiltered : ParseDiagnosticCascadeFilters text lexical recoveryTrace keptRecovery) :
    ParseDiagnosticCascadeFilters text lexical ((coreTrace ++ [coreReport]) ++ recoveryTrace)
      ((coreTrace ++ keptReport) ++ keptRecovery) :=
  ((coreRejected.cascadeFilters text lexical).append reportFiltered).append recoveryFiltered

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParameterListTraceProperties
/-! Exactness lifts from the public parameter outcomes. No child existence or
carrier premise is needed. Recovered events and committed terminal reports are
not asserted to be unconditionally protected against lexical suppression. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem functionParametersTraceExactOutcomeSpec :
    TraceExactOutcomeSpec FunctionParametersTraceParses FunctionParametersTraceRejects source endByte :=
  (trailingDelimitedListTraceOutcomeAgreement (opening := .leftParen) (closing := .rightParen)
    (allowEmpty := true) (context := .parameter)
    namedParameterTraceExactOutcomeSpec.toTraceOutcomeAgreement).toTraceExactOutcomeSpec

theorem lambdaParametersTraceExactOutcomeSpec :
    TraceExactOutcomeSpec LambdaParametersTraceParses LambdaParametersTraceRejects source endByte :=
  (trailingDelimitedListTraceOutcomeAgreement (opening := .leftParen) (closing := .rightParen)
    (allowEmpty := true) (context := .parameter)
    lambdaParameterTraceExactOutcomeSpec.toTraceOutcomeAgreement).toTraceExactOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
end
