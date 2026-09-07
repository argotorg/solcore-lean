import Solcore.Syntax.DeclarativeIdentifierCascadeProperties

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
