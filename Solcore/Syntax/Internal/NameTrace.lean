import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.DeclarativeLiteralDiagnosticTraceGrammar
import Solcore.Syntax.DeclarativeCoreIdentifierExpressionOutcomeGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeLiteralDiagnosticTraceProperties
import Solcore.Syntax.Internal.TraceBasics

/-!
Exact diagnostic traces of identifiers and expression names, with the
cascade laws of a checked identifier.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeIdentifierTraceGrammar
/-! Independent spelling and diagnostic traces for one identifier token. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A written identifier contains the ASCII hyphen character. -/
def IdentifierHyphenSpelling (text : String) : Prop :=
  '-' ∈ text.toList

/-- Checked identifiers emit one located spelling diagnostic exactly when
their written name contains a hyphen, regardless of its multiplicity. -/
inductive IdentifierDiagnosticTrace (name : Syntax.Identifier) :
    List ParseDiagnostic → Prop where
  | clean (absent : ¬ IdentifierHyphenSpelling name.value) :
      IdentifierDiagnosticTrace name []
  | hyphen (present : IdentifierHyphenSpelling name.value) :
      IdentifierDiagnosticTrace name
        [{ span := name.span, kind := .invalidIdentifierHyphen name.value }]

/-- Raw identifier success retains its exact token and emits no event. -/
inductive RawIdentifierTraceParses :
    Remainder → Syntax.Identifier → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier}
      (ordinary : IdentifierParses input name output) :
      RawIdentifierTraceParses input name output []

/-- Checked identifier success pairs the existing token grammar with its
independent spelling trace, in emission order after all earlier diagnostics. -/
inductive IdentifierTraceParses :
    Remainder → Syntax.Identifier → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier}
      {trace : List ParseDiagnostic}
      (ordinary : IdentifierParses input name output)
      (diagnostics : IdentifierDiagnosticTrace name trace) :
      IdentifierTraceParses input name output trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionNameTraceGrammar
/-! Independent Boolean-first names and identifier-expression traces. Checked
ordinary names retain their complete located spelling diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionNameTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Identifier → Remainder → List ParseDiagnostic → Prop where
  | boolean {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
      (parsed : BooleanIdentifierTraceParses source endByte input name output trace) :
      ExpressionNameTraceParses source endByte input name output trace
  | identifier {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
      (booleanAbsent : BooleanPatternAbsentAt input)
      (parsed : IdentifierTraceParses input name output trace) :
      ExpressionNameTraceParses source endByte input name output trace

/-- Rejection occurs only after both Boolean guards fail. Identifier failure
is uncommitted and does not emit a checked-spelling event. -/
def ExpressionNameTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  BooleanPatternAbsentAt input ∧ IdentifierRejects input rejected ∧
    RejectAtReports source endByte { head := .identifier, tail := [] }
      .expression rejected diagnostic ∧ trace = []

inductive IdentifierExpressionTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
      (nameParsed : ExpressionNameTraceParses source endByte input name output trace) :
      IdentifierExpressionTraceParses source endByte input {
        span := name.span, value := .identifier name
      } output trace

abbrev IdentifierExpressionTraceRejects := ExpressionNameTraceRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeIdentifierTraceProperties
/-! Exact identifier values, endpoints, and spelling-dependent event sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Character membership agrees with the executable spelling test. -/
theorem identifierHyphenSpelling_iff_contains (text : String) :
    IdentifierHyphenSpelling text ↔ text.toList.contains '-' = true := by
  simp [IdentifierHyphenSpelling]

/-- Every identifier spelling selects one complete diagnostic sequence. -/
theorem identifierDiagnosticTrace_total (name : Syntax.Identifier) :
    ∃ trace, IdentifierDiagnosticTrace name trace := by
  by_cases hyphen : IdentifierHyphenSpelling name.value
  · exact ⟨_, .hyphen hyphen⟩
  · exact ⟨_, .clean hyphen⟩

/-- The spelling determines the complete diagnostic sequence uniquely. -/
theorem IdentifierDiagnosticTrace.trace_unique {name : Syntax.Identifier}
    {left right : List ParseDiagnostic}
    (leftTrace : IdentifierDiagnosticTrace name left)
    (rightTrace : IdentifierDiagnosticTrace name right) : left = right := by
  cases leftTrace <;> cases rightTrace <;> first | rfl | contradiction

/-- Raw trace erasure preserves the existing token grammar and empty trace. -/
theorem rawIdentifierTraceParses_iff
    {input output : Remainder} {name : Syntax.Identifier}
    {trace : List ParseDiagnostic} :
    RawIdentifierTraceParses input name output trace ↔
      IdentifierParses input name output ∧ trace = [] := by
  constructor
  · intro parsed
    cases parsed with
    | parsed ordinary => exact ⟨ordinary, rfl⟩
  · rintro ⟨ordinary, rfl⟩
    exact .parsed ordinary

/-- Checked trace erasure preserves both token and spelling evidence. -/
theorem identifierTraceParses_iff
    {input output : Remainder} {name : Syntax.Identifier}
    {trace : List ParseDiagnostic} :
    IdentifierTraceParses input name output trace ↔
      IdentifierParses input name output ∧ IdentifierDiagnosticTrace name trace := by
  constructor
  · intro parsed
    cases parsed with
    | parsed ordinary diagnostics => exact ⟨ordinary, diagnostics⟩
  · rintro ⟨ordinary, diagnostics⟩
    exact .parsed ordinary diagnostics

/-- A raw token derivation fixes its full AST, remainder, and trace. -/
theorem RawIdentifierTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : RawIdentifierTraceParses input left afterLeft leftTrace)
    (rightParsed : RawIdentifierTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftOrdinary =>
      cases rightParsed with
      | parsed rightOrdinary =>
          rcases leftOrdinary.result_unique rightOrdinary with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

/-- Checked identifiers also fix every located diagnostic event exactly. -/
theorem IdentifierTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : IdentifierTraceParses input left afterLeft leftTrace)
    (rightParsed : IdentifierTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftOrdinary leftDiagnostics =>
      cases rightParsed with
      | parsed rightOrdinary rightDiagnostics =>
          rcases leftOrdinary.result_unique rightOrdinary with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, leftDiagnostics.trace_unique rightDiagnostics⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionNameTraceProperties
/-! Independent exactness, ordinary erasure, and total Boolean-first name traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem ExpressionNameTraceParses.ordinary
    {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : ExpressionNameTraceParses source endByte input name output trace) :
    ExpressionNameParses input name output := by
  cases parsed with
  | boolean parsed => exact .boolean parsed.1
  | identifier absent parsed => exact .identifier absent.1 absent.2 (identifierTraceParses_iff.mp parsed).1

theorem ExpressionNameTraceParses.output_eq
    {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : ExpressionNameTraceParses source endByte input name output trace) :
    output = { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | boolean parsed => cases parsed.1 <;> rfl
  | identifier _ parsed =>
      have ordinary := (identifierTraceParses_iff.mp parsed).1
      rcases output with ⟨tokens, endIndex, cursor⟩
      rcases ordinary.2 with ⟨rfl, rfl, rfl⟩
      rfl

theorem ExpressionNameTraceRejects.ordinary
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : ExpressionNameTraceRejects source endByte input rejected diagnostic trace) :
    ExpressionNameRejects input rejected := by
  rcases traced with ⟨booleanAbsent, identifierRejected, _, _⟩
  cases identifierRejected with
  | absent nameAbsent => exact .absent ⟨booleanAbsent.1, booleanAbsent.2, nameAbsent⟩

theorem ExpressionNameTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionNameTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionNameTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | boolean left =>
      cases rightParsed with
      | boolean right => exact left.result_unique right
      | identifier absent _ =>
          cases left.1 with
          | trueKeyword token => exact False.elim (absent.1 ⟨_, token⟩)
          | falseKeyword token => exact False.elim (absent.2 ⟨_, token⟩)
  | identifier absent left =>
      cases rightParsed with
      | identifier _ right => exact left.result_unique right
      | boolean right =>
          cases right.1 with
          | trueKeyword token => exact False.elim (absent.1 ⟨_, token⟩)
          | falseKeyword token => exact False.elim (absent.2 ⟨_, token⟩)

theorem ExpressionNameTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ExpressionNameTraceRejects source endByte input afterLeft left leftTrace)
    (rightRejected : ExpressionNameTraceRejects source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  rcases leftRejected with ⟨_, leftOrdinary, leftReport, leftEvents⟩
  rcases rightRejected with ⟨_, rightOrdinary, rightReport, rightEvents⟩
  cases leftOrdinary
  cases rightOrdinary
  exact ⟨rfl, leftReport.diagnostic_unique rightReport, leftEvents.trans rightEvents.symm⟩

theorem ExpressionNameTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {name : Syntax.Identifier}
    {rejectTrace successTrace : List ParseDiagnostic}
    (rejectedTrace : ExpressionNameTraceRejects source endByte input rejected diagnostic rejectTrace)
    (successful : ExpressionNameTraceParses source endByte input name after successTrace) : False :=
  rejectedTrace.ordinary.disjointOrdinary ⟨name, after, successful.ordinary⟩

theorem expressionNameTrace_outcome_total (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ name after trace, ExpressionNameTraceParses source endByte input name after trace) ∨
    ∃ rejected diagnostic trace,
      ExpressionNameTraceRejects source endByte input rejected diagnostic trace := by
  classical
  rcases booleanIdentifierTrace_outcome_total source endByte input with boolean | noBoolean
  · rcases boolean with ⟨name, after, trace, parsed⟩
    exact Or.inl ⟨name, after, trace, .boolean parsed⟩
  · rcases noBoolean with ⟨_, _, _, absent, _, _, _⟩
    by_cases success : ∃ name after, IdentifierParses input name after
    · rcases success with ⟨name, after, ordinary⟩
      rcases identifierDiagnosticTrace_total name with ⟨trace, checked⟩
      exact Or.inl ⟨name, after, trace, .identifier absent (.parsed ordinary checked)⟩
    · have noName : IdentifierAbsentAt input := by
        rintro ⟨span, text, token⟩
        exact success ⟨{ span, value := text }, { input with cursor := input.cursor + 1 },
          token, rfl, rfl, rfl⟩
      rcases rejectAtReports_total source endByte { head := .identifier, tail := [] }
        .expression input with ⟨diagnostic, reported⟩
      exact Or.inr ⟨input, diagnostic, [], absent, .absent noName, reported, rfl⟩

theorem IdentifierExpressionTraceParses.ordinary
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : IdentifierExpressionTraceParses source endByte input value output trace) :
    IdentifierExpressionParses input value output := by
  cases parsed with
  | parsed name => exact .parsed name.ordinary

theorem IdentifierExpressionTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : IdentifierExpressionTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : IdentifierExpressionTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName =>
          rcases leftName.result_unique rightName with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem identifierExpressionTrace_exactOutcomeSpec (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte where
  successResultUnique := IdentifierExpressionTraceParses.result_unique
  rejectResultUnique := ExpressionNameTraceRejects.result_unique
  successRejectDisjoint := by
    rintro input rejected diagnostic trace rejecting ⟨value, after, events, successful⟩
    cases successful with
    | parsed name => exact rejecting.disjoint_success name

theorem identifierExpressionTrace_outcomeExists (source : SourceId) (endByte : Nat) :
    ExpressionTraceOutcomeExists IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte := by
  intro input
  rcases expressionNameTrace_outcome_total source endByte input with successful | rejected
  · rcases successful with ⟨name, after, trace, parsed⟩
    exact Or.inl ⟨_, after, trace, .parsed parsed⟩
  · exact Or.inr rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeIdentifierCascadeProperties
/-! Identifier spelling traces have no removable lexical-cascade events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every identifier event is protected, including repeated hyphens in its text. -/
theorem IdentifierDiagnosticTrace.not_candidate
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (diagnostics : IdentifierDiagnosticTrace name trace) :
    ∀ diagnostic ∈ trace, ¬ LexicalCascadeCandidate diagnostic.kind := by
  cases diagnostics with
  | clean absent => simp
  | hyphen present =>
      intro diagnostic member
      have exactDiagnostic : diagnostic =
          { span := name.span, kind := .invalidIdentifierHyphen name.value } := by
        simpa only [List.mem_singleton] using member
      subst diagnostic
      exact id

/-- Lexical errors never suppress an independent identifier spelling trace. -/
theorem IdentifierDiagnosticTrace.cascadeFilters
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (diagnostics : IdentifierDiagnosticTrace name trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace trace :=
  parseDiagnosticCascadeFilters_of_protected source lexical diagnostics.not_candidate

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties
/-! Checked-name events survive lexical cascade filtering unchanged, including
their complete spans, spellings, source order, and repeated occurrences. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem IdentifierTraceParses.cascadeFilters
    {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : IdentifierTraceParses input name output trace) (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  (identifierTraceParses_iff.mp parsed).2.cascadeFilters text lexical

theorem ExpressionNameTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : ExpressionNameTraceParses source endByte input name output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | boolean parsed => rw [parsed.2]; exact .nil
  | identifier _ parsed => exact parsed.cascadeFilters text lexical

theorem IdentifierExpressionTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : IdentifierExpressionTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed name => exact name.cascadeFilters text lexical

/-- Rejected names have no committed event; their separate failure report is
not covered by this preservation claim. -/
theorem ExpressionNameTraceRejects.cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionNameTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [rejection.2.2.2]
  exact .nil

end Solcore.Syntax.DeclarativeGrammar
end
