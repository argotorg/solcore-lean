import Solcore.Syntax.DeclarativeCoreBlockTraceGrammar
import Solcore.Syntax.DeclarativeCoreBlockTailTraceProperties
import Solcore.Syntax.DeclarativeCoreTypePrimitiveProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Raw-block trace erasure, exact functionality, and cursor/window laws.
Only the abstract statement judgment needs corresponding context-preservation
and result-uniqueness premises; no execution or rejection assumptions occur. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
  {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}

/-- Erasing every inner event sequence recovers the existing block-items grammar. -/
theorem CoreBlockItemsTraceParses.ordinary
    (statementErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        statementOrdinary input statement output)
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) :
    CoreBlockItemsParses statementOrdinary input statements closingSpan output := by
  induction parsed with
  | close span token => exact .close span token
  | next inside absent statement progress tail ih =>
      exact .next inside absent (statementErases statement) progress ih

/-- Tail reports do not remove ordinary success or modify its AST and remainder. -/
theorem CoreBlockTraceParses.ordinary
    (statementErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        statementOrdinary input statement output)
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    CoreBlockOrdinaryParses statementOrdinary policy input body output := by
  cases parsed with
  | parsed opening closing token items validated =>
      exact .parsed opening closing token (items.ordinary statementErases)

/-- At least the final closing brace is consumed. -/
theorem CoreBlockItemsTraceParses.cursor_lt
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) : input.cursor < output.cursor := by
  induction parsed with
  | close span token => rcases token with ⟨_, rfl⟩; simp
  | next _ _ _ progress _ ih => exact Nat.lt_trans progress ih

/-- The closing token bounds the final cursor, even before any statement
carrier-preservation premise is imposed. -/
theorem CoreBlockItemsTraceParses.output_cursor_le_endIndex
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) : output.cursor ≤ output.endIndex := by
  induction parsed with
  | close span token => rcases token with ⟨inside, rfl⟩; exact inside.1
  | next _ _ _ _ _ ih => exact ih

/-- Each statement advances strictly and the closing brace needs one more slot. -/
theorem CoreBlockItemsTraceParses.length_lt_cursor_distance
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) :
    statements.length < output.cursor - input.cursor := by
  induction parsed with
  | close span token => rcases token with ⟨_, rfl⟩; simp
  | next _ _ _ progress _ ih => simp only [List.length_cons]; omega

/-- Abstract statement window preservation lifts through the ordered list. -/
theorem CoreBlockItemsTraceParses.output_window
    (statementWindow : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | close span token => rcases token with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
  | next _ _ statement _ _ ih =>
      have step := statementWindow statement
      exact ⟨ih.1.trans step.1, ih.2.trans step.2⟩

theorem CoreBlockTraceParses.cursor_lt
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed opening closing token items validated =>
      rcases token with ⟨_, rfl⟩
      exact Nat.lt_trans (by simp) items.cursor_lt

theorem CoreBlockTraceParses.output_cursor_le_endIndex
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    output.cursor ≤ output.endIndex := by
  cases parsed with
  | parsed opening closing token items validated => exact items.output_cursor_le_endIndex

theorem CoreBlockTraceParses.output_window
    (statementWindow : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed opening closing token items validated =>
      rcases token with ⟨_, rfl⟩
      exact items.output_window statementWindow

/-- Closing-branch priority and exact inner traces fix the complete statement
list, final brace span, remainder, and all events, including duplicate events. -/
theorem CoreBlockItemsTraceParses.result_unique
    (statementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      statementTrace source endByte input left afterLeft leftTrace →
      statementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Statement}
    {leftClosing rightClosing : SourceSpan} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : CoreBlockItemsTraceParses statementTrace source endByte
      input left leftClosing afterLeft leftTrace)
    (rightParsed : CoreBlockItemsTraceParses statementTrace source endByte
      input right rightClosing afterRight rightTrace) :
    left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right afterRight rightClosing rightTrace with
  | close span token =>
      cases rightParsed with
      | close rightSpan rightToken =>
          rcases token.result_unique rightToken with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | next _ absent _ _ _ =>
          exact False.elim (typeTokenAbsent_conflicts_token absent token.1)
  | next _ absent statement _ _ ih =>
      cases rightParsed with
      | close span token => exact False.elim (typeTokenAbsent_conflicts_token absent token.1)
      | next _ _ rightStatement _ rightTail =>
          rcases statementUnique statement rightStatement with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exact statement traces and deterministic tail validation fix the covering
AST, remainder, and full statement-events-then-validation-events sequence. -/
theorem CoreBlockTraceParses.result_unique
    (statementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      statementTrace source endByte input left afterLeft leftTrace →
      statementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Block}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : CoreBlockTraceParses statementTrace policy source endByte
      input left afterLeft leftTrace)
    (rightParsed : CoreBlockTraceParses statementTrace policy source endByte
      input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftOpening leftClosing leftToken leftItems leftValidated =>
      cases rightParsed with
      | parsed rightOpening rightClosing rightToken rightItems rightValidated =>
          rcases leftToken.result_unique rightToken with ⟨rfl, rfl⟩
          rcases leftItems.result_unique statementUnique rightItems with ⟨rfl, rfl, rfl, rfl⟩
          rw [leftValidated.output_unique rightValidated]
          exact ⟨rfl, rfl, rfl⟩

/-- An empty total trace forces tail validity; ordinary parses with nonempty
constraint traces are not incorrectly reclassified as diagnostic-free syntax. -/
theorem CoreBlockTraceParses.empty_trace_tailsValid
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
    (empty : trace = []) : CoreBlockTailsValid policy body.value := by
  cases parsed with
  | parsed opening closing token items validated =>
      exact validated.empty_iff.mp (List.append_eq_nil_iff.mp empty).2

end Solcore.Syntax.DeclarativeGrammar
