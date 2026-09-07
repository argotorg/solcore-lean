import Solcore.Syntax.DeclarativeFunctionReturnsTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceProtectionProperties

/-! Independent optional-return structure, ordinary erasure, and exactness.
Only ordinary list erasure and carrier preservation require a child carrier law. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem FunctionReturnsTraceParses.present_token
    {input output : Remainder} {values : DelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input (some values) output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .identifier ContextualKeyword.returns.spelling } := by
  cases parsed with
  | present span marker _ => exact ⟨span, marker.1⟩

theorem FunctionReturnsTraceParses.output_window
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present span marker values => simpa only [marker.2] using values.output_window childWindow

theorem FunctionReturnsTraceParses.some_progress
    {input output : Remainder} {values : DelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input (some values) output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | present span marker values =>
      have progress := values.progress
      rw [marker.2] at progress
      exact Nat.lt_trans (Nat.lt_succ_self _) progress

theorem FunctionReturnsTraceParses.cursor_le
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    input.cursor ≤ output.cursor := by
  cases values with
  | none => cases parsed; exact Nat.le_refl _
  | some => exact Nat.le_of_lt parsed.some_progress

private theorem returnsTypeTail_of_generic {input output : Remainder}
    {values : List Syntax.TypeExpr} {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailParses .rightParen TypeExprParses input values closingSpan output) :
    TypeExprTrailingDelimitedTailParses .rightParen input values closingSpan output := by
  induction parsed with
  | close absent token => exact .close absent token
  | trailing comma closing => exact .trailing comma closing
  | next comma absent child progress tail ih => exact .next comma absent progress rfl child ih

theorem FunctionReturnsTraceParses.ordinary
    (childOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    OptionalFunctionTypeReturnsParses input values output := by
  cases parsed with
  | absent absent => exact .absent absent
  | present span marker values =>
      apply OptionalFunctionTypeReturnsParses.present span marker
      have frame := values.output_window childWindow
      cases values with
      | empty openingSpan closingSpan allowed opening closing =>
          rcases opening with ⟨opening, rfl⟩
          rcases closing with ⟨closing, rfl⟩
          exact .empty openingSpan closingSpan rfl rfl opening closing
      | nonempty openingSpan closingSpan opening continues first progress tail =>
          rcases opening with ⟨opening, rfl⟩
          cases continues with
          | absent absent =>
              exact .nonempty openingSpan closingSpan absent opening progress frame.1 frame.2 rfl rfl
                (childOrdinary first) (returnsTypeTail_of_generic (tail.ordinary childOrdinary))

theorem FunctionReturnsTraceParses.result_unique
    (childUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option (DelimitedList Syntax.TypeExpr)}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : FunctionReturnsTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : FunctionReturnsTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent absent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present span marker _ => exact False.elim (absent ⟨span, marker.1⟩)
  | present span marker values =>
      cases rightParsed with
      | absent absent => exact False.elim (absent ⟨span, marker.1⟩)
      | present otherSpan otherMarker other =>
          cases marker.output_unique otherMarker
          rcases values.result_unique childUnique other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem FunctionReturnsTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present _ _ values => exact values.cascadeFilters childProtected

end Solcore.Syntax.DeclarativeGrammar
