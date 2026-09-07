import Solcore.Syntax.DeclarativeFunctionTypeTraceGrammar
import Solcore.Syntax.DeclarativeFunctionReturnsTraceProperties

/-! Function-type structure and exactness are independent of parser execution.
Only ordinary erasure and output-carrier preservation need a child carrier law. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem functionTypeTail_of_generic {input output : Remainder}
    {values : List Syntax.TypeExpr} {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailParses .rightParen TypeExprParses input values closingSpan output) :
    TypeExprTrailingDelimitedTailParses .rightParen input values closingSpan output := by
  induction parsed with
  | close absent token => exact .close absent token
  | trailing comma closing => exact .trailing comma closing
  | next comma absent child progress tail ih => exact .next comma absent progress rfl child ih

theorem FunctionTypeTraceParses.ordinary
    (childOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | parsed span marker parameters returns =>
      refine TypeExprParses.function span marker rfl ?_ (returns.ordinary childOrdinary childWindow)
      have frame := parameters.output_window childWindow
      cases parameters with
      | empty openingSpan closingSpan allowed opening closing =>
          rcases opening with ⟨opening, rfl⟩
          rcases closing with ⟨closing, rfl⟩
          exact .empty openingSpan closingSpan rfl rfl opening closing
      | nonempty openingSpan closingSpan opening continues first progress tail =>
          rcases opening with ⟨opening, rfl⟩
          cases continues with
          | absent absent =>
              exact .nonempty openingSpan closingSpan absent opening progress frame.1 frame.2 rfl rfl
                (childOrdinary first) (functionTypeTail_of_generic (tail.ordinary childOrdinary))

theorem FunctionTypeTraceParses.output_window
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed span marker parameters returns =>
      have first := parameters.output_window childWindow
      have last := returns.output_window childWindow
      simpa only [marker.2] using And.intro (last.1.trans first.1) (last.2.trans first.2)

theorem FunctionTypeTraceParses.progress
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed span marker parameters returns =>
      have first := parameters.progress
      rw [marker.2] at first
      exact Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.lt_succ_self _) first) returns.cursor_le

theorem FunctionTypeTraceParses.result_unique
    (childUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : FunctionTypeTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : FunctionTypeTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed span marker parameters returns =>
      cases rightParsed with
      | parsed otherSpan otherMarker otherParameters otherReturns =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases parameters.result_unique childUnique otherParameters with ⟨rfl, rfl, rfl⟩
          rcases returns.result_unique childUnique otherReturns with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem FunctionTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ parameters returns =>
      exact (parameters.cascadeFilters childProtected).append (returns.cascadeFilters childProtected)

end Solcore.Syntax.DeclarativeGrammar
