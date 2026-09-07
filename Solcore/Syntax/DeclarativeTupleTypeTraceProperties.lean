import Solcore.Syntax.DeclarativeTupleTypeTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceProtectionProperties

/-! Tuple types retain every list element, including empty and singleton lists.
Ordinary erasure and carrier preservation require their separate child laws;
the independent trace relation itself does not assume those laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem tupleTypeTail_of_generic {input output : Remainder}
    {values : List Syntax.TypeExpr} {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailParses .rightParen TypeExprParses input values closingSpan output) :
    TypeExprTrailingDelimitedTailParses .rightParen input values closingSpan output := by
  induction parsed with
  | close absent token => exact .close absent token
  | trailing comma closing => exact .trailing comma closing
  | next comma absent child progress tail ih => exact .next comma absent progress rfl child ih

theorem TupleTypeTraceParses.ordinary
    (childOrdinary : ∀ {input value output trace},
      typeTrace source endByte input value output trace → TypeExprParses input value output)
    (childWindow : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | parsed elements =>
      apply TypeExprParses.tuple rfl
      have frame := elements.output_window childWindow
      cases elements with
      | empty openingSpan closingSpan allowed marker closing =>
          rcases marker with ⟨marker, rfl⟩
          rcases closing with ⟨closing, rfl⟩
          exact .empty openingSpan closingSpan rfl rfl marker closing
      | nonempty openingSpan closingSpan marker continues first progress tail =>
          rcases marker with ⟨marker, rfl⟩
          cases continues with
          | absent absent =>
              exact .nonempty openingSpan closingSpan absent marker progress frame.1 frame.2 rfl rfl
                (childOrdinary first) (tupleTypeTail_of_generic (tail.ordinary childOrdinary))

theorem TupleTypeTraceParses.output_window
    (childWindow : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed elements => exact elements.output_window childWindow

theorem TupleTypeTraceParses.progress
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed elements => exact elements.progress

theorem TupleTypeTraceParses.result_unique
    (childUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TupleTypeTraceParses typeTrace source endByte input left afterLeft leftTrace)
    (rightParsed : TupleTypeTraceParses typeTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed left =>
      cases rightParsed with
      | parsed right =>
          rcases left.result_unique childUnique right with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem TupleTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed elements => exact elements.cascadeFilters childProtected

end Solcore.Syntax.DeclarativeGrammar
