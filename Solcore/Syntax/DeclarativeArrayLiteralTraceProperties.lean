import Solcore.Syntax.DeclarativeArrayLiteralTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceProtectionProperties
import Solcore.Syntax.DeclarativeCoreCollectionAtomGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceOutcomeProperties

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
