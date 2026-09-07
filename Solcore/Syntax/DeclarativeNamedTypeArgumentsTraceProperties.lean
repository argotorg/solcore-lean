import Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceProtectionProperties

/-! Structural nonemptiness, ordinary erasure, exactness, and event protection.
Only carrier preservation and ordinary erasure require separate child laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TrailingDelimitedListTraceParses.nonempty_elements {α : Type}
    {opening closing : Symbol}
    {child : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing false child source endByte input values output trace) :
    values.elements ≠ [] := by
  cases parsed with
  | empty _ _ allowed => contradiction
  | nonempty => simp

private theorem namedArguments_opening_token
    {input output : Remainder} {values : DelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses .less .greater false elementTrace source endByte input values output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .less } := by
  cases parsed with
  | empty _ _ allowed => contradiction
  | nonempty span _ marker => exact ⟨span, marker.1⟩

theorem NamedTypeArgumentsTraceParses.present_token
    {input output : Remainder} {arguments : NonemptyDelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input (some arguments) output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .less } := by
  cases parsed with
  | present parsed => exact namedArguments_opening_token parsed

theorem NamedTypeArgumentsTraceParses.output_window
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present parsed => exact parsed.output_window elementWindow

theorem NamedTypeArgumentsTraceParses.cursor_le
    {input output : Remainder} {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    input.cursor ≤ output.cursor := by
  cases parsed with
  | absent => exact Nat.le_refl _
  | present parsed => exact Nat.le_of_lt parsed.progress

theorem NamedTypeArgumentsTraceParses.some_progress
    {input output : Remainder} {arguments : NonemptyDelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input (some arguments) output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | present parsed => exact parsed.progress

private theorem typeTail_of_generic {input output : Remainder} {values : List Syntax.TypeExpr}
    {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailParses .greater TypeExprParses input values closingSpan output) :
    TypeExprTrailingDelimitedTailParses .greater input values closingSpan output := by
  induction parsed with
  | close absent token => exact .close absent token
  | trailing comma closing => exact .trailing comma closing
  | next comma absent child progress tail ih => exact .next comma absent progress rfl child ih

theorem NamedTypeArgumentsTraceParses.ordinary
    (elementOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    OptionalNamedTypeArgumentsParses input arguments output := by
  cases parsed with
  | absent absent => exact .absent absent
  | present parsed =>
      rcases parsed.ordinary elementOrdinary elementWindow with
        ⟨openingSpan, first, afterFirst, rest, closingSpan, tokensEq, endIndexEq,
          marker, firstParsed, progress, tail, elementsEq, spanEq⟩
      exact .present openingSpan closingSpan marker progress tokensEq endIndexEq elementsEq spanEq
        firstParsed (typeTail_of_generic tail)

theorem NamedTypeArgumentsTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedTypeArgumentsTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : NamedTypeArgumentsTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent absent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present parsed => exact False.elim (absent (NamedTypeArgumentsTraceParses.present parsed).present_token)
  | present parsed =>
      cases rightParsed with
      | absent absent => exact False.elim (absent (NamedTypeArgumentsTraceParses.present parsed).present_token)
      | present other =>
          rename_i left right
          rcases parsed.result_unique elementUnique other with ⟨same, rfl, rfl⟩
          have valuesEq : left = right := by
            cases left with
            | mk leftSpan leftValues =>
                cases right with
                | mk rightSpan rightValues =>
                    cases leftValues
                    cases rightValues
                    simp only [NonemptyList.toList, DelimitedList.mk.injEq, List.cons.injEq] at same
                    rcases same with ⟨rfl, rfl, rfl⟩
                    rfl
          exact ⟨congrArg some valuesEq, rfl, rfl⟩

theorem NamedTypeArgumentsTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (elementProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present parsed => exact parsed.cascadeFilters elementProtected

end Solcore.Syntax.DeclarativeGrammar
