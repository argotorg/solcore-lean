import Solcore.Syntax.DeclarativeNamedTypeTraceGrammar
import Solcore.Syntax.DeclarativeQualifiedNameTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeFinishingTraceProperties

/-! Raw named types preserve exact structure and every event occurrence.
Ordinary erasure is componentwise: selecting the prioritized type-expression
branch requires separate dispatch guards and is outside this raw boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem NamedTypeTraceParses.ordinary_components
    (elementOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    ∃ name afterName arguments, QualifiedNameParses input name afterName ∧
      OptionalNamedTypeArgumentsParses afterName arguments output ∧ value = namedTypeTraceValue name arguments := by
  cases parsed with
  | parsed name arguments finished =>
      exact ⟨_, _, _, name.ordinary, arguments.ordinary elementOrdinary elementWindow, rfl⟩

theorem NamedTypeTraceParses.output_window
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed name arguments finished =>
      have frame := arguments.output_window elementWindow
      exact ⟨frame.1.trans name.output_window.1, frame.2.trans name.output_window.2⟩

theorem NamedTypeTraceParses.progress
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed name arguments finished => exact Nat.lt_of_lt_of_le name.cursor_lt arguments.cursor_le

theorem NamedTypeTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedTypeTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : NamedTypeTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed name arguments finished =>
      cases rightParsed with
      | parsed otherName otherArguments otherFinished =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases arguments.result_unique elementUnique otherArguments with ⟨rfl, rfl, rfl⟩
          cases finished.trace_unique otherFinished
          exact ⟨rfl, rfl, rfl⟩

theorem NamedTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (elementProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed name arguments finished =>
      exact ((name.cascadeFilters text lexical).append (arguments.cascadeFilters elementProtected)).append
        (finished.cascadeFilters text lexical)

end Solcore.Syntax.DeclarativeGrammar
