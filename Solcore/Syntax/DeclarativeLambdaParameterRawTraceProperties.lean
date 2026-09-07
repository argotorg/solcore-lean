import Solcore.Syntax.DeclarativeLambdaParameterRawTraceGrammar
import Solcore.Syntax.DeclarativeLambdaParameterTailTraceProperties

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
