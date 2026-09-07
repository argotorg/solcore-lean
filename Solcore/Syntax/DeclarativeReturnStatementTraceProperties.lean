import Solcore.Syntax.DeclarativeReturnStatementTraceGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Independent return-trace erasure, context structure, and exact uniqueness. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalReturnValueTraceParses.ordinary
    (erases : ∀ {input value output trace}, expressionTrace source endByte input value output trace →
      expressionOrdinary input value output)
    {input output : Remainder} {value : Option Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : OptionalReturnValueTraceParses expressionTrace source endByte input value output trace) :
    OptionalReturnValueParses expressionOrdinary input value output := by
  cases parsed with
  | absent span current => exact .absent span current
  | present absent valueParsed => exact .present absent (erases valueParsed)

theorem ReturnStatementTraceParses.ordinary
    (erases : ∀ {input value output trace}, expressionTrace source endByte input value output trace →
      expressionOrdinary input value output)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : ReturnStatementTraceParses expressionTrace source endByte input statement output trace) :
    ReturnStatementParses expressionOrdinary input statement output := by
  cases parsed with
  | parsed marker semicolon markerParsed valueParsed semicolonParsed =>
      exact .parsed marker semicolon markerParsed (valueParsed.ordinary erases) semicolonParsed

theorem OptionalReturnValueTraceParses.output_window
    (expressionWindow : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Option Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : OptionalReturnValueTraceParses expressionTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present _ valueParsed => exact expressionWindow valueParsed

theorem ReturnStatementTraceParses.output_window
    (expressionWindow : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : ReturnStatementTraceParses expressionTrace source endByte input statement output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed marker semicolon markerParsed valueParsed semicolonParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      rcases semicolonParsed with ⟨_, rfl⟩
      exact valueParsed.output_window expressionWindow

theorem OptionalReturnValueTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      expressionTrace source endByte input left afterLeft leftTrace →
      expressionTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OptionalReturnValueTraceParses expressionTrace source endByte
      input left afterLeft leftTrace)
    (rightParsed : OptionalReturnValueTraceParses expressionTrace source endByte
      input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent span current =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present absent _ => exact False.elim (absent ⟨span, current⟩)
  | present absent valueParsed =>
      cases rightParsed with
      | absent span current => exact False.elim (absent ⟨span, current⟩)
      | present _ rightValue =>
          rcases unique valueParsed rightValue with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ReturnStatementTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      expressionTrace source endByte input left afterLeft leftTrace →
      expressionTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Statement}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ReturnStatementTraceParses expressionTrace source endByte
      input left afterLeft leftTrace)
    (rightParsed : ReturnStatementTraceParses expressionTrace source endByte
      input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftMarker leftSemicolon markerLeft valueLeft semicolonLeft =>
      cases rightParsed with
      | parsed rightMarker rightSemicolon markerRight valueRight semicolonRight =>
          rcases markerLeft.result_unique markerRight with ⟨rfl, rfl⟩
          rcases valueLeft.result_unique unique valueRight with ⟨rfl, rfl, rfl⟩
          rcases semicolonLeft.result_unique semicolonRight with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
