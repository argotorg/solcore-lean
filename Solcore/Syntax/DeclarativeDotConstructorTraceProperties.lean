import Solcore.Syntax.DeclarativeDotConstructorTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceExactnessProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProperties

/-! Ordinary erasure, progress, and exact structure. The older whole-list
grammar needs child carrier/end-index preservation, supplied separately here. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {elementParses : Remainder → Syntax.Expr → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalDotConstructorArgumentsTraceParses.present_token
    {input output : Remainder} {arguments : DelimitedList Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte
      input (some arguments) output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen } := by
  cases parsed with
  | present arguments =>
      cases arguments with
      | empty span _ _ opening _ | nonempty span _ opening _ _ _ _ => exact ⟨span, opening.1⟩

theorem OptionalDotConstructorArgumentsTraceParses.ordinary
    (erases : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {arguments : Option (DelimitedList Syntax.Expr)} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    OptionalDotConstructorArgumentsParses elementParses input arguments output := by
  cases parsed with
  | absent absent => exact .absent absent
  | present arguments => exact .present (arguments.ordinary erases elementWindow)

theorem DotConstructorTraceParses.ordinary
    (erases : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses elementTrace source endByte input value output trace) :
    DotConstructorParses elementParses input value output := by
  cases parsed with
  | parsed span dot name args => exact .parsed span dot name.ordinary (args.ordinary erases elementWindow)

theorem OptionalDotConstructorArgumentsTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {arguments : Option (DelimitedList Syntax.Expr)} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present args => exact args.output_window elementWindow

theorem DotConstructorTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed span dot name args =>
      have frame := args.output_window elementWindow
      simpa only [name.output_eq, dot.2] using frame

theorem OptionalDotConstructorArgumentsTraceParses.cursor_le
    {input output : Remainder} {arguments : Option (DelimitedList Syntax.Expr)} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    input.cursor ≤ output.cursor := by
  cases parsed with
  | absent => exact Nat.le_refl _
  | present args =>
      cases args with
      | empty _ _ _ opening closing =>
          rw [closing.2, opening.2]
          exact Nat.le_add_right _ 2
      | nonempty _ _ opening _ _ progress tail =>
          have finalProgress := tail.progress
          rw [opening.2] at progress
          exact Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_lt progress))
            (Nat.le_of_lt finalProgress)

theorem DotConstructorTraceParses.cursor_lt
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed span dot name args =>
      have progress := args.cursor_le
      rw [name.output_eq, dot.2] at progress
      exact Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)) progress

theorem OptionalDotConstructorArgumentsTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option (DelimitedList Syntax.Expr)}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent absent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present args => exact False.elim (absent (OptionalDotConstructorArgumentsTraceParses.present args).present_token)
  | present args =>
      cases rightParsed with
      | absent absent => exact False.elim (absent (OptionalDotConstructorArgumentsTraceParses.present args).present_token)
      | present other =>
          rcases args.result_unique unique other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem DotConstructorTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : DotConstructorTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : DotConstructorTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed span dot name args =>
      cases rightParsed with
      | parsed _ otherDot otherName otherArgs =>
          rcases dot.result_unique otherDot with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases args.result_unique unique otherArgs with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
