import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact success functionality includes every element, both covering endpoints,
the complete remainder, and every ordered diagnostic occurrence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem NoTrailingDelimitedTailTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : List α}
    {leftClosing rightClosing : SourceSpan} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input left leftClosing afterLeft leftTrace)
    (rightParsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input right rightClosing afterRight rightTrace) :
    left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightClosing afterRight rightTrace with
  | close absent finish =>
      cases rightParsed with
      | close _ rightFinish =>
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | next span comma _ _ _ => exact False.elim (absent ⟨span, comma.1⟩)
  | next span comma element progress tail ih =>
      cases rightParsed with
      | close absent _ => exact False.elim (absent ⟨span, comma.1⟩)
      | next rightSpan rightComma rightElement _ rightTail =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          rcases elementUnique element rightElement with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

theorem NoTrailingDelimitedListTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : DelimitedList α}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      source endByte input left afterLeft leftTrace)
    (rightParsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | empty openingSpan closingSpan allowed marker finish =>
      cases rightParsed with
      | empty rightOpening rightClosing _ rightMarker rightFinish =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | nonempty _ _ rightMarker continues _ _ _ =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rw [allowed] at continues
          cases continues with
          | absent absent => exact False.elim (absent ⟨closingSpan, finish.1⟩)
  | nonempty openingSpan closingSpan marker continues first progress tail =>
      cases rightParsed with
      | empty _ rightClosing allowed rightMarker finish =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rw [allowed] at continues
          cases continues with
          | absent absent => exact False.elim (absent ⟨rightClosing, finish.1⟩)
      | nonempty _ _ rightMarker _ rightFirst _ rightTail =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rcases elementUnique first rightFirst with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique elementUnique rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
