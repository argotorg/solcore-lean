import Solcore.Syntax.DeclarativeDelimitedTrailingTraceGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeTraceOutcomeAgreement

/-! Successful trailing lists agree under pairwise child success agreement.
The left and right child relations need not be internally functional. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {leftParses rightParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}
  (successAgree : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    leftParses source endByte input left afterLeft leftTrace →
    rightParses source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)

include successAgree in
theorem TrailingDelimitedTailTraceParses.result_agree
    {input afterLeft afterRight : Remainder} {left right : List α}
    {leftClosing rightClosing : SourceSpan} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TrailingDelimitedTailTraceParses closing leftParses source endByte
      input left leftClosing afterLeft leftTrace)
    (rightParsed : TrailingDelimitedTailTraceParses closing rightParses source endByte
      input right rightClosing afterRight rightTrace) :
    left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightClosing afterRight rightTrace with
  | close absent finish =>
      cases rightParsed with
      | close _ rightFinish =>
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | trailing span comma _ | next span comma _ _ _ _ =>
          exact False.elim (absent ⟨span, comma.1⟩)
  | trailing span comma finish =>
      cases rightParsed with
      | close absent _ => exact False.elim (absent ⟨span, comma.1⟩)
      | trailing rightSpan rightComma rightFinish =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | next rightSpan rightComma absent _ _ _ =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          exact False.elim (absent ⟨_, finish.1⟩)
  | next span comma absent element progress tail ih =>
      cases rightParsed with
      | close absent _ => exact False.elim (absent ⟨span, comma.1⟩)
      | trailing rightSpan rightComma finish =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          exact False.elim (absent ⟨_, finish.1⟩)
      | next rightSpan rightComma _ rightElement _ rightTail =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          rcases successAgree element rightElement with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

include successAgree in
theorem TrailingDelimitedListTraceParses.result_agree
    {input afterLeft afterRight : Remainder} {left right : DelimitedList α}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TrailingDelimitedListTraceParses opening closing allowEmpty leftParses
      source endByte input left afterLeft leftTrace)
    (rightParsed : TrailingDelimitedListTraceParses opening closing allowEmpty rightParses
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
          rcases successAgree first rightFirst with ⟨rfl, rfl, rfl⟩
          rcases tail.result_agree successAgree rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
