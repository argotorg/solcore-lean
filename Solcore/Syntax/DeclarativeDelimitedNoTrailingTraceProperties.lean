import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceGrammar

/-! Erasure and structural laws. Only whole-list erasure needs the separate
child carrier/end-index law demanded by the older ordinary list grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementParses : Remainder → α → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem NoTrailingDelimitedTailTraceParses.ordinary
    (elementOrdinary : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    NoTrailingDelimitedTailParses closing elementParses input values closingSpan output := by
  induction parsed with
  | close absent token => rw [token.2]; exact .close absent token.1
  | next span comma element progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      exact .next token (elementOrdinary element) progress ih

theorem NoTrailingDelimitedTailTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | close absent token => rw [token.2]; exact ⟨rfl, rfl⟩
  | next span comma element progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      have frame := elementWindow element
      exact ⟨ih.1.trans frame.1, ih.2.trans frame.2⟩

theorem NoTrailingDelimitedTailTraceParses.progress
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) : input.cursor < output.cursor := by
  induction parsed with
  | close absent token => rw [token.2]; exact Nat.lt_succ_self _
  | next span comma element progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) ih

theorem NoTrailingDelimitedListTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) : output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | empty _ _ _ marker finish => rw [finish.2, marker.2]; exact ⟨rfl, rfl⟩
  | nonempty _ _ marker _ first _ tail =>
      have tailFrame := tail.output_window elementWindow
      have firstFrame := elementWindow first
      rcases marker with ⟨_, rfl⟩
      exact ⟨tailFrame.1.trans firstFrame.1, tailFrame.2.trans firstFrame.2⟩

/-- A tail can never close on a comma: that branch always starts another child. -/
theorem NoTrailingDelimitedTailTraceParses.closing_ne_comma
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) : closing ≠ .comma := by
  induction parsed with
  | close absent finish => intro same; subst closing; exact absent ⟨_, finish.1⟩
  | next _ _ _ _ _ ih => exact ih

theorem NoTrailingDelimitedListTraceParses.ordinary
    (elementOrdinary : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) :
    if allowEmpty then NoTrailingDelimitedListParses opening closing elementParses input values output
    else NonemptyNoTrailingDelimitedListParses opening closing elementParses input values output := by
  have frame := parsed.output_window elementWindow
  cases parsed with
  | empty openingSpan closingSpan allowed marker finish =>
      rw [allowed]
      rcases marker with ⟨marker, rfl⟩
      rcases finish with ⟨finish, rfl⟩
      simpa only [Bool.true_eq, ↓reduceIte, Nat.add_assoc] using
        NoTrailingDelimitedListParses.empty (elementParses := elementParses)
          openingSpan closingSpan marker finish
  | nonempty openingSpan closingSpan marker continues first progress tail =>
      rcases marker with ⟨marker, rfl⟩
      have ordinary : NonemptyNoTrailingDelimitedListParses opening closing elementParses
          input { span := SourceSpan.cover openingSpan closingSpan, elements := _ } output :=
        ⟨openingSpan, _, _, _, closingSpan, frame.1, frame.2, marker,
          elementOrdinary first, progress, tail.ordinary elementOrdinary, rfl, rfl⟩
      cases continues with
      | disabled => exact ordinary
      | absent absent => exact .nonempty absent ordinary

end Solcore.Syntax.DeclarativeGrammar
