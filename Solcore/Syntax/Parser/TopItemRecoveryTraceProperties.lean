import Solcore.Syntax.Parser.TopItemRecoveryCompletenessProperties

/-! Exact raw diagnostic effects of standalone top-level recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem advance?_diagnosticsRev_eq {input next : State}
    {token : Token} (advanced : input.advance? = some (token, next)) :
    next.diagnosticsRev = input.diagnosticsRev := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

/-- Finishing a recovery adds exactly its recovered-span diagnostic. -/
theorem finishRecoveredTopItem_success_diagnosticsRev_eq
    {first last : SourceSpan} {input output : State} {item : TopItem}
    (result : finishRecoveredTopItem first last input = .ok item output) :
    output.diagnosticsRev =
      { span := item.span, kind := .recovered .topItem } ::
        input.diagnosticsRev := by
  unfold finishRecoveredTopItem at result
  cases result
  rfl

/-- Scanning consumes tokens silently before adding one recovery diagnostic. -/
theorem recoverTopItemAux_success_diagnosticsRev_eq (first : SourceSpan) :
    ∀ fuel last input item output,
      recoverTopItemAux first last fuel input = .ok item output →
      output.diagnosticsRev =
        { span := item.span, kind := .recovered .topItem } ::
          input.diagnosticsRev := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input item output result
      simp [recoverTopItemAux] at result
  | succ fuel ih =>
      intro last input item output result
      unfold recoverTopItemAux at result
      split at result
      · exact finishRecoveredTopItem_success_diagnosticsRev_eq result
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            exact finishRecoveredTopItem_success_diagnosticsRev_eq result
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            simpa only [advance?_diagnosticsRev_eq advanced] using
              ih token.span next item output result

/-- The mandatory first token is silent; complete recovery adds one event. -/
theorem recoverTopItem_success_diagnosticsRev_eq
    {input output : State} {item : TopItem}
    (result : recoverTopItem input = .ok item output) :
    output.diagnosticsRev =
      { span := item.span, kind := .recovered .topItem } ::
        input.diagnosticsRev := by
  unfold recoverTopItem at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      simpa only [advance?_diagnosticsRev_eq advanced] using
        recoverTopItemAux_success_diagnosticsRev_eq token.span
          (next.remainingCount + 1) token.span next item output result

/-- Finishing recovery preserves prior forward-order diagnostics exactly. -/
theorem finishRecoveredTopItem_success_diagnostics_eq
    {first last : SourceSpan} {input output : State} {item : TopItem}
    (result : finishRecoveredTopItem first last input = .ok item output) :
    output.diagnostics = input.diagnostics ++
      [{ span := item.span, kind := .recovered .topItem }] := by
  simp only [State.diagnostics,
    finishRecoveredTopItem_success_diagnosticsRev_eq result, List.reverse_cons]

/-- Auxiliary recovery has the same exact forward-order singleton effect. -/
theorem recoverTopItemAux_success_diagnostics_eq
    {first last : SourceSpan} {fuel : Nat} {input output : State}
    {item : TopItem}
    (result : recoverTopItemAux first last fuel input = .ok item output) :
    output.diagnostics = input.diagnostics ++
      [{ span := item.span, kind := .recovered .topItem }] := by
  simp only [State.diagnostics,
    recoverTopItemAux_success_diagnosticsRev_eq first fuel last input item
      output result, List.reverse_cons]

/-- Standalone recovery appends exactly one diagnostic at its AST span. -/
theorem recoverTopItem_success_diagnostics_eq
    {input output : State} {item : TopItem}
    (result : recoverTopItem input = .ok item output) :
    output.diagnostics = input.diagnostics ++
      [{ span := item.span, kind := .recovered .topItem }] := by
  simp only [State.diagnostics,
    recoverTopItem_success_diagnosticsRev_eq result, List.reverse_cons]

/-- An unavailable first token rejects without modifying the diagnostics. -/
theorem recoverTopItem_reject_diagnosticsRev_eq
    {input output : State} {failure : Failure}
    (result : recoverTopItem input = .reject failure output) :
    output.diagnosticsRev = input.diagnosticsRev := by
  unfold recoverTopItem at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      rfl
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverTopItemAux_production_exists_ok token.span token.span next
          with ⟨item, final, recovered⟩
      rw [recovered] at result
      contradiction

/-- Rejection retains the complete prior forward-order diagnostic list. -/
theorem recoverTopItem_reject_diagnostics_eq
    {input output : State} {failure : Failure}
    (result : recoverTopItem input = .reject failure output) :
    output.diagnostics = input.diagnostics := by
  simp only [State.diagnostics, recoverTopItem_reject_diagnosticsRev_eq result]

/-- Independent recovery success also fixes the exact added raw diagnostic. -/
theorem recoverTopItem_ordinary_success_iff_with_trace
    {input : State} {item : TopItem}
    {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder item remainder ↔
      ∃ output, recoverTopItem input = .ok item output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++
          [{ span := item.span, kind := .recovered .topItem }] := by
  constructor
  · intro parsed
    rcases recoverTopItem_ordinary_success_iff.mp parsed with
      ⟨output, result, after⟩
    exact ⟨output, result, after, recoverTopItem_success_diagnostics_eq result⟩
  · rintro ⟨output, result, after, _trace⟩
    exact recoverTopItem_ordinary_success_iff.mpr ⟨output, result, after⟩

/-- Independent recovery rejection corresponds to execution with no events. -/
theorem recoverTopItem_ordinary_reject_iff_with_trace
    {input : State} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRecoveryRejects
      input.declarativeRemainder remainder ↔
      ∃ failure output, recoverTopItem input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics := by
  constructor
  · intro rejected
    rcases recoverTopItem_ordinary_reject_iff.mp rejected with
      ⟨failure, output, result, after⟩
    exact ⟨failure, output, result, after,
      recoverTopItem_reject_diagnostics_eq result⟩
  · rintro ⟨failure, output, result, after, _trace⟩
    exact recoverTopItem_ordinary_reject_iff.mpr ⟨failure, output, result, after⟩

end Solcore.Syntax.Parser.FileInternals
