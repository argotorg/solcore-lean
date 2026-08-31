import Solcore.Syntax.Parser.PrimitiveTotalityProperties
import Solcore.Syntax.Parser.Derive

/-! Resource and ordinary-result contracts for canonical derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace DeriveTargetInternals

/-- A derive component has only an ordinary success or rejection. -/
theorem deriveComponent_ordinary (state : State) :
    (∃ name final, deriveComponent state = .ok name final) ∨
      (∃ failure final,
        deriveComponent state = .reject failure final) := by
  unfold deriveComponent
  cases found : state.peek? with
  | none =>
      right
      simp [rejectAt]
  | some token =>
      cases reserved : reservedDeriveKeyword? token.value with
      | some keyword =>
          left
          simp [reserved]
      | none =>
          simpa only [reserved] using identifier_ordinary .topItem state

/-- A derive component can never expose a parser invariant. -/
theorem deriveComponent_ne_invariant (state : State)
    (error : ParserInvariantError) :
    deriveComponent state ≠ .invariant error := by
  intro failed
  rcases deriveComponent_ordinary state with
    ⟨name, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Component success advances exactly one token and preserves the window. -/
theorem deriveComponent_ok_cursor_window
    {input final : State} {name : Identifier}
    (parsed : deriveComponent input = .ok name final) :
    final.cursor = input.cursor + 1 ∧ final.window = input.window := by
  unfold deriveComponent at parsed
  cases found : input.peek? with
  | none => simp [found, rejectAt] at parsed
  | some token =>
      simp only [found] at parsed
      cases reserved : reservedDeriveKeyword? token.value with
      | some keyword =>
          simp only [reserved] at parsed
          cases parsed
          simp [State.emit]
      | none =>
          simp only [reserved] at parsed
          have shape := identifier_ok_state_shape .topItem parsed
          have window := identifier_preservesTokenWindow .topItem input
          rw [parsed] at window
          exact ⟨shape.choose_spec.2.2.2, window.2⟩

private theorem remainingCount_lt_after_dot_component
    {input afterDot next : State} {dot : Token} {component : Identifier}
    {fuel : Nat}
    (dotResult : symbol .dot .topItem input = .ok dot afterDot)
    (componentResult : deriveComponent afterDot = .ok component next)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have dotShape := symbol_ok_state_shape .dot .topItem dotResult
  have componentShape := deriveComponent_ok_cursor_window componentResult
  have componentFound : ∃ token, afterDot.peek? = some token := by
    unfold deriveComponent at componentResult
    cases found : afterDot.peek? with
    | none => simp [found, rejectAt] at componentResult
    | some token => exact ⟨token, rfl⟩
  rcases componentFound with ⟨token, found⟩
  have afterDotBeforeEnd :=
    State.cursor_lt_endIndex_of_peek?_eq_some found
  have dotCursorEq : afterDot.cursor = input.cursor + 1 := by
    rw [dotShape.2]
  have dotWindowEq : afterDot.window = input.window := by
    rw [dotShape.2]
  have afterDotBeforeEnd' :
      input.cursor + 1 < input.window.endIndex := by
    simpa [dotCursorEq, dotWindowEq] using afterDotBeforeEnd
  have inputTwoBound : input.cursor + 2 ≤ input.window.endIndex := by
    omega
  have nextCursorEq : next.cursor = input.cursor + 2 := by
    rw [componentShape.1, dotCursorEq]
  have nextEndIndexEq :
      next.window.endIndex = input.window.endIndex := by
    exact congrArg TokenWindow.endIndex
      (componentShape.2.trans dotWindowEq)
  simp only [State.remainingCount] at adequate ⊢
  rw [nextEndIndexEq, nextCursorEq]
  omega

/-- Adequate fuel makes the dotted-tail loop return only ordinary results. -/
theorem deriveTargetTail_ordinary_of_remainingCount_lt
    (first : Identifier) :
    ∀ fuel last tailRev state,
      state.remainingCount < fuel →
      (∃ target final,
        deriveTargetTail first fuel last tailRev state = .ok target final) ∨
        (∃ failure final,
          deriveTargetTail first fuel last tailRev state =
            .reject failure final) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev state adequate
      unfold deriveTargetTail
      split
      · cases dotResult : symbol .dot .topItem state with
        | invariant error =>
            exact False.elim (symbol_ne_invariant .dot .topItem state
              error dotResult)
        | reject failure rejected =>
            right
            exact ⟨failure, rejected, rfl⟩
        | ok dot afterDot =>
            cases componentResult : deriveComponent afterDot with
            | invariant error =>
                exact False.elim
                  (deriveComponent_ne_invariant afterDot error componentResult)
            | reject failure rejected =>
                right
                simp [componentResult]
            | ok component next =>
                have nextAdequate := remainingCount_lt_after_dot_component
                  dotResult componentResult adequate
                simpa only [componentResult] using
                  inductionHypothesis component (component :: tailRev)
                    next nextAdequate
      · left
        exact ⟨_, _, rfl⟩

/-- The production fuel for a derive-target tail is always adequate. -/
theorem deriveTargetTail_production_ordinary
    (first last : Identifier) (tailRev : List Identifier) (state : State) :
    (∃ target final,
      deriveTargetTail first (state.remainingCount + 1) last tailRev state =
        .ok target final) ∨
      (∃ failure final,
        deriveTargetTail first (state.remainingCount + 1) last tailRev state =
          .reject failure final) :=
  deriveTargetTail_ordinary_of_remainingCount_lt first
    (state.remainingCount + 1) last tailRev state (by omega)

/-- An adequately fueled derive-target tail cannot expose an invariant. -/
theorem deriveTargetTail_ne_invariant_of_remainingCount_lt
    (first last : Identifier) (tailRev : List Identifier)
    (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    deriveTargetTail first fuel last tailRev state ≠ .invariant error := by
  intro failed
  rcases deriveTargetTail_ordinary_of_remainingCount_lt first fuel last tailRev
      state adequate with
    ⟨target, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

end DeriveTargetInternals

open DeriveTargetInternals

/-- Public derive-target parsing has only an ordinary result. -/
theorem deriveTarget_ordinary (state : State) :
    (∃ target final, deriveTarget state = .ok target final) ∨
      (∃ failure final, deriveTarget state = .reject failure final) := by
  rcases deriveComponent_ordinary state with success | rejection
  · rcases success with ⟨first, next, firstResult⟩
    unfold deriveTarget
    simp only [firstResult]
    exact deriveTargetTail_production_ordinary first first [] next
  · rcases rejection with ⟨failure, next, firstResult⟩
    right
    unfold deriveTarget
    simp only [firstResult]
    exact ⟨failure, next, rfl⟩

/-- Public derive-target parsing cannot expose an internal invariant. -/
theorem deriveTarget_ne_invariant (state : State)
    (error : ParserInvariantError) :
    deriveTarget state ≠ .invariant error := by
  intro failed
  rcases deriveTarget_ordinary state with
    ⟨target, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Derive targets instantiate the generic strict delimited-element boundary. -/
theorem deriveTarget_elementTotalityContract :
    ElementTotalityContract deriveTarget := {
  validFor := deriveTarget_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := deriveTarget_preservesTokenWindow
  cursorLtOnSuccess := fun parsed =>
    (deriveTarget_ok_state_shape parsed).choose_spec.2.2.2
  invariantFree := fun input _ error =>
    deriveTarget_ne_invariant input error
}

end Solcore.Syntax.Parser
