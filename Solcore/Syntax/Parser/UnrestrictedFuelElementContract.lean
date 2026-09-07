import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Fuel-aware ordinary execution on arbitrary states. Only successful child
end indices and strict cursor progress are constrained; no validity, token,
source, diagnostic, or rejected-state frame is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

structure UnrestrictedFuelElementContract {α : Type}
    (element : Parser α) (fuel : Nat) : Prop where
  endIndexOnSuccess : ∀ {input next : State} {value : α},
    element input = .ok value next → next.window.endIndex = input.window.endIndex
  cursorLtOnSuccess : ∀ {input next : State} {value : α},
    element input = .ok value next → input.cursor < next.cursor
  ordinary : ∀ input, input.remainingCount < fuel →
    (∃ value next, element input = .ok value next) ∨
      (∃ failure next, element input = .reject failure next)

theorem remainingCount_le_of_endIndex_eq {input next : State}
    (endIndexEq : next.window.endIndex = input.window.endIndex)
    (cursorLe : input.cursor ≤ next.cursor) : next.remainingCount ≤ input.remainingCount := by
  simp only [State.remainingCount, endIndexEq]
  omega

theorem remainingCount_lt_of_endIndex_eq {input next : State} {fuel : Nat}
    (endIndexEq : next.window.endIndex = input.window.endIndex)
    (cursorLe : input.cursor ≤ next.cursor) (adequate : input.remainingCount < fuel) :
    next.remainingCount < fuel :=
  Nat.lt_of_le_of_lt (remainingCount_le_of_endIndex_eq endIndexEq cursorLe) adequate

/-- A real token, not a global state invariant, pays for one recursive unit. -/
theorem acceptToken_remainingCount_lt_of_success {input next : State} {token : Token} {fuel : Nat}
    (expected : ParseExpectation) (context : ParseContext) (accepts : TokenKind → Bool)
    (result : acceptToken expected context accepts input = .ok token next)
    (adequate : input.remainingCount < fuel + 1) : next.remainingCount < fuel := by
  rcases acceptToken_ok_state_shape expected context accepts result with ⟨found, rfl⟩
  have beforeEnd := State.cursor_lt_endIndex_of_peek?_eq_some found
  simp only [State.remainingCount] at adequate ⊢
  omega

theorem symbol_remainingCount_lt_of_success {input next : State} {token : Token} {fuel : Nat}
    (value : Symbol) (context : ParseContext)
    (result : symbol value context input = .ok token next)
    (adequate : input.remainingCount < fuel + 1) : next.remainingCount < fuel :=
  acceptToken_remainingCount_lt_of_success (.symbol value) context (· == .symbol value) result adequate

theorem keyword_remainingCount_lt_of_success {input next : State} {token : Token} {fuel : Nat}
    (value : HardKeyword) (context : ParseContext)
    (result : keyword value context input = .ok token next)
    (adequate : input.remainingCount < fuel + 1) : next.remainingCount < fuel :=
  acceptToken_remainingCount_lt_of_success (.keyword value) context (· == .keyword value) result adequate

theorem contextual_remainingCount_lt_of_success {input next : State} {token : Token} {fuel : Nat}
    (value : ContextualKeyword) (context : ParseContext)
    (result : contextual value context input = .ok token next)
    (adequate : input.remainingCount < fuel + 1) : next.remainingCount < fuel :=
  acceptToken_remainingCount_lt_of_success (.contextual value) context (·.isContextual value) result adequate

namespace UnrestrictedFuelElementContract

theorem weaken {α : Type} {element : Parser α} {smallFuel largeFuel : Nat}
    (contract : UnrestrictedFuelElementContract element largeFuel)
    (bound : smallFuel ≤ largeFuel) : UnrestrictedFuelElementContract element smallFuel where
  endIndexOnSuccess := contract.endIndexOnSuccess
  cursorLtOnSuccess := contract.cursorLtOnSuccess
  ordinary input adequate := contract.ordinary input (Nat.lt_of_lt_of_le adequate bound)

theorem ne_invariant {α : Type} {element : Parser α} {fuel : Nat}
    (contract : UnrestrictedFuelElementContract element fuel)
    (input : State) (adequate : input.remainingCount < fuel) (error : ParserInvariantError) :
    element input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem remainingCount_le_of_success {α : Type} {element : Parser α} {fuel : Nat}
    (contract : UnrestrictedFuelElementContract element fuel)
    {input next : State} {value : α} (result : element input = .ok value next) :
    next.remainingCount ≤ input.remainingCount :=
  remainingCount_le_of_endIndex_eq (contract.endIndexOnSuccess result)
    (Nat.le_of_lt (contract.cursorLtOnSuccess result))

theorem remainingCount_lt_of_success {α : Type} {element : Parser α} {fuel bound : Nat}
    (contract : UnrestrictedFuelElementContract element fuel)
    {input next : State} {value : α} (result : element input = .ok value next)
    (adequate : input.remainingCount < bound) : next.remainingCount < bound :=
  Nat.lt_of_le_of_lt (contract.remainingCount_le_of_success result) adequate

end UnrestrictedFuelElementContract

end Solcore.Syntax.Parser
