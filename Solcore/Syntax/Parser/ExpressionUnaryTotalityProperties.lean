import Solcore.Syntax.Parser.ExpressionProperties
import Solcore.Syntax.Parser.InvariantFreeProperties

/-! Fuel adequacy and totality for prefix unary-operator scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- More fuel than remaining tokens makes unary-operator scanning terminate. -/
theorem unaryOperators_exists_ok_of_remainingCount_lt :
    ∀ fuel operatorsRev state, state.remainingCount < fuel →
      ∃ operators final,
        unaryOperators fuel operatorsRev state = .ok operators final := by
  intro fuel
  induction fuel with
  | zero =>
      intro operatorsRev state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro operatorsRev state adequate
      unfold unaryOperators
      cases found : state.peek? with
      | none => exact ⟨_, _, rfl⟩
      | some token =>
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded]
              exact ⟨_, _, rfl⟩
          | some operator =>
              simp only [decoded]
              apply inductionHypothesis
                ({ span := token.span, value := operator } :: operatorsRev)
                { state with cursor := state.cursor + 1 }
              have cursorBeforeEnd :=
                State.cursor_lt_endIndex_of_peek?_eq_some found
              simp only [State.remainingCount] at adequate ⊢
              omega

/-- Adequately fueled unary-operator scanning has an ordinary success result. -/
theorem unaryOperators_ordinary_of_remainingCount_lt
    (fuel : Nat) (operatorsRev : List (Located UnaryOp)) (state : State)
    (adequate : state.remainingCount < fuel) :
    (∃ operators final,
      unaryOperators fuel operatorsRev state = .ok operators final) ∨
      (∃ failure final,
        unaryOperators fuel operatorsRev state = .reject failure final) :=
  Or.inl (unaryOperators_exists_ok_of_remainingCount_lt fuel operatorsRev
    state adequate)

/-- Adequately fueled unary-operator scanning cannot expose an invariant. -/
theorem unaryOperators_ne_invariant_of_remainingCount_lt
    (fuel : Nat) (operatorsRev : List (Located UnaryOp)) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    unaryOperators fuel operatorsRev state ≠ .invariant error := by
  intro failed
  rcases unaryOperators_exists_ok_of_remainingCount_lt fuel operatorsRev state
      adequate with ⟨operators, final, result⟩
  rw [result] at failed
  contradiction

/-- The production fuel selected by unary-expression parsing is adequate. -/
theorem unaryOperators_production_exists_ok
    (operatorsRev : List (Located UnaryOp)) (state : State) :
    ∃ operators final,
      unaryOperators (state.remainingCount + 1) operatorsRev state =
        .ok operators final :=
  unaryOperators_exists_ok_of_remainingCount_lt
    (state.remainingCount + 1) operatorsRev state (by omega)

/-- Production-fueled unary-operator scanning is ordinary on every input. -/
theorem unaryOperators_production_ordinary
    (operatorsRev : List (Located UnaryOp)) :
    Parser.Ordinary (fun state =>
      unaryOperators (state.remainingCount + 1) operatorsRev state) := by
  intro state
  exact Or.inl (unaryOperators_production_exists_ok operatorsRev state)

/-- Production-fueled scanning is invariant-free on valid parser states. -/
theorem unaryOperators_production_invariantFreeOnValid
    (operatorsRev : List (Located UnaryOp)) :
    Parser.InvariantFreeOnValid (fun state =>
      unaryOperators (state.remainingCount + 1) operatorsRev state) :=
  (unaryOperators_production_ordinary operatorsRev).invariantFreeOnValid

/-- Production-fueled unary-operator scanning cannot exhaust its fuel. -/
theorem unaryOperators_production_ne_invariant
    (operatorsRev : List (Located UnaryOp)) (state : State)
    (error : ParserInvariantError) :
    unaryOperators (state.remainingCount + 1) operatorsRev state ≠
      .invariant error :=
  (unaryOperators_production_ordinary operatorsRev).ne_invariant state error

end Solcore.Syntax.Parser.ExpressionInternals
