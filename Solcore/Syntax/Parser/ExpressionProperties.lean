import Solcore.Syntax.Parser.Expression
import Solcore.Syntax.CollectionValidity

/-! Provenance and state contracts for canonical Core expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ExpressionInternals

/-- Prefix unary scanning preserves operator spans and parser-state validity. -/
theorem unaryOperators_validFor :
    ∀ fuel operatorsRev input,
      input.ValidFor →
      List.ValidFor Located.ValidFor input.file operatorsRev →
      (unaryOperators fuel operatorsRev input).ValidFor input
        (List.ValidFor Located.ValidFor) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro operatorsRev input inputValid operatorsValid
      unfold unaryOperators
      cases found : input.peek? with
      | none =>
          exact ⟨by
            intro operator member
            exact operatorsValid operator (by simpa using member),
            inputValid, rfl⟩
      | some token =>
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded]
              exact ⟨by
                intro operator member
                exact operatorsValid operator (by simpa using member),
                inputValid, rfl⟩
          | some operator =>
              simp only [decoded]
              have advanced : input.advance? = some (token,
                  { input with cursor := input.cursor + 1 }) := by
                unfold State.advance?
                rw [found]
                rfl
              have nextValid := inputValid.advance?_validFor advanced
              have tokenValid := inputValid.peek?_span_validFor found
              have accumulatedValid : List.ValidFor Located.ValidFor
                  ({ input with cursor := input.cursor + 1 } : State).file
                  ({ span := token.span, value := operator } ::
                    operatorsRev) := by
                intro retained member
                rcases List.mem_cons.mp member with rfl | member
                · simpa only [Located.ValidFor] using tokenValid
                · simpa using operatorsValid retained member
              exact (inductionHypothesis
                ({ span := token.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 }
                nextValid accumulatedValid).of_file_eq rfl

/-- Prefix unary scanning preserves the complete immutable token window. -/
theorem unaryOperators_preservesTokenWindow (fuel : Nat)
    (operatorsRev : List (Located UnaryOp)) :
    Parser.PreservesTokenWindow (unaryOperators fuel operatorsRev) := by
  intro input
  induction fuel generalizing operatorsRev input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold unaryOperators
      cases found : input.peek? with
      | none => exact ⟨rfl, rfl⟩
      | some token =>
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded]
              exact ⟨rfl, rfl⟩
          | some operator =>
              simp only [decoded]
              exact (inductionHypothesis
                ({ span := token.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 }).trans ⟨rfl, rfl⟩

theorem unaryOperators_preservesTokensOnSuccess (fuel : Nat)
    (operatorsRev : List (Located UnaryOp)) :
    Parser.PreservesTokensOnSuccess (unaryOperators fuel operatorsRev) :=
  (unaryOperators_preservesTokenWindow fuel
    operatorsRev).preservesTokensOnSuccess

/-- Prefix unary scanning never rewinds its input cursor. -/
theorem unaryOperators_cursorMonotoneOnSuccess (fuel : Nat)
    (operatorsRev : List (Located UnaryOp)) :
    Parser.CursorMonotoneOnSuccess (unaryOperators fuel operatorsRev) := by
  intro input operators next parsed
  induction fuel generalizing operatorsRev input with
  | zero => contradiction
  | succ fuel inductionHypothesis =>
      unfold unaryOperators at parsed
      cases found : input.peek? with
      | none =>
          simp only [found] at parsed
          cases parsed
          exact Nat.le_refl _
      | some token =>
          simp only [found] at parsed
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded] at parsed
              cases parsed
              exact Nat.le_refl _
          | some operator =>
              simp only [decoded] at parsed
              exact Nat.le_trans (by simp)
                (inductionHypothesis
                  ({ span := token.span, value := operator } :: operatorsRev)
                  { input with cursor := input.cursor + 1 } parsed)

end ExpressionInternals
end Solcore.Syntax.Parser
