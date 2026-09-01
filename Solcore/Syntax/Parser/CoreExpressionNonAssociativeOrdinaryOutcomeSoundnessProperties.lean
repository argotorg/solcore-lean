import Solcore.Syntax.DeclarativeCoreExpressionNonAssociativeOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionBinaryLayerSoundnessProperties

/-!
Executable ordinary-success and exact-rejection bridges for one Core
non-associative binary precedence layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Every executable non-associative success is either an operator-absent
plain operand or one exact binary node. -/
theorem nonAssociative_success_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (precedence : Nat) {input output : State} {expression : Expr}
    (result : nonAssociative operand precedence input =
      .ok expression output) :
    DeclarativeGrammar.NonAssociativeOrdinaryParses operandOrdinary precedence
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold nonAssociative at result
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at result
  | reject failure rejected => simp [leftResult] at result
  | ok left afterLeft =>
      simp only [leftResult] at result
      cases operatorResult : binaryAtPrecedence? afterLeft precedence with
      | none =>
          simp only [operatorResult] at result
          cases result
          exact .plain (operandSuccessSound leftResult)
            (binaryAtPrecedence?_none_absentAt operatorResult)
      | some operator =>
          let afterOperator := { afterLeft with
            cursor := afterLeft.cursor + 1 }
          have consumedResult :
              consumeBinary operator afterLeft = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator afterLeft
          cases rightResult : operand afterOperator with
          | invariant error =>
              simp [operatorResult, consumedResult, rightResult] at result
          | reject failure rejected =>
              simp [operatorResult, consumedResult, rightResult] at result
          | ok right final =>
              simp only [operatorResult, consumedResult, rightResult] at result
              cases result
              have parsed : DeclarativeGrammar.NonAssociativeOrdinaryParses
                  operandOrdinary precedence input.declarativeRemainder
                    (DeclarativeGrammar.binaryNode left operator right)
                      output.declarativeRemainder :=
                .binary (operandSuccessSound leftResult)
                  (consumeBinary_success_sound_of_binaryAtPrecedence?_some
                    operatorResult consumedResult)
                  (operandSuccessSound rightResult)
              simpa only [binaryNode, DeclarativeGrammar.binaryNode] using
                parsed

/-- Every executable non-associative rejection is the first operand or the
right operand after an exact selected operator. -/
theorem nonAssociative_reject_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (operandRejectSound : ∀ {input rejected : State} {failure : Failure},
      operand input = .reject failure rejected →
        operandRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (precedence : Nat) {input rejected : State} {failure : Failure}
    (result : nonAssociative operand precedence input =
      .reject failure rejected) :
    DeclarativeGrammar.NonAssociativeRejects operandOrdinary operandRejects
      precedence input.declarativeRemainder rejected.declarativeRemainder := by
  unfold nonAssociative at result
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at result
  | reject operandFailure operandRejected =>
      simp only [leftResult] at result
      cases result
      exact .firstRejected (operandRejectSound leftResult)
  | ok left afterLeft =>
      simp only [leftResult] at result
      cases operatorResult : binaryAtPrecedence? afterLeft precedence with
      | none => simp [operatorResult] at result
      | some operator =>
          let afterOperator := { afterLeft with
            cursor := afterLeft.cursor + 1 }
          have consumedResult :
              consumeBinary operator afterLeft = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator afterLeft
          cases rightResult : operand afterOperator with
          | invariant error =>
              simp [operatorResult, consumedResult, rightResult] at result
          | ok right final =>
              simp [operatorResult, consumedResult, rightResult] at result
          | reject rightFailure rightRejected =>
              simp only [operatorResult, consumedResult, rightResult] at result
              cases result
              exact .rightRejected (operandSuccessSound leftResult)
                (consumeBinary_success_sound_of_binaryAtPrecedence?_some
                  operatorResult consumedResult)
                (operandRejectSound rightResult)

/-- Package both executable non-associative outcomes. -/
theorem nonAssociative_ordinaryOutcome_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (operandRejectSound : ∀ {input rejected : State} {failure : Failure},
      operand input = .reject failure rejected →
        operandRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (precedence : Nat) :
    (∀ {input output : State} {expression : Expr},
      nonAssociative operand precedence input = .ok expression output →
        DeclarativeGrammar.NonAssociativeOrdinaryParses operandOrdinary
          precedence input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      nonAssociative operand precedence input = .reject failure rejected →
        DeclarativeGrammar.NonAssociativeRejects operandOrdinary operandRejects
          precedence input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨nonAssociative_success_ordinary_sound operand operandOrdinary
      operandSuccessSound precedence,
    nonAssociative_reject_ordinary_sound operand operandOrdinary operandRejects
      operandSuccessSound operandRejectSound precedence⟩

/-- Lift a deterministic operand contract through one non-associative layer. -/
theorem nonAssociative_ordinaryOutcomeSpec
    {operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec operandOrdinary
      operandRejects) (precedence : Nat) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.NonAssociativeOrdinaryParses operandOrdinary
        precedence)
      (DeclarativeGrammar.NonAssociativeRejects operandOrdinary operandRejects
        precedence) :=
  DeclarativeGrammar.nonAssociativeDeterministicOutcomeSpec outcomes precedence

end Solcore.Syntax.Parser.ExpressionInternals
