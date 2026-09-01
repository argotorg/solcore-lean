import Solcore.Syntax.DeclarativeCoreExpressionUnaryLeftOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionBinaryLayerSoundnessProperties

/-!
Executable ordinary-success and exact-rejection bridges for one Core
left-associative binary precedence layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Every executable left-associative tail success follows the maximal
operator/operand sequence at the selected precedence. -/
theorem leftAssociativeTail_success_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (precedence : Nat) :
    ∀ fuel left input expression output,
      leftAssociativeTail operand precedence fuel left input =
          .ok expression output →
        DeclarativeGrammar.LeftAssociativeTailParses operandOrdinary
          precedence input.declarativeRemainder left expression
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input expression output result
      simp [leftAssociativeTail] at result
  | succ fuel inductionHypothesis =>
      intro left input expression output result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [leftAssociativeTail, operatorResult] at result
          cases result
          exact .done (binaryAtPrecedence?_none_absentAt operatorResult)
      | some operator =>
          let afterOperator := { input with cursor := input.cursor + 1 }
          have consumedResult :
              consumeBinary operator input = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator input
          cases operandResult : operand afterOperator with
          | invariant error =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | reject failure rejected =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | ok right afterRight =>
              simp only [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
              have tailParsed := inductionHypothesis
                (binaryNode left operator right) afterRight expression output
                  result
              apply DeclarativeGrammar.LeftAssociativeTailParses.next
                (consumeBinary_success_sound_of_binaryAtPrecedence?_some
                  operatorResult consumedResult)
                (operandSuccessSound operandResult)
              simpa only [binaryNode, DeclarativeGrammar.binaryNode] using
                tailParsed

/-- Every executable left-associative tail rejection records the exact first
rejected right operand or a rejection in a later suffix. -/
theorem leftAssociativeTail_reject_ordinary_sound
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
    ∀ fuel left input rejected failure,
      leftAssociativeTail operand precedence fuel left input =
          .reject failure rejected →
        DeclarativeGrammar.LeftAssociativeTailRejects operandOrdinary
          operandRejects precedence input.declarativeRemainder left
            rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input rejected failure result
      simp [leftAssociativeTail] at result
  | succ fuel inductionHypothesis =>
      intro left input rejected failure result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp [leftAssociativeTail, operatorResult] at result
      | some operator =>
          let afterOperator := { input with cursor := input.cursor + 1 }
          have consumedResult :
              consumeBinary operator input = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator input
          have operatorParsed :=
            consumeBinary_success_sound_of_binaryAtPrecedence?_some
              operatorResult consumedResult
          cases operandResult : operand afterOperator with
          | invariant error =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | reject operandFailure operandRejected =>
              simp only [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
              cases result
              exact .rightRejected operatorParsed
                (operandRejectSound operandResult)
          | ok right afterRight =>
              simp only [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
              have tailRejected := inductionHypothesis
                (binaryNode left operator right) afterRight rejected failure
                  result
              apply DeclarativeGrammar.LeftAssociativeTailRejects.laterRejected
                operatorParsed (operandSuccessSound operandResult)
              simpa only [binaryNode, DeclarativeGrammar.binaryNode] using
                tailRejected

/-- Every executable complete left-associative success follows its ordinary
first operand and maximal operator tail. -/
theorem leftAssociative_success_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (precedence : Nat) {input output : State} {expression : Expr}
    (result : leftAssociative operand precedence input =
      .ok expression output) :
    DeclarativeGrammar.LeftAssociativeOrdinaryParses operandOrdinary
      precedence input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold leftAssociative at result
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at result
  | reject failure rejected => simp [operandResult] at result
  | ok left afterLeft =>
      simp only [operandResult] at result
      exact ⟨left, afterLeft.declarativeRemainder,
        operandSuccessSound operandResult,
        leftAssociativeTail_success_ordinary_sound operand operandOrdinary
          operandSuccessSound precedence (afterLeft.remainingCount + 1) left
            afterLeft expression output result⟩

/-- Every executable complete left-associative rejection is the first operand
rejection or an exact rejection in its maximal operator tail. -/
theorem leftAssociative_reject_ordinary_sound
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
    (result : leftAssociative operand precedence input =
      .reject failure rejected) :
    DeclarativeGrammar.LeftAssociativeRejects operandOrdinary operandRejects
      precedence input.declarativeRemainder rejected.declarativeRemainder := by
  unfold leftAssociative at result
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at result
  | reject operandFailure operandRejected =>
      simp only [operandResult] at result
      cases result
      exact .firstRejected (operandRejectSound operandResult)
  | ok left afterLeft =>
      simp only [operandResult] at result
      exact .tailRejected (operandSuccessSound operandResult)
        (leftAssociativeTail_reject_ordinary_sound operand operandOrdinary
          operandRejects operandSuccessSound operandRejectSound precedence
            (afterLeft.remainingCount + 1) left afterLeft rejected failure
              result)

/-- Package both executable outcomes for one supplied operand bridge. -/
theorem leftAssociative_ordinaryOutcome_sound
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
      leftAssociative operand precedence input = .ok expression output →
        DeclarativeGrammar.LeftAssociativeOrdinaryParses operandOrdinary
          precedence input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      leftAssociative operand precedence input = .reject failure rejected →
        DeclarativeGrammar.LeftAssociativeRejects operandOrdinary
          operandRejects precedence input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨leftAssociative_success_ordinary_sound operand operandOrdinary
      operandSuccessSound precedence,
    leftAssociative_reject_ordinary_sound operand operandOrdinary
      operandRejects operandSuccessSound operandRejectSound precedence⟩

/-- Lift a deterministic operand contract through one precedence layer. -/
theorem leftAssociative_ordinaryOutcomeSpec
    {operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec operandOrdinary
      operandRejects) (precedence : Nat) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LeftAssociativeOrdinaryParses operandOrdinary
        precedence)
      (DeclarativeGrammar.LeftAssociativeRejects operandOrdinary
        operandRejects precedence) :=
  DeclarativeGrammar.leftAssociativeDeterministicOutcomeSpec outcomes
    precedence

end Solcore.Syntax.Parser.ExpressionInternals
