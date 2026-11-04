import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.ExpressionProofs
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Parser.Internal.ParameterTotality
import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Parser.Internal.Basics

/-!
Totality of the parsers of expressions: on valid input they make progress and end in an
ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionNonAssociativeTotalityProperties
/-! Fuel-aware totality for non-associative expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem nonAssociative_ordinary_of_elementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < operandFuel) :
    (∃ expression next,
      nonAssociative operand precedence input = .ok expression next) ∨
    (∃ failure next,
      nonAssociative operand precedence input = .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨left, next, leftResult⟩ | ⟨failure, rejected, leftResult⟩
  · have leftValid := contract.validFor input inputValid
    rw [leftResult] at leftValid
    have leftWindow := contract.preservesTokenWindow input
    rw [leftResult] at leftWindow
    have nextAdequate : next.remainingCount < operandFuel :=
      remainingCount_lt_of_cursor_le leftWindow.2
        (Nat.le_of_lt (contract.cursorLtOnSuccess leftResult)) adequate
    cases operatorResult : binaryAtPrecedence? next precedence with
    | none =>
        exact Or.inl ⟨left, next, by
          simp only [nonAssociative, leftResult, operatorResult]⟩
    | some operator =>
        rcases binaryAtPrecedence?_some_state_shape operatorResult with
          ⟨_operatorToken, _operatorFound, _decoded, _precedence, operatorBound⟩
        have operatorPositive := BinaryOp.tokenCount_pos operator.value
        let afterOperator := { next with cursor := next.cursor + operator.value.tokenCount }
        have consumedResult :
            consumeBinary operator next = .ok () afterOperator := by
          exact consumeBinary_ok_state_shape operator next
        have consumedValid := consumeBinary_reply_validFor operator
          leftValid.2.1 operatorBound
        rw [consumedResult] at consumedValid
        have afterOperatorAdequate :
            afterOperator.remainingCount < operandFuel :=
          remainingCount_lt_of_cursor_le (by rfl)
            (by dsimp [afterOperator]; omega) nextAdequate
        rcases contract.ordinary afterOperator consumedValid.2.1
            afterOperatorAdequate with
          ⟨right, final, rightResult⟩ |
          ⟨failure, rejected, rightResult⟩
        · exact Or.inl ⟨binaryNode left operator right, final, by
            simp only [nonAssociative, leftResult, operatorResult,
              consumedResult, rightResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [nonAssociative, leftResult, operatorResult,
              consumedResult, rightResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [nonAssociative, leftResult]⟩

theorem nonAssociative_ne_invariant_of_elementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < operandFuel)
    (error : ParserInvariantError) :
    nonAssociative operand precedence input ≠ .invariant error := by
  intro failed
  rcases nonAssociative_ordinary_of_elementFuel operand operandFuel
      precedence contract input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionConditionalTotalityProperties
/-! Fuel-aware totality for conditional-expression parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem conditionalTail_ordinary_of_fuels
    (nested alternative : Parser Expr)
    (nestedFuel alternativeFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (alternativeContract :
      FuelElementTotalityContract alternative alternativeFuel) :
    ∀ loopFuel headsRev condition input,
      input.ValidFor →
      input.remainingCount < loopFuel →
      input.remainingCount < nestedFuel + 1 →
      input.remainingCount < alternativeFuel →
      (∃ expression next,
        conditionalTail nested alternative loopFuel headsRev condition input =
          .ok expression next) ∨
      (∃ failure next,
        conditionalTail nested alternative loopFuel headsRev condition input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro headsRev condition input inputValid loopAdequate
        nestedAdequate alternativeAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro headsRev condition input inputValid loopAdequate
        nestedAdequate alternativeAdequate
      by_cases questionPresent : isSymbol input .question
      · rcases (symbol_ordinary .question .expression) input with
          ⟨question, afterQuestion, questionResult⟩ |
          ⟨failure, rejected, questionResult⟩
        · have questionValid := symbol_validFor .question .expression
            input inputValid
          rw [questionResult] at questionValid
          have questionWindow := symbol_preservesTokenWindow
            .question .expression input
          rw [questionResult] at questionWindow
          have questionProgress : input.cursor < afterQuestion.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .question) .expression
              (· == .symbol .question) questionResult
          have afterQuestionNestedAdequate :
              afterQuestion.remainingCount < nestedFuel :=
            remainingCount_lt_after_strict_progress questionValid.2.1
              questionWindow.2 questionProgress nestedAdequate
          rcases nestedContract.ordinary afterQuestion questionValid.2.1
              afterQuestionNestedAdequate with
            ⟨thenBranch, afterThen, thenResult⟩ |
            ⟨failure, rejected, thenResult⟩
          · have thenValid := nestedContract.validFor afterQuestion
                questionValid.2.1
            rw [thenResult] at thenValid
            have thenWindow := nestedContract.preservesTokenWindow
              afterQuestion
            rw [thenResult] at thenWindow
            have thenProgress := nestedContract.cursorLtOnSuccess thenResult
            rcases (symbol_ordinary .colon .expression) afterThen with
              ⟨colon, afterColon, colonResult⟩ |
              ⟨failure, rejected, colonResult⟩
            · have colonValid := symbol_validFor .colon .expression
                  afterThen thenValid.2.1
              rw [colonResult] at colonValid
              have colonWindow := symbol_preservesTokenWindow
                .colon .expression afterThen
              rw [colonResult] at colonWindow
              have colonProgress : afterThen.cursor < afterColon.cursor :=
                acceptToken_cursor_lt_onSuccess (.symbol .colon) .expression
                  (· == .symbol .colon) colonResult
              have afterColonWindow : afterColon.window = input.window :=
                colonWindow.2.trans
                  (thenWindow.2.trans questionWindow.2)
              have inputBeforeColon : input.cursor ≤ afterColon.cursor :=
                Nat.le_of_lt (Nat.lt_trans questionProgress
                  (Nat.lt_trans thenProgress colonProgress))
              have afterColonAlternativeAdequate :
                  afterColon.remainingCount < alternativeFuel :=
                remainingCount_lt_of_cursor_le afterColonWindow
                  inputBeforeColon alternativeAdequate
              rcases alternativeContract.ordinary afterColon colonValid.2.1
                  afterColonAlternativeAdequate with
                ⟨nextCondition, next, alternativeResult⟩ |
                ⟨failure, rejected, alternativeResult⟩
              · have alternativeValid := alternativeContract.validFor
                    afterColon colonValid.2.1
                rw [alternativeResult] at alternativeValid
                have alternativeWindow :=
                  alternativeContract.preservesTokenWindow afterColon
                rw [alternativeResult] at alternativeWindow
                have alternativeProgress :=
                  alternativeContract.cursorLtOnSuccess alternativeResult
                have nextWindow : next.window = input.window :=
                  alternativeWindow.2.trans afterColonWindow
                have inputProgress : input.cursor < next.cursor :=
                  Nat.lt_trans questionProgress
                    (Nat.lt_trans thenProgress
                      (Nat.lt_trans colonProgress alternativeProgress))
                have nextLoopAdequate :
                    next.remainingCount < loopFuel :=
                  remainingCount_lt_after_strict_progress
                    alternativeValid.2.1 nextWindow inputProgress
                    loopAdequate
                have nextNestedAdequate :
                    next.remainingCount < nestedFuel + 1 :=
                  remainingCount_lt_of_cursor_le nextWindow
                    (Nat.le_of_lt inputProgress) nestedAdequate
                have nextAlternativeAdequate :
                    next.remainingCount < alternativeFuel :=
                  remainingCount_lt_of_cursor_le nextWindow
                    (Nat.le_of_lt inputProgress) alternativeAdequate
                rcases inductionHypothesis ({
                      condition
                      question := question.span
                      thenBranch
                      colon := colon.span
                    } :: headsRev) nextCondition next alternativeValid.2.1
                    nextLoopAdequate nextNestedAdequate
                    nextAlternativeAdequate with
                  ⟨expression, final, recursiveResult⟩ |
                  ⟨failure, rejected, recursiveResult⟩
                · exact Or.inl ⟨expression, final, by
                    simp only [conditionalTail, questionPresent, ↓reduceIte,
                      questionResult, thenResult, colonResult,
                      alternativeResult]
                    exact recursiveResult⟩
                · exact Or.inr ⟨failure, rejected, by
                    simp only [conditionalTail, questionPresent, ↓reduceIte,
                      questionResult, thenResult, colonResult,
                      alternativeResult]
                    exact recursiveResult⟩
              · exact Or.inr ⟨failure, rejected, by
                  simp only [conditionalTail, questionPresent, ↓reduceIte,
                    questionResult, thenResult, colonResult,
                    alternativeResult]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [conditionalTail, questionPresent, ↓reduceIte,
                  questionResult, thenResult, colonResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [conditionalTail, questionPresent, ↓reduceIte,
                questionResult, thenResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [conditionalTail, questionPresent, ↓reduceIte,
              questionResult]⟩
      · have questionAbsent : isSymbol input .question = false := by
          cases found : isSymbol input .question with
          | false => rfl
          | true => exact False.elim (questionPresent found)
        exact Or.inl ⟨headsRev.foldl foldConditionalHead condition,
          input, by
            simp only [conditionalTail, questionAbsent, Bool.false_eq_true,
              ↓reduceIte]⟩

theorem conditionalTail_ne_invariant_of_fuels
    (nested alternative : Parser Expr)
    (nestedFuel alternativeFuel loopFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (alternativeContract :
      FuelElementTotalityContract alternative alternativeFuel)
    (headsRev : List ConditionalHead) (condition : Expr)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (alternativeAdequate : input.remainingCount < alternativeFuel)
    (error : ParserInvariantError) :
    conditionalTail nested alternative loopFuel headsRev condition input ≠
      .invariant error := by
  intro failed
  rcases conditionalTail_ordinary_of_fuels nested alternative nestedFuel
      alternativeFuel nestedContract alternativeContract loopFuel headsRev
      condition input inputValid loopAdequate nestedAdequate
      alternativeAdequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem conditional_ordinary_of_elementFuels
    (nested alternative : Parser Expr)
    (nestedFuel alternativeFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (alternativeContract :
      FuelElementTotalityContract alternative alternativeFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (alternativeAdequate : input.remainingCount < alternativeFuel) :
    (∃ expression next,
      conditional nested alternative input = .ok expression next) ∨
    (∃ failure next,
      conditional nested alternative input = .reject failure next) := by
  rcases alternativeContract.ordinary input inputValid
      alternativeAdequate with
    ⟨condition, next, alternativeResult⟩ |
    ⟨failure, rejected, alternativeResult⟩
  · have conditionValid := alternativeContract.validFor input inputValid
    rw [alternativeResult] at conditionValid
    have conditionWindow := alternativeContract.preservesTokenWindow input
    rw [alternativeResult] at conditionWindow
    have conditionProgress :=
      alternativeContract.cursorLtOnSuccess alternativeResult
    have nextNestedAdequate : next.remainingCount < nestedFuel + 1 :=
      remainingCount_lt_of_cursor_le conditionWindow.2
        (Nat.le_of_lt conditionProgress) nestedAdequate
    have nextAlternativeAdequate :
        next.remainingCount < alternativeFuel :=
      remainingCount_lt_of_cursor_le conditionWindow.2
        (Nat.le_of_lt conditionProgress) alternativeAdequate
    rcases conditionalTail_ordinary_of_fuels nested alternative nestedFuel
        alternativeFuel nestedContract alternativeContract
        (next.remainingCount + 1) [] condition next conditionValid.2.1
        (by omega) nextNestedAdequate nextAlternativeAdequate with
      ⟨expression, final, tailResult⟩ |
      ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨expression, final, by
        simp only [conditional, alternativeResult]
        exact tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [conditional, alternativeResult]
        exact tailResult⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [conditional, alternativeResult]⟩

theorem conditional_ne_invariant_of_elementFuels
    (nested alternative : Parser Expr)
    (nestedFuel alternativeFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (alternativeContract :
      FuelElementTotalityContract alternative alternativeFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (alternativeAdequate : input.remainingCount < alternativeFuel)
    (error : ParserInvariantError) :
    conditional nested alternative input ≠ .invariant error := by
  intro failed
  rcases conditional_ordinary_of_elementFuels nested alternative nestedFuel
      alternativeFuel nestedContract alternativeContract input inputValid
      nestedAdequate alternativeAdequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionLeftAssociativeTotalityProperties
/-! Fuel-aware totality for left-associative expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/--
The loop fuel decreases after a recognized operator, while the independent
operand fuel remains adequate because every successful operand is strict.
-/
theorem leftAssociativeTail_ordinary_of_fuels
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel) :
    ∀ loopFuel left input,
      input.ValidFor →
      input.remainingCount < loopFuel →
      input.remainingCount < operandFuel →
      (∃ expression next,
        leftAssociativeTail operand precedence loopFuel left input =
          .ok expression next) ∨
      (∃ failure next,
        leftAssociativeTail operand precedence loopFuel left input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro left input inputValid loopAdequate operandAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro left input inputValid loopAdequate operandAdequate
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          exact Or.inl ⟨left, input, by
            simp only [leftAssociativeTail, operatorResult]⟩
      | some operator =>
          rcases binaryAtPrecedence?_some_state_shape operatorResult with
            ⟨_operatorToken, _operatorFound, _decoded, _precedence, operatorBound⟩
          have operatorPositive := BinaryOp.tokenCount_pos operator.value
          let afterOperator := { input with cursor := input.cursor + operator.value.tokenCount }
          have consumedResult :
              consumeBinary operator input = .ok () afterOperator := by
            exact consumeBinary_ok_state_shape operator input
          have consumedValid := consumeBinary_reply_validFor operator
            inputValid operatorBound
          rw [consumedResult] at consumedValid
          have afterOperatorAdequate :
              afterOperator.remainingCount < operandFuel :=
            remainingCount_lt_of_cursor_le (by rfl)
              (by dsimp [afterOperator]; omega)
              operandAdequate
          rcases contract.ordinary afterOperator consumedValid.2.1
              afterOperatorAdequate with
            ⟨right, next, operandResult⟩ |
            ⟨failure, rejected, operandResult⟩
          · have rightValid := contract.validFor afterOperator
              consumedValid.2.1
            rw [operandResult] at rightValid
            have rightWindow := contract.preservesTokenWindow afterOperator
            rw [operandResult] at rightWindow
            have rightProgress := contract.cursorLtOnSuccess operandResult
            have nextWindow : next.window = input.window := by
              exact rightWindow.2
            have inputProgress : input.cursor < next.cursor := by
              exact Nat.lt_trans (by simp only [afterOperator]; omega) rightProgress
            have nextLoopAdequate :
                next.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress rightValid.2.1
                nextWindow inputProgress loopAdequate
            have nextOperandAdequate :
                next.remainingCount < operandFuel :=
              remainingCount_lt_of_cursor_le nextWindow
                (Nat.le_of_lt inputProgress) operandAdequate
            rcases inductionHypothesis (binaryNode left operator right) next
                rightValid.2.1 nextLoopAdequate nextOperandAdequate with
              ⟨expression, final, recursiveResult⟩ |
              ⟨failure, rejected, recursiveResult⟩
            · exact Or.inl ⟨expression, final, by
                simp only [leftAssociativeTail, operatorResult,
                  consumedResult, operandResult]
                exact recursiveResult⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [leftAssociativeTail, operatorResult,
                  consumedResult, operandResult]
                exact recursiveResult⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [leftAssociativeTail, operatorResult,
                consumedResult, operandResult]⟩

theorem leftAssociativeTail_ne_invariant_of_fuels
    (operand : Parser Expr) (operandFuel precedence loopFuel : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (left : Expr) (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (operandAdequate : input.remainingCount < operandFuel)
    (error : ParserInvariantError) :
    leftAssociativeTail operand precedence loopFuel left input ≠
      .invariant error := by
  intro failed
  rcases leftAssociativeTail_ordinary_of_fuels operand operandFuel
      precedence contract loopFuel left input inputValid loopAdequate
      operandAdequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- One complete left-associative layer inherits its operand fuel bound. -/
theorem leftAssociative_ordinary_of_elementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < operandFuel) :
    (∃ expression next,
      leftAssociative operand precedence input = .ok expression next) ∨
    (∃ failure next,
      leftAssociative operand precedence input = .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨left, next, operandResult⟩ | ⟨failure, rejected, operandResult⟩
  · have leftValid := contract.validFor input inputValid
    rw [operandResult] at leftValid
    have leftWindow := contract.preservesTokenWindow input
    rw [operandResult] at leftWindow
    have nextAdequate : next.remainingCount < operandFuel :=
      remainingCount_lt_of_cursor_le leftWindow.2
        (Nat.le_of_lt (contract.cursorLtOnSuccess operandResult)) adequate
    rcases leftAssociativeTail_ordinary_of_fuels operand operandFuel
        precedence contract (next.remainingCount + 1) left next
        leftValid.2.1 (by omega) nextAdequate with
      ⟨expression, final, tailResult⟩ |
      ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨expression, final, by
        simp only [leftAssociative, operandResult]
        exact tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [leftAssociative, operandResult]
        exact tailResult⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [leftAssociative, operandResult]⟩

theorem leftAssociative_ne_invariant_of_elementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < operandFuel)
    (error : ParserInvariantError) :
    leftAssociative operand precedence input ≠ .invariant error := by
  intro failed
  rcases leftAssociative_ordinary_of_elementFuel operand operandFuel
      precedence contract input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionUnaryTotalityProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionUnaryLayerTotalityProperties
/-! Fuel-aware totality for complete prefix-unary expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Prefix scanning preserves the fuel bound required by the postfix parser. -/
theorem expressionUnary_ordinary_of_postfixFuel
    (nested : Parser Expr) (block : Parser Block) (postfixFuel : Nat)
    (postfixContract : FuelElementTotalityContract
      (expressionPostfix nested block) postfixFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < postfixFuel) :
    (∃ expression next,
      expressionUnary nested block input = .ok expression next) ∨
    (∃ failure next,
      expressionUnary nested block input = .reject failure next) := by
  rcases unaryOperators_production_exists_ok [] input with
    ⟨operators, afterOperators, operatorsResult⟩
  have operatorsValid := unaryOperators_validFor
    (input.remainingCount + 1) [] input inputValid (by
      simp [List.ValidFor])
  rw [operatorsResult] at operatorsValid
  have operatorsWindow := unaryOperators_preservesTokenWindow
    (input.remainingCount + 1) [] input
  rw [operatorsResult] at operatorsWindow
  have operatorsCursor := unaryOperators_cursorMonotoneOnSuccess
    (input.remainingCount + 1) [] input operators afterOperators
      operatorsResult
  have afterOperatorsAdequate :
      afterOperators.remainingCount < postfixFuel :=
    remainingCount_lt_of_cursor_le operatorsWindow.2 operatorsCursor adequate
  rcases postfixContract.ordinary afterOperators operatorsValid.2.1
      afterOperatorsAdequate with
    ⟨base, next, postfixResult⟩ | ⟨failure, rejected, postfixResult⟩
  · exact Or.inl ⟨applyUnaryOperators operators base, next, by
      simp only [expressionUnary, operatorsResult, postfixResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [expressionUnary, operatorsResult, postfixResult]⟩

theorem expressionUnary_ne_invariant_of_postfixFuel
    (nested : Parser Expr) (block : Parser Block) (postfixFuel : Nat)
    (postfixContract : FuelElementTotalityContract
      (expressionPostfix nested block) postfixFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < postfixFuel)
    (error : ParserInvariantError) :
    expressionUnary nested block input ≠ .invariant error := by
  intro failed
  rcases expressionUnary_ordinary_of_postfixFuel nested block postfixFuel
      postfixContract input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionFuelContractProperties
/-! Compositional fuel-totality lifts for expression parser layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem leftAssociative_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (operand : Parser Expr) (fuel precedence : Nat)
    (syntaxContract : ExpressionContract statementValid operand)
    (totality : FuelElementTotalityContract operand fuel) :
    FuelElementTotalityContract (leftAssociative operand precedence) fuel := by
  let layer := ExpressionContract.leftAssociative syntaxContract precedence
  exact {
    validFor := layer.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := layer.preservesTokenWindow
    cursorLtOnSuccess := layer.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      leftAssociative_ordinary_of_elementFuel operand fuel precedence
        totality input inputValid adequate
  }

theorem nonAssociative_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (operand : Parser Expr) (fuel precedence : Nat)
    (syntaxContract : ExpressionContract statementValid operand)
    (totality : FuelElementTotalityContract operand fuel) :
    FuelElementTotalityContract (nonAssociative operand precedence) fuel := by
  let layer := ExpressionContract.nonAssociative syntaxContract precedence
  exact {
    validFor := layer.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := layer.preservesTokenWindow
    cursorLtOnSuccess := layer.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      nonAssociative_ordinary_of_elementFuel operand fuel precedence
        totality input inputValid adequate
  }

theorem expressionUnary_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (postfixSyntax : ExpressionContract statementValid
      (expressionPostfix nested block))
    (postfixTotality : FuelElementTotalityContract
      (expressionPostfix nested block) fuel) :
    FuelElementTotalityContract (expressionUnary nested block) fuel := by
  let layer := ExpressionContract.unary statementValid nested block
    postfixSyntax
  exact {
    validFor := layer.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := layer.preservesTokenWindow
    cursorLtOnSuccess := layer.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      expressionUnary_ordinary_of_postfixFuel nested block fuel
        postfixTotality input inputValid adequate
  }

/--
The conditional layer uses the alternative's outer fuel. The supplied bound
ensures that consuming `?` places every recursive expression below its fuel.
-/
theorem conditional_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested alternative : Parser Expr)
    (nestedFuel outerFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (alternativeSyntax : ExpressionContract statementValid alternative)
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (alternativeTotality :
      FuelElementTotalityContract alternative outerFuel)
    (fuelBound : outerFuel ≤ nestedFuel + 1) :
    FuelElementTotalityContract
      (conditional nested alternative) outerFuel := by
  let layer := ExpressionContract.conditional nestedSyntax alternativeSyntax
  exact {
    validFor := layer.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := layer.preservesTokenWindow
    cursorLtOnSuccess := layer.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      conditional_ordinary_of_elementFuels nested alternative nestedFuel
        outerFuel nestedTotality alternativeTotality input inputValid
          (by omega) adequate
  }

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionLayerFuelContractProperties
/-! Fuel-totality for one complete expression precedence layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/--
Lift a recursive expression contract through postfix, unary, all binary
precedence levels, and the conditional expression layer. The outer layer has
one more unit of fuel than its recursive expression operand.
-/
theorem expressionLayer_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (postfixSyntax : ExpressionContract statementValid
      (expressionPostfix nested block))
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (postfixTotality : FuelElementTotalityContract
      (expressionPostfix nested block) (nestedFuel + 1)) :
    FuelElementTotalityContract
      (expressionLayer nested block) (nestedFuel + 1) := by
  have unarySyntax := ExpressionContract.unary statementValid nested block
    postfixSyntax
  have unaryTotality := expressionUnary_fuelTotalityContract nested block
    (nestedFuel + 1) postfixSyntax postfixTotality
  have multiplySyntax := ExpressionContract.leftAssociative unarySyntax 9
  have multiplyTotality := leftAssociative_fuelTotalityContract
    (expressionUnary nested block) (nestedFuel + 1) 9 unarySyntax
      unaryTotality
  have addSyntax := ExpressionContract.leftAssociative multiplySyntax 8
  have addTotality := leftAssociative_fuelTotalityContract
    (leftAssociative (expressionUnary nested block) 9) (nestedFuel + 1) 8
      multiplySyntax multiplyTotality
  have shiftSyntax := ExpressionContract.leftAssociative addSyntax 7
  have shiftTotality := leftAssociative_fuelTotalityContract
    (leftAssociative
      (leftAssociative (expressionUnary nested block) 9) 8)
      (nestedFuel + 1) 7 addSyntax addTotality
  have bitAndSyntax := ExpressionContract.leftAssociative shiftSyntax 6
  have bitAndTotality := leftAssociative_fuelTotalityContract _
    (nestedFuel + 1) 6 shiftSyntax shiftTotality
  have bitXorSyntax := ExpressionContract.leftAssociative bitAndSyntax 5
  have bitXorTotality := leftAssociative_fuelTotalityContract _
    (nestedFuel + 1) 5 bitAndSyntax bitAndTotality
  have bitOrSyntax := ExpressionContract.leftAssociative bitXorSyntax 4
  have bitOrTotality := leftAssociative_fuelTotalityContract _
    (nestedFuel + 1) 4 bitXorSyntax bitXorTotality
  have relationalSyntax := ExpressionContract.nonAssociative bitOrSyntax 3
  have relationalTotality := nonAssociative_fuelTotalityContract _
    (nestedFuel + 1) 3 bitOrSyntax bitOrTotality
  have equalitySyntax := ExpressionContract.nonAssociative relationalSyntax 2
  have equalityTotality := nonAssociative_fuelTotalityContract _
    (nestedFuel + 1) 2 relationalSyntax relationalTotality
  have logicalAndSyntax := ExpressionContract.leftAssociative equalitySyntax 1
  have logicalAndTotality := leftAssociative_fuelTotalityContract _
    (nestedFuel + 1) 1 equalitySyntax equalityTotality
  have logicalOrSyntax := ExpressionContract.leftAssociative logicalAndSyntax 0
  have logicalOrTotality := leftAssociative_fuelTotalityContract _
    (nestedFuel + 1) 0 logicalAndSyntax logicalAndTotality
  simpa only [expressionLayer] using
    conditional_fuelTotalityContract nested _ nestedFuel (nestedFuel + 1)
      nestedSyntax logicalOrSyntax nestedTotality logicalOrTotality (by omega)

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionCollectionNumericWindowProperties
/-! Raw collection atoms retain the numeric endIndex of both ordinary
outcomes under only the same child law. Their children may change file,
tokens, byte endpoints, and diagnostics or return invariants. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem closeTuple_preservesEndIndex (opening : Token) (values : List Expr) :
    Parser.PreservesEndIndex (closeTuple opening values) := by
  unfold closeTuple
  apply bind_preservesEndIndex (symbol_preservesTokenWindow .rightParen .expression).preservesEndIndex
  intro closing input
  split <;> rfl

theorem tupleTail_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) (opening : Token) :
    ∀ fuel values, Parser.PreservesEndIndex (tupleTail nested opening fuel values) := by
  intro fuel
  induction fuel with
  | zero => intro values input; trivial
  | succ fuel ih =>
      intro values input
      unfold tupleTail
      cases commaResult : symbol .comma .expression input with
      | invariant error => trivial
      | reject failure rejected => exact (symbol_preservesTokenWindow .comma .expression).preservesEndIndex.endIndex_eq_of_reject commaResult
      | ok comma afterComma =>
          have commaFrame := (symbol_preservesTokenWindow .comma .expression).preservesEndIndex.endIndex_eq_of_ok commaResult
          simp only
          split
          · exact (closeTuple_preservesEndIndex opening values afterComma).trans commaFrame
          · cases childResult : nested afterComma with
            | invariant error => trivial
            | reject failure rejected => exact (child.endIndex_eq_of_reject childResult).trans commaFrame
            | ok value next =>
                have childFrame := child.endIndex_eq_of_ok childResult
                simp only
                split
                · split
                  · exact (ih (value :: values) next).trans (childFrame.trans commaFrame)
                  · exact (closeTuple_preservesEndIndex opening (value :: values) next).trans (childFrame.trans commaFrame)
                · trivial

theorem parenthesized_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) : Parser.PreservesEndIndex (parenthesized nested) := by
  intro input
  unfold parenthesized
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => trivial
  | reject failure rejected => exact (symbol_preservesTokenWindow .leftParen .expression).preservesEndIndex.endIndex_eq_of_reject openingResult
  | ok opening afterOpening =>
      have openingFrame := (symbol_preservesTokenWindow .leftParen .expression).preservesEndIndex.endIndex_eq_of_ok openingResult
      simp only
      split
      · exact (closeTuple_preservesEndIndex opening [] afterOpening).trans openingFrame
      · cases childResult : nested afterOpening with
        | invariant error => trivial
        | reject failure rejected => exact (child.endIndex_eq_of_reject childResult).trans openingFrame
        | ok first next =>
            have childFrame := child.endIndex_eq_of_ok childResult
            simp only
            split
            · trivial
            · split
              · exact (tupleTail_preservesEndIndex nested child opening
                  (next.remainingCount + 1) [first] next).trans (childFrame.trans openingFrame)
              · exact (closeTuple_preservesEndIndex opening [first] next).trans (childFrame.trans openingFrame)

theorem optionalDotConstructorArguments_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) :
    Parser.PreservesEndIndex (optionalDotConstructorArguments nested) := by
  intro input
  unfold optionalDotConstructorArguments
  simp only [bind, getState]
  split
  · exact bind_preservesEndIndex
      (delimitedWithPolicy_preservesEndIndex .leftParen .rightParen true false nested .expression .expression child)
      (fun _ => pure_preservesEndIndex _) input
  · rfl

theorem dotConstructor_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) : Parser.PreservesEndIndex (dotConstructor nested) := by
  unfold dotConstructor
  apply bind_preservesEndIndex (symbol_preservesTokenWindow .dot .expression).preservesEndIndex
  intro dot
  apply bind_preservesEndIndex expressionName_preservesTokenWindow.preservesEndIndex
  intro name
  apply bind_preservesEndIndex (optionalDotConstructorArguments_preservesEndIndex nested child)
  intro arguments
  exact pure_preservesEndIndex _

theorem arrayLiteral_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) : Parser.PreservesEndIndex (arrayLiteral nested) := by
  unfold arrayLiteral
  apply bind_preservesEndIndex
    (delimitedWithPolicy_preservesEndIndex .leftBracket .rightBracket true false nested .expression .expression child)
  intro values
  exact pure_preservesEndIndex _

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomNumericWindowProperties
/-! Selected raw atoms and public recovery retain the numeric token endpoint
when successful and rejected recursive children do. Reject frames are crucial:
public recovery retains the failed child's carrier and window when rewinding
the cursor. No source, token-carrier, or endByte assumption is imposed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExpressionAtomInternals

theorem lambdaExpression_preservesEndIndex (block : Parser Block)
    (child : Parser.PreservesEndIndex block) : Parser.PreservesEndIndex (lambdaExpression block) := by
  unfold lambdaExpression
  apply bind_preservesEndIndex (keyword_preservesTokenWindow .lamKw .expression).preservesEndIndex
  intro marker
  apply bind_preservesEndIndex
    (delimitedWithPolicy_preservesEndIndex .leftParen .rightParen true true lambdaParameter .parameter .expression
      lambdaParameter_preservesTokenWindow.preservesEndIndex)
  intro parameters
  apply bind_preservesEndIndex optionalLambdaReturnType_preservesTokenWindow.preservesEndIndex
  intro returnType
  apply bind_preservesEndIndex child
  intro body
  exact pure_preservesEndIndex _

theorem expressionAtomCore_preservesEndIndex (nested : Parser Expr) (block : Parser Block)
    (nestedFrame : Parser.PreservesEndIndex nested) (blockFrame : Parser.PreservesEndIndex block) :
    Parser.PreservesEndIndex (expressionAtomCore nested block) := by
  intro input
  unfold expressionAtomCore
  split
  · exact literalExpression_preservesTokenWindow.preservesEndIndex input
  · split
    · exact identifierExpression_preservesTokenWindow.preservesEndIndex input
    · split
      · exact dotConstructor_preservesEndIndex nested nestedFrame input
      · split
        · exact proxyExpression_preservesTokenWindow.preservesEndIndex input
        · split
          · exact parenthesized_preservesEndIndex nested nestedFrame input
          · split
            · exact arrayLiteral_preservesEndIndex nested nestedFrame input
            · split
              · exact lambdaExpression_preservesEndIndex block blockFrame input
              · rfl

end ExpressionAtomInternals

open ExpressionAtomInternals

theorem expressionAtom_preservesEndIndex (nested : Parser Expr) (block : Parser Block)
    (nestedFrame : Parser.PreservesEndIndex nested) (blockFrame : Parser.PreservesEndIndex block) :
    Parser.PreservesEndIndex (expressionAtom nested block) := by
  intro input
  unfold expressionAtom
  cases coreResult : expressionAtomCore nested block input with
  | invariant error => trivial
  | ok value next => exact (expressionAtomCore_preservesEndIndex nested block nestedFrame blockFrame).endIndex_eq_of_ok coreResult
  | reject failure failed =>
      have coreFrame := (expressionAtomCore_preservesEndIndex nested block nestedFrame blockFrame).endIndex_eq_of_reject coreResult
      simp only
      split
      · exact coreFrame
      · exact (recoverAtom_preservesTokenWindow.preservesEndIndex _).trans coreFrame

/-- Numeric child success and rejection laws alone suffice, including when
public success is obtained by recovering from a rejected nested/body parser. -/
theorem expressionAtom_endIndex_onSuccess {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ∀ {input output value}, nested input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (blockSuccess : ∀ {input output value}, block input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    {input output : State} {value : Expr}
    (result : expressionAtom nested block input = .ok value output) :
    output.window.endIndex = input.window.endIndex :=
  (expressionAtom_preservesEndIndex nested block
    (.of_success_reject nestedSuccess nestedReject) (.of_success_reject blockSuccess blockReject)).endIndex_eq_of_ok result

theorem expressionAtom_endIndex_onReject {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ∀ {input output value}, nested input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (blockSuccess : ∀ {input output value}, block input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    {input rejected : State} {failure : Failure}
    (result : expressionAtom nested block input = .reject failure rejected) :
    rejected.window.endIndex = input.window.endIndex :=
  (expressionAtom_preservesEndIndex nested block
    (.of_success_reject nestedSuccess nestedReject) (.of_success_reject blockSuccess blockReject)).endIndex_eq_of_reject result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixNumericWindowProperties
/-! Postfix suffixes preserve only the numeric endIndex of their supplied
children. Successful and rejected replies are both framed; source, tokens,
endByte, diagnostics, cursor progress, validity, and ordinary execution are
deliberately not required by this structural layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExpressionAtomInternals

theorem postfixTail_preservesEndIndex (nested : Parser Expr) (block : Parser Block)
    (child : Parser.PreservesEndIndex nested) :
    ∀ fuel base, Parser.PreservesEndIndex (postfixTail nested block fuel base) := by
  intro fuel
  induction fuel with
  | zero => intro base input; trivial
  | succ fuel ih =>
      intro base input
      unfold postfixTail
      split
      · cases openingResult : symbol .leftBracket .expression input with
        | invariant error => trivial
        | reject failure rejected =>
            exact (symbol_preservesTokenWindow .leftBracket .expression).preservesEndIndex.endIndex_eq_of_reject openingResult
        | ok opening afterOpening =>
            have openingFrame := (symbol_preservesTokenWindow .leftBracket .expression).preservesEndIndex.endIndex_eq_of_ok openingResult
            simp only
            cases childResult : nested afterOpening with
            | invariant error => trivial
            | reject failure rejected => exact (child.endIndex_eq_of_reject childResult).trans openingFrame
            | ok index afterIndex =>
                have indexFrame := child.endIndex_eq_of_ok childResult
                simp only
                cases closingResult : symbol .rightBracket .expression afterIndex with
                | invariant error => trivial
                | reject failure rejected =>
                    exact ((symbol_preservesTokenWindow .rightBracket .expression).preservesEndIndex.endIndex_eq_of_reject closingResult).trans
                      (indexFrame.trans openingFrame)
                | ok closing afterClosing =>
                    have closingFrame := (symbol_preservesTokenWindow .rightBracket .expression).preservesEndIndex.endIndex_eq_of_ok closingResult
                    exact (ih _ afterClosing).trans (closingFrame.trans (indexFrame.trans openingFrame))
      · split
        · have argumentsFrame := delimitedWithPolicy_preservesEndIndex .leftParen .rightParen true false
            nested .expression .expression child
          cases argumentResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
          | invariant error => trivial
          | reject failure rejected => exact argumentsFrame.endIndex_eq_of_reject argumentResult
          | ok arguments afterArguments => exact (ih _ afterArguments).trans (argumentsFrame.endIndex_eq_of_ok argumentResult)
        · split
          · cases dotResult : symbol .dot .expression input with
            | invariant error => trivial
            | reject failure rejected =>
                exact (symbol_preservesTokenWindow .dot .expression).preservesEndIndex.endIndex_eq_of_reject dotResult
            | ok dot afterDot =>
                have dotFrame := (symbol_preservesTokenWindow .dot .expression).preservesEndIndex.endIndex_eq_of_ok dotResult
                simp only
                cases nameResult : identifier .expression afterDot with
                | invariant error => trivial
                | reject failure rejected =>
                    exact ((identifier_preservesTokenWindow .expression).preservesEndIndex.endIndex_eq_of_reject nameResult).trans dotFrame
                | ok name afterName =>
                    exact (ih _ afterName).trans
                      (((identifier_preservesTokenWindow .expression).preservesEndIndex.endIndex_eq_of_ok nameResult).trans dotFrame)
          · rfl

end ExpressionAtomInternals

/-- Actual production fuel is irrelevant to this numeric frame. The atom
frame is explicit here; separate child laws can construct it without a source frame. -/
theorem expressionPostfix_preservesEndIndex (nested : Parser Expr) (block : Parser Block)
    (atomFrame : Parser.PreservesEndIndex (expressionAtom nested block))
    (nestedFrame : Parser.PreservesEndIndex nested) :
    Parser.PreservesEndIndex (expressionPostfix nested block) := by
  intro input
  unfold expressionPostfix
  cases atomResult : expressionAtom nested block input with
  | invariant error => trivial
  | reject failure rejected => exact atomFrame.endIndex_eq_of_reject atomResult
  | ok base next =>
      exact (ExpressionAtomInternals.postfixTail_preservesEndIndex nested block nestedFrame
        (next.remainingCount + 1) base next).trans (atomFrame.endIndex_eq_of_ok atomResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Expression.LambdaTotalityProperties
/-! Totality for lambda expressions over an abstract block parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem lambdaParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid
      (delimited .leftParen .rightParen true lambdaParameter
        .parameter .expression) := by
  intro input inputValid
  exact delimited_ordinary .leftParen .rightParen true lambdaParameter
    .parameter .expression lambdaParameter_elementTotalityContract input
      inputValid

/-- A lambda is ordinary whenever its supplied block parser is ordinary. -/
theorem lambdaExpression_invariantFreeOnValid (block : Parser Block)
    (blockValid : block.ValidFor (fun _ _ => True))
    (blockFree : Parser.InvariantFreeOnValid block) :
    Parser.InvariantFreeOnValid (lambdaExpression block) := by
  unfold lambdaExpression
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .lamKw .expression)
    (keyword_ordinary .lamKw .expression).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    ((delimited_validFor LambdaParameter.ValidFor .leftParen .rightParen true
      lambdaParameter .parameter .expression lambdaParameter_validFor
        lambdaParameter_preservesTokensOnSuccess).mono (fun _ _ _ => trivial))
    lambdaParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid
    (optionalLambdaReturnType_validFor.mono (fun _ _ _ => trivial))
    optionalLambdaReturnType_invariantFreeOnValid
  intro returnType
  apply Parser.bind_invariantFreeOnValid blockValid blockFree
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := .lambda marker.span parameters returnType body
  } : Expr)

theorem lambdaExpression_ne_invariant (block : Parser Block)
    (blockValid : block.ValidFor (fun _ _ => True))
    (blockFree : Parser.InvariantFreeOnValid block)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    lambdaExpression block input ≠ .invariant error :=
  Parser.InvariantFreeOnValid.ne_invariant
    (lambdaExpression_invariantFreeOnValid block blockValid blockFree)
      input inputValid error

/-- Package lambda syntax and totality for use by expression-atom dispatch. -/
theorem lambdaExpression_elementTotalityContract
    (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span))
    (blockFree : Parser.InvariantFreeOnValid block) :
    ElementTotalityContract (lambdaExpression block) := {
  validFor := (lambdaExpression_validFor block statementValid blockValid
    blockStarts).mono (fun _ _ _ => trivial)
  preservesTokenWindow := lambdaExpression_preservesTokenWindow block
    lambdaParameter_preservesTokenWindow blockWindow
  cursorLtOnSuccess := lambdaExpression_cursor_lt_onSuccess block blockCursor
  invariantFree := (lambdaExpression_invariantFreeOnValid block
    (blockValid.mono (fun _ _ _ => trivial)) blockFree).ne_invariant
}

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Expression.PostfixTailFuelTotalityProperties
/-! Fuel-aware totality for the postfix-expression tail loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem postfixTail_ordinary_of_fuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel) :
    ∀ loopFuel base input, input.ValidFor →
      input.remainingCount < loopFuel →
      input.remainingCount < nestedFuel + 1 →
      (∃ value next,
        postfixTail nested block loopFuel base input = .ok value next) ∨
      (∃ failure next,
        postfixTail nested block loopFuel base input = .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro base input inputValid loopAdequate nestedAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro base input inputValid loopAdequate nestedAdequate
      unfold postfixTail
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true]
        rcases (symbol_ordinary .leftBracket .expression) input with
          ⟨opening, afterOpening, openingResult⟩ |
          ⟨failure, rejected, openingResult⟩
        · have openingValid := symbol_validFor .leftBracket .expression input
            inputValid
          rw [openingResult] at openingValid
          have openingWindow := symbol_preservesTokenWindow .leftBracket
            .expression input
          rw [openingResult] at openingWindow
          have afterOpeningNested : afterOpening.remainingCount < nestedFuel :=
            remainingCount_lt_after_strict_progress openingValid.2.1
              openingWindow.2
              (acceptToken_cursor_lt_onSuccess (.symbol .leftBracket)
                .expression (· == .symbol .leftBracket) openingResult)
              nestedAdequate
          rcases contract.ordinary afterOpening openingValid.2.1
              afterOpeningNested with
            ⟨index, afterIndex, indexResult⟩ |
            ⟨failure, rejected, indexResult⟩
          · have indexValid := contract.validFor afterOpening openingValid.2.1
            rw [indexResult] at indexValid
            rcases (symbol_ordinary .rightBracket .expression) afterIndex with
              ⟨closing, afterClosing, closingResult⟩ |
              ⟨failure, rejected, closingResult⟩
            · have closingValid := symbol_validFor .rightBracket .expression
                afterIndex indexValid.2.1
              rw [closingResult] at closingValid
              have suffixWindow :=
                (symbol_preservesTokenWindow .rightBracket .expression
                  afterIndex)
              rw [closingResult] at suffixWindow
              have indexWindow := contract.preservesTokenWindow afterOpening
              rw [indexResult] at indexWindow
              have afterClosingWindow : afterClosing.window = input.window :=
                suffixWindow.2.trans (indexWindow.2.trans openingWindow.2)
              have loopNext : afterClosing.remainingCount < loopFuel :=
                remainingCount_lt_after_strict_progress closingValid.2.1
                  afterClosingWindow
                  (Nat.lt_of_lt_of_le
                    (acceptToken_cursor_lt_onSuccess (.symbol .leftBracket)
                      .expression (· == .symbol .leftBracket) openingResult)
                    (Nat.le_trans (Nat.le_of_lt
                      (contract.cursorLtOnSuccess indexResult))
                      (symbol_cursorMonotoneOnSuccess .rightBracket .expression
                        afterIndex closing afterClosing closingResult)))
                  loopAdequate
              have nestedNext : afterClosing.remainingCount < nestedFuel + 1 :=
                remainingCount_lt_of_cursor_le afterClosingWindow
                  (Nat.le_trans
                    (symbol_cursorMonotoneOnSuccess .leftBracket .expression
                      input opening afterOpening openingResult)
                    (Nat.le_trans (Nat.le_of_lt
                      (contract.cursorLtOnSuccess indexResult))
                      (symbol_cursorMonotoneOnSuccess .rightBracket .expression
                        afterIndex closing afterClosing closingResult)))
                  nestedAdequate
              rcases inductionHypothesis {
                    span := SourceSpan.cover base.span closing.span
                    value := .index base
                      (SourceSpan.cover opening.span closing.span) index
                  } afterClosing closingValid.2.1 loopNext nestedNext with
                ⟨value, final, tailResult⟩ |
                ⟨failure, final, tailResult⟩
              · exact Or.inl ⟨value, final, by
                  simp only [openingResult, indexResult, closingResult,
                    tailResult]⟩
              · exact Or.inr ⟨failure, final, by
                  simp only [openingResult, indexResult, closingResult,
                    tailResult]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [openingResult, indexResult, closingResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [openingResult, indexResult]⟩
        · exact Or.inr ⟨failure, rejected, by simp only [openingResult]⟩
      · simp only [indexed, Bool.false_eq_true, if_false]
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true]
          rcases delimitedWithPolicy_ordinary_of_elementFuel .leftParen
              .rightParen true false nested .expression .expression nestedFuel
              contract input inputValid nestedAdequate with
            ⟨arguments, next, argumentsResult⟩ |
            ⟨failure, rejected, argumentsResult⟩
          · have ordinaryResult : delimitedNoTrailing .leftParen .rightParen
                true nested .expression .expression input = .ok arguments next :=
              by simpa only [delimitedNoTrailing] using argumentsResult
            have argumentsValid := delimitedNoTrailing_validFor (fun _ _ => True)
              .leftParen .rightParen true nested .expression .expression
              contract.validFor
              contract.preservesTokenWindow.preservesTokensOnSuccess input
              inputValid
            rw [ordinaryResult] at argumentsValid
            have argumentsWindow := delimitedWithPolicy_preservesTokenWindow
              .leftParen .rightParen true false nested .expression .expression
              contract.preservesTokenWindow input
            rw [argumentsResult] at argumentsWindow
            have strict := delimitedWithPolicy_cursor_lt_onSuccess .leftParen
              .rightParen true false nested .expression .expression
              argumentsResult
            have loopNext := remainingCount_lt_after_strict_progress
              argumentsValid.2.1 argumentsWindow.2 strict loopAdequate
            have nestedNext := remainingCount_lt_of_cursor_le argumentsWindow.2
              (Nat.le_of_lt strict) nestedAdequate
            rcases inductionHypothesis {
                  span := SourceSpan.cover base.span arguments.span
                  value := .call base arguments
                } next argumentsValid.2.1 loopNext nestedNext with
              ⟨value, final, tailResult⟩ |
              ⟨failure, final, tailResult⟩
            · exact Or.inl ⟨value, final, by
                simp only [ordinaryResult, tailResult]⟩
            · exact Or.inr ⟨failure, final, by
                simp only [ordinaryResult, tailResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [delimitedNoTrailing, argumentsResult]⟩
        · simp only [called, Bool.false_eq_true, if_false]
          by_cases field : isSymbol input .dot
          · simp only [field, if_true]
            rcases (symbol_ordinary .dot .expression) input with
              ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
            · have dotValid := symbol_validFor .dot .expression input inputValid
              rw [dotResult] at dotValid
              rcases (identifier_ordinary .expression) afterDot with
                ⟨name, next, nameResult⟩ | ⟨failure, rejected, nameResult⟩
              · have nameValid := identifier_validFor .expression afterDot
                    dotValid.2.1
                rw [nameResult] at nameValid
                have dotWindow := symbol_preservesTokenWindow .dot .expression
                  input
                rw [dotResult] at dotWindow
                have nameWindow := identifier_preservesTokenWindow .expression
                  afterDot
                rw [nameResult] at nameWindow
                have nextWindow : next.window = input.window :=
                  nameWindow.2.trans dotWindow.2
                have strict := acceptToken_cursor_lt_onSuccess (.symbol .dot)
                  .expression (· == .symbol .dot) dotResult
                have loopNext := remainingCount_lt_after_strict_progress
                  nameValid.2.1 nextWindow
                    (Nat.lt_of_lt_of_le strict
                      (identifier_cursorMonotoneOnSuccess .expression afterDot
                        name next nameResult)) loopAdequate
                have nestedNext := remainingCount_lt_of_cursor_le nextWindow
                  (Nat.le_trans
                    (symbol_cursorMonotoneOnSuccess .dot .expression input dot
                      afterDot dotResult)
                    (identifier_cursorMonotoneOnSuccess .expression afterDot
                      name next nameResult)) nestedAdequate
                rcases inductionHypothesis {
                      span := SourceSpan.cover base.span name.span
                      value := .field base dot.span name
                    } next nameValid.2.1 loopNext nestedNext with
                  ⟨value, final, tailResult⟩ |
                  ⟨failure, final, tailResult⟩
                · exact Or.inl ⟨value, final, by
                    simp only [dotResult, nameResult, tailResult]⟩
                · exact Or.inr ⟨failure, final, by
                    simp only [dotResult, nameResult, tailResult]⟩
              · exact Or.inr ⟨failure, rejected, by
                  simp only [dotResult, nameResult]⟩
            · exact Or.inr ⟨failure, rejected, by simp only [dotResult]⟩
          · have absent : isSymbol input .dot = false := by
              cases found : isSymbol input .dot with
              | false => rfl
              | true => exact False.elim (field found)
            exact Or.inl ⟨base, input, by
              simp only [absent, Bool.false_eq_true, if_false]⟩

theorem postfixTail_ne_invariant_of_fuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel loopFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (base : Expr) (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    postfixTail nested block loopFuel base input ≠ .invariant error := by
  intro failed
  rcases postfixTail_ordinary_of_fuel nested block nestedFuel contract loopFuel
      base input inputValid loopAdequate nestedAdequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

theorem postfixTail_production_ordinary
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (base : Expr) (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next,
      postfixTail nested block (input.remainingCount + 1) base input =
        .ok value next) ∨
    (∃ failure next,
      postfixTail nested block (input.remainingCount + 1) base input =
        .reject failure next) :=
  postfixTail_ordinary_of_fuel nested block nestedFuel contract
    (input.remainingCount + 1) base input inputValid (by omega) nestedAdequate

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionLayerBlockFuelTotalityProperties
/-! Fuel-aware expression layers whose lambda bodies are recursive blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- A lambda is ordinary when its body has enough fuel after `lam` advances. -/
theorem lambdaExpression_ordinary_of_blockFuel (block : Parser Block)
    (blockFuel : Nat)
    (blockContract : FuelElementTotalityContract block blockFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < blockFuel + 1) :
    (exists value next, lambdaExpression block input = .ok value next) ∨
      (exists failure next,
        lambdaExpression block input = .reject failure next) := by
  rcases (keyword_ordinary .lamKw .expression) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .lamKw .expression input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .lamKw .expression input
    rw [markerResult] at markerWindow
    have markerProgress := acceptToken_cursor_lt_onSuccess
      (.keyword .lamKw) .expression (· == .keyword .lamKw) markerResult
    have afterMarkerAdequate : afterMarker.remainingCount < blockFuel :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress adequate
    rcases delimited_ordinary .leftParen .rightParen true lambdaParameter
        .parameter .expression lambdaParameter_elementTotalityContract
        afterMarker markerReply.2.1 with
      ⟨parameters, afterParameters, parametersResult⟩ |
      ⟨failure, rejected, parametersResult⟩
    · have parametersReply := delimited_validFor LambdaParameter.ValidFor
        .leftParen .rightParen true lambdaParameter .parameter .expression
        lambdaParameter_validFor lambdaParameter_preservesTokensOnSuccess
        afterMarker markerReply.2.1
      rw [parametersResult] at parametersReply
      have parametersWindow := delimited_preservesTokenWindow .leftParen
        .rightParen true lambdaParameter .parameter .expression
        lambdaParameter_preservesTokenWindow afterMarker
      rw [parametersResult] at parametersWindow
      have parametersCursor := delimited_cursorMonotoneOnSuccess .leftParen
        .rightParen true lambdaParameter .parameter .expression afterMarker
        parameters afterParameters parametersResult
      have afterParametersAdequate :
          afterParameters.remainingCount < blockFuel :=
        remainingCount_lt_of_cursor_le parametersWindow.2 parametersCursor
          afterMarkerAdequate
      rcases optionalLambdaReturnType_invariantFreeOnValid afterParameters
          parametersReply.2.1 with
        ⟨returnType, afterReturnType, returnTypeResult⟩ |
        ⟨failure, rejected, returnTypeResult⟩
      · have returnTypeReply := optionalLambdaReturnType_validFor
          afterParameters parametersReply.2.1
        rw [returnTypeResult] at returnTypeReply
        have returnTypeWindow :=
          optionalLambdaReturnType_preservesTokenWindow afterParameters
        rw [returnTypeResult] at returnTypeWindow
        have returnTypeCursor :=
          optionalLambdaReturnType_cursorMonotoneOnSuccess afterParameters
            returnType afterReturnType returnTypeResult
        have bodyAdequate : afterReturnType.remainingCount < blockFuel :=
          remainingCount_lt_of_cursor_le returnTypeWindow.2 returnTypeCursor
            afterParametersAdequate
        rcases blockContract.ordinary afterReturnType returnTypeReply.2.1
            bodyAdequate with
          ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
        · exact Or.inl ⟨{
              span := SourceSpan.cover marker.span body.span
              value := .lambda marker.span parameters returnType body
            }, final, by
              simp only [lambdaExpression, bind, markerResult,
                parametersResult, returnTypeResult, bodyResult, pure]⟩
        · exact Or.inr ⟨failure, rejected, by
              simp only [lambdaExpression, bind, markerResult,
                parametersResult, returnTypeResult, bodyResult]⟩
      · exact Or.inr ⟨failure, rejected, by
            simp only [lambdaExpression, bind, markerResult,
              parametersResult, returnTypeResult]⟩
    · exact Or.inr ⟨failure, rejected, by
          simp only [lambdaExpression, bind, markerResult, parametersResult]⟩
  · exact Or.inr ⟨failure, rejected, by
        simp only [lambdaExpression, bind, markerResult]⟩

private theorem expressionAtomCore_ordinary_of_fuels
    (nested : Parser Expr) (block : Parser Block)
    (nestedFuel blockFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (blockContract : FuelElementTotalityContract block blockFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (blockAdequate : input.remainingCount < blockFuel + 1) :
    (exists value next,
      expressionAtomCore nested block input = .ok value next) ∨
    (exists failure next,
      expressionAtomCore nested block input = .reject failure next) := by
  unfold expressionAtomCore
  split
  · exact literalExpression_invariantFreeOnValid input inputValid
  · split
    · exact identifierExpression_invariantFreeOnValid input inputValid
    · split
      · exact dotConstructor_ordinary_of_elementFuel nested nestedFuel
          nestedContract input inputValid nestedAdequate
      · split
        · exact proxyExpression_invariantFreeOnValid input inputValid
        · split
          · exact parenthesized_ordinary_of_elementFuel nested nestedFuel
              nestedContract input inputValid nestedAdequate
          · split
            · exact arrayLiteral_ordinary_of_elementFuel nested nestedFuel
                nestedContract input inputValid nestedAdequate
            · split
              · exact lambdaExpression_ordinary_of_blockFuel block blockFuel
                  blockContract input inputValid blockAdequate
              · exact Parser.rejectAt_invariantFreeOnValid
                  { head := .expression, tail := [] } .expression input inputValid

private theorem expressionAtom_ordinary_of_fuels
    (nested : Parser Expr) (block : Parser Block)
    (nestedFuel blockFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (blockContract : FuelElementTotalityContract block blockFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (blockAdequate : input.remainingCount < blockFuel + 1) :
    (exists value next, expressionAtom nested block input = .ok value next) ∨
    (exists failure next,
      expressionAtom nested block input = .reject failure next) := by
  rcases expressionAtomCore_ordinary_of_fuels nested block nestedFuel
      blockFuel nestedContract blockContract input inputValid nestedAdequate
      blockAdequate with
    ⟨value, next, coreResult⟩ | ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨value, next, by simp [expressionAtom, coreResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : isAtomBoundary rewound
    · exact Or.inr ⟨failure, rewound, by
          simp [expressionAtom, coreResult, rewound, boundary]⟩
    · have boundaryFalse : isAtomBoundary rewound = false := by
        cases found : isAtomBoundary rewound with
        | false => rfl
        | true => exact False.elim (boundary found)
      rcases recoverAtom_ordinary (rewound.emit failure.toDiagnostic) with
        ⟨recovered, final, recoveryResult⟩ |
        ⟨recoveryFailure, rejected, recoveryResult⟩
      · exact Or.inl ⟨recovered, final, by
            simp [expressionAtom, coreResult, rewound, boundaryFalse,
              recoveryResult]⟩
      · exact Or.inr ⟨recoveryFailure, rejected, by
            simp [expressionAtom, coreResult, rewound, boundaryFalse,
              recoveryResult]⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Lift one expression layer while keeping lambda-block fuel explicit. -/
theorem expressionLayer_blockFuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block)
    (nestedFuel blockFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span))
    (blockTotality : FuelElementTotalityContract block blockFuel) :
    FuelElementTotalityContract (expressionLayer nested block)
      (Nat.min nestedFuel blockFuel + 1) := by
  let commonFuel := Nat.min nestedFuel blockFuel
  let commonNested : FuelElementTotalityContract nested commonFuel :=
    nestedTotality.weaken (by
      exact Nat.min_le_left nestedFuel blockFuel)
  let atomSyntax := ExpressionContract.atom statementValid nested block
    nestedSyntax blockValid blockWindow blockCursor blockStarts
  let postfixSyntax := ExpressionContract.concretePostfix statementValid
    nested block nestedSyntax blockValid blockWindow blockCursor blockStarts
  have postfixTotality : FuelElementTotalityContract
      (expressionPostfix nested block) (commonFuel + 1) := {
    validFor := postfixSyntax.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := postfixSyntax.preservesTokenWindow
    cursorLtOnSuccess := postfixSyntax.cursorLtOnSuccess
    ordinary := by
      intro input inputValid adequate
      rcases ExpressionAtomInternals.expressionAtom_ordinary_of_fuels nested
          block commonFuel blockFuel commonNested blockTotality input inputValid
          adequate (Nat.lt_of_lt_of_le adequate (by
            exact Nat.add_le_add_right
              (Nat.min_le_right nestedFuel blockFuel) 1)) with
        ⟨base, next, atomResult⟩ | ⟨failure, rejected, atomResult⟩
      · have atomReply := atomSyntax.validFor input inputValid
        rw [atomResult] at atomReply
        have atomWindow := atomSyntax.preservesTokenWindow input
        rw [atomResult] at atomWindow
        have nextAdequate : next.remainingCount < commonFuel + 1 :=
          remainingCount_lt_of_cursor_le atomWindow.2
            (Nat.le_of_lt (atomSyntax.cursorLtOnSuccess atomResult)) adequate
        rcases ExpressionAtomInternals.postfixTail_production_ordinary nested
            block commonFuel commonNested base next atomReply.2.1
            nextAdequate with
          ⟨value, final, tailResult⟩ | ⟨failure, rejected, tailResult⟩
        · exact Or.inl ⟨value, final, by
              simp [expressionPostfix, atomResult, tailResult]⟩
        · exact Or.inr ⟨failure, rejected, by
              simp [expressionPostfix, atomResult, tailResult]⟩
      · exact Or.inr ⟨failure, rejected, by
            simp [expressionPostfix, atomResult]⟩
  }
  simpa only [commonFuel] using expressionLayer_fuelTotalityContract nested
    block commonFuel nestedSyntax postfixSyntax commonNested postfixTotality

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Expression.PostfixTotalityProperties
/-! Fuel-aware totality for complete postfix expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem expressionPostfix_ordinary_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (atomValid : (expressionAtom nested block).ValidFor (fun _ _ => True))
    (atomWindow : Parser.PreservesTokenWindow
      (expressionAtom nested block))
    (atomStrict : ∀ {input next : State} {value : Expr},
      expressionAtom nested block input = .ok value next →
        input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      expressionPostfix nested block input = .ok expression next) ∨
    (∃ failure next,
      expressionPostfix nested block input = .reject failure next) := by
  rcases expressionAtom_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree input inputValid adequate with
    ⟨base, next, atomResult⟩ | ⟨failure, rejected, atomResult⟩
  · have atomReply := atomValid input inputValid
    rw [atomResult] at atomReply
    have atomShape := atomWindow input
    rw [atomResult] at atomShape
    have nextAdequate : next.remainingCount < nestedFuel + 1 :=
      remainingCount_lt_of_cursor_le atomShape.2
        (Nat.le_of_lt (atomStrict atomResult)) adequate
    rcases postfixTail_production_ordinary nested block nestedFuel
        nestedContract base next atomReply.2.1 nextAdequate with
      ⟨expression, final, tailResult⟩ |
      ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨expression, final, by
        simp only [expressionPostfix, atomResult]
        exact tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [expressionPostfix, atomResult]
        exact tailResult⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [expressionPostfix, atomResult]⟩

theorem expressionPostfix_ne_invariant_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (atomValid : (expressionAtom nested block).ValidFor (fun _ _ => True))
    (atomWindow : Parser.PreservesTokenWindow
      (expressionAtom nested block))
    (atomStrict : ∀ {input next : State} {value : Expr},
      expressionAtom nested block input = .ok value next →
        input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    expressionPostfix nested block input ≠ .invariant error := by
  intro failed
  rcases expressionPostfix_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree atomValid atomWindow atomStrict input
      inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Expression.PostfixFuelContractProperties
/-! Compositional fuel-totality contract for postfix expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem expressionPostfix_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span))
    (lambdaFree : Parser.InvariantFreeOnValid
      (ExpressionAtomInternals.lambdaExpression block)) :
    FuelElementTotalityContract
      (expressionPostfix nested block) (nestedFuel + 1) := by
  let atomSyntax := ExpressionContract.atom statementValid nested block
    nestedSyntax blockValid blockWindow blockCursor blockStarts
  let postfixSyntax := ExpressionContract.concretePostfix statementValid
    nested block nestedSyntax blockValid blockWindow blockCursor blockStarts
  exact {
    validFor := postfixSyntax.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := postfixSyntax.preservesTokenWindow
    cursorLtOnSuccess := postfixSyntax.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      ExpressionAtomInternals.expressionPostfix_ordinary_of_elementFuel
        nested block nestedFuel nestedTotality lambdaFree
          (atomSyntax.validFor.mono (fun _ _ _ => trivial))
            atomSyntax.preservesTokenWindow atomSyntax.cursorLtOnSuccess
              input inputValid adequate
  }

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionLayerConcreteFuelContractProperties
/-! Concrete fuel-totality bridge for one complete expression layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/--
Build the concrete postfix syntax and lambda totality internally, then lift
them through the complete precedence layer with one extra unit of fuel.
-/
theorem expressionLayer_concrete_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span))
    (blockFree : Parser.InvariantFreeOnValid block) :
    FuelElementTotalityContract
      (expressionLayer nested block) (nestedFuel + 1) := by
  let lambdaFree :=
    ExpressionAtomInternals.lambdaExpression_invariantFreeOnValid block
      (blockValid.mono (fun _ _ _ => trivial)) blockFree
  let postfixSyntax := ExpressionContract.concretePostfix statementValid
    nested block nestedSyntax blockValid blockWindow blockCursor blockStarts
  let postfixTotality := expressionPostfix_fuelTotalityContract
    nested block nestedFuel nestedSyntax nestedTotality blockValid blockWindow
      blockCursor blockStarts lambdaFree
  exact expressionLayer_fuelTotalityContract nested block nestedFuel
    nestedSyntax postfixSyntax nestedTotality postfixTotality

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionAtomDispatcherLookaheadProperties
/-!
Bridges between executable atom-dispatch lookaheads and the independent
declarative starter predicates.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem isCoreLiteral_eq_true_of_decimalTokenAt {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .decimalLiteral spelling }) :
    isCoreLiteral input = true := by
  unfold isCoreLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem isCoreLiteral_eq_true_of_hexadecimalTokenAt {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .hexadecimalLiteral spelling }) :
    isCoreLiteral input = true := by
  unfold isCoreLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem isCoreLiteral_eq_true_of_stringTokenAt {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .stringLiteral spelling }) :
    isCoreLiteral input = true := by
  unfold isCoreLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

/-- Declarative literal presence makes the executable literal guard true. -/
theorem isCoreLiteral_eq_true_of_coreLiteralStartsAt {input : State}
    (starts : DeclarativeGrammar.CoreLiteralStartsAt
      input.declarativeRemainder) :
    isCoreLiteral input = true := by
  rcases starts with ⟨span, spelling, token⟩ |
      ⟨span, spelling, token⟩ | ⟨span, spelling, token⟩
  · exact isCoreLiteral_eq_true_of_decimalTokenAt token
  · exact isCoreLiteral_eq_true_of_hexadecimalTokenAt token
  · exact isCoreLiteral_eq_true_of_stringTokenAt token

/-- A false executable literal guard excludes the declarative starter. -/
theorem not_coreLiteralStartsAt_of_isCoreLiteral_eq_false {input : State}
    (absent : isCoreLiteral input = false) :
    ¬ DeclarativeGrammar.CoreLiteralStartsAt input.declarativeRemainder := by
  intro starts
  rw [isCoreLiteral_eq_true_of_coreLiteralStartsAt starts] at absent
  contradiction

private theorem isKeyword_eq_true_of_tokenAt (keyword : HardKeyword)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword keyword }) :
    isKeyword input keyword = true := by
  unfold isKeyword State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  change instBEqTokenKind.beq (.keyword keyword) (.keyword keyword) = true
  simp only [instBEqTokenKind.beq]
  change instBEqHardKeyword.beq keyword keyword = true
  unfold instBEqHardKeyword.beq
  cases keyword <;> rfl

private theorem isIdentifier_eq_true_of_tokenAt {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .identifier spelling }) :
    isIdentifier input = true := by
  unfold isIdentifier State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

/--
Declarative Boolean-or-identifier presence makes the executable disjunctive
name guard true, including both hard-keyword Boolean spellings.
-/
theorem expressionNameGuard_eq_true_of_expressionNameStartsAt
    {input : State}
    (starts : DeclarativeGrammar.ExpressionNameStartsAt
      input.declarativeRemainder) :
    (isBooleanValue input || isIdentifier input) = true := by
  rcases starts with ⟨span, token⟩ | ⟨span, token⟩ |
      ⟨span, spelling, token⟩
  · have present := isKeyword_eq_true_of_tokenAt .trueKw token
    simp [isBooleanValue, present]
  · have present := isKeyword_eq_true_of_tokenAt .falseKw token
    simp [isBooleanValue, present]
  · have present := isIdentifier_eq_true_of_tokenAt token
    simp [present]

/-- A false Boolean-or-identifier guard excludes every expression name. -/
theorem not_expressionNameStartsAt_of_expressionNameGuard_eq_false
    {input : State}
    (absent : (isBooleanValue input || isIdentifier input) = false) :
    ¬ DeclarativeGrammar.ExpressionNameStartsAt
      input.declarativeRemainder := by
  intro starts
  rw [expressionNameGuard_eq_true_of_expressionNameStartsAt starts] at absent
  contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
end
