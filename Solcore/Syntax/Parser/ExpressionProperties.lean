import Solcore.Syntax.Parser.Expression
import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.ExpressionValidity

/-! Provenance and state contracts for canonical Core expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ExpressionInternals

namespace ConditionalHead

/-- Every range retained by a pending conditional prefix belongs to one source. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (head : ConditionalHead) : Prop :=
  Expr.ValidFor statementValid file head.condition ∧
    head.question.ValidFor file ∧
    Expr.ValidFor statementValid file head.thenBranch ∧
    head.colon.ValidFor file

end ConditionalHead

/-- Attaching one conditional prefix preserves the else branch's source end. -/
theorem foldConditionalHead_preservesElseEnd
    (elseBranch : Expr) (head : ConditionalHead) :
    (foldConditionalHead elseBranch head).span.endByte =
      elseBranch.span.endByte := by
  rfl

@[simp] theorem foldConditionalHead_startByte
    (elseBranch : Expr) (head : ConditionalHead) :
    (foldConditionalHead elseBranch head).span.startByte =
      head.condition.span.startByte := rfl

/-- Folding the same pending prefixes depends only on the base's left edge. -/
theorem foldConditionalHeads_start_congr
    (heads : List ConditionalHead) (first second : Expr)
    (sameStart : first.span.startByte = second.span.startByte) :
    (heads.foldl foldConditionalHead first).span.startByte =
      (heads.foldl foldConditionalHead second).span.startByte := by
  induction heads generalizing first second with
  | nil => exact sameStart
  | cons head rest inductionHypothesis =>
      simp only [List.foldl]
      exact inductionHypothesis _ _ rfl

/-- Attaching a valid conditional prefix retains every recursive source range. -/
theorem foldConditionalHead_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (elseBranch : Expr) (head : ConditionalHead)
    (headValid : head.ValidFor statementValid file)
    (elseValid : Expr.ValidFor statementValid file elseBranch)
    (ordered : head.condition.span.startByte ≤
      elseBranch.span.endByte) :
    Expr.ValidFor statementValid file
      (foldConditionalHead elseBranch head) := by
  rcases headValid with
    ⟨conditionValid, questionValid, thenValid, colonValid⟩
  have outerValid := SourceSpan.cover_validFor conditionValid.span_valid
    elseValid.span_valid ordered
  exact Expr.ValidFor.conditional outerValid conditionValid questionValid
    thenValid colonValid elseValid

/-- Folding pending prefixes preserves the final else branch's source end. -/
theorem foldConditionalHeads_preservesBaseEnd
    (heads : List ConditionalHead) (base : Expr) :
    (heads.foldl foldConditionalHead base).span.endByte =
      base.span.endByte := by
  induction heads generalizing base with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      simpa only [List.foldl] using
        (inductionHypothesis (foldConditionalHead base head)).trans
          (foldConditionalHead_preservesElseEnd base head)

/-- Folding valid pending prefixes retains every recursive source range. -/
theorem foldConditionalHeads_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (heads : List ConditionalHead) (base : Expr)
    (headsValid : List.ValidFor
      (ConditionalHead.ValidFor statementValid) file heads)
    (baseValid : Expr.ValidFor statementValid file base)
    (ordered : ∀ head ∈ heads,
      head.condition.span.startByte ≤ base.span.endByte) :
    Expr.ValidFor statementValid file
      (heads.foldl foldConditionalHead base) := by
  induction heads generalizing base with
  | nil => simpa only [List.foldl] using baseValid
  | cons head rest inductionHypothesis =>
      have headValid := headsValid head (by simp)
      have restValid : List.ValidFor
          (ConditionalHead.ValidFor statementValid) file rest := by
        intro retained member
        exact headsValid retained (by simp [member])
      have attachedValid := foldConditionalHead_validFor statementValid file
        base head headValid baseValid (ordered head (by simp))
      apply inductionHypothesis (foldConditionalHead base head) restValid
        attachedValid
      intro retained member
      rw [foldConditionalHead_preservesElseEnd]
      exact ordered retained (by simp [member])

/-- The conditional-prefix loop preserves every ordinary token window. -/
theorem conditionalTail_preservesTokenWindow
    (nested alternative : Parser Expr)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (alternativeWindow : Parser.PreservesTokenWindow alternative) :
    ∀ fuel heads condition,
      Parser.PreservesTokenWindow
        (conditionalTail nested alternative fuel heads condition) := by
  intro fuel
  induction fuel with
  | zero => intro heads condition input; trivial
  | succ fuel inductionHypothesis =>
      intro heads condition input
      unfold conditionalTail
      by_cases present : isSymbol input .question
      · simp only [present, if_true]
        have questionShape :=
          symbol_preservesTokenWindow .question .expression input
        cases questionResult : symbol .question .expression input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [questionResult] at questionShape
            exact questionShape
        | ok question afterQuestion =>
            rw [questionResult] at questionShape
            simp only
            have thenShape := nestedWindow afterQuestion
            cases thenResult : nested afterQuestion with
            | invariant error => trivial
            | reject failure rejected =>
                rw [thenResult] at thenShape
                exact thenShape.trans questionShape
            | ok thenBranch afterThen =>
                rw [thenResult] at thenShape
                simp only
                have colonShape :=
                  symbol_preservesTokenWindow .colon .expression afterThen
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => trivial
                | reject failure rejected =>
                    rw [colonResult] at colonShape
                    exact (colonShape.trans thenShape).trans questionShape
                | ok colon afterColon =>
                    rw [colonResult] at colonShape
                    simp only
                    have alternativeShape := alternativeWindow afterColon
                    cases alternativeResult : alternative afterColon with
                    | invariant error => trivial
                    | reject failure rejected =>
                        rw [alternativeResult] at alternativeShape
                        exact ((alternativeShape.trans colonShape).trans
                          thenShape).trans questionShape
                    | ok nextCondition next =>
                        rw [alternativeResult] at alternativeShape
                        exact ((((inductionHypothesis ({
                            condition
                            question := question.span
                            thenBranch
                            colon := colon.span
                          } :: heads) nextCondition next).trans
                            alternativeShape).trans colonShape).trans
                              thenShape).trans questionShape
      · simp only [present]
        exact ⟨rfl, rfl⟩

theorem conditionalTail_preservesTokensOnSuccess
    (nested alternative : Parser Expr)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (alternativeWindow : Parser.PreservesTokenWindow alternative)
    (fuel : Nat) (heads : List ConditionalHead) (condition : Expr) :
    Parser.PreservesTokensOnSuccess
      (conditionalTail nested alternative fuel heads condition) :=
  (conditionalTail_preservesTokenWindow nested alternative nestedWindow
    alternativeWindow fuel heads condition).preservesTokensOnSuccess

/-- Successful conditional-prefix parsing never rewinds its caller. -/
theorem conditionalTail_cursorMonotoneOnSuccess
    (nested alternative : Parser Expr)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (alternativeCursor : Parser.CursorMonotoneOnSuccess alternative) :
    ∀ fuel heads condition,
      Parser.CursorMonotoneOnSuccess
        (conditionalTail nested alternative fuel heads condition) := by
  intro fuel
  induction fuel with
  | zero =>
      intro heads condition input expression final parsed
      unfold conditionalTail at parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro heads condition input expression final parsed
      unfold conditionalTail at parsed
      by_cases present : isSymbol input .question
      · simp only [present, if_true] at parsed
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at parsed
        | reject failure rejected => simp [questionResult] at parsed
        | ok question afterQuestion =>
            simp only [questionResult] at parsed
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at parsed
            | reject failure rejected => simp [thenResult] at parsed
            | ok thenBranch afterThen =>
                simp only [thenResult] at parsed
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at parsed
                | reject failure rejected => simp [colonResult] at parsed
                | ok colon afterColon =>
                    simp only [colonResult] at parsed
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at parsed
                    | reject failure rejected =>
                        simp [alternativeResult] at parsed
                    | ok nextCondition next =>
                        simp only [alternativeResult] at parsed
                        exact Nat.le_trans
                          (symbol_cursorMonotoneOnSuccess .question .expression
                            input question afterQuestion questionResult)
                          (Nat.le_trans
                            (nestedCursor afterQuestion thenBranch afterThen
                              thenResult)
                            (Nat.le_trans
                              (symbol_cursorMonotoneOnSuccess .colon .expression
                                afterThen colon afterColon colonResult)
                              (Nat.le_trans
                                (alternativeCursor afterColon nextCondition next
                                  alternativeResult)
                                (inductionHypothesis ({
                                    condition
                                    question := question.span
                                    thenBranch
                                    colon := colon.span
                                  } :: heads) nextCondition next expression
                                    final parsed))))
      · simp only [present] at parsed
        cases parsed
        exact Nat.le_refl _

/-- A conditional tail preserves the left edge represented by its accumulator. -/
theorem conditionalTail_preservesFoldStartOnSuccess
    (nested alternative : Parser Expr) :
    ∀ fuel heads condition input expression final,
      conditionalTail nested alternative fuel heads condition input =
        .ok expression final →
      expression.span.startByte =
        (heads.foldl foldConditionalHead condition).span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro heads condition input expression final parsed
      unfold conditionalTail at parsed
      by_cases present : isSymbol input .question
      · simp only [present, if_true] at parsed
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at parsed
        | reject failure rejected => simp [questionResult] at parsed
        | ok question afterQuestion =>
            simp only [questionResult] at parsed
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at parsed
            | reject failure rejected => simp [thenResult] at parsed
            | ok thenBranch afterThen =>
                simp only [thenResult] at parsed
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at parsed
                | reject failure rejected => simp [colonResult] at parsed
                | ok colon afterColon =>
                    simp only [colonResult] at parsed
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at parsed
                    | reject failure rejected =>
                        simp [alternativeResult] at parsed
                    | ok nextCondition next =>
                        simp only [alternativeResult] at parsed
                        calc
                          expression.span.startByte =
                              (({
                                condition
                                question := question.span
                                thenBranch
                                colon := colon.span
                              } :: heads).foldl foldConditionalHead
                                nextCondition).span.startByte :=
                            inductionHypothesis _ _ next expression final parsed
                          _ = (heads.foldl foldConditionalHead
                              (foldConditionalHead nextCondition {
                                condition
                                question := question.span
                                thenBranch
                                colon := colon.span
                              })).span.startByte := rfl
                          _ = (heads.foldl foldConditionalHead
                              condition).span.startByte :=
                            foldConditionalHeads_start_congr heads _ _ rfl
      · simp only [present] at parsed
        cases parsed
        rfl

/-- The conditional-prefix loop retains every pending and parsed source range. -/
theorem conditionalTail_validFor
    (nested alternative : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedTokens : Parser.PreservesTokensOnSuccess nested)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (alternativeValid : alternative.ValidFor
      (Expr.ValidFor statementValid))
    (alternativeTokens : Parser.PreservesTokensOnSuccess alternative)
    (alternativeCursorLt : ∀ {input next : State} {value : Expr},
      alternative input = .ok value next → input.cursor < next.cursor)
    (alternativeStarts :
      Parser.StartsAtCurrentTokenOnSuccess alternative (·.span)) :
    ∀ fuel heads condition input,
      input.ValidFor →
      List.ValidFor (ConditionalHead.ValidFor statementValid)
        input.file heads →
      Expr.ValidFor statementValid input.file condition →
      (∀ head ∈ heads, head.condition.span.startByte ≤
        condition.span.startByte) →
      (∀ token, input.peek? = some token →
        condition.span.startByte ≤ token.span.startByte) →
      (conditionalTail nested alternative fuel heads condition input).ValidFor
        input (Expr.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro heads condition input inputValid headsValid conditionValid
        headsBefore conditionBefore
      unfold conditionalTail
      by_cases present : isSymbol input .question
      · simp only [present, if_true]
        cases questionResult : symbol .question .expression input with
        | invariant error => trivial
        | reject failure rejected =>
            have reply := symbol_validFor .question .expression input inputValid
            rw [questionResult] at reply
            exact reply
        | ok question afterQuestion =>
            have questionReply := symbol_validFor .question .expression input
              inputValid
            rw [questionResult] at questionReply
            simp only
            cases thenResult : nested afterQuestion with
            | invariant error => trivial
            | reject failure rejected =>
                have reply := nestedValid afterQuestion questionReply.2.1
                rw [thenResult] at reply
                exact reply.of_file_eq questionReply.2.2
            | ok thenBranch afterThen =>
                have thenReply := nestedValid afterQuestion questionReply.2.1
                rw [thenResult] at thenReply
                simp only
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => trivial
                | reject failure rejected =>
                    have reply := symbol_validFor .colon .expression afterThen
                      thenReply.2.1
                    rw [colonResult] at reply
                    exact reply.of_file_eq
                      (thenReply.2.2.trans questionReply.2.2)
                | ok colon afterColon =>
                    have colonReply := symbol_validFor .colon .expression
                      afterThen thenReply.2.1
                    rw [colonResult] at colonReply
                    simp only
                    cases alternativeResult : alternative afterColon with
                    | invariant error => trivial
                    | reject failure rejected =>
                        have reply := alternativeValid afterColon colonReply.2.1
                        rw [alternativeResult] at reply
                        exact reply.of_file_eq (colonReply.2.2.trans
                          (thenReply.2.2.trans questionReply.2.2))
                    | ok nextCondition next =>
                        have alternativeReply := alternativeValid afterColon
                          colonReply.2.1
                        rw [alternativeResult] at alternativeReply
                        have questionShape := symbol_ok_state_shape .question
                          .expression questionResult
                        have colonShape := symbol_ok_state_shape .colon
                          .expression colonResult
                        have questionAt :=
                          State.getElem?_eq_some_of_peek?_eq_some
                            questionShape.1
                        rcases alternativeStarts afterColon nextCondition next
                            alternativeResult with
                          ⟨nextToken, nextFound, nextStart⟩
                        have nextAtAfterColon :=
                          State.getElem?_eq_some_of_peek?_eq_some nextFound
                        have questionTokens :=
                          symbol_preservesTokensOnSuccess .question .expression
                            input question afterQuestion questionResult
                        have thenTokens := nestedTokens afterQuestion thenBranch
                          afterThen thenResult
                        have colonTokens :=
                          symbol_preservesTokensOnSuccess .colon .expression
                            afterThen colon afterColon colonResult
                        have nextAtInput : input.tokens[afterColon.cursor]? =
                            some nextToken := by
                          simpa [colonTokens, thenTokens, questionTokens] using
                            nextAtAfterColon
                        have questionBeforeNext :=
                          inputValid.token_end_le_token_start_of_getElem?_lt
                            questionAt nextAtInput
                            (Nat.lt_of_lt_of_le
                              (acceptToken_cursor_lt_onSuccess
                                (.symbol .question) .expression
                                (· == .symbol .question) questionResult)
                              (Nat.le_trans
                                (nestedCursor afterQuestion thenBranch afterThen
                                  thenResult)
                                (symbol_cursorMonotoneOnSuccess .colon
                                  .expression afterThen colon afterColon
                                  colonResult)))
                        have questionSpan : question.span.ValidFor input.file := by
                          simpa only [Located.ValidFor] using questionReply.1
                        have conditionBeforeNext :
                            condition.span.startByte ≤
                              nextCondition.span.startByte := by
                          calc
                            condition.span.startByte ≤
                                question.span.startByte :=
                              conditionBefore question questionShape.1
                            _ ≤ question.span.endByte := questionSpan.2.1
                            _ ≤ nextToken.span.startByte := questionBeforeNext
                            _ = nextCondition.span.startByte := nextStart
                        have thenValidInput : Expr.ValidFor statementValid
                            input.file thenBranch := by
                          simpa [thenReply.2.2, questionReply.2.2] using
                            thenReply.1
                        have colonSpan : colon.span.ValidFor input.file := by
                          simpa only [Located.ValidFor, thenReply.2.2,
                            questionReply.2.2] using colonReply.1
                        have nextFileEq : next.file = input.file :=
                          alternativeReply.2.2.trans (colonReply.2.2.trans
                            (thenReply.2.2.trans questionReply.2.2))
                        have nextConditionValidInput :
                            Expr.ValidFor statementValid input.file
                              nextCondition := by
                          simpa [colonReply.2.2, thenReply.2.2,
                            questionReply.2.2] using alternativeReply.1
                        have accumulatedInput : List.ValidFor
                            (ConditionalHead.ValidFor statementValid) input.file
                            ({
                              condition
                              question := question.span
                              thenBranch
                              colon := colon.span
                            } :: heads) := by
                          intro head member
                          rcases List.mem_cons.mp member with rfl | member
                          · exact ⟨conditionValid, questionSpan,
                              thenValidInput, colonSpan⟩
                          · exact headsValid head member
                        have accumulatedNext : List.ValidFor
                            (ConditionalHead.ValidFor statementValid) next.file
                            ({
                              condition
                              question := question.span
                              thenBranch
                              colon := colon.span
                            } :: heads) := by
                          simpa [nextFileEq] using accumulatedInput
                        have headsBeforeNext : ∀ head ∈ ({
                              condition
                              question := question.span
                              thenBranch
                              colon := colon.span
                            } :: heads),
                            head.condition.span.startByte ≤
                              nextCondition.span.startByte := by
                          intro head member
                          rcases List.mem_cons.mp member with rfl | member
                          · exact conditionBeforeNext
                          · exact Nat.le_trans (headsBefore head member)
                              conditionBeforeNext
                        have nextConditionBefore : ∀ future,
                            next.peek? = some future →
                            nextCondition.span.startByte ≤
                              future.span.startByte := by
                          intro future futureFound
                          have nextAt :=
                            State.getElem?_eq_some_of_peek?_eq_some nextFound
                          have futureAtNext :=
                            State.getElem?_eq_some_of_peek?_eq_some futureFound
                          have alternativeCarrier := alternativeTokens afterColon
                            nextCondition next alternativeResult
                          have futureAt : afterColon.tokens[next.cursor]? =
                              some future := by
                            simpa [alternativeCarrier] using futureAtNext
                          have separated :=
                            colonReply.2.1.token_end_le_token_start_of_getElem?_lt
                              nextAt futureAt
                                (alternativeCursorLt alternativeResult)
                          calc
                            nextCondition.span.startByte =
                                nextToken.span.startByte := nextStart.symm
                            _ ≤ nextToken.span.endByte :=
                              (colonReply.2.1.peek?_span_validFor nextFound).2.1
                            _ ≤ future.span.startByte := separated
                        have recursive := inductionHypothesis ({
                            condition
                            question := question.span
                            thenBranch
                            colon := colon.span
                          } :: heads) nextCondition next alternativeReply.2.1
                            accumulatedNext
                            (by simpa [nextFileEq] using
                              nextConditionValidInput)
                            headsBeforeNext nextConditionBefore
                        exact recursive.of_file_eq nextFileEq
      · simp only [present]
        have folded := foldConditionalHeads_validFor statementValid input.file
          heads condition headsValid conditionValid (by
            intro head member
            exact Nat.le_trans (headsBefore head member)
              conditionValid.span_valid.2.1)
        exact ⟨folded, inputValid, rfl⟩

/-- A complete conditional layer preserves every ordinary token window. -/
theorem conditional_preservesTokenWindow
    (nested alternative : Parser Expr)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (alternativeWindow : Parser.PreservesTokenWindow alternative) :
    Parser.PreservesTokenWindow (conditional nested alternative) := by
  intro input
  unfold conditional
  have alternativeShape := alternativeWindow input
  cases alternativeResult : alternative input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [alternativeResult] at alternativeShape
      exact alternativeShape
  | ok condition next =>
      rw [alternativeResult] at alternativeShape
      exact (conditionalTail_preservesTokenWindow nested alternative
        nestedWindow alternativeWindow (next.remainingCount + 1) [] condition
          next).trans alternativeShape

theorem conditional_preservesTokensOnSuccess
    (nested alternative : Parser Expr)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (alternativeWindow : Parser.PreservesTokenWindow alternative) :
    Parser.PreservesTokensOnSuccess (conditional nested alternative) :=
  (conditional_preservesTokenWindow nested alternative nestedWindow
    alternativeWindow).preservesTokensOnSuccess

/-- A complete conditional layer never rewinds the token cursor. -/
theorem conditional_cursorMonotoneOnSuccess
    (nested alternative : Parser Expr)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (alternativeCursor : Parser.CursorMonotoneOnSuccess alternative) :
    Parser.CursorMonotoneOnSuccess (conditional nested alternative) := by
  intro input expression final parsed
  unfold conditional at parsed
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at parsed
  | reject failure rejected => simp [alternativeResult] at parsed
  | ok condition next =>
      simp only [alternativeResult] at parsed
      exact Nat.le_trans
        (alternativeCursor input condition next alternativeResult)
        (conditionalTail_cursorMonotoneOnSuccess nested alternative
          nestedCursor alternativeCursor (next.remainingCount + 1) []
            condition next expression final parsed)

/-- A complete conditional layer retains its first alternative's left edge. -/
theorem conditional_startsAtCurrentTokenOnSuccess
    (nested alternative : Parser Expr)
    (alternativeStarts :
      Parser.StartsAtCurrentTokenOnSuccess alternative (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (conditional nested alternative) (·.span) := by
  intro input expression final parsed
  unfold conditional at parsed
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at parsed
  | reject failure rejected => simp [alternativeResult] at parsed
  | ok condition next =>
      simp only [alternativeResult] at parsed
      rcases alternativeStarts input condition next alternativeResult with
        ⟨token, found, starts⟩
      have retained := conditionalTail_preservesFoldStartOnSuccess nested
        alternative (next.remainingCount + 1) [] condition next expression
          final parsed
      exact ⟨token, found, starts.trans (by simpa using retained.symm)⟩

/-- A complete conditional layer retains every recursive source range. -/
theorem conditional_validFor
    (nested alternative : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedTokens : Parser.PreservesTokensOnSuccess nested)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (alternativeValid : alternative.ValidFor
      (Expr.ValidFor statementValid))
    (alternativeTokens : Parser.PreservesTokensOnSuccess alternative)
    (alternativeCursorLt : ∀ {input next : State} {value : Expr},
      alternative input = .ok value next → input.cursor < next.cursor)
    (alternativeStarts :
      Parser.StartsAtCurrentTokenOnSuccess alternative (·.span)) :
    (conditional nested alternative).ValidFor
      (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold conditional
  cases alternativeResult : alternative input with
  | invariant error => trivial
  | reject failure rejected =>
      have reply := alternativeValid input inputValid
      rw [alternativeResult] at reply
      exact reply
  | ok condition next =>
      have alternativeReply := alternativeValid input inputValid
      rw [alternativeResult] at alternativeReply
      rcases alternativeStarts input condition next alternativeResult with
        ⟨firstToken, firstFound, firstStart⟩
      have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
      have carrier := alternativeTokens input condition next alternativeResult
      have conditionBefore : ∀ future, next.peek? = some future →
          condition.span.startByte ≤ future.span.startByte := by
        intro future futureFound
        have futureAtNext :=
          State.getElem?_eq_some_of_peek?_eq_some futureFound
        have futureAt : input.tokens[next.cursor]? = some future := by
          simpa [carrier] using futureAtNext
        have separated := inputValid.token_end_le_token_start_of_getElem?_lt
          firstAt futureAt (alternativeCursorLt alternativeResult)
        have firstValid := inputValid.peek?_span_validFor firstFound
        calc
          condition.span.startByte = firstToken.span.startByte := firstStart.symm
          _ ≤ firstToken.span.endByte := firstValid.2.1
          _ ≤ future.span.startByte := separated
      have recursive := conditionalTail_validFor nested alternative
        statementValid nestedValid nestedTokens nestedCursor alternativeValid
          alternativeTokens alternativeCursorLt alternativeStarts
            (next.remainingCount + 1) [] condition next alternativeReply.2.1
              (by simp [List.ValidFor])
              (by simpa [alternativeReply.2.2] using alternativeReply.1)
                (by simp)
                conditionBefore
      exact recursive.of_file_eq alternativeReply.2.2

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

/-- Unary wrapping preserves the final operand's source end. -/
theorem applyUnaryOperators_preservesBaseEnd
    (operators : List (Located UnaryOp)) (base : Expr) :
    (applyUnaryOperators operators base).span.endByte =
      base.span.endByte := by
  induction operators with
  | nil => rfl
  | cons operator rest inductionHypothesis =>
      simpa only [applyUnaryOperators, List.foldr, SourceSpan.cover] using
        inductionHypothesis

/-- Unary wrapping retains every operator and operand source range. -/
theorem applyUnaryOperators_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (operators : List (Located UnaryOp)) (base : Expr)
    (operatorsValid : List.ValidFor Located.ValidFor file operators)
    (baseValid : Expr.ValidFor statementValid file base)
    (ordered : ∀ operator ∈ operators,
      operator.span.startByte ≤ base.span.endByte) :
    Expr.ValidFor statementValid file
      (applyUnaryOperators operators base) := by
  induction operators with
  | nil => simpa only [applyUnaryOperators, List.foldr] using baseValid
  | cons operator rest inductionHypothesis =>
      have operatorValid : operator.span.ValidFor file := by
        simpa only [Located.ValidFor] using
          operatorsValid operator (by simp)
      have restValid : List.ValidFor Located.ValidFor file rest := by
        intro retained member
        exact operatorsValid retained (by simp [member])
      have restOrdered : ∀ retained ∈ rest,
          retained.span.startByte ≤ base.span.endByte := by
        intro retained member
        exact ordered retained (by simp [member])
      have operandValid := inductionHypothesis restValid restOrdered
      have outerValid := SourceSpan.cover_validFor operatorValid
        operandValid.span_valid (by
          rw [applyUnaryOperators_preservesBaseEnd]
          exact ordered operator (by simp))
      simpa only [applyUnaryOperators, List.foldr] using
        (Expr.ValidFor.unary outerValid operatorValid operandValid)

/-- Successful precedence lookup identifies the current token exactly. -/
theorem binaryAtPrecedence?_some_state_shape {input : State}
    {precedence : Nat} {operator : Located BinaryOp}
    (result : binaryAtPrecedence? input precedence = some operator) :
    ∃ token, input.peek? = some token ∧
      binaryOp? token.value = some operator.value ∧
      token.span = operator.span := by
  unfold binaryAtPrecedence? at result
  cases found : input.peek? with
  | none => simp [found] at result
  | some token =>
      simp only [found] at result
      cases decoded : binaryOp? token.value with
      | none => simp [decoded] at result
      | some value =>
          simp only [decoded] at result
          split at result
          · cases result
            exact ⟨token, rfl, by simpa using decoded, rfl⟩
          · contradiction

/-- Every recognized binary operator belongs to the active source. -/
theorem binaryAtPrecedence?_validFor {input : State}
    {precedence : Nat} {operator : Located BinaryOp}
    (inputValid : input.ValidFor)
    (result : binaryAtPrecedence? input precedence = some operator) :
    Located.ValidFor input.file operator := by
  rcases binaryAtPrecedence?_some_state_shape result with
    ⟨token, found, _decoded, span⟩
  simpa only [Located.ValidFor, ← span] using
    inputValid.peek?_span_validFor found

/-- Binary consumption is the exact one-token cursor update. -/
theorem consumeBinary_ok_state_shape (operator : Located BinaryOp)
    (input : State) :
    consumeBinary operator input =
      .ok () { input with cursor := input.cursor + 1 } := rfl

/-- Consuming a recognized current token preserves state validity. -/
theorem consumeBinary_reply_validFor (operator : Located BinaryOp)
    {input : State} (inputValid : input.ValidFor) {token : Token}
    (found : input.peek? = some token) :
    (consumeBinary operator input).ValidFor input (fun _ _ => True) := by
  unfold consumeBinary modifyState Reply.ValidFor
  refine ⟨trivial, ?_, rfl⟩
  apply inputValid.advance?_validFor (token := token)
  unfold State.advance?
  rw [found]
  rfl

/-- Binary consumption preserves the immutable token window. -/
theorem consumeBinary_preservesTokenWindow (operator : Located BinaryOp) :
    Parser.PreservesTokenWindow (consumeBinary operator) :=
  modifyState_preservesTokenWindow _ (fun _ => ⟨rfl, rfl⟩)

theorem consumeBinary_preservesTokensOnSuccess
    (operator : Located BinaryOp) :
    Parser.PreservesTokensOnSuccess (consumeBinary operator) :=
  (consumeBinary_preservesTokenWindow operator).preservesTokensOnSuccess

/-- Binary consumption advances the cursor by exactly one. -/
theorem consumeBinary_cursor_lt_onSuccess (operator : Located BinaryOp)
    {input final : State} {value : Unit}
    (result : consumeBinary operator input = .ok value final) :
    input.cursor < final.cursor := by
  unfold consumeBinary modifyState at result
  cases result
  simp

theorem consumeBinary_cursorMonotoneOnSuccess
    (operator : Located BinaryOp) :
    Parser.CursorMonotoneOnSuccess (consumeBinary operator) := by
  intro input value final result
  exact Nat.le_of_lt (consumeBinary_cursor_lt_onSuccess operator result)

/-- A binary node retains its two operands and operator provenance. -/
theorem binaryNode_validFor
    (statementValid : SourceFile → Statement → Prop) (file : SourceFile)
    (left : Expr) (operator : Located BinaryOp) (right : Expr)
    (leftValid : Expr.ValidFor statementValid file left)
    (operatorValid : Located.ValidFor file operator)
    (rightValid : Expr.ValidFor statementValid file right)
    (ordered : left.span.startByte ≤ right.span.endByte) :
    Expr.ValidFor statementValid file (binaryNode left operator right) := by
  unfold binaryNode
  exact Expr.ValidFor.binary
    (SourceSpan.cover_validFor leftValid.span_valid rightValid.span_valid ordered)
    leftValid (by simpa only [Located.ValidFor] using operatorValid) rightValid

@[simp] theorem binaryNode_startByte (left : Expr)
    (operator : Located BinaryOp) (right : Expr) :
    (binaryNode left operator right).span.startByte = left.span.startByte := rfl

@[simp] theorem binaryNode_endByte (left : Expr)
    (operator : Located BinaryOp) (right : Expr) :
    (binaryNode left operator right).span.endByte = right.span.endByte := rfl

/-- A left-associative tail preserves every ordinary token window. -/
theorem leftAssociativeTail_preservesTokenWindow (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) : ∀ fuel left,
    Parser.PreservesTokenWindow
      (leftAssociativeTail operand precedence fuel left) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input
      trivial
  | succ fuel inductionHypothesis =>
      intro left input
      unfold leftAssociativeTail
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => exact ⟨rfl, rfl⟩
      | some operator =>
          simp only
          have consumedShape := consumeBinary_preservesTokenWindow
            operator input
          cases consumedResult : consumeBinary operator input with
          | invariant error =>
              simp only
              trivial
          | reject failure rejected =>
              rw [consumedResult] at consumedShape
              simp only
              exact consumedShape
          | ok value afterOperator =>
              rw [consumedResult] at consumedShape
              simp only
              have operandShape := operandWindow afterOperator
              cases operandResult : operand afterOperator with
              | invariant error =>
                  simp only
                  trivial
              | reject failure rejected =>
                  rw [operandResult] at operandShape
                  simp only
                  exact operandShape.trans consumedShape
              | ok right next =>
                  rw [operandResult] at operandShape
                  simp only
                  exact (inductionHypothesis
                    (binaryNode left operator right) next).trans
                      (operandShape.trans consumedShape)

theorem leftAssociativeTail_preservesTokensOnSuccess
    (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence fuel : Nat) (left : Expr) :
    Parser.PreservesTokensOnSuccess
      (leftAssociativeTail operand precedence fuel left) :=
  (leftAssociativeTail_preservesTokenWindow operand operandWindow precedence
    fuel left).preservesTokensOnSuccess

/-- A left-associative tail never rewinds the parser cursor. -/
theorem leftAssociativeTail_cursorMonotoneOnSuccess
    (operand : Parser Expr)
    (operandCursor : Parser.CursorMonotoneOnSuccess operand)
    (precedence : Nat) : ∀ fuel left,
    Parser.CursorMonotoneOnSuccess
      (leftAssociativeTail operand precedence fuel left) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input expression final parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro left input expression final parsed
      unfold leftAssociativeTail at parsed
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          exact Nat.le_refl _
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator input with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              have consumedMonotone :=
                consumeBinary_cursorMonotoneOnSuccess operator input value
                  afterOperator consumedResult
              cases operandResult : operand afterOperator with
              | invariant error => simp [operandResult] at parsed
              | reject failure rejected => simp [operandResult] at parsed
              | ok right next =>
                  simp only [operandResult] at parsed
                  exact Nat.le_trans consumedMonotone
                    (Nat.le_trans
                      (operandCursor afterOperator right next operandResult)
                      (inductionHypothesis
                        (binaryNode left operator right) next expression final
                          parsed))

/-- Every successful left-associative tail keeps its original left edge. -/
theorem leftAssociativeTail_preservesLeftStartOnSuccess
    (operand : Parser Expr) (precedence : Nat) :
    ∀ fuel left input expression final,
      leftAssociativeTail operand precedence fuel left input =
        .ok expression final →
      expression.span.startByte = left.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro left input expression final parsed
      unfold leftAssociativeTail at parsed
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          rfl
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator input with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              cases operandResult : operand afterOperator with
              | invariant error => simp [operandResult] at parsed
              | reject failure rejected => simp [operandResult] at parsed
              | ok right next =>
                  simp only [operandResult] at parsed
                  simpa using inductionHypothesis
                    (binaryNode left operator right) next expression final
                      parsed

/-- A left-associative tail retains every operand and operator source range. -/
theorem leftAssociativeTail_validFor
    (operand : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (operandValid : operand.ValidFor (Expr.ValidFor statementValid))
    (operandTokens : Parser.PreservesTokensOnSuccess operand)
    (operandCursor : Parser.CursorMonotoneOnSuccess operand)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) : ∀ fuel left input,
    input.ValidFor →
    Expr.ValidFor statementValid input.file left →
    (∀ token, input.peek? = some token →
      left.span.startByte ≤ token.span.startByte) →
    (leftAssociativeTail operand precedence fuel left input).ValidFor input
      (Expr.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro left input inputValid leftValid leftBefore
      unfold leftAssociativeTail
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => exact ⟨leftValid, inputValid, rfl⟩
      | some operator =>
          simp only
          rcases binaryAtPrecedence?_some_state_shape operatorResult with
            ⟨operatorToken, operatorFound, _decoded, _operatorSpan⟩
          have operatorValid := binaryAtPrecedence?_validFor inputValid
            operatorResult
          have consumedReply := consumeBinary_reply_validFor operator
            inputValid operatorFound
          cases consumedResult : consumeBinary operator input with
          | invariant error => trivial
          | reject failure rejected =>
              rw [consumedResult] at consumedReply
              simp only
              exact consumedReply
          | ok value afterOperator =>
              rw [consumedResult] at consumedReply
              have exactConsumed := consumeBinary_ok_state_shape operator input
              rw [consumedResult] at exactConsumed
              cases exactConsumed
              simp only
              cases operandResult : operand
                  { input with cursor := input.cursor + 1 } with
              | invariant error => trivial
              | reject failure rejected =>
                  have rejectedValid := operandValid
                    { input with cursor := input.cursor + 1 }
                    consumedReply.2.1
                  rw [operandResult] at rejectedValid
                  simp only
                  exact rejectedValid.of_file_eq consumedReply.2.2
              | ok right next =>
                  have rightReply := operandValid
                    { input with cursor := input.cursor + 1 }
                    consumedReply.2.1
                  rw [operandResult] at rightReply
                  have rightValidInput :
                      Expr.ValidFor statementValid input.file right := by
                    simpa [rightReply.2.2, consumedReply.2.2] using rightReply.1
                  rcases operandStarts
                      { input with cursor := input.cursor + 1 } right next
                      operandResult with
                    ⟨rightToken, rightFound, rightStart⟩
                  have operatorAt :=
                    State.getElem?_eq_some_of_peek?_eq_some operatorFound
                  have rightAt : input.tokens[input.cursor + 1]? =
                      some rightToken := by
                    simpa using
                      State.getElem?_eq_some_of_peek?_eq_some rightFound
                  have separated :=
                    inputValid.token_end_le_token_start_of_getElem?_lt
                      operatorAt rightAt (by omega)
                  have operatorSpanValid :
                      operatorToken.span.ValidFor input.file :=
                    inputValid.peek?_span_validFor operatorFound
                  have ordered : left.span.startByte ≤ right.span.endByte := by
                    calc
                      left.span.startByte ≤ operatorToken.span.startByte :=
                        leftBefore operatorToken operatorFound
                      _ ≤ operatorToken.span.endByte := operatorSpanValid.2.1
                      _ ≤ rightToken.span.startByte := separated
                      _ = right.span.startByte := rightStart
                      _ ≤ right.span.endByte := rightValidInput.span_valid.2.1
                  have combinedValidInput := binaryNode_validFor statementValid
                    input.file left operator right leftValid operatorValid
                      rightValidInput ordered
                  have combinedValidNext : Expr.ValidFor statementValid
                      next.file (binaryNode left operator right) := by
                    simpa [rightReply.2.2, consumedReply.2.2] using
                      combinedValidInput
                  have tokensEq := operandTokens
                    { input with cursor := input.cursor + 1 } right next
                      operandResult
                  have cursorOrder : input.cursor < next.cursor :=
                    Nat.lt_of_lt_of_le (by simp)
                      (operandCursor
                        { input with cursor := input.cursor + 1 } right next
                          operandResult)
                  have combinedBefore : ∀ future,
                      next.peek? = some future →
                      (binaryNode left operator right).span.startByte ≤
                        future.span.startByte := by
                    intro future futureFound
                    have futureAtNext :=
                      State.getElem?_eq_some_of_peek?_eq_some futureFound
                    have futureAt : input.tokens[next.cursor]? = some future := by
                      simpa [tokensEq] using futureAtNext
                    have beforeFuture :=
                      inputValid.token_end_le_token_start_of_getElem?_lt
                        operatorAt futureAt cursorOrder
                    rw [binaryNode_startByte]
                    exact Nat.le_trans (leftBefore operatorToken operatorFound)
                      (Nat.le_trans operatorSpanValid.2.1 beforeFuture)
                  have recursive := inductionHypothesis
                    (binaryNode left operator right) next rightReply.2.1
                      combinedValidNext combinedBefore
                  simp only
                  exact recursive.of_file_eq
                    (rightReply.2.2.trans consumedReply.2.2)

/-- A complete left-associative layer preserves every ordinary token window. -/
theorem leftAssociative_preservesTokenWindow (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) :
    Parser.PreservesTokenWindow (leftAssociative operand precedence) := by
  intro input
  unfold leftAssociative
  have operandShape := operandWindow input
  cases operandResult : operand input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [operandResult] at operandShape
      exact operandShape
  | ok left next =>
      rw [operandResult] at operandShape
      exact (leftAssociativeTail_preservesTokenWindow operand operandWindow
        precedence (next.remainingCount + 1) left next).trans operandShape

theorem leftAssociative_preservesTokensOnSuccess (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) :
    Parser.PreservesTokensOnSuccess (leftAssociative operand precedence) :=
  (leftAssociative_preservesTokenWindow operand operandWindow
    precedence).preservesTokensOnSuccess

/-- A complete left-associative layer never rewinds the parser cursor. -/
theorem leftAssociative_cursorMonotoneOnSuccess (operand : Parser Expr)
    (operandCursor : Parser.CursorMonotoneOnSuccess operand)
    (precedence : Nat) :
    Parser.CursorMonotoneOnSuccess (leftAssociative operand precedence) := by
  intro input expression final parsed
  unfold leftAssociative at parsed
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at parsed
  | reject failure rejected => simp [operandResult] at parsed
  | ok left next =>
      simp only [operandResult] at parsed
      exact Nat.le_trans (operandCursor input left next operandResult)
        (leftAssociativeTail_cursorMonotoneOnSuccess operand operandCursor
          precedence (next.remainingCount + 1) left next expression final
            parsed)

/-- A complete left-associative layer retains its first operand's token. -/
theorem leftAssociative_startsAtCurrentTokenOnSuccess
    (operand : Parser Expr)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) :
    Parser.StartsAtCurrentTokenOnSuccess
      (leftAssociative operand precedence) (·.span) := by
  intro input expression final parsed
  unfold leftAssociative at parsed
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at parsed
  | reject failure rejected => simp [operandResult] at parsed
  | ok left next =>
      simp only [operandResult] at parsed
      rcases operandStarts input left next operandResult with
        ⟨first, found, starts⟩
      have retained := leftAssociativeTail_preservesLeftStartOnSuccess operand
        precedence (next.remainingCount + 1) left next expression final parsed
      exact ⟨first, found, starts.trans retained.symm⟩

/-- A complete left-associative layer retains all recursive source ranges. -/
theorem leftAssociative_validFor
    (operand : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (operandValid : operand.ValidFor (Expr.ValidFor statementValid))
    (operandTokens : Parser.PreservesTokensOnSuccess operand)
    (operandCursorLt : ∀ {input next : State} {value : Expr},
      operand input = .ok value next → input.cursor < next.cursor)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) :
    (leftAssociative operand precedence).ValidFor
      (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold leftAssociative
  cases operandResult : operand input with
  | invariant error => trivial
  | reject failure rejected =>
      have rejectedValid := operandValid input inputValid
      rw [operandResult] at rejectedValid
      exact rejectedValid
  | ok left next =>
      have leftReply := operandValid input inputValid
      rw [operandResult] at leftReply
      have leftValidNext : Expr.ValidFor statementValid next.file left := by
        simpa [leftReply.2.2] using leftReply.1
      have tokensEq := operandTokens input left next operandResult
      rcases operandStarts input left next operandResult with
        ⟨first, firstFound, firstStart⟩
      have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
      have firstValid := inputValid.peek?_span_validFor firstFound
      have leftBefore : ∀ token, next.peek? = some token →
          left.span.startByte ≤ token.span.startByte := by
        intro token found
        have tokenAtNext := State.getElem?_eq_some_of_peek?_eq_some found
        have tokenAt : input.tokens[next.cursor]? = some token := by
          simpa [tokensEq] using tokenAtNext
        have separated := inputValid.token_end_le_token_start_of_getElem?_lt
          firstAt tokenAt (operandCursorLt operandResult)
        exact Nat.le_trans (by simpa [firstStart] using firstValid.2.1)
          separated
      have recursive := leftAssociativeTail_validFor operand statementValid
        operandValid operandTokens
          (fun _ _ _ result => Nat.le_of_lt (operandCursorLt result))
          operandStarts precedence (next.remainingCount + 1) left next
          leftReply.2.1 leftValidNext leftBefore
      exact recursive.of_file_eq leftReply.2.2

/-- A non-associative precedence layer preserves every ordinary token window. -/
theorem nonAssociative_preservesTokenWindow (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) :
    Parser.PreservesTokenWindow (nonAssociative operand precedence) := by
  intro input
  unfold nonAssociative
  have leftShape := operandWindow input
  cases leftResult : operand input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [leftResult] at leftShape
      exact leftShape
  | ok left next =>
      rw [leftResult] at leftShape
      simp only
      cases operatorResult : binaryAtPrecedence? next precedence with
      | none =>
          simp only
          exact leftShape
      | some operator =>
          simp only
          have consumedShape := consumeBinary_preservesTokenWindow
            operator next
          cases consumedResult : consumeBinary operator next with
          | invariant error =>
              simp only
              trivial
          | reject failure rejected =>
              rw [consumedResult] at consumedShape
              simp only
              exact consumedShape.trans leftShape
          | ok value afterOperator =>
              rw [consumedResult] at consumedShape
              simp only
              have rightShape := operandWindow afterOperator
              cases rightResult : operand afterOperator with
              | invariant error =>
                  simp only
                  trivial
              | reject failure rejected =>
                  rw [rightResult] at rightShape
                  simp only
                  exact rightShape.trans (consumedShape.trans leftShape)
              | ok right final =>
                  rw [rightResult] at rightShape
                  simp only
                  exact rightShape.trans (consumedShape.trans leftShape)

theorem nonAssociative_preservesTokensOnSuccess (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) :
    Parser.PreservesTokensOnSuccess (nonAssociative operand precedence) :=
  (nonAssociative_preservesTokenWindow operand operandWindow
    precedence).preservesTokensOnSuccess

/-- A non-associative precedence layer never rewinds the parser cursor. -/
theorem nonAssociative_cursorMonotoneOnSuccess (operand : Parser Expr)
    (operandCursor : Parser.CursorMonotoneOnSuccess operand)
    (precedence : Nat) :
    Parser.CursorMonotoneOnSuccess (nonAssociative operand precedence) := by
  intro input expression final parsed
  unfold nonAssociative at parsed
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at parsed
  | reject failure rejected => simp [leftResult] at parsed
  | ok left next =>
      simp only [leftResult] at parsed
      have leftMonotone := operandCursor input left next leftResult
      cases operatorResult : binaryAtPrecedence? next precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          exact leftMonotone
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator next with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              have consumedMonotone :=
                consumeBinary_cursorMonotoneOnSuccess operator next value
                  afterOperator consumedResult
              cases rightResult : operand afterOperator with
              | invariant error => simp [rightResult] at parsed
              | reject failure rejected => simp [rightResult] at parsed
              | ok right afterRight =>
                  simp only [rightResult] at parsed
                  have rightMonotone :=
                    operandCursor afterOperator right afterRight rightResult
                  cases parsed
                  exact Nat.le_trans leftMonotone
                    (Nat.le_trans consumedMonotone rightMonotone)

/-- A non-associative layer retains its first operand's start token. -/
theorem nonAssociative_startsAtCurrentTokenOnSuccess
    (operand : Parser Expr)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) :
    Parser.StartsAtCurrentTokenOnSuccess
      (nonAssociative operand precedence) (·.span) := by
  intro input expression final parsed
  unfold nonAssociative at parsed
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at parsed
  | reject failure rejected => simp [leftResult] at parsed
  | ok left next =>
      simp only [leftResult] at parsed
      rcases operandStarts input left next leftResult with
        ⟨first, found, starts⟩
      cases operatorResult : binaryAtPrecedence? next precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          exact ⟨first, found, starts⟩
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator next with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              cases rightResult : operand afterOperator with
              | invariant error => simp [rightResult] at parsed
              | reject failure rejected => simp [rightResult] at parsed
              | ok right afterRight =>
                  simp only [rightResult] at parsed
                  cases parsed
                  exact ⟨first, found, by simpa using starts⟩

/-- A non-associative precedence layer retains all recursive source ranges. -/
theorem nonAssociative_validFor
    (operand : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (operandValid : operand.ValidFor (Expr.ValidFor statementValid))
    (operandTokens : Parser.PreservesTokensOnSuccess operand)
    (operandCursorLt : ∀ {input next : State} {value : Expr},
      operand input = .ok value next → input.cursor < next.cursor)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) :
    (nonAssociative operand precedence).ValidFor
      (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold nonAssociative
  cases leftResult : operand input with
  | invariant error => trivial
  | reject failure rejected =>
      have rejectedValid := operandValid input inputValid
      rw [leftResult] at rejectedValid
      exact rejectedValid
  | ok left next =>
      have leftReply := operandValid input inputValid
      rw [leftResult] at leftReply
      simp only
      cases operatorResult : binaryAtPrecedence? next precedence with
      | none =>
          simp only
          exact leftReply
      | some operator =>
          simp only
          rcases binaryAtPrecedence?_some_state_shape operatorResult with
            ⟨operatorToken, operatorFound, _decoded, _operatorSpan⟩
          have operatorValidNext := binaryAtPrecedence?_validFor
            leftReply.2.1 operatorResult
          have leftTokens := operandTokens input left next leftResult
          rcases operandStarts input left next leftResult with
            ⟨leftToken, leftFound, leftStart⟩
          have leftAt := State.getElem?_eq_some_of_peek?_eq_some leftFound
          have operatorAtNext :=
            State.getElem?_eq_some_of_peek?_eq_some operatorFound
          have operatorAt : input.tokens[next.cursor]? = some operatorToken := by
            simpa [leftTokens] using operatorAtNext
          have beforeOperator :=
            inputValid.token_end_le_token_start_of_getElem?_lt leftAt
              operatorAt (operandCursorLt leftResult)
          have leftTokenValid := inputValid.peek?_span_validFor leftFound
          have leftBeforeOperator : left.span.startByte ≤
              operatorToken.span.startByte := by
            exact Nat.le_trans
              (by simpa [leftStart] using leftTokenValid.2.1) beforeOperator
          have consumedReply := consumeBinary_reply_validFor operator
            leftReply.2.1 operatorFound
          cases consumedResult : consumeBinary operator next with
          | invariant error =>
              simp only
              trivial
          | reject failure rejected =>
              rw [consumedResult] at consumedReply
              simp only
              exact consumedReply.of_file_eq leftReply.2.2
          | ok value afterOperator =>
              rw [consumedResult] at consumedReply
              have exactConsumed := consumeBinary_ok_state_shape operator next
              rw [consumedResult] at exactConsumed
              cases exactConsumed
              simp only
              cases rightResult : operand
                  { next with cursor := next.cursor + 1 } with
              | invariant error =>
                  simp only
                  trivial
              | reject failure rejected =>
                  have rejectedValid := operandValid
                    { next with cursor := next.cursor + 1 }
                    consumedReply.2.1
                  rw [rightResult] at rejectedValid
                  simp only
                  exact rejectedValid.of_file_eq
                    (consumedReply.2.2.trans leftReply.2.2)
              | ok right afterRight =>
                  have rightReply := operandValid
                    { next with cursor := next.cursor + 1 }
                    consumedReply.2.1
                  rw [rightResult] at rightReply
                  have rightValidInput :
                      Expr.ValidFor statementValid input.file right := by
                    simpa [rightReply.2.2, consumedReply.2.2,
                      leftReply.2.2] using rightReply.1
                  rcases operandStarts
                      { next with cursor := next.cursor + 1 } right afterRight
                      rightResult with
                    ⟨rightToken, rightFound, rightStart⟩
                  have rightAtAfter :=
                    State.getElem?_eq_some_of_peek?_eq_some rightFound
                  have rightAt : input.tokens[next.cursor + 1]? =
                      some rightToken := by
                    simpa [leftTokens] using rightAtAfter
                  have operatorBeforeRight :=
                    inputValid.token_end_le_token_start_of_getElem?_lt
                      operatorAt rightAt (by omega)
                  have operatorTokenValid :=
                    inputValid.token_span_validFor_of_getElem?_eq_some
                      operatorAt
                  have ordered : left.span.startByte ≤ right.span.endByte := by
                    calc
                      left.span.startByte ≤ operatorToken.span.startByte :=
                        leftBeforeOperator
                      _ ≤ operatorToken.span.endByte := operatorTokenValid.2.1
                      _ ≤ rightToken.span.startByte := operatorBeforeRight
                      _ = right.span.startByte := rightStart
                      _ ≤ right.span.endByte := rightValidInput.span_valid.2.1
                  have operatorValidInput : Located.ValidFor input.file
                      operator := by
                    simpa [leftReply.2.2] using operatorValidNext
                  have binaryValid := binaryNode_validFor statementValid
                    input.file left operator right leftReply.1
                      operatorValidInput rightValidInput ordered
                  exact ⟨binaryValid, rightReply.2.1,
                    rightReply.2.2.trans
                      (consumedReply.2.2.trans leftReply.2.2)⟩

end ExpressionInternals
end Solcore.Syntax.Parser
