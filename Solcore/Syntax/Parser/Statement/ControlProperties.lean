import Solcore.Syntax.Parser.Statement.Control
import Solcore.Syntax.Parser.Statement.SimpleProperties
import Solcore.Syntax.Parser.Yul.StatementProperties
import Solcore.Syntax.StatementValidity

/-! Contracts for canonical Core control-statement parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem controlBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
      next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

namespace ControlInternals

/-- The comma loop retains every accumulated and newly parsed for item. -/
theorem forItemsTail_validFor
    (expression : Parser Expr) (stop : Symbol)
    (expressionValueValid : SourceFile → Expr → Prop)
    (itemContract : (forItem expression).ValidFor
      (ForItem.ValidFor expressionValueValid)) :
    ∀ fuel itemsRev input, input.ValidFor →
      List.ValidFor (ForItem.ValidFor expressionValueValid)
        input.file itemsRev →
      (forItemsTail expression stop fuel itemsRev input).ValidFor input
        (List.ValidFor (ForItem.ValidFor expressionValueValid)) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro itemsRev input inputValid itemsValid
      unfold forItemsTail
      by_cases commaPresent : isSymbol input .comma
      · simp only [commaPresent, if_true]
        cases commaResult : symbol .comma .statement input with
        | invariant error => trivial
        | reject failure rejected =>
            have reply := symbol_validFor .comma .statement input inputValid
            rw [commaResult] at reply
            exact reply
        | ok comma afterComma =>
            have commaReply := symbol_validFor .comma .statement input inputValid
            rw [commaResult] at commaReply
            simp only
            by_cases stopped : isSymbol afterComma stop
            · simp only [stopped, if_true]
              have rejected := rejectAt_reject_validFor
                (α := List ForItem) commaReply.2.1
                { head := .expression, tail := [] } .statement rfl
              exact ⟨by simpa [commaReply.2.2] using rejected.1,
                rejected.2.1, rejected.2.2.trans commaReply.2.2⟩
            · simp only [stopped]
              cases itemResult : forItem expression afterComma with
              | invariant error => trivial
              | reject failure rejected =>
                  have reply := itemContract afterComma commaReply.2.1
                  rw [itemResult] at reply
                  exact reply.of_file_eq commaReply.2.2
              | ok item next =>
                  have itemReply := itemContract afterComma commaReply.2.1
                  rw [itemResult] at itemReply
                  by_cases progress : next.cursor > afterComma.cursor
                  · simp only [progress, if_true]
                    have accumulated : List.ValidFor
                        (ForItem.ValidFor expressionValueValid) next.file
                        (item :: itemsRev) := by
                      intro retained member
                      rcases List.mem_cons.mp member with rfl | member
                      · simpa [itemReply.2.2] using itemReply.1
                      · simpa [itemReply.2.2, commaReply.2.2] using
                          itemsValid retained member
                    exact (inductionHypothesis (item :: itemsRev) next
                      itemReply.2.1 accumulated).of_file_eq
                        (itemReply.2.2.trans commaReply.2.2)
                  · simp only [progress]
                    trivial
      · simp only [commaPresent]
        exact ⟨by
          intro retained member
          exact itemsValid retained (by simpa using member), inputValid, rfl⟩

/-- The comma loop preserves complete token windows. -/
theorem forItemsTail_preservesTokenWindow
    (expression : Parser Expr) (stop : Symbol)
    (itemWindow : Parser.PreservesTokenWindow (forItem expression)) :
    ∀ fuel itemsRev,
      Parser.PreservesTokenWindow
        (forItemsTail expression stop fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero => intro itemsRev input; trivial
  | succ fuel inductionHypothesis =>
      intro itemsRev input
      unfold forItemsTail
      by_cases commaPresent : isSymbol input .comma
      · simp only [commaPresent, if_true]
        have commaWindow := symbol_preservesTokenWindow .comma .statement input
        cases commaResult : symbol .comma .statement input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [commaResult] at commaWindow
            exact commaWindow
        | ok comma afterComma =>
            rw [commaResult] at commaWindow
            simp only
            by_cases stopped : isSymbol afterComma stop
            · simp only [stopped, if_true]
              exact (rejectAt_preservesTokenWindow afterComma _ _).trans
                commaWindow
            · simp only [stopped]
              have itemShape := itemWindow afterComma
              cases itemResult : forItem expression afterComma with
              | invariant error => trivial
              | reject failure rejected =>
                  rw [itemResult] at itemShape
                  exact itemShape.trans commaWindow
              | ok item next =>
                  rw [itemResult] at itemShape
                  by_cases progress : next.cursor > afterComma.cursor
                  · simp only [progress, if_true]
                    exact ((inductionHypothesis (item :: itemsRev) next).trans
                      itemShape).trans commaWindow
                  · simp only [progress]
                    trivial
      · simp only [commaPresent]
        exact ⟨rfl, rfl⟩

/-- Successful comma-loop parsing never rewinds its caller. -/
theorem forItemsTail_cursorMonotoneOnSuccess
    (expression : Parser Expr) (stop : Symbol)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    ∀ fuel itemsRev,
      Parser.CursorMonotoneOnSuccess
        (forItemsTail expression stop fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items next parsed
      unfold forItemsTail at parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro itemsRev input items next parsed
      unfold forItemsTail at parsed
      by_cases commaPresent : isSymbol input .comma
      · simp only [commaPresent, if_true] at parsed
        cases commaResult : symbol .comma .statement input with
        | invariant error => simp [commaResult] at parsed
        | reject failure rejected => simp [commaResult] at parsed
        | ok comma afterComma =>
            simp only [commaResult] at parsed
            by_cases stopped : isSymbol afterComma stop
            · simp [stopped, rejectAt] at parsed
            · simp only [stopped] at parsed
              cases itemResult : forItem expression afterComma with
              | invariant error => simp [itemResult] at parsed
              | reject failure rejected => simp [itemResult] at parsed
              | ok item afterItem =>
                  simp only [itemResult] at parsed
                  by_cases progress : afterItem.cursor > afterComma.cursor
                  · simp only [progress, if_true] at parsed
                    exact Nat.le_trans
                      (symbol_cursorMonotoneOnSuccess .comma .statement input
                        comma afterComma commaResult)
                      (Nat.le_trans
                        (forItem_cursorMonotoneOnSuccess expression
                          expressionCursor afterComma item afterItem itemResult)
                        (inductionHypothesis (item :: itemsRev) afterItem items
                          next parsed))
                  · simp [progress] at parsed
      · simp only [commaPresent] at parsed
        cases parsed
        exact Nat.le_refl _

/-- A complete for-item list retains source provenance. -/
theorem forItems_validFor
    (expression : Parser Expr) (stop : Symbol)
    (expressionValueValid : SourceFile → Expr → Prop)
    (itemContract : (forItem expression).ValidFor
      (ForItem.ValidFor expressionValueValid)) :
    (forItems expression stop).ValidFor
      (List.ValidFor (ForItem.ValidFor expressionValueValid)) := by
  intro input inputValid
  unfold forItems
  by_cases stopped : isSymbol input stop
  · simp only [stopped, if_true]
    exact ⟨by simp [List.ValidFor], inputValid, rfl⟩
  · simp only [stopped]
    cases itemResult : forItem expression input with
    | invariant error => trivial
    | reject failure rejected =>
        have reply := itemContract input inputValid
        rw [itemResult] at reply
        exact reply
    | ok item next =>
        have itemReply := itemContract input inputValid
        rw [itemResult] at itemReply
        exact (forItemsTail_validFor expression stop expressionValueValid
          itemContract (next.remainingCount + 1) [item] next itemReply.2.1
          (by simpa [List.ValidFor, itemReply.2.2] using itemReply.1)).of_file_eq
            itemReply.2.2

/-- Complete for-item lists preserve every ordinary token window. -/
theorem forItems_preservesTokenWindow
    (expression : Parser Expr) (stop : Symbol)
    (itemWindow : Parser.PreservesTokenWindow (forItem expression)) :
    Parser.PreservesTokenWindow (forItems expression stop) := by
  intro input
  unfold forItems
  by_cases stopped : isSymbol input stop
  · simp only [stopped, if_true]
    exact ⟨rfl, rfl⟩
  · simp only [stopped]
    have itemShape := itemWindow input
    cases itemResult : forItem expression input with
    | invariant error => trivial
    | reject failure rejected => rw [itemResult] at itemShape; exact itemShape
    | ok item next =>
        rw [itemResult] at itemShape
        exact (forItemsTail_preservesTokenWindow expression stop itemWindow
          (next.remainingCount + 1) [item] next).trans itemShape

theorem forItems_preservesTokensOnSuccess
    (expression : Parser Expr) (stop : Symbol)
    (itemWindow : Parser.PreservesTokenWindow (forItem expression)) :
    Parser.PreservesTokensOnSuccess (forItems expression stop) :=
  (forItems_preservesTokenWindow expression stop
    itemWindow).preservesTokensOnSuccess

/-- Successful complete for-item lists never rewind their caller. -/
theorem forItems_cursorMonotoneOnSuccess
    (expression : Parser Expr) (stop : Symbol)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (forItems expression stop) := by
  intro input items next parsed
  unfold forItems at parsed
  by_cases stopped : isSymbol input stop
  · simp only [stopped, if_true] at parsed
    cases parsed
    exact Nat.le_refl _
  · simp only [stopped] at parsed
    cases itemResult : forItem expression input with
    | invariant error => simp [itemResult] at parsed
    | reject failure rejected => simp [itemResult] at parsed
    | ok item afterItem =>
        simp only [itemResult] at parsed
        exact Nat.le_trans
          (forItem_cursorMonotoneOnSuccess expression expressionCursor input
            item afterItem itemResult)
          (forItemsTail_cursorMonotoneOnSuccess expression stop
            expressionCursor (afterItem.remainingCount + 1) [item]
              afterItem items next parsed)

end ControlInternals

/-- For statements preserve every nested parser token window. -/
theorem forStatement_preservesTokenWindow
    (statement : Parser Statement) (expression : Parser Expr)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (forStatement statement expression) := by
  unfold forStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .forKw .statement); intro marker
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .leftParen .statement); intro opening
  apply Parser.bind_preservesTokenWindow
    (ControlInternals.forItems_preservesTokenWindow expression .semicolon
      (forItem_preservesTokenWindow expression expressionWindow)); intro initial
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .statement); intro firstSeparator
  apply Parser.bind_preservesTokenWindow expressionWindow; intro condition
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .statement); intro secondSeparator
  apply Parser.bind_preservesTokenWindow
    (ControlInternals.forItems_preservesTokenWindow expression .rightParen
      (forItem_preservesTokenWindow expression expressionWindow)); intro post
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightParen .statement); intro closing
  apply Parser.bind_preservesTokenWindow
    (coreBlock_preservesTokenWindow statement .require statementWindow); intro body
  exact Parser.pure_preservesTokenWindow _

theorem forStatement_preservesTokensOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (forStatement statement expression) :=
  (forStatement_preservesTokenWindow statement expression statementWindow
    expressionWindow).preservesTokensOnSuccess

/-- For-statement parsing never rewinds the token cursor. -/
theorem forStatement_cursorMonotoneOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (forStatement statement expression) := by
  unfold forStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .forKw .statement); intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement); intro opening
  apply Parser.bind_cursorMonotoneOnSuccess
    (ControlInternals.forItems_cursorMonotoneOnSuccess expression .semicolon
      expressionCursor); intro initial
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro firstSeparator
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor; intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro secondSeparator
  apply Parser.bind_cursorMonotoneOnSuccess
    (ControlInternals.forItems_cursorMonotoneOnSuccess expression .rightParen
      expressionCursor); intro post
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement); intro closing
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require); intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A complete for statement starts at its leading keyword. -/
theorem forStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (forStatement statement expression) (·.span) := by
  unfold forStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .forKw)
      .statement (· == .keyword .forKw))
  intro marker input parsedStatement final parsed
  rcases controlBind_ok_components parsed with ⟨_, _, _, rest⟩
  rcases controlBind_ok_components rest with ⟨_, _, _, rest⟩
  rcases controlBind_ok_components rest with ⟨_, _, _, rest⟩
  rcases controlBind_ok_components rest with ⟨_, _, _, rest⟩
  rcases controlBind_ok_components rest with ⟨_, _, _, rest⟩
  rcases controlBind_ok_components rest with ⟨_, _, _, rest⟩
  rcases controlBind_ok_components rest with ⟨_, _, _, rest⟩
  rcases controlBind_ok_components rest with ⟨_, _, _, finished⟩
  cases finished
  rfl

/-- For statements retain both header and body provenance on every result. -/
theorem forStatement_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursorLt : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    (forStatement statement expression).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid) := by
  let itemContract := forItem_validFor expression expressionValueValid
    expressionValid expressionSpan expressionWindow expressionCursorLt
      expressionStarts
  let itemWindow := forItem_preservesTokenWindow expression expressionWindow
  let expressionCursor : Parser.CursorMonotoneOnSuccess expression :=
    fun _ _ _ result => Nat.le_of_lt (expressionCursorLt result)
  let listValid (stop : Symbol) := ControlInternals.forItems_validFor
    expression stop expressionValueValid itemContract
  let bodyValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
      (fun _ _ valid => valid.span_valid)
  have weak : (forStatement statement expression).ValidFor
      (fun _ _ => True) := by
    unfold forStatement
    apply Parser.bind_validFor (keyword_validFor .forKw .statement); intro marker
    apply Parser.bind_validFor (symbol_validFor .leftParen .statement); intro opening
    apply Parser.bind_validFor (listValid .semicolon); intro initial
    apply Parser.bind_validFor (symbol_validFor .semicolon .statement); intro sep1
    apply Parser.bind_validFor expressionValid; intro condition
    apply Parser.bind_validFor (symbol_validFor .semicolon .statement); intro sep2
    apply Parser.bind_validFor (listValid .rightParen); intro post
    apply Parser.bind_validFor (symbol_validFor .rightParen .statement); intro closing
    apply Parser.bind_validFor bodyValid; intro body
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  intro input inputValid
  have weakReply := weak input inputValid
  cases parsed : forStatement statement expression input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weakReply; exact weakReply
  | ok parsedStatement final =>
      rw [parsed] at weakReply
      have stages := parsed
      unfold forStatement at stages
      rcases controlBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨opening, afterOpening, openingResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨initial, afterInitial, initialResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨sep1, afterSep1, sep1Result, rest⟩
      rcases controlBind_ok_components rest with
        ⟨condition, afterCondition, conditionResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨sep2, afterSep2, sep2Result, rest⟩
      rcases controlBind_ok_components rest with
        ⟨post, afterPost, postResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨closing, afterClosing, closingResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerReply := keyword_validFor .forKw .statement input inputValid
      rw [markerResult] at markerReply
      have openingReply := symbol_validFor .leftParen .statement afterMarker
        markerReply.2.1
      rw [openingResult] at openingReply
      have initialReply := listValid .semicolon afterOpening openingReply.2.1
      rw [initialResult] at initialReply
      have sep1Reply := symbol_validFor .semicolon .statement afterInitial
        initialReply.2.1
      rw [sep1Result] at sep1Reply
      have conditionReply := expressionValid afterSep1 sep1Reply.2.1
      rw [conditionResult] at conditionReply
      have sep2Reply := symbol_validFor .semicolon .statement afterCondition
        conditionReply.2.1
      rw [sep2Result] at sep2Reply
      have postReply := listValid .rightParen afterSep2 sep2Reply.2.1
      rw [postResult] at postReply
      have closingReply := symbol_validFor .rightParen .statement afterPost
        postReply.2.1
      rw [closingResult] at closingReply
      have bodyReply := bodyValid afterClosing closingReply.2.1
      rw [bodyResult] at bodyReply
      have markerSpan : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerReply.1
      have openingSpan : opening.span.ValidFor input.file := by
        simpa only [Located.ValidFor, markerReply.2.2] using openingReply.1
      have closingSpan : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor, postReply.2.2, sep2Reply.2.2, conditionReply.2.2,
          sep1Reply.2.2, initialReply.2.2, openingReply.2.2,
          markerReply.2.2] using closingReply.1
      have initialValid : List.ValidFor
          (ForItem.ValidFor expressionValueValid) input.file initial := by
        simpa [openingReply.2.2, markerReply.2.2] using initialReply.1
      have conditionValid : expressionValueValid input.file condition := by
        simpa [sep1Reply.2.2, initialReply.2.2, openingReply.2.2,
          markerReply.2.2] using conditionReply.1
      have postValid : List.ValidFor (ForItem.ValidFor expressionValueValid)
          input.file post := by
        simpa [sep2Reply.2.2, conditionReply.2.2, sep1Reply.2.2,
          initialReply.2.2, openingReply.2.2, markerReply.2.2] using postReply.1
      have bodyInput : Block.ValidFor
          (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
          input.file body := by
        simpa [bodyReply.2.2, closingReply.2.2, postReply.2.2,
          sep2Reply.2.2, conditionReply.2.2, sep1Reply.2.2,
          initialReply.2.2, openingReply.2.2, markerReply.2.2] using bodyReply.1
      have markerTokens := keyword_preservesTokensOnSuccess .forKw .statement
        input marker afterMarker markerResult
      have openingTokens := symbol_preservesTokensOnSuccess .leftParen .statement
        afterMarker opening afterOpening openingResult
      have initialTokens := ControlInternals.forItems_preservesTokensOnSuccess
        expression .semicolon itemWindow afterOpening initial afterInitial initialResult
      have sep1Tokens := symbol_preservesTokensOnSuccess .semicolon .statement
        afterInitial sep1 afterSep1 sep1Result
      have conditionTokens := expressionWindow.preservesTokensOnSuccess
        afterSep1 condition afterCondition conditionResult
      have sep2Tokens := symbol_preservesTokensOnSuccess .semicolon .statement
        afterCondition sep2 afterSep2 sep2Result
      have postTokens := ControlInternals.forItems_preservesTokensOnSuccess
        expression .rightParen itemWindow afterSep2 post afterPost postResult
      have closingTokens := symbol_preservesTokensOnSuccess .rightParen .statement
        afterPost closing afterClosing closingResult
      have headerCursor : afterMarker.cursor < afterPost.cursor :=
        Nat.lt_of_lt_of_le (acceptToken_cursor_lt_onSuccess
          (.symbol .leftParen) .statement (· == .symbol .leftParen) openingResult)
          (Nat.le_trans (ControlInternals.forItems_cursorMonotoneOnSuccess
            expression .semicolon expressionCursor afterOpening initial
              afterInitial initialResult) (Nat.le_trans
            (symbol_cursorMonotoneOnSuccess .semicolon .statement _ _ _ sep1Result)
            (Nat.le_trans (expressionCursor _ _ _ conditionResult) (Nat.le_trans
              (symbol_cursorMonotoneOnSuccess .semicolon .statement _ _ _ sep2Result)
              (ControlInternals.forItems_cursorMonotoneOnSuccess expression
                .rightParen expressionCursor _ _ _ postResult)))))
      have openingAt := State.getElem?_eq_some_of_peek?_eq_some
        (symbol_ok_state_shape .leftParen .statement openingResult).1
      have closingAtAfter := State.getElem?_eq_some_of_peek?_eq_some
        (symbol_ok_state_shape .rightParen .statement closingResult).1
      have closingAt : afterMarker.tokens[afterPost.cursor]? = some closing := by
        simpa [postTokens, sep2Tokens, conditionTokens, sep1Tokens,
          initialTokens, openingTokens] using closingAtAfter
      have headerSeparated := markerReply.2.1.token_end_le_token_start_of_getElem?_lt
        openingAt closingAt headerCursor
      have headerValid := SourceSpan.cover_validFor openingSpan closingSpan
        (Nat.le_trans openingSpan.2.1
          (Nat.le_trans headerSeparated closingSpan.2.1))
      rcases coreBlock_startsAtCurrentTokenOnSuccess statement .require
          afterClosing body afterBody bodyResult with
        ⟨bodyOpening, bodyFound, bodyStart⟩
      have bodyAtAfter := State.getElem?_eq_some_of_peek?_eq_some bodyFound
      have bodyAt : input.tokens[afterClosing.cursor]? = some bodyOpening := by
        simpa [closingTokens, postTokens, sep2Tokens, conditionTokens,
          sep1Tokens, initialTokens, openingTokens, markerTokens] using bodyAtAfter
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some
        (acceptToken_ok_state_shape (.keyword .forKw) .statement
          (· == .keyword .forKw) markerResult).1
      have beforeBody : input.cursor < afterClosing.cursor :=
        Nat.lt_of_lt_of_le (acceptToken_cursor_lt_onSuccess (.keyword .forKw)
          .statement (· == .keyword .forKw) markerResult)
          (Nat.le_trans (symbol_cursorMonotoneOnSuccess .leftParen .statement
            _ _ _ openingResult) (Nat.le_trans
            (ControlInternals.forItems_cursorMonotoneOnSuccess expression
              .semicolon expressionCursor _ _ _ initialResult) (Nat.le_trans
            (symbol_cursorMonotoneOnSuccess .semicolon .statement _ _ _ sep1Result)
            (Nat.le_trans (expressionCursor _ _ _ conditionResult) (Nat.le_trans
            (symbol_cursorMonotoneOnSuccess .semicolon .statement _ _ _ sep2Result)
            (Nat.le_trans (ControlInternals.forItems_cursorMonotoneOnSuccess
              expression .rightParen expressionCursor _ _ _ postResult)
              (symbol_cursorMonotoneOnSuccess .rightParen .statement _ _ _
                closingResult)))))))
      have outerSeparated := inputValid.token_end_le_token_start_of_getElem?_lt
        markerAt bodyAt beforeBody
      have outerValid := SourceSpan.cover_validFor markerSpan bodyInput.1
        (Nat.le_trans markerSpan.2.1 (Nat.le_trans outerSeparated
          (by simpa [bodyStart] using bodyInput.1.2.1)))
      cases finished
      exact ⟨Statement.ValidFor.forLoop outerValid headerValid initialValid
        conditionValid postValid bodyInput.1 bodyInput.2,
        weakReply.2.1, weakReply.2.2⟩

/-- A braced statement wrapper retains the block range and every body item. -/
theorem blockStatement_validFor
    (statement : Parser Statement)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement) :
    (blockStatement statement).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  unfold blockStatement
  apply Parser.bind_validFor_of_value
    (coreBlock_validFor
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      statement .require statementValid statementTokens
      (fun _ _ valid => valid.span_valid))
  intro body next nextValid bodyValid
  exact ⟨Statement.ValidFor.block bodyValid.1 bodyValid.2, nextValid, rfl⟩

/-- Braced statement wrappers preserve the complete token window. -/
theorem blockStatement_preservesTokenWindow
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (blockStatement statement) := by
  unfold blockStatement
  apply Parser.bind_preservesTokenWindow
    (coreBlock_preservesTokenWindow statement .require statementWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Braced statement wrappers retain the immutable token carrier on success. -/
theorem blockStatement_preservesTokensOnSuccess
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokensOnSuccess (blockStatement statement) :=
  (blockStatement_preservesTokenWindow statement
    statementWindow).preservesTokensOnSuccess

/-- A braced statement wrapper never rewinds the token cursor. -/
theorem blockStatement_cursorMonotoneOnSuccess
    (statement : Parser Statement) :
    Parser.CursorMonotoneOnSuccess (blockStatement statement) := by
  unfold blockStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A braced statement wrapper starts at its opening brace. -/
theorem blockStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) :
    Parser.StartsAtCurrentTokenOnSuccess
      (blockStatement statement) (·.span) := by
  unfold blockStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (coreBlock_startsAtCurrentTokenOnSuccess statement .require)
  intro body input wrapped final parsed
  cases parsed
  rfl

/-- A successful `while` statement retains a valid keyword-to-body range. -/
theorem whileStatement_span_validOnSuccess
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionTokens : Parser.PreservesTokensOnSuccess expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {parsedStatement : Statement}
    (inputValid : input.ValidFor)
    (parsed : whileStatement statement expression input =
      .ok parsedStatement final) :
    parsedStatement.span.ValidFor input.file := by
  have stages := parsed
  unfold whileStatement at stages
  rcases controlBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨condition, afterCondition, conditionResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  have markerReply := contextual_validFor .while .statement input inputValid
  rw [markerResult] at markerReply
  have openingReply := symbol_validFor .leftParen .statement afterMarker
    markerReply.2.1
  rw [openingResult] at openingReply
  have conditionReply := expressionValid afterOpening openingReply.2.1
  rw [conditionResult] at conditionReply
  have closingReply := symbol_validFor .rightParen .statement afterCondition
    conditionReply.2.1
  rw [closingResult] at closingReply
  have bodyParserValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  have bodyReply := bodyParserValid afterClosing closingReply.2.1
  rw [bodyResult] at bodyReply
  have markerValid : marker.span.ValidFor input.file := by
    simpa only [Located.ValidFor] using markerReply.1
  have bodyValid : Block.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      input.file body := by
    simpa [bodyReply.2.2, closingReply.2.2, conditionReply.2.2,
      openingReply.2.2, markerReply.2.2] using bodyReply.1
  rcases coreBlock_startsAtCurrentTokenOnSuccess statement .require
      afterClosing body afterBody bodyResult with
    ⟨bodyOpening, bodyOpeningFound, bodyStart⟩
  have markerAt := State.getElem?_eq_some_of_peek?_eq_some
    (acceptToken_ok_state_shape (.contextual .while) .statement
      (·.isContextual .while) markerResult).1
  have bodyOpeningAtAfter :=
    State.getElem?_eq_some_of_peek?_eq_some bodyOpeningFound
  have bodyOpeningAt : input.tokens[afterClosing.cursor]? =
      some bodyOpening := by
    simpa [
      contextual_preservesTokensOnSuccess .while .statement input marker
        afterMarker markerResult,
      symbol_preservesTokensOnSuccess .leftParen .statement afterMarker
        opening afterOpening openingResult,
      expressionTokens afterOpening condition afterCondition conditionResult,
      symbol_preservesTokensOnSuccess .rightParen .statement afterCondition
        closing afterClosing closingResult] using bodyOpeningAtAfter
  have cursorOrder : input.cursor < afterClosing.cursor :=
    Nat.lt_of_lt_of_le
      (acceptToken_cursor_lt_onSuccess (.contextual .while) .statement
        (·.isContextual .while) markerResult)
      (Nat.le_trans
        (symbol_cursorMonotoneOnSuccess .leftParen .statement afterMarker
          opening afterOpening openingResult)
        (Nat.le_trans
          (expressionCursor afterOpening condition afterCondition
            conditionResult)
          (symbol_cursorMonotoneOnSuccess .rightParen .statement
            afterCondition closing afterClosing closingResult)))
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt
    markerAt bodyOpeningAt cursorOrder
  have ordered : marker.span.startByte ≤ body.span.endByte := by
    calc
      marker.span.startByte ≤ marker.span.endByte := markerValid.2.1
      _ ≤ bodyOpening.span.startByte := separated
      _ = body.span.startByte := bodyStart
      _ ≤ body.span.endByte := bodyValid.1.2.1
  cases finished
  exact SourceSpan.cover_validFor markerValid bodyValid.1 ordered

/-- `while` parsing retains its condition, body, and complete outer range. -/
theorem whileStatement_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionTokens : Parser.PreservesTokensOnSuccess expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    (whileStatement statement expression).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  have bodyValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  have weak : (whileStatement statement expression).ValidFor
      (fun _ _ => True) := by
    unfold whileStatement
    apply Parser.bind_validFor (contextual_validFor .while .statement)
    intro marker
    apply Parser.bind_validFor (symbol_validFor .leftParen .statement)
    intro opening
    apply Parser.bind_validFor expressionValid
    intro condition
    apply Parser.bind_validFor (symbol_validFor .rightParen .statement)
    intro closing
    apply Parser.bind_validFor bodyValid
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakReply := weak input inputValid
  cases parsed : whileStatement statement expression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakReply
      exact weakReply
  | ok parsedStatement final =>
      rw [parsed] at weakReply
      have stages := parsed
      unfold whileStatement at stages
      rcases controlBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨opening, afterOpening, openingResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨condition, afterCondition, conditionResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨closing, afterClosing, closingResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerReply := contextual_validFor .while .statement input
        inputValid
      rw [markerResult] at markerReply
      have openingReply := symbol_validFor .leftParen .statement afterMarker
        markerReply.2.1
      rw [openingResult] at openingReply
      have conditionReply := expressionValid afterOpening openingReply.2.1
      rw [conditionResult] at conditionReply
      have closingReply := symbol_validFor .rightParen .statement
        afterCondition conditionReply.2.1
      rw [closingResult] at closingReply
      have bodyReply := bodyValid afterClosing closingReply.2.1
      rw [bodyResult] at bodyReply
      have conditionValidInput : expressionValueValid input.file condition := by
        simpa [conditionReply.2.2, openingReply.2.2,
          markerReply.2.2] using conditionReply.1
      have bodyValidInput : Block.ValidFor
          (Statement.ValidFor expressionValueValid patternValueValid
            yulValueValid) input.file body := by
        simpa [bodyReply.2.2, closingReply.2.2, conditionReply.2.2,
          openingReply.2.2, markerReply.2.2] using bodyReply.1
      have outerValid := whileStatement_span_validOnSuccess
        expressionValueValid patternValueValid yulValueValid statement
          expression statementValid statementTokens expressionValid
          expressionTokens expressionCursor inputValid parsed
      cases finished
      exact ⟨Statement.ValidFor.whileLoop outerValid conditionValidInput
        bodyValidInput.1 bodyValidInput.2, weakReply.2.1,
        weakReply.2.2⟩

/-- `while` parsing preserves every ordinary token window. -/
theorem whileStatement_preservesTokenWindow
    (statement : Parser Statement) (expression : Parser Expr)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (whileStatement statement expression) := by
  unfold whileStatement
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .while .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .leftParen .statement)
  intro opening
  apply Parser.bind_preservesTokenWindow expressionWindow
  intro condition
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightParen .statement)
  intro closing
  apply Parser.bind_preservesTokenWindow
    (coreBlock_preservesTokenWindow statement .require statementWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Successful `while` parsing preserves the immutable token carrier. -/
theorem whileStatement_preservesTokensOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (whileStatement statement expression) :=
  (whileStatement_preservesTokenWindow statement expression statementWindow
    expressionWindow).preservesTokensOnSuccess

/-- A successful `while` statement never rewinds the token cursor. -/
theorem whileStatement_cursorMonotoneOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (whileStatement statement expression) := by
  unfold whileStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .while .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement)
  intro opening
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement)
  intro closing
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A `while` statement starts at its contextual keyword token. -/
theorem whileStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (whileStatement statement expression) (·.span) := by
  intro input parsedStatement final parsed
  have stages := parsed
  unfold whileStatement at stages
  rcases controlBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨condition, afterCondition, conditionResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  rcases contextual_startsAtCurrentTokenOnSuccess .while .statement input
      marker afterMarker markerResult with ⟨token, found, starts⟩
  cases finished
  exact ⟨token, found, starts⟩

namespace ControlInternals

/-- An optional `else` body retains its complete recursive block validity. -/
theorem optionalElseBody_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement) :
    (optionalElseBody statement).ValidFor
      (Option.ValidFor (Block.ValidFor
        (Statement.ValidFor expressionValueValid patternValueValid
          yulValueValid))) := by
  have bodyValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  unfold optionalElseBody
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed .elseKw
  · simp only [present, if_true]
    apply Parser.bind_validFor (keyword_validFor .elseKw .statement)
    intro marker
    apply Parser.bind_validFor_of_value bodyValid
    intro body next nextValid retainedValid
    exact ⟨by simpa only [Option.ValidFor] using retainedValid,
      nextValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional `else` parsing preserves every ordinary token window. -/
theorem optionalElseBody_preservesTokenWindow
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (optionalElseBody statement) := by
  unfold optionalElseBody
  have getWindow : Parser.PreservesTokenWindow getState := by
    intro input
    exact ⟨rfl, rfl⟩
  apply Parser.bind_preservesTokenWindow
    getWindow
  intro observed
  by_cases present : isKeyword observed .elseKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .elseKw .statement)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (coreBlock_preservesTokenWindow statement .require statementWindow)
    intro body
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

/-- Present or absent `else` bodies preserve the immutable token carrier. -/
theorem optionalElseBody_preservesTokensOnSuccess
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokensOnSuccess (optionalElseBody statement) :=
  (optionalElseBody_preservesTokenWindow statement
    statementWindow).preservesTokensOnSuccess

/-- Optional `else` parsing never rewinds the token cursor. -/
theorem optionalElseBody_cursorMonotoneOnSuccess
    (statement : Parser Statement) :
    Parser.CursorMonotoneOnSuccess (optionalElseBody statement) := by
  unfold optionalElseBody
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed .elseKw
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess .elseKw .statement)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (coreBlock_cursorMonotoneOnSuccess statement .require)
    intro body
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present `else` body starts at the brace following its keyword. -/
theorem optionalElseBody_some_startsAfterKeyword
    (statement : Parser Statement) {input final : State} {body : Block}
    (parsed : optionalElseBody statement input = .ok (some body) final) :
    ∃ marker afterMarker opening,
      keyword .elseKw .statement input = .ok marker afterMarker ∧
      afterMarker.peek? = some opening ∧
      opening.span.startByte = body.span.startByte := by
  unfold optionalElseBody getState at parsed
  simp only [bind] at parsed
  by_cases present : isKeyword input .elseKw
  · simp only [present, if_true] at parsed
    rcases controlBind_ok_components parsed with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases controlBind_ok_components rest with
      ⟨parsedBody, afterBody, bodyResult, finished⟩
    have bodyEq : parsedBody = body := by
      cases finished
      rfl
    subst parsedBody
    rcases coreBlock_startsAtCurrentTokenOnSuccess statement .require
        afterMarker body afterBody bodyResult with
      ⟨opening, found, starts⟩
    exact ⟨marker, afterMarker, opening, markerResult, found, starts⟩
  · simp only [present] at parsed
    change Reply.ok none input = .ok (some body) final at parsed
    cases parsed

end ControlInternals

/-- `if` parsing retains its condition and every selected branch body. -/
theorem ifStatement_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionTokens : Parser.PreservesTokensOnSuccess expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    (ifStatement statement expression).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  have bodyValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  have elseValid := ControlInternals.optionalElseBody_validFor
    expressionValueValid patternValueValid yulValueValid statement
      statementValid statementTokens
  have weak : (ifStatement statement expression).ValidFor
      (fun _ _ => True) := by
    unfold ifStatement
    apply Parser.bind_validFor (keyword_validFor .ifKw .statement)
    intro marker
    apply Parser.bind_validFor (symbol_validFor .leftParen .statement)
    intro opening
    apply Parser.bind_validFor expressionValid
    intro condition
    apply Parser.bind_validFor (symbol_validFor .rightParen .statement)
    intro closing
    apply Parser.bind_validFor bodyValid
    intro thenBody
    apply Parser.bind_validFor elseValid
    intro elseBody
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakReply := weak input inputValid
  cases parsed : ifStatement statement expression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakReply
      exact weakReply
  | ok parsedStatement final =>
      rw [parsed] at weakReply
      have stages := parsed
      unfold ifStatement at stages
      rcases controlBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨opening, afterOpening, openingResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨condition, afterCondition, conditionResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨closing, afterClosing, closingResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨thenBody, afterThen, thenResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨elseBody, afterElse, elseResult, finished⟩
      have markerReply := keyword_validFor .ifKw .statement input inputValid
      rw [markerResult] at markerReply
      have openingReply := symbol_validFor .leftParen .statement afterMarker
        markerReply.2.1
      rw [openingResult] at openingReply
      have conditionReply := expressionValid afterOpening openingReply.2.1
      rw [conditionResult] at conditionReply
      have closingReply := symbol_validFor .rightParen .statement
        afterCondition conditionReply.2.1
      rw [closingResult] at closingReply
      have thenReply := bodyValid afterClosing closingReply.2.1
      rw [thenResult] at thenReply
      have elseReply := elseValid afterThen thenReply.2.1
      rw [elseResult] at elseReply
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerReply.1
      have conditionValidInput : expressionValueValid input.file condition := by
        simpa [conditionReply.2.2, openingReply.2.2,
          markerReply.2.2] using conditionReply.1
      have thenValidInput : Block.ValidFor
          (Statement.ValidFor expressionValueValid patternValueValid
            yulValueValid) input.file thenBody := by
        simpa [thenReply.2.2, closingReply.2.2, conditionReply.2.2,
          openingReply.2.2, markerReply.2.2] using thenReply.1
      have elseValidInput : Option.ValidFor (Block.ValidFor
          (Statement.ValidFor expressionValueValid patternValueValid
            yulValueValid)) input.file elseBody := by
        simpa [thenReply.2.2, closingReply.2.2, conditionReply.2.2,
          openingReply.2.2, markerReply.2.2] using elseReply.1
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some
        (acceptToken_ok_state_shape (.keyword .ifKw) .statement
          (fun kind => kind == .keyword .ifKw) markerResult).1
      cases elseBody with
      | none =>
          rcases coreBlock_startsAtCurrentTokenOnSuccess statement .require
              afterClosing thenBody afterThen thenResult with
            ⟨bodyOpening, bodyOpeningFound, bodyStart⟩
          have bodyOpeningAtAfter :=
            State.getElem?_eq_some_of_peek?_eq_some bodyOpeningFound
          have bodyOpeningAt : input.tokens[afterClosing.cursor]? =
              some bodyOpening := by
            simpa [
              keyword_preservesTokensOnSuccess .ifKw .statement input marker
                afterMarker markerResult,
              symbol_preservesTokensOnSuccess .leftParen .statement
                afterMarker opening afterOpening openingResult,
              expressionTokens afterOpening condition afterCondition
                conditionResult,
              symbol_preservesTokensOnSuccess .rightParen .statement
                afterCondition closing afterClosing closingResult] using
                  bodyOpeningAtAfter
          have cursorOrder : input.cursor < afterClosing.cursor :=
            Nat.lt_of_lt_of_le
              (acceptToken_cursor_lt_onSuccess (.keyword .ifKw) .statement
                (fun kind => kind == .keyword .ifKw) markerResult)
              (Nat.le_trans
                (symbol_cursorMonotoneOnSuccess .leftParen .statement
                  afterMarker opening afterOpening openingResult)
                (Nat.le_trans
                  (expressionCursor afterOpening condition afterCondition
                    conditionResult)
                  (symbol_cursorMonotoneOnSuccess .rightParen .statement
                    afterCondition closing afterClosing closingResult)))
          have separated := inputValid.token_end_le_token_start_of_getElem?_lt
            markerAt bodyOpeningAt cursorOrder
          have outerValid := SourceSpan.cover_validFor markerSpanValid
            thenValidInput.1 (by
              calc
                marker.span.startByte ≤ marker.span.endByte :=
                  markerSpanValid.2.1
                _ ≤ bodyOpening.span.startByte := separated
                _ = thenBody.span.startByte := bodyStart
                _ ≤ thenBody.span.endByte := thenValidInput.1.2.1)
          cases finished
          exact ⟨Statement.ValidFor.ifThen outerValid conditionValidInput
            thenValidInput.1 thenValidInput.2 (by simp) (by simp),
            weakReply.2.1, weakReply.2.2⟩
      | some selectedElse =>
          simp only [Option.ValidFor] at elseValidInput
          rcases ControlInternals.optionalElseBody_some_startsAfterKeyword
              statement elseResult with
            ⟨elseMarker, afterElseMarker, bodyOpening, elseMarkerResult,
              bodyOpeningFound, bodyStart⟩
          have bodyOpeningAtAfter :=
            State.getElem?_eq_some_of_peek?_eq_some bodyOpeningFound
          have bodyOpeningAt : input.tokens[afterElseMarker.cursor]? =
              some bodyOpening := by
            simpa [
              keyword_preservesTokensOnSuccess .ifKw .statement input marker
                afterMarker markerResult,
              symbol_preservesTokensOnSuccess .leftParen .statement
                afterMarker opening afterOpening openingResult,
              expressionTokens afterOpening condition afterCondition
                conditionResult,
              symbol_preservesTokensOnSuccess .rightParen .statement
                afterCondition closing afterClosing closingResult,
              coreBlock_preservesTokensOnSuccess statement .require
                statementTokens afterClosing thenBody afterThen thenResult,
              keyword_preservesTokensOnSuccess .elseKw .statement afterThen
                elseMarker afterElseMarker elseMarkerResult] using
                  bodyOpeningAtAfter
          have cursorOrder : input.cursor < afterElseMarker.cursor :=
            Nat.lt_of_lt_of_le
              (acceptToken_cursor_lt_onSuccess (.keyword .ifKw) .statement
                (fun kind => kind == .keyword .ifKw) markerResult)
              (calc
                afterMarker.cursor ≤ afterOpening.cursor :=
                  symbol_cursorMonotoneOnSuccess .leftParen .statement
                    afterMarker opening afterOpening openingResult
                _ ≤ afterCondition.cursor := expressionCursor afterOpening
                  condition afterCondition conditionResult
                _ ≤ afterClosing.cursor :=
                  symbol_cursorMonotoneOnSuccess .rightParen .statement
                    afterCondition closing afterClosing closingResult
                _ ≤ afterThen.cursor := coreBlock_cursorMonotoneOnSuccess
                  statement .require afterClosing thenBody afterThen thenResult
                _ ≤ afterElseMarker.cursor :=
                  keyword_cursorMonotoneOnSuccess .elseKw .statement afterThen
                    elseMarker afterElseMarker elseMarkerResult)
          have separated := inputValid.token_end_le_token_start_of_getElem?_lt
            markerAt bodyOpeningAt cursorOrder
          have outerValid := SourceSpan.cover_validFor markerSpanValid
            elseValidInput.1 (by
              calc
                marker.span.startByte ≤ marker.span.endByte :=
                  markerSpanValid.2.1
                _ ≤ bodyOpening.span.startByte := separated
                _ = selectedElse.span.startByte := bodyStart
                _ ≤ selectedElse.span.endByte := elseValidInput.1.2.1)
          cases finished
          exact ⟨Statement.ValidFor.ifThen outerValid conditionValidInput
            thenValidInput.1 thenValidInput.2
            (by simpa using elseValidInput.1)
            (by simpa using elseValidInput.2), weakReply.2.1,
            weakReply.2.2⟩

/-- `if` parsing preserves every ordinary token window. -/
theorem ifStatement_preservesTokenWindow
    (statement : Parser Statement) (expression : Parser Expr)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (ifStatement statement expression) := by
  unfold ifStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .ifKw .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .leftParen .statement)
  intro opening
  apply Parser.bind_preservesTokenWindow expressionWindow
  intro condition
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightParen .statement)
  intro closing
  apply Parser.bind_preservesTokenWindow
    (coreBlock_preservesTokenWindow statement .require statementWindow)
  intro thenBody
  apply Parser.bind_preservesTokenWindow
    (ControlInternals.optionalElseBody_preservesTokenWindow statement
      statementWindow)
  intro elseBody
  exact Parser.pure_preservesTokenWindow _

/-- Successful `if` parsing preserves the immutable token carrier. -/
theorem ifStatement_preservesTokensOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (ifStatement statement expression) :=
  (ifStatement_preservesTokenWindow statement expression statementWindow
    expressionWindow).preservesTokensOnSuccess

/-- A successful `if` statement never rewinds the token cursor. -/
theorem ifStatement_cursorMonotoneOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (ifStatement statement expression) := by
  unfold ifStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .ifKw .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement)
  intro opening
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement)
  intro closing
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require)
  intro thenBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (ControlInternals.optionalElseBody_cursorMonotoneOnSuccess statement)
  intro elseBody
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- An `if` statement starts at its `if` keyword token. -/
theorem ifStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (ifStatement statement expression) (·.span) := by
  intro input parsedStatement final parsed
  have stages := parsed
  unfold ifStatement at stages
  rcases controlBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨condition, afterCondition, conditionResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨thenBody, afterThen, thenResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨elseBody, afterElse, elseResult, finished⟩
  rcases acceptToken_startsAtCurrentTokenOnSuccess (.keyword .ifKw)
      .statement (fun kind => kind == .keyword .ifKw) input marker
      afterMarker markerResult with ⟨token, found, starts⟩
  cases finished
  exact ⟨token, found, starts⟩

/-- Inline assembly retains its keyword, Yul body, and outer range. -/
theorem assemblyStatement_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (yulValid : ∀ file statement,
      YulStmt.ValidFor file statement → yulValueValid file statement) :
    assemblyStatement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  intro input inputValid
  have weak : assemblyStatement.ValidFor (fun _ _ => True) := by
    unfold assemblyStatement
    apply Parser.bind_validFor (keyword_validFor .assemblyKw .statement)
    intro marker
    apply Parser.bind_validFor (yulBody_validFor.mono (fun _ _ _ => trivial))
    intro body
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  have weakResult := weak input inputValid
  cases parsed : assemblyStatement input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold assemblyStatement at stages
      rcases controlBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerReply := keyword_validFor .assemblyKw .statement input inputValid
      rw [markerResult] at markerReply
      have bodyReply := yulBody_validFor afterMarker markerReply.2.1
      rw [bodyResult] at bodyReply
      have markerValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerReply.1
      have bodyValid : YulParsedBlock.ValidFor YulStmt.ValidFor input.file body := by
        simpa [markerReply.2.2] using bodyReply.1
      have markerShape := acceptToken_ok_state_shape (.keyword .assemblyKw)
        .statement (· == .keyword .assemblyKw) markerResult
      rcases yulBody_startsAtCurrentTokenOnSuccess afterMarker body afterBody
          bodyResult with
        ⟨opening, openingFound, bodyStart⟩
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      have openingAtAfter :=
        State.getElem?_eq_some_of_peek?_eq_some openingFound
      have markerTokens := keyword_preservesTokensOnSuccess .assemblyKw
        .statement input marker afterMarker markerResult
      have openingAt : input.tokens[afterMarker.cursor]? = some opening := by
        simpa [markerTokens] using openingAtAfter
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        markerAt openingAt
          (acceptToken_cursor_lt_onSuccess (.keyword .assemblyKw) .statement
            (· == .keyword .assemblyKw) markerResult)
      have ordered : marker.span.startByte ≤ body.span.endByte :=
        Nat.le_trans markerValid.2.1 (Nat.le_trans separated
          (by rw [bodyStart]; exact bodyValid.1.2.1))
      have outerValid := SourceSpan.cover_validFor markerValid bodyValid.1 ordered
      cases finished
      exact ⟨Statement.ValidFor.assembly outerValid (fun retained member =>
        yulValid input.file retained (bodyValid.2 retained member)),
          weakResult.2.1, weakResult.2.2⟩

theorem assemblyStatement_preservesTokenWindow :
    Parser.PreservesTokenWindow assemblyStatement := by
  unfold assemblyStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .assemblyKw .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow yulBody_preservesTokenWindow
  intro body
  exact Parser.pure_preservesTokenWindow _

theorem assemblyStatement_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess assemblyStatement :=
  assemblyStatement_preservesTokenWindow.preservesTokensOnSuccess

theorem assemblyStatement_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess assemblyStatement := by
  unfold assemblyStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .assemblyKw .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulBody_cursorMonotoneOnSuccess
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem assemblyStatement_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess assemblyStatement (·.span) := by
  unfold assemblyStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .assemblyKw)
      .statement (· == .keyword .assemblyKw))
  intro marker input statement final parsed
  rcases controlBind_ok_components parsed with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  rfl

theorem assemblyStatement_cursor_lt_onSuccess
    {input final : State} {statement : Statement}
    (parsed : assemblyStatement input = .ok statement final) :
    input.cursor < final.cursor := by
  have stages := parsed
  unfold assemblyStatement at stages
  rcases controlBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (acceptToken_cursor_lt_onSuccess (.keyword .assemblyKw) .statement
      (· == .keyword .assemblyKw) markerResult)
    (yulBody_cursorMonotoneOnSuccess afterMarker body final bodyResult)

namespace ControlInternals

/-- A terminated control parser retains its marker, semicolon, and value. -/
theorem terminatedControl_validFor (keywordValue : HardKeyword)
    (value : StatementValue) :
    (terminatedControl keywordValue value).ValidFor
      (fun file statement =>
        statement.span.ValidFor file ∧ statement.value = value) := by
  intro input inputValid
  have weak : (terminatedControl keywordValue value).ValidFor
      (fun _ _ => True) := by
    unfold terminatedControl
    apply Parser.bind_validFor (keyword_validFor keywordValue .statement)
    intro marker
    apply Parser.bind_validFor (symbol_validFor .semicolon .statement)
    intro semicolon
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  have weakResult := weak input inputValid
  cases parsed : terminatedControl keywordValue value input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold terminatedControl at stages
      rcases controlBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
      have markerReply := keyword_validFor keywordValue .statement input inputValid
      rw [markerResult] at markerReply
      have semicolonReply := symbol_validFor .semicolon .statement afterMarker
        markerReply.2.1
      rw [semicolonResult] at semicolonReply
      have markerValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerReply.1
      have semicolonValid : semicolon.span.ValidFor input.file := by
        simpa only [Located.ValidFor, markerReply.2.2] using semicolonReply.1
      have markerShape := acceptToken_ok_state_shape (.keyword keywordValue)
        .statement (· == .keyword keywordValue) markerResult
      have semicolonShape := symbol_ok_state_shape .semicolon .statement
        semicolonResult
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      have semicolonAtAfter :=
        State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
      have markerTokens := keyword_preservesTokensOnSuccess keywordValue
        .statement input marker afterMarker markerResult
      have semicolonAt : input.tokens[afterMarker.cursor]? = some semicolon := by
        simpa [markerTokens] using semicolonAtAfter
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        markerAt semicolonAt
          (acceptToken_cursor_lt_onSuccess (.keyword keywordValue) .statement
            (· == .keyword keywordValue) markerResult)
      have outerValid := SourceSpan.cover_validFor markerValid semicolonValid
        (Nat.le_trans markerValid.2.1
          (Nat.le_trans separated semicolonValid.2.1))
      cases finished
      exact ⟨⟨outerValid, rfl⟩, weakResult.2.1, weakResult.2.2⟩

theorem terminatedControl_preservesTokenWindow (keywordValue : HardKeyword)
    (value : StatementValue) :
    Parser.PreservesTokenWindow (terminatedControl keywordValue value) := by
  unfold terminatedControl
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow keywordValue .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .statement)
  intro semicolon
  exact Parser.pure_preservesTokenWindow _

theorem terminatedControl_cursorMonotoneOnSuccess (keywordValue : HardKeyword)
    (value : StatementValue) :
    Parser.CursorMonotoneOnSuccess (terminatedControl keywordValue value) := by
  unfold terminatedControl
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess keywordValue .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement)
  intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem terminatedControl_startsAtCurrentTokenOnSuccess
    (keywordValue : HardKeyword) (value : StatementValue) :
    Parser.StartsAtCurrentTokenOnSuccess
      (terminatedControl keywordValue value) (·.span) := by
  unfold terminatedControl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword keywordValue)
      .statement (· == .keyword keywordValue))
  intro marker input statement final parsed
  rcases controlBind_ok_components parsed with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  rfl

end ControlInternals

theorem breakStatement_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop) :
    breakStatement.ValidFor (Statement.ValidFor expressionValueValid
      patternValueValid yulValueValid) := by
  simpa only [breakStatement] using
    (ControlInternals.terminatedControl_validFor .breakKw .breakStmt).mono
      (fun _ statement retained => by
        rcases statement with ⟨span, value⟩
        simp only at retained
        cases retained.2
        exact Statement.ValidFor.breakStmt retained.1)

theorem continueStatement_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop) :
    continueStatement.ValidFor (Statement.ValidFor expressionValueValid
      patternValueValid yulValueValid) := by
  simpa only [continueStatement] using
    (ControlInternals.terminatedControl_validFor .continueKw .continueStmt).mono
      (fun _ statement retained => by
        rcases statement with ⟨span, value⟩
        simp only at retained
        cases retained.2
        exact Statement.ValidFor.continueStmt retained.1)

theorem breakStatement_preservesTokenWindow :
    Parser.PreservesTokenWindow breakStatement :=
  ControlInternals.terminatedControl_preservesTokenWindow .breakKw .breakStmt

theorem continueStatement_preservesTokenWindow :
    Parser.PreservesTokenWindow continueStatement :=
  ControlInternals.terminatedControl_preservesTokenWindow
    .continueKw .continueStmt

theorem breakStatement_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess breakStatement :=
  ControlInternals.terminatedControl_cursorMonotoneOnSuccess
    .breakKw .breakStmt

theorem continueStatement_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess continueStatement :=
  ControlInternals.terminatedControl_cursorMonotoneOnSuccess
    .continueKw .continueStmt

theorem breakStatement_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess breakStatement (·.span) :=
  ControlInternals.terminatedControl_startsAtCurrentTokenOnSuccess
    .breakKw .breakStmt

theorem continueStatement_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess continueStatement (·.span) :=
  ControlInternals.terminatedControl_startsAtCurrentTokenOnSuccess
    .continueKw .continueStmt

end Solcore.Syntax.Parser
