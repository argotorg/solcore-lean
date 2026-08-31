import Solcore.Syntax.Parser.Statement.Match
import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.StatementValidity

/-! Contracts for canonical Core match-statement components. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem matchBind_ok_components {alpha beta : Type}
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

namespace MatchInternals

/-- One `case` retains its pattern, recursive body, and outer source range. -/
theorem matchCase_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement)
    (patternValid : patternParser.ValidFor patternValueValid)
    (patternTokens : Parser.PreservesTokensOnSuccess patternParser)
    (patternCursor : Parser.CursorMonotoneOnSuccess patternParser) :
    (matchCase statement patternParser).ValidFor
      (MatchCase.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  have bodyValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  have weak : (matchCase statement patternParser).ValidFor
      (fun _ _ => True) := by
    unfold matchCase
    apply Parser.bind_validFor (keyword_validFor .caseKw .statement)
    intro marker
    apply Parser.bind_validFor patternValid
    intro retainedPattern
    apply Parser.bind_validFor bodyValid
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakReply := weak input inputValid
  cases parsed : matchCase statement patternParser input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakReply
      exact weakReply
  | ok retainedCase final =>
      rw [parsed] at weakReply
      have stages := parsed
      unfold matchCase at stages
      rcases matchBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases matchBind_ok_components rest with
        ⟨retainedPattern, afterPattern, patternResult, rest⟩
      rcases matchBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerReply := keyword_validFor .caseKw .statement input inputValid
      rw [markerResult] at markerReply
      have patternReply := patternValid afterMarker markerReply.2.1
      rw [patternResult] at patternReply
      have bodyReply := bodyValid afterPattern patternReply.2.1
      rw [bodyResult] at bodyReply
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerReply.1
      have retainedPatternValid : patternValueValid input.file
          retainedPattern := by
        simpa [patternReply.2.2, markerReply.2.2] using patternReply.1
      have retainedBodyValid : Block.ValidFor
          (Statement.ValidFor expressionValueValid patternValueValid
            yulValueValid) input.file body := by
        simpa [bodyReply.2.2, patternReply.2.2,
          markerReply.2.2] using bodyReply.1
      rcases coreBlock_startsAtCurrentTokenOnSuccess statement .require
          afterPattern body afterBody bodyResult with
        ⟨bodyOpening, bodyOpeningFound, bodyStart⟩
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some
        (acceptToken_ok_state_shape (.keyword .caseKw) .statement
          (fun kind => kind == .keyword .caseKw) markerResult).1
      have bodyOpeningAtAfter :=
        State.getElem?_eq_some_of_peek?_eq_some bodyOpeningFound
      have bodyOpeningAt : input.tokens[afterPattern.cursor]? =
          some bodyOpening := by
        simpa [keyword_preservesTokensOnSuccess .caseKw .statement input
          marker afterMarker markerResult,
          patternTokens afterMarker retainedPattern afterPattern patternResult]
            using bodyOpeningAtAfter
      have cursorOrder : input.cursor < afterPattern.cursor :=
        Nat.lt_of_lt_of_le
          (acceptToken_cursor_lt_onSuccess (.keyword .caseKw) .statement
            (fun kind => kind == .keyword .caseKw) markerResult)
          (patternCursor afterMarker retainedPattern afterPattern
            patternResult)
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        markerAt bodyOpeningAt cursorOrder
      have outerValid := SourceSpan.cover_validFor markerSpanValid
        retainedBodyValid.1 (by
          calc
            marker.span.startByte ≤ marker.span.endByte :=
              markerSpanValid.2.1
            _ ≤ bodyOpening.span.startByte := separated
            _ = body.span.startByte := bodyStart
            _ ≤ body.span.endByte := retainedBodyValid.1.2.1)
      cases finished
      exact ⟨MatchCase.ValidFor.arm outerValid retainedPatternValid
        retainedBodyValid.1 retainedBodyValid.2, weakReply.2.1,
        weakReply.2.2⟩

/-- One `case` preserves every ordinary token window. -/
theorem matchCase_preservesTokenWindow
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (patternWindow : Parser.PreservesTokenWindow patternParser) :
    Parser.PreservesTokenWindow (matchCase statement patternParser) := by
  unfold matchCase
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .caseKw .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow patternWindow
  intro retainedPattern
  apply Parser.bind_preservesTokenWindow
    (coreBlock_preservesTokenWindow statement .require statementWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Successful `case` parsing preserves the immutable token carrier. -/
theorem matchCase_preservesTokensOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (patternWindow : Parser.PreservesTokenWindow patternParser) :
    Parser.PreservesTokensOnSuccess (matchCase statement patternParser) :=
  (matchCase_preservesTokenWindow statement patternParser statementWindow
    patternWindow).preservesTokensOnSuccess

/-- Successful `case` parsing never rewinds the token cursor. -/
theorem matchCase_cursorMonotoneOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (patternCursor : Parser.CursorMonotoneOnSuccess patternParser) :
    Parser.CursorMonotoneOnSuccess (matchCase statement patternParser) := by
  unfold matchCase
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .caseKw .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess patternCursor
  intro retainedPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- One `case` starts at its `case` keyword token. -/
theorem matchCase_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern) :
    Parser.StartsAtCurrentTokenOnSuccess
      (matchCase statement patternParser) (·.span) := by
  intro input retainedCase final parsed
  have stages := parsed
  unfold matchCase at stages
  rcases matchBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨retainedPattern, afterPattern, patternResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  rcases acceptToken_startsAtCurrentTokenOnSuccess (.keyword .caseKw)
      .statement (fun kind => kind == .keyword .caseKw) input marker
      afterMarker markerResult with ⟨token, found, starts⟩
  cases finished
  exact ⟨token, found, starts⟩

/-- The fuel loop retains every parsed and previously accumulated case. -/
theorem matchCases_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseValid : (matchCase statement patternParser).ValidFor
      (MatchCase.ValidFor expressionValueValid patternValueValid
        yulValueValid)) :
    ∀ fuel casesRev input,
      input.ValidFor →
      List.ValidFor
        (MatchCase.ValidFor expressionValueValid patternValueValid
          yulValueValid) input.file casesRev →
      (matchCases statement patternParser fuel casesRev input).ValidFor input
        (List.ValidFor (MatchCase.ValidFor expressionValueValid
          patternValueValid yulValueValid)) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro casesRev input inputValid accumulatedValid
      unfold matchCases
      split
      · cases caseResult : matchCase statement patternParser input with
        | invariant error => trivial
        | reject failure rejected =>
            have reply := caseValid input inputValid
            rw [caseResult] at reply
            exact reply
        | ok retainedCase next =>
            have reply := caseValid input inputValid
            rw [caseResult] at reply
            simp only
            split
            · have nextAccumulated : List.ValidFor
                  (MatchCase.ValidFor expressionValueValid patternValueValid
                    yulValueValid) next.file (retainedCase :: casesRev) := by
                intro item member
                rcases List.mem_cons.mp member with rfl | member
                · simpa [reply.2.2] using reply.1
                · have prior := accumulatedValid item member
                  simpa [reply.2.2] using prior
              exact (inductionHypothesis (retainedCase :: casesRev) next
                reply.2.1 nextAccumulated).of_file_eq reply.2.2
            · trivial
      · exact ⟨by
          intro item member
          exact accumulatedValid item (by simpa using member), inputValid,
            rfl⟩

/-- The case loop preserves every ordinary token window. -/
theorem matchCases_preservesTokenWindow
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseWindow : Parser.PreservesTokenWindow
      (matchCase statement patternParser)) :
    ∀ fuel casesRev,
      Parser.PreservesTokenWindow
        (matchCases statement patternParser fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero => intro casesRev input; trivial
  | succ fuel inductionHypothesis =>
      intro casesRev input
      unfold matchCases
      split
      · have replyShape := caseWindow input
        cases caseResult : matchCase statement patternParser input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [caseResult] at replyShape
            exact replyShape
        | ok retainedCase next =>
            rw [caseResult] at replyShape
            simp only
            split
            · exact (inductionHypothesis (retainedCase :: casesRev)
                next).trans replyShape
            · trivial
      · exact ⟨rfl, rfl⟩

/-- Successful case-loop parsing preserves the immutable token carrier. -/
theorem matchCases_preservesTokensOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseWindow : Parser.PreservesTokenWindow
      (matchCase statement patternParser)) (fuel : Nat)
    (casesRev : List MatchCase) :
    Parser.PreservesTokensOnSuccess
      (matchCases statement patternParser fuel casesRev) :=
  (matchCases_preservesTokenWindow statement patternParser caseWindow fuel
    casesRev).preservesTokensOnSuccess

/-- The case loop either stays put or advances through complete cases. -/
theorem matchCases_cursorMonotoneOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern) :
    ∀ fuel casesRev,
      Parser.CursorMonotoneOnSuccess
        (matchCases statement patternParser fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input value final parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro casesRev input value final parsed
      unfold matchCases at parsed
      split at parsed
      · cases caseResult : matchCase statement patternParser input with
        | invariant error => simp [caseResult] at parsed
        | reject failure rejected => simp [caseResult] at parsed
        | ok retainedCase next =>
            simp only [caseResult] at parsed
            split at parsed
            · exact Nat.le_trans (Nat.le_of_lt (by assumption))
                (inductionHypothesis (retainedCase :: casesRev) next value
                  final parsed)
            · contradiction
      · cases parsed
        exact Nat.le_refl _

/-- An optional `default` body retains its complete recursive block validity. -/
theorem optionalDefaultBody_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement) :
    (optionalDefaultBody statement).ValidFor
      (Option.ValidFor (Block.ValidFor
        (Statement.ValidFor expressionValueValid patternValueValid
          yulValueValid))) := by
  have bodyValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  unfold optionalDefaultBody
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_validFor (keyword_validFor .defaultKw .statement)
    intro marker
    apply Parser.bind_validFor_of_value bodyValid
    intro body next nextValid retainedValid
    exact ⟨by simpa only [Option.ValidFor] using retainedValid,
      nextValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional `default` parsing preserves every ordinary token window. -/
theorem optionalDefaultBody_preservesTokenWindow
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (optionalDefaultBody statement) := by
  unfold optionalDefaultBody
  have getWindow : Parser.PreservesTokenWindow getState := by
    intro input
    exact ⟨rfl, rfl⟩
  apply Parser.bind_preservesTokenWindow getWindow
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .defaultKw .statement)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (coreBlock_preservesTokenWindow statement .require statementWindow)
    intro body
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

/-- Present or absent `default` bodies preserve the token carrier. -/
theorem optionalDefaultBody_preservesTokensOnSuccess
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokensOnSuccess (optionalDefaultBody statement) :=
  (optionalDefaultBody_preservesTokenWindow statement
    statementWindow).preservesTokensOnSuccess

/-- Optional `default` parsing never rewinds the token cursor. -/
theorem optionalDefaultBody_cursorMonotoneOnSuccess
    (statement : Parser Statement) :
    Parser.CursorMonotoneOnSuccess (optionalDefaultBody statement) := by
  unfold optionalDefaultBody
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess .defaultKw .statement)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (coreBlock_cursorMonotoneOnSuccess statement .require)
    intro body
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present `default` body starts at the brace following its keyword. -/
theorem optionalDefaultBody_some_startsAfterKeyword
    (statement : Parser Statement) {input final : State} {body : Block}
    (parsed : optionalDefaultBody statement input = .ok (some body) final) :
    ∃ marker afterMarker opening,
      keyword .defaultKw .statement input = .ok marker afterMarker ∧
      afterMarker.peek? = some opening ∧
      opening.span.startByte = body.span.startByte := by
  unfold optionalDefaultBody getState at parsed
  simp only [bind] at parsed
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at parsed
    rcases matchBind_ok_components parsed with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases matchBind_ok_components rest with
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

/-- Requiring scrutinees converts a valid nonempty delimited list exactly. -/
theorem requireScrutinees_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (values : DelimitedList Expr) (input : State)
    (inputValid : input.ValidFor)
    (valuesValid : DelimitedList.ValidFor expressionValueValid
      input.file values) :
    (requireScrutinees values input).ValidFor input
      (NonemptyDelimitedList.ValidFor expressionValueValid) := by
  unfold requireScrutinees
  cases elements : values.elements with
  | nil => trivial
  | cons head tail =>
      simp only [pure, Reply.ValidFor, NonemptyDelimitedList.ValidFor]
      refine ⟨⟨valuesValid.1, ?_⟩, inputValid, trivial⟩
      intro expression member
      exact valuesValid.2 expression (by
        simpa [NonemptyList.toList, elements] using member)

/-- Requiring a nonempty scrutinee list does not alter the token window. -/
theorem requireScrutinees_preservesTokenWindow
    (values : DelimitedList Expr) :
    Parser.PreservesTokenWindow (requireScrutinees values) := by
  intro input
  unfold requireScrutinees
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨rfl, rfl⟩

/-- Requiring a nonempty scrutinee list never rewinds the cursor. -/
theorem requireScrutinees_cursorMonotoneOnSuccess
    (values : DelimitedList Expr) :
    Parser.CursorMonotoneOnSuccess (requireScrutinees values) := by
  intro input scrutinees final parsed
  unfold requireScrutinees at parsed
  cases elements : values.elements with
  | nil =>
      rw [elements] at parsed
      contradiction
  | cons head tail =>
      rw [elements] at parsed
      cases parsed
      exact Nat.le_refl _

/-- One arity check preserves the complete token window. -/
theorem validateMatchCaseArity_preservesTokenWindow
    (scrutineeCount : Nat) (retainedCase : MatchCase) :
    Parser.PreservesTokenWindow
      (validateMatchCaseArity scrutineeCount retainedCase) := by
  unfold validateMatchCaseArity
  simp only
  split
  · exact Parser.pure_preservesTokenWindow ()
  · exact emitDiagnostic_preservesTokenWindow _

/-- One arity check leaves the cursor in place. -/
theorem validateMatchCaseArity_cursorMonotoneOnSuccess
    (scrutineeCount : Nat) (retainedCase : MatchCase) :
    Parser.CursorMonotoneOnSuccess
      (validateMatchCaseArity scrutineeCount retainedCase) := by
  unfold validateMatchCaseArity
  simp only
  split
  · exact Parser.pure_cursorMonotoneOnSuccess ()
  · exact emitDiagnostic_cursorMonotoneOnSuccess _

/-- Checking every retained case preserves the complete token window. -/
theorem validateMatchArities_preservesTokenWindow
    (scrutineeCount : Nat) : ∀ cases,
    Parser.PreservesTokenWindow
      (validateMatchArities scrutineeCount cases)
  | [] => Parser.pure_preservesTokenWindow ()
  | retainedCase :: rest => by
      unfold validateMatchArities
      apply Parser.bind_preservesTokenWindow
        (validateMatchCaseArity_preservesTokenWindow scrutineeCount
          retainedCase)
      intro _
      exact validateMatchArities_preservesTokenWindow scrutineeCount rest

/-- Checking every retained case leaves the cursor in place. -/
theorem validateMatchArities_cursorMonotoneOnSuccess
    (scrutineeCount : Nat) : ∀ cases,
    Parser.CursorMonotoneOnSuccess
      (validateMatchArities scrutineeCount cases)
  | [] => Parser.pure_cursorMonotoneOnSuccess ()
  | retainedCase :: rest => by
      unfold validateMatchArities
      apply Parser.bind_cursorMonotoneOnSuccess
        (validateMatchCaseArity_cursorMonotoneOnSuccess scrutineeCount
          retainedCase)
      intro _
      exact validateMatchArities_cursorMonotoneOnSuccess scrutineeCount rest

end MatchInternals

/-- Complete `match` parsing preserves every ordinary token window. -/
theorem matchStatement_preservesTokenWindow
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (patternWindow : Parser.PreservesTokenWindow pattern) :
    Parser.PreservesTokenWindow
      (matchStatement statement expression pattern) := by
  have caseWindow := MatchInternals.matchCase_preservesTokenWindow
    statement pattern statementWindow patternWindow
  have casesWindow : Parser.PreservesTokenWindow (fun input =>
      MatchInternals.matchCases statement pattern
        (input.remainingCount + 1) [] input) := by
    intro input
    exact MatchInternals.matchCases_preservesTokenWindow statement pattern
      caseWindow (input.remainingCount + 1) [] input
  unfold matchStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .matchKw .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftParen .rightParen false expression
      .expression .statement expressionWindow)
  intro values
  apply Parser.bind_preservesTokenWindow
    (MatchInternals.requireScrutinees_preservesTokenWindow values)
  intro scrutinees
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .leftBrace .statement)
  intro opening
  apply Parser.bind_preservesTokenWindow casesWindow
  intro cases
  apply Parser.bind_preservesTokenWindow
    (MatchInternals.optionalDefaultBody_preservesTokenWindow statement
      statementWindow)
  intro defaultBody
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .statement)
  intro closing
  apply Parser.bind_preservesTokenWindow
    (MatchInternals.validateMatchArities_preservesTokenWindow
      scrutinees.elements.toList.length cases)
  intro _
  by_cases missing : cases.isEmpty && defaultBody.isNone
  · simp only [missing, if_true]
    apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindow _)
    intro _
    exact Parser.pure_preservesTokenWindow _
  · simp only [missing]
    exact Parser.pure_preservesTokenWindow _

/-- Successful `match` parsing preserves the immutable token carrier. -/
theorem matchStatement_preservesTokensOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (patternWindow : Parser.PreservesTokenWindow pattern) :
    Parser.PreservesTokensOnSuccess
      (matchStatement statement expression pattern) :=
  (matchStatement_preservesTokenWindow statement expression pattern
    statementWindow expressionWindow patternWindow).preservesTokensOnSuccess

/-- A successful `match` statement never rewinds the token cursor. -/
theorem matchStatement_cursorMonotoneOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) :
    Parser.CursorMonotoneOnSuccess
      (matchStatement statement expression pattern) := by
  have casesCursor : Parser.CursorMonotoneOnSuccess (fun input =>
      MatchInternals.matchCases statement pattern
        (input.remainingCount + 1) [] input) := by
    intro input cases final parsed
    exact MatchInternals.matchCases_cursorMonotoneOnSuccess statement pattern
      (input.remainingCount + 1) [] input cases final parsed
  unfold matchStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .matchKw .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen false
      expression .expression .statement)
  intro values
  apply Parser.bind_cursorMonotoneOnSuccess
    (MatchInternals.requireScrutinees_cursorMonotoneOnSuccess values)
  intro scrutinees
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftBrace .statement)
  intro opening
  apply Parser.bind_cursorMonotoneOnSuccess casesCursor
  intro cases
  apply Parser.bind_cursorMonotoneOnSuccess
    (MatchInternals.optionalDefaultBody_cursorMonotoneOnSuccess statement)
  intro defaultBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightBrace .statement)
  intro closing
  apply Parser.bind_cursorMonotoneOnSuccess
    (MatchInternals.validateMatchArities_cursorMonotoneOnSuccess
      scrutinees.elements.toList.length cases)
  intro _
  by_cases missing : cases.isEmpty && defaultBody.isNone
  · simp only [missing, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (emitDiagnostic_cursorMonotoneOnSuccess _)
    intro _
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [missing]
    exact Parser.pure_cursorMonotoneOnSuccess _

/-- A complete `match` statement starts at its `match` keyword token. -/
theorem matchStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) :
    Parser.StartsAtCurrentTokenOnSuccess
      (matchStatement statement expression pattern) (·.span) := by
  unfold matchStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .matchKw)
      .statement (fun kind => kind == .keyword .matchKw))
  intro marker input parsedStatement final parsed
  rcases matchBind_ok_components parsed with
    ⟨values, afterValues, valuesResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨scrutinees, afterScrutinees, scrutineesResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨cases, afterCases, casesResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨defaultBody, afterDefault, defaultResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨validated, afterValidation, validationResult, rest⟩
  by_cases missing : cases.isEmpty && defaultBody.isNone
  · simp only [missing, if_true] at rest
    rcases matchBind_ok_components rest with
      ⟨presence, afterPresence, presenceResult, finished⟩
    cases finished
    rfl
  · simp only [missing] at rest
    cases rest
    rfl

end Solcore.Syntax.Parser
