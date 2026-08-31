import Solcore.Syntax.Parser.Statement.Match
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

end MatchInternals
end Solcore.Syntax.Parser
