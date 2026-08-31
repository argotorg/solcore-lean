import Solcore.Syntax.Parser.PatternCoreFuelTotalityProperties

/-! Strict cursor progress for canonical pattern-layer dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem bind_cursor_lt_of_first {α β : Type}
    {first : Parser α} {next : α → Parser β}
    (firstStrict : ∀ {input middle : State} {value : α},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [bind, firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [bind, firstResult] at parsed
  | invariant error => simp [bind, firstResult] at parsed

theorem wildcardPattern_cursor_lt_onSuccess
    {input final : State} {value : Pattern}
    (parsed : wildcardPattern input = .ok value final) :
    input.cursor < final.cursor := by
  unfold wildcardPattern at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.symbol .underscore)
      .pattern (· == .symbol .underscore) result)
    (fun marker => Parser.pure_cursorMonotoneOnSuccess _)
    parsed

theorem literalPattern_cursor_lt_onSuccess
    {input final : State} {value : Pattern}
    (parsed : literalPattern input = .ok value final) :
    input.cursor < final.cursor := by
  unfold literalPattern at parsed
  apply bind_cursor_lt_of_first coreLiteral_cursor_lt_onSuccess
    (fun literal => Parser.pure_cursorMonotoneOnSuccess _) parsed

theorem booleanBinderPattern_cursor_lt_onSuccess
    {input final : State} {value : Pattern}
    (parsed : booleanBinderPattern input = .ok value final) :
    input.cursor < final.cursor := by
  unfold booleanBinderPattern at parsed
  apply bind_cursor_lt_of_first booleanIdentifier_cursor_lt_onSuccess
    (fun name => Parser.pure_cursorMonotoneOnSuccess _) parsed

theorem parenthesizedPattern_cursor_lt_onSuccess
    (nested : Parser Pattern)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input final : State} {value : Pattern}
    (parsed : parenthesizedPattern nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parenthesizedPattern at parsed
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      have openingStrict := acceptToken_cursor_lt_onSuccess
        (.symbol .leftParen) .pattern (· == .symbol .leftParen) openingResult
      split at parsed
      · exact Nat.lt_of_lt_of_le openingStrict
          (closePatternTuple_cursorMonotoneOnSuccess opening []
            afterOpening value final parsed)
      · cases nestedResult : nested afterOpening with
        | invariant error => simp [nestedResult] at parsed
        | reject failure rejected => simp [nestedResult] at parsed
        | ok first next =>
            simp only [nestedResult] at parsed
            have firstMonotone := nestedMonotone afterOpening first next
              nestedResult
            split at parsed
            · contradiction
            · split at parsed
              · exact Nat.lt_of_lt_of_le openingStrict
                  (Nat.le_trans firstMonotone
                    (patternTupleTail_cursorMonotoneOnSuccess nested
                      nestedMonotone opening (next.remainingCount + 1)
                      [first] next value final parsed))
              · exact Nat.lt_of_lt_of_le openingStrict
                  (Nat.le_trans firstMonotone
                    (closePatternTuple_cursorMonotoneOnSuccess opening
                      [first] next value final parsed))

theorem dotConstructorPattern_cursor_lt_onSuccess
    (nested : Parser Pattern)
    {input final : State} {value : Pattern}
    (parsed : dotConstructorPattern nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold dotConstructorPattern at parsed
  cases dotResult : symbol .dot .pattern input with
  | reject failure rejected => simp [bind, dotResult] at parsed
  | invariant error => simp [bind, dotResult] at parsed
  | ok dot afterDot =>
      simp only [bind, dotResult] at parsed
      cases nameResult : patternName afterDot with
      | reject failure rejected => simp [nameResult] at parsed
      | invariant error => simp [nameResult] at parsed
      | ok name afterName =>
          simp only [nameResult] at parsed
          cases argumentsResult : optionalConstructorArguments nested afterName with
          | reject failure rejected => simp [argumentsResult] at parsed
          | invariant error => simp [argumentsResult] at parsed
          | ok arguments next =>
              simp only [argumentsResult, pure] at parsed
              have dotStrict := acceptToken_cursor_lt_onSuccess (.symbol .dot)
                .pattern (· == .symbol .dot) dotResult
              have rest := Nat.le_trans
                (patternName_cursorMonotoneOnSuccess afterDot name afterName
                  nameResult)
                (optionalConstructorArguments_cursorMonotoneOnSuccess nested
                  afterName arguments next argumentsResult)
              cases parsed
              exact Nat.lt_of_lt_of_le dotStrict rest

theorem comptimePattern_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionMonotone : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Pattern}
    (parsed : comptimePattern expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold comptimePattern at parsed
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at parsed
  | reject failure rejected => simp [markerResult] at parsed
  | ok marker afterMarker =>
      simp only [markerResult] at parsed
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at parsed
      | reject failure rejected => simp [expressionResult] at parsed
      | ok inner next =>
          simp only [expressionResult] at parsed
          have strict := acceptToken_cursor_lt_onSuccess
            (.contextual .comptime) .pattern (·.isContextual .comptime)
            markerResult
          have rest := expressionMonotone afterMarker inner next
            expressionResult
          cases parsed
          exact Nat.lt_of_lt_of_le strict rest

theorem qualifiedPattern_cursor_lt_onSuccess
    (nested : Parser Pattern)
    {input final : State} {value : Pattern}
    (parsed : qualifiedPattern nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold qualifiedPattern at parsed
  cases pathResult : qualifiedName .pattern .pattern input with
  | reject failure rejected => simp [bind, pathResult] at parsed
  | invariant error => simp [bind, pathResult] at parsed
  | ok path afterPath =>
      simp only [bind, pathResult] at parsed
      cases argumentsResult : optionalConstructorArguments nested afterPath with
      | reject failure rejected => simp [argumentsResult] at parsed
      | invariant error => simp [argumentsResult] at parsed
      | ok arguments next =>
          simp only [argumentsResult] at parsed
          let components := path.value.components.toList
          cases reversed : components.reverse with
          | nil => simp [components, reversed] at parsed
          | cons name qualifiersRev =>
              simp only [components, reversed] at parsed
              split at parsed <;> simp only [pure] at parsed
              all_goals
                have pathStrict := qualifiedName_cursor_lt_onSuccess .pattern
                  .pattern pathResult
                have rest := optionalConstructorArguments_cursorMonotoneOnSuccess
                  nested afterPath arguments next argumentsResult
                cases parsed
                exact Nat.lt_of_lt_of_le pathStrict rest

theorem patternCore_cursor_lt_onSuccess
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (expressionMonotone : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Pattern}
    (parsed : patternCore nested expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold patternCore at parsed
  split at parsed
  · exact wildcardPattern_cursor_lt_onSuccess parsed
  · split at parsed
    · exact literalPattern_cursor_lt_onSuccess parsed
    · split at parsed
      · exact booleanBinderPattern_cursor_lt_onSuccess parsed
      · split at parsed
        · exact parenthesizedPattern_cursor_lt_onSuccess nested
            nestedMonotone parsed
        · split at parsed
          · exact dotConstructorPattern_cursor_lt_onSuccess nested parsed
          · split at parsed
            · exact comptimePattern_cursor_lt_onSuccess expression
                expressionMonotone parsed
            · split at parsed
              · exact qualifiedPattern_cursor_lt_onSuccess nested parsed
              · simp [rejectAt] at parsed

end Solcore.Syntax.Parser.PatternInternals
