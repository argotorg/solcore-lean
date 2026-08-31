import Solcore.Syntax.Parser.TypeRecursiveProperties

/-! Strict cursor progress for every successful canonical type parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_cursor_lt_onSuccess_of_first {α β : Type}
    {first : Parser α} {next : α → Parser β}
    (firstStrict : ∀ {input middle : State} {value : α},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok firstValue middle => next firstValue middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [firstResult] at parsed
  | invariant error => simp [firstResult] at parsed

/-- A named type consumes the first component of its qualified name. -/
theorem parseNamedType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    {input final : State} {value : TypeExpr}
    (parsed : parseNamedType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseNamedType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (qualifiedName_cursor_lt_onSuccess .typeExpr .typeExpr) ?_ parsed
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    (parseNamedTypeArguments_cursorMonotoneOnSuccess nested)
  intro arguments
  exact finishNamedType_cursorMonotoneOnSuccess name arguments

/-- A mapping type consumes its contextual `mapping` marker. -/
theorem parseMappingType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input final : State} {value : TypeExpr}
    (parsed : parseMappingType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseMappingType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.contextual .mapping) .typeExpr (·.isContextual .mapping) result)
    ?_ parsed
  intro mapping
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .typeExpr)
  intro opening
  apply Parser.bind_cursorMonotoneOnSuccess nestedMonotone
  intro key
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .fatArrow .typeExpr)
  intro arrow
  apply Parser.bind_cursorMonotoneOnSuccess nestedMonotone
  intro mapped
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .typeExpr)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A comptime type consumes its contextual `comptime` marker. -/
theorem parseComptimeType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input final : State} {value : TypeExpr}
    (parsed : parseComptimeType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseComptimeType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.contextual .comptime) .typeExpr (·.isContextual .comptime) result)
    ?_ parsed
  intro comptime
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .less .typeExpr)
  intro opening
  apply Parser.bind_cursorMonotoneOnSuccess nestedMonotone
  intro inner
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .greater .typeExpr)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A proxy type consumes its leading `@` marker. -/
theorem parseProxyType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input final : State} {value : TypeExpr}
    (parsed : parseProxyType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseProxyType at parsed
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp [markerResult] at parsed
  | reject failure rejected => simp [markerResult] at parsed
  | ok marker afterMarker =>
      simp only [markerResult] at parsed
      cases innerResult : nested afterMarker with
      | invariant error => simp [innerResult] at parsed
      | reject failure rejected => simp [innerResult] at parsed
      | ok inner next =>
          simp only [innerResult] at parsed
          have innerMonotone :=
            nestedMonotone afterMarker inner next innerResult
          cases parsed
          exact Nat.lt_of_lt_of_le
            (acceptToken_cursor_lt_onSuccess (.symbol .at) .typeExpr
              (· == .symbol .at) markerResult)
            innerMonotone

/-- A tuple type consumes its opening delimiter. -/
theorem parseTupleType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    {input final : State} {value : TypeExpr}
    (parsed : parseTupleType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseTupleType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (delimitedWithPolicy_cursor_lt_onSuccess .leftParen .rightParen true true
      nested .typeExpr .typeExpr) ?_ parsed
  intro tuple
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem parseFunctionReturns_cursorMonotoneOnSuccess
    (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess
      (TypeFunctionInternals.parseFunctionReturns nested) := by
  unfold TypeFunctionInternals.parseFunctionReturns
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isContextual observed .returns
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (contextual_cursorMonotoneOnSuccess .returns .typeExpr)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true nested
        .typeExpr .typeExpr)
    intro values
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A function type consumes its leading `function` keyword. -/
theorem parseFunctionType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    {input final : State} {value : TypeExpr}
    (parsed : parseFunctionType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseFunctionType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.keyword .functionKw) .typeExpr (· == .keyword .functionKw) result)
    ?_ parsed
  intro functionKeyword
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true nested
      .typeExpr .typeExpr)
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    (parseFunctionReturns_cursorMonotoneOnSuccess nested)
  intro returns
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Every successful fuel-bounded type parse consumes at least one token. -/
theorem typeExprWithFuel_cursor_lt_onSuccess (fuel : Nat)
    {input final : State} {value : TypeExpr}
    (parsed : typeExprWithFuel fuel input = .ok value final) :
    input.cursor < final.cursor := by
  cases fuel with
  | zero => simp [typeExprWithFuel] at parsed
  | succ fuel =>
      simp only [typeExprWithFuel] at parsed
      split at parsed
      · exact parseFunctionType_cursor_lt_onSuccess
          (typeExprWithFuel fuel) parsed
      · split at parsed
        · exact parseComptimeType_cursor_lt_onSuccess
            (typeExprWithFuel fuel)
            (typeExprWithFuel_cursorMonotoneOnSuccess fuel) parsed
        · split at parsed
          · exact parseMappingType_cursor_lt_onSuccess
              (typeExprWithFuel fuel)
              (typeExprWithFuel_cursorMonotoneOnSuccess fuel) parsed
          · split at parsed
            · exact parseProxyType_cursor_lt_onSuccess
                (typeExprWithFuel fuel)
                (typeExprWithFuel_cursorMonotoneOnSuccess fuel) parsed
            · split at parsed
              · exact parseTupleType_cursor_lt_onSuccess
                  (typeExprWithFuel fuel) parsed
              · split at parsed
                · exact parseNamedType_cursor_lt_onSuccess
                    (typeExprWithFuel fuel) parsed
                · unfold rejectAt at parsed
                  contradiction

/-- Public recursive type parsing strictly consumes on success. -/
theorem typeExpr_cursor_lt_onSuccess {input final : State} {value : TypeExpr}
    (parsed : typeExpr input = .ok value final) :
    input.cursor < final.cursor := by
  unfold typeExpr at parsed
  exact typeExprWithFuel_cursor_lt_onSuccess
    (input.remainingCount + 1) parsed

end Solcore.Syntax.Parser
