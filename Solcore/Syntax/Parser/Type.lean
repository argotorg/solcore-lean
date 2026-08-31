import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.Name
import Solcore.Syntax.TypeValidity

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected =>
      rw [firstResult] at parsed
      contradiction
  | invariant error =>
      rw [firstResult] at parsed
      contradiction

private def requireNonempty {α : Type} (parsed : DelimitedList α)
    (phase : ParserPhase) : Parser (NonemptyDelimitedList α) :=
  match parsed.elements with
  | head :: tail => pure {
      span := parsed.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress phase parsed.span)

private def parseNamedType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let name ← qualifiedName .typeExpr .typeExpr
  let state ← getState
  let arguments ←
    if isSymbol state .less then
      do
        let parsed ← delimited .less .greater false nested
          .typeExpr .typeExpr
        let nonempty ← requireNonempty parsed .typeExpr
        pure (some nonempty)
    else
      pure none
  let span := match arguments with
    | some values => SourceSpan.cover name.span values.span
    | none => name.span
  let ty : TypeExpr := {
    span
    value := .named name arguments
  }
  if name.value.components.tail.isEmpty &&
      name.value.components.head.value == "mapping" then
    emitDiagnostic {
      span
      kind := .constraintViolation .mappingRequiresCanonicalForm
    }
  else
    pure ()
  pure ty

private def parseMappingType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let mapping ← contextual .mapping .typeExpr
  let opening ← symbol .leftParen .typeExpr
  let key ← nested
  let _ ← symbol .fatArrow .typeExpr
  let value ← nested
  let closing ← symbol .rightParen .typeExpr
  pure {
    span := SourceSpan.cover mapping.span closing.span
    value := .mapping mapping.span
      (SourceSpan.cover opening.span closing.span) key value
  }

/-- Parse a `comptime<...>` type using the supplied recursive parser. -/
def parseComptimeType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let comptime ← contextual .comptime .typeExpr
  let opening ← symbol .less .typeExpr
  let inner ← nested
  let closing ← symbol .greater .typeExpr
  pure {
    span := SourceSpan.cover comptime.span closing.span
    value := .comptime comptime.span
      (SourceSpan.cover opening.span closing.span) inner
  }

/-- Comptime parsing retains valid outer, delimiter, and inner provenance. -/
theorem parseComptimeType_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    (parseComptimeType nested).ValidFor TypeExpr.ValidFor := by
  have weak : (parseComptimeType nested).ValidFor (fun _ _ => True) := by
    unfold parseComptimeType
    apply Parser.bind_validFor
      (contextual_validFor .comptime .typeExpr)
    intro comptime
    apply Parser.bind_validFor (symbol_validFor .less .typeExpr)
    intro opening
    apply Parser.bind_validFor nestedValid
    intro inner
    apply Parser.bind_validFor (symbol_validFor .greater .typeExpr)
    intro closing
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : parseComptimeType nested input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok value final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold parseComptimeType at stages
      rcases bind_ok_components stages with
        ⟨comptime, afterComptime, comptimeResult, afterComptimeResult⟩
      rcases bind_ok_components afterComptimeResult with
        ⟨opening, afterOpening, openingResult, afterOpeningResult⟩
      rcases bind_ok_components afterOpeningResult with
        ⟨inner, afterInner, innerResult, afterInnerResult⟩
      rcases bind_ok_components afterInnerResult with
        ⟨closing, afterClosing, closingResult, finished⟩
      cases finished
      have comptimeValid :=
        contextual_validFor .comptime .typeExpr input inputValid
      rw [comptimeResult] at comptimeValid
      have openingValid :=
        symbol_validFor .less .typeExpr afterComptime comptimeValid.2.1
      rw [openingResult] at openingValid
      have innerValid := nestedValid afterOpening openingValid.2.1
      rw [innerResult] at innerValid
      have closingValid :=
        symbol_validFor .greater .typeExpr afterInner innerValid.2.1
      rw [closingResult] at closingValid
      have comptimeSpanValid : comptime.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using comptimeValid.1
      have openingSpanValid : opening.span.ValidFor input.file := by
        have : opening.span.ValidFor afterComptime.file := by
          simpa only [Located.ValidFor] using openingValid.1
        simpa [comptimeValid.2.2] using this
      have innerValidInput : TypeExpr.ValidFor input.file inner := by
        simpa [openingValid.2.2, comptimeValid.2.2] using innerValid.1
      have closingSpanValid : closing.span.ValidFor input.file := by
        have : closing.span.ValidFor afterInner.file := by
          simpa only [Located.ValidFor] using closingValid.1
        simpa [innerValid.2.2, openingValid.2.2,
          comptimeValid.2.2] using this
      have comptimeShape := acceptToken_ok_state_shape
        (.contextual .comptime) .typeExpr (·.isContextual .comptime)
        comptimeResult
      have comptimeAdvanced :
          input.advance? = some (comptime, afterComptime) := by
        unfold State.advance?
        rw [comptimeShape.1, comptimeShape.2]
        rfl
      have openingShape :=
        symbol_ok_state_shape .less .typeExpr openingResult
      have comptimeBeforeOpening :=
        inputValid.consumed_end_le_peek_start_after_advance
          comptimeAdvanced openingShape.1
      have openingAdvanced :
          afterComptime.advance? = some (opening, afterOpening) := by
        unfold State.advance?
        rw [openingShape.1, openingShape.2]
        rfl
      rcases nestedStarts afterOpening inner afterInner innerResult with
        ⟨innerToken, innerFound, innerStart⟩
      have openingBeforeInnerToken :=
        comptimeValid.2.1.consumed_end_le_peek_start_after_advance
          openingAdvanced innerFound
      have openingBeforeInner :
          opening.span.endByte ≤ inner.span.startByte := by
        rw [← innerStart]
        exact openingBeforeInnerToken
      have innerAtAfterOpening :=
        State.getElem?_eq_some_of_peek?_eq_some innerFound
      have nestedTokens :=
        nestedPreserves afterOpening inner afterInner innerResult
      have innerAtAfterInner :
          afterInner.tokens[afterOpening.cursor]? = some innerToken := by
        rw [nestedTokens]
        exact innerAtAfterOpening
      have closingShape :=
        symbol_ok_state_shape .greater .typeExpr closingResult
      have closingAtAfterInner :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have nestedCursor :=
        nestedMonotone afterOpening inner afterInner innerResult
      have innerTokenStartLeClosingEnd :
          innerToken.span.startByte ≤ closing.span.endByte := by
        rcases Nat.eq_or_lt_of_le nestedCursor with cursorEq | cursorLt
        · have tokenEq : innerToken = closing := by
            apply Option.some.inj
            rw [← innerAtAfterInner, ← closingAtAfterInner, cursorEq]
          rw [tokenEq]
          exact closingSpanValid.2.1
        · have innerSpanNonempty :=
            innerValid.2.1.token_span_nonempty_of_getElem?_eq_some
              innerAtAfterInner
          have ordered :=
            innerValid.2.1.token_end_le_token_start_of_getElem?_lt
              innerAtAfterInner closingAtAfterInner cursorLt
          exact Nat.le_trans (Nat.le_of_lt innerSpanNonempty)
            (Nat.le_trans ordered closingSpanValid.2.1)
      have innerStartLeClosingEnd :
          inner.span.startByte ≤ closing.span.endByte := by
        rw [← innerStart]
        exact innerTokenStartLeClosingEnd
      have argumentsOrdered :
          opening.span.startByte ≤ closing.span.endByte :=
        Nat.le_trans openingSpanValid.2.1
          (Nat.le_trans openingBeforeInner innerStartLeClosingEnd)
      have outerOrdered :
          comptime.span.startByte ≤ closing.span.endByte :=
        Nat.le_trans comptimeSpanValid.2.1
          (Nat.le_trans comptimeBeforeOpening argumentsOrdered)
      have outerValid := SourceSpan.cover_validFor comptimeSpanValid
        closingSpanValid outerOrdered
      have argumentsValid := SourceSpan.cover_validFor openingSpanValid
        closingSpanValid argumentsOrdered
      exact ⟨.comptime outerValid comptimeSpanValid argumentsValid
          innerValidInput,
        weakResult.2.1, weakResult.2.2⟩

/-- Comptime parsing preserves the immutable recursive token carrier. -/
theorem parseComptimeType_preservesTokensOnSuccess
    (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseComptimeType nested) := by
  unfold parseComptimeType
  apply Parser.bind_preservesTokensOnSuccess
    (contextual_preservesTokensOnSuccess .comptime .typeExpr)
  intro comptime
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .less .typeExpr)
  intro opening
  apply Parser.bind_preservesTokensOnSuccess nestedPreserves
  intro inner
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .greater .typeExpr)
  intro closing
  exact Parser.pure_preservesTokensOnSuccess _

/-- Comptime parsing is cursor-monotone when its recursive parser is. -/
theorem parseComptimeType_cursorMonotoneOnSuccess
    (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parseComptimeType nested) := by
  unfold parseComptimeType
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .comptime .typeExpr)
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

/-- A comptime type starts at its current `comptime` token. -/
theorem parseComptimeType_startsAtCurrentTokenOnSuccess
    (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseComptimeType nested) (·.span) := by
  unfold parseComptimeType
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (contextual_startsAtCurrentTokenOnSuccess .comptime .typeExpr)
  intro comptime input value final parsed
  rcases bind_ok_components parsed with
    ⟨opening, afterOpening, _openingResult, afterOpeningResult⟩
  rcases bind_ok_components afterOpeningResult with
    ⟨inner, afterInner, _innerResult, afterInnerResult⟩
  rcases bind_ok_components afterInnerResult with
    ⟨closing, afterClosing, _closingResult, finished⟩
  cases finished
  rfl

/-- Parse a proxy type whose outer range begins at its `@` marker. -/
def parseProxyType (nested : Parser TypeExpr) : Parser TypeExpr := fun input =>
  match symbol .at .typeExpr input with
  | .ok marker afterMarker =>
      match nested afterMarker with
      | .ok inner next => .ok {
          span := SourceSpan.cover marker.span inner.span
          value := .proxy marker.span inner
        } next
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Proxy parsing preserves its marker, inner type, and covering provenance. -/
theorem parseProxyType_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span)) :
    (parseProxyType nested).ValidFor TypeExpr.ValidFor := by
  intro input inputValid
  unfold parseProxyType
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have markerValid := symbol_validFor .at .typeExpr input inputValid
      rw [markerResult] at markerValid
      simpa only [Reply.ValidFor] using markerValid
  | ok marker afterMarker =>
      have markerValid := symbol_validFor .at .typeExpr input inputValid
      rw [markerResult] at markerValid
      cases innerResult : nested afterMarker with
      | invariant error =>
          simp only [innerResult, Reply.ValidFor]
      | reject failure rejected =>
          have innerValid := nestedValid afterMarker markerValid.2.1
          rw [innerResult] at innerValid
          simpa only [innerResult, Reply.ValidFor] using
            innerValid.of_file_eq markerValid.2.2
      | ok inner next =>
          have innerValid := nestedValid afterMarker markerValid.2.1
          rw [innerResult] at innerValid
          rcases nestedStarts afterMarker inner next innerResult with
            ⟨innerToken, innerFound, innerStart⟩
          have markerShape :=
            symbol_ok_state_shape .at .typeExpr markerResult
          have advanced : input.advance? = some (marker, afterMarker) := by
            unfold State.advance?
            rw [markerShape.1, markerShape.2]
            rfl
          have markerBeforeInnerToken :=
            inputValid.consumed_end_le_peek_start_after_advance
              advanced innerFound
          have markerBeforeInner :
              marker.span.endByte ≤ inner.span.startByte := by
            rw [← innerStart]
            exact markerBeforeInnerToken
          have markerSpanValid : marker.span.ValidFor input.file := by
            simpa only [Located.ValidFor] using markerValid.1
          have innerValidInput : TypeExpr.ValidFor input.file inner := by
            simpa [markerValid.2.2] using innerValid.1
          have innerSpanValid := innerValidInput.span_valid
          have coverValid :
              (SourceSpan.cover marker.span inner.span).ValidFor input.file := by
            apply SourceSpan.cover_validFor markerSpanValid innerSpanValid
            exact Nat.le_trans markerSpanValid.2.1
              (Nat.le_trans markerBeforeInner innerSpanValid.2.1)
          simp only [innerResult, Reply.ValidFor]
          exact ⟨.proxy coverValid markerSpanValid innerValidInput,
            innerValid.2.1,
            innerValid.2.2.trans markerValid.2.2⟩

/-- Proxy parsing never replaces or reorders the immutable token carrier. -/
theorem parseProxyType_preservesTokensOnSuccess (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseProxyType nested) := by
  intro input value next result
  unfold parseProxyType at result
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases innerResult : nested afterMarker with
      | invariant error => simp [innerResult] at result
      | reject failure rejected => simp [innerResult] at result
      | ok inner final =>
          simp only [innerResult] at result
          have nestedTokens :=
            nestedPreserves afterMarker inner final innerResult
          have markerTokens :=
            symbol_preservesTokensOnSuccess .at .typeExpr input marker
              afterMarker markerResult
          cases result
          exact nestedTokens.trans markerTokens

/-- Proxy parsing is cursor-monotone when its recursive parser is. -/
theorem parseProxyType_cursorMonotoneOnSuccess (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parseProxyType nested) := by
  intro input value next result
  unfold parseProxyType at result
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases innerResult : nested afterMarker with
      | invariant error => simp [innerResult] at result
      | reject failure rejected => simp [innerResult] at result
      | ok inner final =>
          simp only [innerResult] at result
          have markerMonotone :=
            symbol_cursorMonotoneOnSuccess .at .typeExpr input marker
              afterMarker markerResult
          have innerMonotone :=
            nestedMonotone afterMarker inner final innerResult
          cases result
          exact Nat.le_trans markerMonotone innerMonotone

/-- A proxy type starts at the current `@` token. -/
theorem parseProxyType_startsAtCurrentTokenOnSuccess
    (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseProxyType nested) (·.span) := by
  intro input value next result
  unfold parseProxyType at result
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases innerResult : nested afterMarker with
      | invariant error => simp [innerResult] at result
      | reject failure rejected => simp [innerResult] at result
      | ok inner final =>
          simp only [innerResult] at result
          cases result
          rcases symbol_startsAtCurrentTokenOnSuccess .at .typeExpr
              input marker afterMarker markerResult with
            ⟨token, found, start⟩
          exact ⟨token, found, start⟩

/-- Parse a parenthesized tuple type using the supplied recursive parser. -/
def parseTupleType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let tuple ← delimited .leftParen .rightParen true nested
    .typeExpr .typeExpr
  pure {
    span := tuple.span
    value := .tuple tuple.elements
  }

/-- Tuple parsing preserves delimiter and recursive element provenance. -/
theorem parseTupleType_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parseTupleType nested).ValidFor TypeExpr.ValidFor := by
  unfold parseTupleType
  apply Parser.bind_validFor_of_value
    (delimited_validFor TypeExpr.ValidFor .leftParen .rightParen true
      nested .typeExpr .typeExpr nestedValid nestedPreserves)
  intro tuple input inputValid tupleValid
  exact ⟨.tuple tupleValid.1 tupleValid.2, inputValid, rfl⟩

/-- Tuple parsing never replaces or reorders the immutable token carrier. -/
theorem parseTupleType_preservesTokensOnSuccess (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseTupleType nested) := by
  unfold parseTupleType
  apply Parser.bind_preservesTokensOnSuccess
  · exact delimited_preservesTokensOnSuccess .leftParen .rightParen true
      nested .typeExpr .typeExpr nestedPreserves
  · intro tuple
    exact Parser.pure_preservesTokensOnSuccess _

/-- Tuple parsing never moves the parser cursor backwards. -/
theorem parseTupleType_cursorMonotoneOnSuccess (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseTupleType nested) := by
  unfold parseTupleType
  apply Parser.bind_cursorMonotoneOnSuccess
  · exact delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
      nested .typeExpr .typeExpr
  · intro tuple
    exact Parser.pure_cursorMonotoneOnSuccess _

/-- A tuple type starts at its current opening parenthesis token. -/
theorem parseTupleType_startsAtCurrentTokenOnSuccess
    (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseTupleType nested) (·.span) := by
  unfold parseTupleType
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
  · exact delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen
      true nested .typeExpr .typeExpr
  · intro tuple input value final parsed
    cases parsed
    rfl

private def parseFunctionType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let functionKeyword ← keyword .functionKw .typeExpr
  let parameters ← delimited .leftParen .rightParen true nested
    .typeExpr .typeExpr
  let state ← getState
  let returns ←
    if isContextual state .returns then
      do
        let _ ← contextual .returns .typeExpr
        let values ← delimited .leftParen .rightParen true nested
          .typeExpr .typeExpr
        pure (some values)
    else
      pure none
  let endSpan := match returns with
    | some values => values.span
    | none => parameters.span
  pure {
    span := SourceSpan.cover functionKeyword.span endSpan
    value := .function functionKeyword.span parameters returns
  }

private def hasFollowingSymbol (state : State) (value : Symbol) : Bool :=
  state.peekOffsetKind? 1 == some (.symbol value)

/-- Whether the current token can begin a canonical Core type. -/
def startsTypeExpr (state : State) : Bool :=
  isKeyword state .functionKw || isSymbol state .at ||
    isSymbol state .leftParen || isIdentifier state

/-- Recursive Core type parser, parameterized by remaining nesting depth. -/
def typeExprWithFuel : Nat → Parser TypeExpr
  | 0 => fun state =>
      .invariant (.fuelExhausted .typeExpr state.currentSpan)
  | fuel + 1 => fun state =>
      let nested := typeExprWithFuel fuel
      if isKeyword state .functionKw then
        parseFunctionType nested state
      else if isContextual state .comptime &&
          hasFollowingSymbol state .less then
        parseComptimeType nested state
      else if isContextual state .mapping &&
          hasFollowingSymbol state .leftParen then
        parseMappingType nested state
      else if isSymbol state .at then
        parseProxyType nested state
      else if isSymbol state .leftParen then
        parseTupleType nested state
      else if isIdentifier state then
        parseNamedType nested state
      else
        rejectAt state { head := .typeExpr, tail := [] } .typeExpr

/-- Parse one complete canonical Core type expression. -/
def typeExpr : Parser TypeExpr := fun state =>
  typeExprWithFuel (state.remainingCount + 1) state

end Solcore.Syntax.Parser
