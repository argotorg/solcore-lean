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

/-- Convert a successfully parsed list to its required nonempty carrier. -/
def requireNonempty {α : Type} (parsed : DelimitedList α)
    (phase : ParserPhase) : Parser (NonemptyDelimitedList α) :=
  match parsed.elements with
  | head :: tail => pure {
      span := parsed.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress phase parsed.span)

/-- Parse the optional, structurally nonempty arguments of a named type. -/
def parseNamedTypeArguments (nested : Parser TypeExpr) :
    Parser (Option (NonemptyDelimitedList TypeExpr)) := do
  let state ← getState
  if isSymbol state .less then
    let parsed ← delimited .less .greater false nested
      .typeExpr .typeExpr
    let nonempty ← requireNonempty parsed .typeExpr
    pure (some nonempty)
  else
    pure none

/-- Build the source-shaped syntax value retained by named-type parsing. -/
def makeNamedType (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) : TypeExpr :=
  let span := match arguments with
    | some values => SourceSpan.cover name.span values.span
    | none => name.span
  {
    span
    value := .named name arguments
  }

/-- Build a named type and emit the canonical-spelling diagnostic if needed. -/
def finishNamedType (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) : Parser TypeExpr := do
  let ty := makeNamedType name arguments
  if name.value.components.tail.isEmpty &&
      name.value.components.head.value == "mapping" then
    emitDiagnostic {
      span := ty.span
      kind := .constraintViolation .mappingRequiresCanonicalForm
    }
  else
    pure ()
  pure ty

/-- Parse an ordinary named type and its optional generic arguments. -/
def parseNamedType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let name ← qualifiedName .typeExpr .typeExpr
  let arguments ← parseNamedTypeArguments nested
  finishNamedType name arguments

/-- Parse the canonical `mapping(key => value)` type form. -/
def parseMappingType (nested : Parser TypeExpr) : Parser TypeExpr := do
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

private theorem nested_start_le_following_end
    {nested : Parser TypeExpr}
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (followingSymbol : Symbol)
    {input after final : State} {value : TypeExpr} {following : Token}
    (afterValid : after.ValidFor)
    (nestedResult : nested input = .ok value after)
    (followingResult : symbol followingSymbol .typeExpr after =
      .ok following final) :
    value.span.startByte ≤ following.span.endByte := by
  rcases nestedStarts input value after nestedResult with
    ⟨first, firstFound, firstStart⟩
  have firstAtInput := State.getElem?_eq_some_of_peek?_eq_some firstFound
  have firstAtAfter : after.tokens[input.cursor]? = some first := by
    rw [nestedPreserves input value after nestedResult]
    exact firstAtInput
  have followingShape := acceptToken_ok_state_shape
    (.symbol followingSymbol) .typeExpr
    (· == .symbol followingSymbol) followingResult
  have followingAtAfter :=
    State.getElem?_eq_some_of_peek?_eq_some followingShape.1
  rw [← firstStart]
  rcases Nat.eq_or_lt_of_le
      (nestedMonotone input value after nestedResult) with cursorEq | cursorLt
  · have tokenEq : first = following := by
      apply Option.some.inj
      rw [← firstAtAfter, ← followingAtAfter, cursorEq]
    rw [tokenEq]
    exact (afterValid.token_span_validFor_of_getElem?_eq_some
      followingAtAfter).2.1
  · have firstNonempty :=
      afterValid.token_span_nonempty_of_getElem?_eq_some firstAtAfter
    have ordered := afterValid.token_end_le_token_start_of_getElem?_lt
      firstAtAfter followingAtAfter cursorLt
    have followingValid :=
      afterValid.token_span_validFor_of_getElem?_eq_some followingAtAfter
    exact Nat.le_trans (Nat.le_of_lt firstNonempty)
      (Nat.le_trans ordered followingValid.2.1)

/-- Mapping parsing retains valid outer, delimiter, key, and value ranges. -/
theorem parseMappingType_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    (parseMappingType nested).ValidFor TypeExpr.ValidFor := by
  have weak : (parseMappingType nested).ValidFor (fun _ _ => True) := by
    unfold parseMappingType
    apply Parser.bind_validFor (contextual_validFor .mapping .typeExpr)
    intro mapping
    apply Parser.bind_validFor (symbol_validFor .leftParen .typeExpr)
    intro opening
    apply Parser.bind_validFor nestedValid
    intro key
    apply Parser.bind_validFor (symbol_validFor .fatArrow .typeExpr)
    intro arrow
    apply Parser.bind_validFor nestedValid
    intro value
    apply Parser.bind_validFor (symbol_validFor .rightParen .typeExpr)
    intro closing
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : parseMappingType nested input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold parseMappingType at stages
      rcases bind_ok_components stages with
        ⟨mapping, afterMapping, mappingResult, rest⟩
      rcases bind_ok_components rest with
        ⟨opening, afterOpening, openingResult, rest⟩
      rcases bind_ok_components rest with
        ⟨key, afterKey, keyResult, rest⟩
      rcases bind_ok_components rest with
        ⟨arrow, afterArrow, arrowResult, rest⟩
      rcases bind_ok_components rest with
        ⟨value, afterValue, valueResult, rest⟩
      rcases bind_ok_components rest with
        ⟨closing, afterClosing, closingResult, finished⟩
      cases finished
      have mappingValid := contextual_validFor .mapping .typeExpr input inputValid
      rw [mappingResult] at mappingValid
      have openingValid := symbol_validFor .leftParen .typeExpr afterMapping
        mappingValid.2.1
      rw [openingResult] at openingValid
      have keyValid := nestedValid afterOpening openingValid.2.1
      rw [keyResult] at keyValid
      have arrowValid := symbol_validFor .fatArrow .typeExpr afterKey keyValid.2.1
      rw [arrowResult] at arrowValid
      have valueValid := nestedValid afterArrow arrowValid.2.1
      rw [valueResult] at valueValid
      have closingValid := symbol_validFor .rightParen .typeExpr afterValue
        valueValid.2.1
      rw [closingResult] at closingValid
      have mappingSpanValid : mapping.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using mappingValid.1
      have openingSpanValid : opening.span.ValidFor input.file := by
        simpa only [Located.ValidFor, mappingValid.2.2] using openingValid.1
      have keyValidInput : TypeExpr.ValidFor input.file key := by
        simpa [openingValid.2.2, mappingValid.2.2] using keyValid.1
      have arrowSpanValid : arrow.span.ValidFor input.file := by
        simpa only [Located.ValidFor, keyValid.2.2, openingValid.2.2,
          mappingValid.2.2] using arrowValid.1
      have valueValidInput : TypeExpr.ValidFor input.file value := by
        simpa [arrowValid.2.2, keyValid.2.2, openingValid.2.2,
          mappingValid.2.2] using valueValid.1
      have closingSpanValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor, valueValid.2.2, arrowValid.2.2,
          keyValid.2.2, openingValid.2.2, mappingValid.2.2] using closingValid.1
      have mappingShape := acceptToken_ok_state_shape
        (.contextual .mapping) .typeExpr (·.isContextual .mapping) mappingResult
      have mappingAdvanced : input.advance? = some (mapping, afterMapping) := by
        unfold State.advance?
        rw [mappingShape.1, mappingShape.2]
        rfl
      have openingShape := symbol_ok_state_shape .leftParen .typeExpr openingResult
      have mappingBeforeOpening :=
        inputValid.consumed_end_le_peek_start_after_advance
          mappingAdvanced openingShape.1
      have openingAdvanced :
          afterMapping.advance? = some (opening, afterOpening) := by
        unfold State.advance?
        rw [openingShape.1, openingShape.2]
        rfl
      rcases nestedStarts afterOpening key afterKey keyResult with
        ⟨keyToken, keyFound, keyStart⟩
      have openingBeforeKey : opening.span.endByte ≤ key.span.startByte := by
        rw [← keyStart]
        exact mappingValid.2.1.consumed_end_le_peek_start_after_advance
          openingAdvanced keyFound
      have keyStartLeArrowEnd := nested_start_le_following_end
        nestedStarts nestedPreserves nestedMonotone .fatArrow keyValid.2.1
        keyResult arrowResult
      have arrowShape := symbol_ok_state_shape .fatArrow .typeExpr arrowResult
      have arrowAdvanced : afterKey.advance? = some (arrow, afterArrow) := by
        unfold State.advance?
        rw [arrowShape.1, arrowShape.2]
        rfl
      rcases nestedStarts afterArrow value afterValue valueResult with
        ⟨valueToken, valueFound, valueStart⟩
      have arrowBeforeValue : arrow.span.endByte ≤ value.span.startByte := by
        rw [← valueStart]
        exact keyValid.2.1.consumed_end_le_peek_start_after_advance
          arrowAdvanced valueFound
      have valueStartLeClosingEnd := nested_start_le_following_end
        nestedStarts nestedPreserves nestedMonotone .rightParen valueValid.2.1
        valueResult closingResult
      have argumentsOrdered : opening.span.startByte ≤ closing.span.endByte :=
        Nat.le_trans openingSpanValid.2.1
          (Nat.le_trans openingBeforeKey
            (Nat.le_trans keyStartLeArrowEnd
              (Nat.le_trans arrowBeforeValue valueStartLeClosingEnd)))
      have outerOrdered : mapping.span.startByte ≤ closing.span.endByte :=
        Nat.le_trans mappingSpanValid.2.1
          (Nat.le_trans mappingBeforeOpening argumentsOrdered)
      exact ⟨.mapping
          (SourceSpan.cover_validFor mappingSpanValid closingSpanValid outerOrdered)
          mappingSpanValid
          (SourceSpan.cover_validFor openingSpanValid closingSpanValid
            argumentsOrdered)
          keyValidInput valueValidInput,
        weakResult.2.1, weakResult.2.2⟩

/-- Mapping parsing preserves the immutable recursive token carrier. -/
theorem parseMappingType_preservesTokensOnSuccess
    (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseMappingType nested) := by
  unfold parseMappingType
  apply Parser.bind_preservesTokensOnSuccess
    (contextual_preservesTokensOnSuccess .mapping .typeExpr)
  intro mapping
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .leftParen .typeExpr)
  intro opening
  apply Parser.bind_preservesTokensOnSuccess nestedPreserves
  intro key
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .fatArrow .typeExpr)
  intro arrow
  apply Parser.bind_preservesTokensOnSuccess nestedPreserves
  intro value
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .rightParen .typeExpr)
  intro closing
  exact Parser.pure_preservesTokensOnSuccess _

/-- Mapping parsing is cursor-monotone when its recursive parser is. -/
theorem parseMappingType_cursorMonotoneOnSuccess
    (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parseMappingType nested) := by
  unfold parseMappingType
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .mapping .typeExpr)
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
  intro value
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .typeExpr)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A mapping type starts at its current `mapping` token. -/
theorem parseMappingType_startsAtCurrentTokenOnSuccess
    (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseMappingType nested) (·.span) := by
  unfold parseMappingType
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (contextual_startsAtCurrentTokenOnSuccess .mapping .typeExpr)
  intro mapping input value final parsed
  rcases bind_ok_components parsed with ⟨opening, afterOpening, _, rest⟩
  rcases bind_ok_components rest with ⟨key, afterKey, _, rest⟩
  rcases bind_ok_components rest with ⟨arrow, afterArrow, _, rest⟩
  rcases bind_ok_components rest with ⟨inner, afterInner, _, rest⟩
  rcases bind_ok_components rest with ⟨closing, afterClosing, _, finished⟩
  cases finished
  rfl

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

private def parseFunctionReturns (nested : Parser TypeExpr) : Parser (Option (DelimitedList TypeExpr)) := do
  let state ← getState
  if isContextual state .returns then
    let _ ← contextual .returns .typeExpr
    let values ← delimited .leftParen .rightParen true nested .typeExpr .typeExpr
    pure (some values)
  else
    pure none

private theorem parseFunctionReturns_preservesTokensOnSuccess (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) : Parser.PreservesTokensOnSuccess
      (parseFunctionReturns nested) := by
  unfold parseFunctionReturns
  apply Parser.bind_preservesTokensOnSuccess getState_preservesTokensOnSuccess
  intro state
  by_cases hasReturns : isContextual state .returns
  · simp only [hasReturns, if_true]
    apply Parser.bind_preservesTokensOnSuccess (contextual_preservesTokensOnSuccess .returns .typeExpr)
    intro returnsKeyword
    apply Parser.bind_preservesTokensOnSuccess (delimited_preservesTokensOnSuccess
      .leftParen .rightParen true nested .typeExpr .typeExpr nestedPreserves)
    intro values
    exact Parser.pure_preservesTokensOnSuccess _
  · simp only [hasReturns]
    exact Parser.pure_preservesTokensOnSuccess none

private theorem parseFunctionReturns_cursorMonotoneOnSuccess (nested : Parser TypeExpr) : Parser.CursorMonotoneOnSuccess (parseFunctionReturns nested) := by
  unfold parseFunctionReturns
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro state
  by_cases hasReturns : isContextual state .returns
  · simp only [hasReturns, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess (contextual_cursorMonotoneOnSuccess .returns .typeExpr)
    intro returnsKeyword
    apply Parser.bind_cursorMonotoneOnSuccess (delimited_cursorMonotoneOnSuccess
      .leftParen .rightParen true nested .typeExpr .typeExpr)
    intro values
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [hasReturns]
    exact Parser.pure_cursorMonotoneOnSuccess none

private theorem parseFunctionReturns_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor) (nestedPreserves : Parser.PreservesTokensOnSuccess nested) : (parseFunctionReturns nested).ValidFor
      (Option.ValidFor (DelimitedList.ValidFor TypeExpr.ValidFor)) := by
  unfold parseFunctionReturns
  apply Parser.bind_validFor getState_validFor
  intro state
  by_cases hasReturns : isContextual state .returns
  · simp only [hasReturns, if_true]
    apply Parser.bind_validFor (contextual_validFor .returns .typeExpr)
    intro returnsKeyword
    apply Parser.bind_validFor_of_value (delimited_validFor TypeExpr.ValidFor
      .leftParen .rightParen true nested .typeExpr .typeExpr nestedValid nestedPreserves)
    intro values input inputValid valuesValid
    exact ⟨by simpa only [Option.ValidFor] using valuesValid,
      inputValid, rfl⟩
  · simp only [hasReturns]
    exact Parser.pure_validFor none (Option.ValidFor (DelimitedList.ValidFor TypeExpr.ValidFor)) (fun _ => trivial)

/-- Parse a function type, including its optional `returns` type list. -/
def parseFunctionType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let functionKeyword ← keyword .functionKw .typeExpr
  let parameters ← delimited .leftParen .rightParen true nested .typeExpr .typeExpr
  let returns ← parseFunctionReturns nested
  let endSpan := match returns with
    | some values => values.span
    | none => parameters.span
  pure {
    span := SourceSpan.cover functionKeyword.span endSpan
    value := .function functionKeyword.span parameters returns
  }

/-- Function-type parsing retains valid keyword, parameter, and result ranges. -/
theorem parseFunctionType_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parseFunctionType nested).ValidFor TypeExpr.ValidFor := by
  have weak : (parseFunctionType nested).ValidFor (fun _ _ => True) := by
    unfold parseFunctionType
    apply Parser.bind_validFor (keyword_validFor .functionKw .typeExpr)
    intro functionKeyword
    apply Parser.bind_validFor
      (delimited_validFor TypeExpr.ValidFor .leftParen .rightParen true
        nested .typeExpr .typeExpr nestedValid nestedPreserves)
    intro parameters
    apply Parser.bind_validFor (parseFunctionReturns_validFor nested nestedValid nestedPreserves)
    intro returns
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : parseFunctionType nested input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold parseFunctionType at stages
      rcases bind_ok_components stages with
        ⟨functionKeyword, afterKeyword, keywordResult, rest⟩
      rcases bind_ok_components rest with ⟨parameters, afterParameters,
        parametersResult, rest⟩
      rcases bind_ok_components rest with
        ⟨returns, afterReturns, returnsResult, finished⟩
      cases finished
      have keywordValid := keyword_validFor .functionKw .typeExpr input inputValid
      rw [keywordResult] at keywordValid
      have parametersValid := delimited_validFor TypeExpr.ValidFor
        .leftParen .rightParen true nested .typeExpr .typeExpr
        nestedValid nestedPreserves afterKeyword keywordValid.2.1
      rw [parametersResult] at parametersValid
      have returnsValid := parseFunctionReturns_validFor nested nestedValid
        nestedPreserves afterParameters parametersValid.2.1
      rw [returnsResult] at returnsValid
      have keywordSpanValid : functionKeyword.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using keywordValid.1
      have parametersValidInput : DelimitedList.ValidFor TypeExpr.ValidFor
          input.file parameters := by
        simpa only [keywordValid.2.2] using parametersValid.1
      have keywordShape := acceptToken_ok_state_shape (.keyword .functionKw) .typeExpr
        (· == .keyword .functionKw) keywordResult
      have keywordAdvanced : input.advance? = some (functionKeyword, afterKeyword) := by
        unfold State.advance?
        rw [keywordShape.1, keywordShape.2]
        rfl
      cases returns with
      | none =>
          rcases delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen
              true nested .typeExpr .typeExpr afterKeyword parameters
              afterParameters parametersResult with
            ⟨opening, openingFound, openingStart⟩
          have keywordBeforeParameters : functionKeyword.span.endByte ≤
              parameters.span.startByte := by
            rw [← openingStart]
            exact inputValid.consumed_end_le_peek_start_after_advance
              keywordAdvanced openingFound
          have outerOrdered : functionKeyword.span.startByte ≤
              parameters.span.endByte :=
            Nat.le_trans keywordSpanValid.2.1
              (Nat.le_trans keywordBeforeParameters
                parametersValidInput.1.2.1)
          exact ⟨.functionWithoutReturns
              (SourceSpan.cover_validFor keywordSpanValid
                parametersValidInput.1 outerOrdered)
              keywordSpanValid parametersValidInput.1
              parametersValidInput.2,
            weakResult.2.1, weakResult.2.2⟩
      | some values =>
          have returnsValidInput : DelimitedList.ValidFor TypeExpr.ValidFor
              input.file values := by
            simpa only [Option.ValidFor, parametersValid.2.2,
              keywordValid.2.2] using returnsValid.1
          have returnsStages := returnsResult
          unfold parseFunctionReturns at returnsStages
          rcases bind_ok_components returnsStages with
            ⟨observed, afterObserved, observedResult, returnsRest⟩
          unfold getState at observedResult
          cases observedResult
          by_cases hasReturns : isContextual afterParameters .returns
          · simp only [hasReturns, if_true] at returnsRest
            rcases bind_ok_components returnsRest with
              ⟨returnsKeyword, afterReturnsKeyword,
                returnsKeywordResult, valuesRest⟩
            rcases bind_ok_components valuesRest with
              ⟨parsedValues, afterValues, valuesResult, returnsFinished⟩
            cases returnsFinished
            have returnsKeywordValid := contextual_validFor .returns .typeExpr
              afterParameters parametersValid.2.1
            rw [returnsKeywordResult] at returnsKeywordValid
            rcases delimited_startsAtCurrentTokenOnSuccess .leftParen
                .rightParen true nested .typeExpr .typeExpr
                afterReturnsKeyword values final valuesResult with
              ⟨opening, openingFound, openingStart⟩
            have keywordFound :=
              State.getElem?_eq_some_of_peek?_eq_some keywordShape.1
            have openingAtReturns :=
              State.getElem?_eq_some_of_peek?_eq_some openingFound
            have keywordTokens := keyword_preservesTokensOnSuccess
              .functionKw .typeExpr input functionKeyword afterKeyword
              keywordResult
            have parameterTokens := delimited_preservesTokensOnSuccess
              .leftParen .rightParen true nested .typeExpr .typeExpr
              nestedPreserves afterKeyword parameters afterParameters
              parametersResult
            have returnsKeywordTokens :=
              contextual_preservesTokensOnSuccess .returns .typeExpr
                afterParameters returnsKeyword afterReturnsKeyword
                returnsKeywordResult
            have keywordAtReturns : afterReturnsKeyword.tokens[input.cursor]? =
                some functionKeyword := by
              rw [returnsKeywordTokens, parameterTokens, keywordTokens]
              exact keywordFound
            have keywordProgress := acceptToken_cursor_lt_onSuccess
              (.keyword .functionKw) .typeExpr
              (· == .keyword .functionKw) keywordResult
            have parametersMonotone :=
              delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
                nested .typeExpr .typeExpr afterKeyword parameters
                afterParameters parametersResult
            have returnsKeywordProgress := acceptToken_cursor_lt_onSuccess
              (.contextual .returns) .typeExpr (·.isContextual .returns)
              returnsKeywordResult
            have cursorOrder : input.cursor < afterReturnsKeyword.cursor :=
              Nat.lt_trans
                (Nat.lt_of_lt_of_le keywordProgress parametersMonotone)
                returnsKeywordProgress
            have keywordBeforeOpening :=
              returnsKeywordValid.2.1.token_end_le_token_start_of_getElem?_lt
                keywordAtReturns openingAtReturns cursorOrder
            have keywordBeforeReturns : functionKeyword.span.endByte ≤
                values.span.startByte := by
              rw [← openingStart]
              exact keywordBeforeOpening
            have outerOrdered : functionKeyword.span.startByte ≤
                values.span.endByte :=
              Nat.le_trans keywordSpanValid.2.1
                (Nat.le_trans keywordBeforeReturns
                  returnsValidInput.1.2.1)
            exact ⟨.functionWithReturns
                (SourceSpan.cover_validFor keywordSpanValid
                  returnsValidInput.1 outerOrdered)
                keywordSpanValid parametersValidInput.1
                parametersValidInput.2 returnsValidInput.1
                returnsValidInput.2,
              weakResult.2.1, weakResult.2.2⟩
          · simp only [hasReturns] at returnsRest
            cases returnsRest

/-- Function-type parsing preserves the immutable recursive token carrier. -/
theorem parseFunctionType_preservesTokensOnSuccess
    (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseFunctionType nested) := by
  unfold parseFunctionType
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .functionKw .typeExpr)
  intro functionKeyword
  apply Parser.bind_preservesTokensOnSuccess
    (delimited_preservesTokensOnSuccess .leftParen .rightParen true
      nested .typeExpr .typeExpr nestedPreserves)
  intro parameters
  apply Parser.bind_preservesTokensOnSuccess
    (parseFunctionReturns_preservesTokensOnSuccess nested nestedPreserves)
  intro returns
  exact Parser.pure_preservesTokensOnSuccess _

/-- Function-type parsing never moves the parser cursor backwards. -/
theorem parseFunctionType_cursorMonotoneOnSuccess
    (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseFunctionType nested) := by
  unfold parseFunctionType
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .functionKw .typeExpr)
  intro functionKeyword
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
      nested .typeExpr .typeExpr)
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    (parseFunctionReturns_cursorMonotoneOnSuccess nested)
  intro returns
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A function type starts at its current `function` keyword token. -/
theorem parseFunctionType_startsAtCurrentTokenOnSuccess (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseFunctionType nested) (·.span) := by
  unfold parseFunctionType
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .functionKw) .typeExpr (· == .keyword .functionKw))
  intro functionKeyword input value final parsed
  rcases bind_ok_components parsed with
    ⟨parameters, afterParameters, _, rest⟩
  rcases bind_ok_components rest with ⟨returns, afterReturns, _, finished⟩
  cases finished
  rfl

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
