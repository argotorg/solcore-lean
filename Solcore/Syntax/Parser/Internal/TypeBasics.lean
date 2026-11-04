import Solcore.Syntax.Parser.Types
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Validity

/-!
Basic proofs about the type parsers. `Parser/Signatures` and `Parser/Blocks` keep theorems
beside private helpers and those theorems need this file, so production code imports it.
Keep it small.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Type
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

/-- Mapping parsing preserves the active token window on every reply. -/
theorem parseMappingType_preservesTokenWindow (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseMappingType nested) := by
  unfold parseMappingType
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .mapping .typeExpr)
  intro mapping
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .leftParen .typeExpr)
  intro opening
  apply Parser.bind_preservesTokenWindow nestedPreserves
  intro key
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .fatArrow .typeExpr)
  intro arrow
  apply Parser.bind_preservesTokenWindow nestedPreserves
  intro value
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightParen .typeExpr)
  intro closing
  exact Parser.pure_preservesTokenWindow _

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

/-- Comptime parsing preserves the active token window on every reply. -/
theorem parseComptimeType_preservesTokenWindow (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseComptimeType nested) := by
  unfold parseComptimeType
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .comptime .typeExpr)
  intro comptime
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .less .typeExpr)
  intro opening
  apply Parser.bind_preservesTokenWindow nestedPreserves
  intro inner
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .greater .typeExpr)
  intro closing
  exact Parser.pure_preservesTokenWindow _

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

/-- Proxy parsing preserves the active token window on every reply. -/
theorem parseProxyType_preservesTokenWindow (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseProxyType nested) := by
  intro input
  unfold parseProxyType
  have markerShape := symbol_preservesTokenWindow .at .typeExpr input
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [markerResult] at markerShape
      exact markerShape
  | ok marker afterMarker =>
      rw [markerResult] at markerShape
      have innerShape := nestedPreserves afterMarker
      cases innerResult : nested afterMarker with
      | invariant error =>
          simp only [innerResult, Reply.PreservesTokenWindow]
      | reject failure rejected =>
          rw [innerResult] at innerShape
          simp only [innerResult]
          exact innerShape.trans markerShape
      | ok inner next =>
          rw [innerResult] at innerShape
          simp only [innerResult]
          exact innerShape.trans markerShape

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

/-- Tuple parsing preserves the active token window on every reply. -/
theorem parseTupleType_preservesTokenWindow (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseTupleType nested) := by
  unfold parseTupleType
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftParen .rightParen true nested
      .typeExpr .typeExpr nestedPreserves)
  intro tuple
  exact Parser.pure_preservesTokenWindow _

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

open TypeFunctionInternals

private theorem getState_preservesTokenWindowForType :
    Parser.PreservesTokenWindow getState := by
  intro input
  exact ⟨rfl, rfl⟩

private theorem parseFunctionReturns_preservesTokenWindow
    (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseFunctionReturns nested) := by
  unfold parseFunctionReturns
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindowForType
  intro state
  by_cases hasReturns : isContextual state .returns
  · simp only [hasReturns, if_true]
    apply Parser.bind_preservesTokenWindow
      (contextual_preservesTokenWindow .returns .typeExpr)
    intro returnsKeyword
    apply Parser.bind_preservesTokenWindow
      (delimited_preservesTokenWindow .leftParen .rightParen true nested
        .typeExpr .typeExpr nestedPreserves)
    intro values
    exact Parser.pure_preservesTokenWindow _
  · simp only [hasReturns]
    exact Parser.pure_preservesTokenWindow none

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

/-- Function-type parsing preserves the active window on every reply. -/
theorem parseFunctionType_preservesTokenWindow (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseFunctionType nested) := by
  unfold parseFunctionType
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .functionKw .typeExpr)
  intro functionKeyword
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftParen .rightParen true nested
      .typeExpr .typeExpr nestedPreserves)
  intro parameters
  apply Parser.bind_preservesTokenWindow
    (parseFunctionReturns_preservesTokenWindow nested nestedPreserves)
  intro returns
  exact Parser.pure_preservesTokenWindow _

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

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeNamedProperties
/-! Contracts for the named branch of the recursive type parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components_variant {α β : Type} {first : Parser α}
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
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem requireNonempty_preservesTokensOnSuccess {α : Type}
    (parsed : DelimitedList α) (phase : ParserPhase) :
    Parser.PreservesTokensOnSuccess (requireNonempty parsed phase) := by
  intro input value next result
  unfold requireNonempty at result
  cases elements : parsed.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail => rw [elements] at result; cases result; rfl

private theorem requireNonempty_cursorMonotoneOnSuccess {α : Type}
    (parsed : DelimitedList α) (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess (requireNonempty parsed phase) := by
  intro input value next result
  unfold requireNonempty at result
  cases elements : parsed.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact Nat.le_refl _

private theorem requireNonempty_preservesTokenWindow {α : Type}
    (parsed : DelimitedList α) (phase : ParserPhase) :
    Parser.PreservesTokenWindow (requireNonempty parsed phase) := by
  intro input
  unfold requireNonempty
  cases parsed.elements with
  | nil => trivial
  | cons head tail => exact ⟨rfl, rfl⟩

/-- Optional named-type arguments preserve delimiter and element provenance. -/
theorem parseNamedTypeArguments_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parseNamedTypeArguments nested).ValidFor
      (Option.ValidFor
        (NonemptyDelimitedList.ValidFor TypeExpr.ValidFor)) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .less
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (delimited_validFor TypeExpr.ValidFor .less .greater false nested
        .typeExpr .typeExpr nestedValid nestedPreserves)
    intro parsed input inputValid parsedValid
    unfold requireNonempty
    cases elements : parsed.elements with
    | nil => simp only [bind, Reply.ValidFor]
    | cons head tail =>
        simp only [bind, Reply.ValidFor, Option.ValidFor,
          NonemptyDelimitedList.ValidFor]
        refine ⟨⟨parsedValid.1, ?_⟩, inputValid, rfl⟩
        intro element member
        exact parsedValid.2 element (by
          simpa [NonemptyList.toList, elements] using member)
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional named-type arguments retain the recursive token carrier. -/
theorem parseNamedTypeArguments_preservesTokensOnSuccess
    (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_preservesTokensOnSuccess getState_preservesTokensOnSuccess
  intro observed
  by_cases present : isSymbol observed .less
  · simp only [present, if_true]
    apply Parser.bind_preservesTokensOnSuccess
      (delimited_preservesTokensOnSuccess .less .greater false nested
        .typeExpr .typeExpr nestedPreserves)
    intro parsed
    apply Parser.bind_preservesTokensOnSuccess
      (requireNonempty_preservesTokensOnSuccess parsed .typeExpr)
    intro nonempty
    exact Parser.pure_preservesTokensOnSuccess _
  · simp only [present]
    exact Parser.pure_preservesTokensOnSuccess none

/-- Optional named-type arguments preserve every ordinary token window. -/
theorem parseNamedTypeArguments_preservesTokenWindow
    (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isSymbol observed .less
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (delimited_preservesTokenWindow .less .greater false nested
        .typeExpr .typeExpr nestedPreserves)
    intro parsed
    apply Parser.bind_preservesTokenWindow
      (requireNonempty_preservesTokenWindow parsed .typeExpr)
    intro nonempty
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

/-- Optional named-type arguments never rewind the recursive cursor. -/
theorem parseNamedTypeArguments_cursorMonotoneOnSuccess
    (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .less
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (delimited_cursorMonotoneOnSuccess .less .greater false nested
        .typeExpr .typeExpr)
    intro parsed
    apply Parser.bind_cursorMonotoneOnSuccess
      (requireNonempty_cursorMonotoneOnSuccess parsed .typeExpr)
    intro nonempty
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- Present named-type arguments start at the current `<` token. -/
theorem parseNamedTypeArguments_some_startsAtCurrentTokenOnSuccess
    (nested : Parser TypeExpr) {input next : State}
    {arguments : NonemptyDelimitedList TypeExpr}
    (result : parseNamedTypeArguments nested input = .ok (some arguments) next) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = arguments.span.startByte := by
  unfold parseNamedTypeArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .less
  · simp only [present, if_true] at result
    rcases bind_ok_components_variant result with
      ⟨parsed, afterParsed, parsedResult, rest⟩
    rcases bind_ok_components_variant rest with
      ⟨nonempty, afterNonempty, nonemptyResult, finished⟩
    unfold requireNonempty at nonemptyResult
    cases elements : parsed.elements with
    | nil => rw [elements] at nonemptyResult; contradiction
    | cons head tail =>
        have starts := delimited_startsAtCurrentTokenOnSuccess .less .greater
          false nested .typeExpr .typeExpr input parsed afterParsed parsedResult
        rw [elements] at nonemptyResult
        cases nonemptyResult
        cases finished
        exact starts
  · simp only [present] at result
    cases result

private theorem finishNamedType_validFor {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList TypeExpr)} {input : State}
    (inputValid : input.ValidFor)
    (valueValid : TypeExpr.ValidFor input.file
      (makeNamedType name arguments)) :
    (finishNamedType name arguments input).ValidFor input
      TypeExpr.ValidFor := by
  unfold finishNamedType
  dsimp only
  split
  · unfold emitDiagnostic modifyState Reply.ValidFor
    exact ⟨valueValid,
      inputValid.emit_validFor _ valueValid.span_valid, rfl⟩
  · exact ⟨valueValid, inputValid, rfl⟩

/-- Named-type parsing retains all name, argument, and outer provenance. -/
theorem parseNamedType_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parseNamedType nested).ValidFor TypeExpr.ValidFor := by
  intro input inputValid
  unfold parseNamedType
  cases nameResult : qualifiedName .typeExpr .typeExpr input with
  | invariant error =>
      simp only [bind, nameResult, Reply.ValidFor]
  | reject failure rejected =>
      have valid := qualifiedName_validFor .typeExpr .typeExpr input inputValid
      rw [nameResult] at valid
      simp only [bind, nameResult, Reply.ValidFor]
      exact ⟨valid.1, valid.2.1, valid.2.2⟩
  | ok name afterName =>
      have nameValid := qualifiedName_validFor .typeExpr .typeExpr input inputValid
      rw [nameResult] at nameValid
      simp only [bind, nameResult]
      cases argumentsResult : parseNamedTypeArguments nested afterName with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := parseNamedTypeArguments_validFor nested nestedValid
            nestedPreserves afterName nameValid.2.1
          rw [argumentsResult] at valid
          exact valid.of_file_eq nameValid.2.2
      | ok arguments afterArguments =>
          have argumentsValid := parseNamedTypeArguments_validFor nested
            nestedValid nestedPreserves afterName nameValid.2.1
          rw [argumentsResult] at argumentsValid
          simp only
          have nameValidFinal : QualifiedName.ValidFor afterArguments.file name := by
            simpa [argumentsValid.2.2] using
              (show QualifiedName.ValidFor afterName.file name from
                by simpa [nameValid.2.2] using nameValid.1)
          have valueValid : TypeExpr.ValidFor afterArguments.file
              (makeNamedType name arguments) := by
            cases arguments with
            | none => exact .namedWithoutArguments nameValidFinal.1 nameValidFinal
            | some values =>
                have valuesValid : NonemptyDelimitedList.ValidFor
                    TypeExpr.ValidFor afterArguments.file values := by
                  simpa [Option.ValidFor, argumentsValid.2.2] using argumentsValid.1
                rcases qualifiedName_startsAtCurrentTokenOnSuccess .typeExpr
                    .typeExpr input name afterName nameResult with
                  ⟨first, firstFound, nameStart⟩
                rcases parseNamedTypeArguments_some_startsAtCurrentTokenOnSuccess
                    nested argumentsResult with ⟨opening, openingFound, argsStart⟩
                have firstAtAfter : afterName.tokens[input.cursor]? = some first := by
                  rw [qualifiedName_preservesTokensOnSuccess .typeExpr .typeExpr
                    input name afterName nameResult]
                  exact State.getElem?_eq_some_of_peek?_eq_some firstFound
                have openingAtAfter :=
                  State.getElem?_eq_some_of_peek?_eq_some openingFound
                have ordered := nameValid.2.1.token_end_le_token_start_of_getElem?_lt
                  firstAtAfter openingAtAfter
                  (qualifiedName_cursor_lt_onSuccess .typeExpr .typeExpr nameResult)
                have firstValid := nameValid.2.1.token_span_validFor_of_getElem?_eq_some
                  firstAtAfter
                have outerOrder : name.span.startByte ≤ values.span.endByte := by
                  rw [← nameStart]
                  exact Nat.le_trans firstValid.2.1
                    (Nat.le_trans ordered (by
                      rw [argsStart]
                      exact valuesValid.1.2.1))
                exact .namedWithArguments
                  (SourceSpan.cover_validFor nameValidFinal.1 valuesValid.1
                    outerOrder)
                  nameValidFinal valuesValid.1 valuesValid.2
          exact (finishNamedType_validFor argumentsValid.2.1 valueValid).of_file_eq
            (argumentsValid.2.2.trans nameValid.2.2)

/-- Finishing a named type preserves the full ordinary token window. -/
theorem finishNamedType_preservesTokenWindow (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.PreservesTokenWindow (finishNamedType name arguments) := by
  intro input
  unfold finishNamedType
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Finishing a named type leaves the cursor in place. -/
theorem finishNamedType_cursorMonotoneOnSuccess (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.CursorMonotoneOnSuccess (finishNamedType name arguments) := by
  intro input value next result
  unfold finishNamedType at result
  dsimp only at result
  split at result
  · unfold emitDiagnostic modifyState at result
    simp only [bind] at result
    cases result
    exact Nat.le_refl _
  · cases result
    exact Nat.le_refl _

/-- Named-type parsing preserves tokens and its active window on every reply. -/
theorem parseNamedType_preservesTokenWindow (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_preservesTokenWindow
    (qualifiedName_preservesTokenWindow .typeExpr .typeExpr)
  intro name
  apply Parser.bind_preservesTokenWindow
    (parseNamedTypeArguments_preservesTokenWindow nested nestedPreserves)
  intro arguments
  exact finishNamedType_preservesTokenWindow name arguments

/-- Successful named-type parsing retains the recursive token carrier. -/
theorem parseNamedType_preservesTokensOnSuccess (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_preservesTokensOnSuccess
    (qualifiedName_preservesTokensOnSuccess .typeExpr .typeExpr)
  intro name
  apply Parser.bind_preservesTokensOnSuccess
    (parseNamedTypeArguments_preservesTokensOnSuccess nested nestedPreserves)
  intro arguments
  exact (finishNamedType_preservesTokenWindow name arguments).preservesTokensOnSuccess

/-- Named-type parsing never rewinds the recursive parser cursor. -/
theorem parseNamedType_cursorMonotoneOnSuccess (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_cursorMonotoneOnSuccess
    (qualifiedName_cursorMonotoneOnSuccess .typeExpr .typeExpr)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    (parseNamedTypeArguments_cursorMonotoneOnSuccess nested)
  intro arguments
  exact finishNamedType_cursorMonotoneOnSuccess name arguments

private theorem finishNamedType_ok_value {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList TypeExpr)}
    {input next : State} {value : TypeExpr}
    (result : finishNamedType name arguments input = .ok value next) :
    value = makeNamedType name arguments := by
  unfold finishNamedType at result
  dsimp only at result
  split at result
  · unfold emitDiagnostic modifyState at result
    simp only [bind] at result
    cases result
    rfl
  · cases result
    rfl

/-- A named type starts at the first component of its qualified name. -/
theorem parseNamedType_startsAtCurrentTokenOnSuccess
    (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseNamedType nested) (·.span) := by
  unfold parseNamedType
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (qualifiedName_startsAtCurrentTokenOnSuccess .typeExpr .typeExpr)
  intro name input value final parsed
  rcases bind_ok_components_variant parsed with
    ⟨arguments, afterArguments, _argumentsResult, finished⟩
  rw [finishNamedType_ok_value finished]
  cases arguments <;> rfl

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeRecursiveProperties
/-! Fuel-inductive contracts for the complete recursive type parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem typeExprWithFuel_contracts : ∀ fuel,
    (typeExprWithFuel fuel).ValidFor TypeExpr.ValidFor ∧
    Parser.PreservesTokenWindow (typeExprWithFuel fuel) ∧
    Parser.PreservesTokensOnSuccess (typeExprWithFuel fuel) ∧
    Parser.CursorMonotoneOnSuccess (typeExprWithFuel fuel) ∧
    Parser.StartsAtCurrentTokenOnSuccess
      (typeExprWithFuel fuel) (·.span) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro input inputValid
        simp [typeExprWithFuel, Reply.ValidFor]
      · intro input
        simp [typeExprWithFuel, Reply.PreservesTokenWindow]
      · intro input value next result
        simp [typeExprWithFuel] at result
      · intro input value next result
        simp [typeExprWithFuel] at result
      · intro input value next result
        simp [typeExprWithFuel] at result
  | succ fuel inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨nestedValid, nestedWindow, nestedTokens, nestedCursor, nestedStarts⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro input inputValid
        simp only [typeExprWithFuel]
        split
        · exact parseFunctionType_validFor (typeExprWithFuel fuel)
            nestedValid nestedTokens input inputValid
        · split
          · exact parseComptimeType_validFor (typeExprWithFuel fuel)
              nestedValid nestedStarts nestedTokens nestedCursor input inputValid
          · split
            · exact parseMappingType_validFor (typeExprWithFuel fuel)
                nestedValid nestedStarts nestedTokens nestedCursor input inputValid
            · split
              · exact parseProxyType_validFor (typeExprWithFuel fuel)
                  nestedValid nestedStarts input inputValid
              · split
                · exact parseTupleType_validFor (typeExprWithFuel fuel)
                    nestedValid nestedTokens input inputValid
                · split
                  · exact parseNamedType_validFor (typeExprWithFuel fuel)
                      nestedValid nestedTokens input inputValid
                  · unfold rejectAt Reply.ValidFor
                    exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
      · intro input
        simp only [typeExprWithFuel]
        split
        · exact parseFunctionType_preservesTokenWindow
            (typeExprWithFuel fuel) nestedWindow input
        · split
          · exact parseComptimeType_preservesTokenWindow
              (typeExprWithFuel fuel) nestedWindow input
          · split
            · exact parseMappingType_preservesTokenWindow
                (typeExprWithFuel fuel) nestedWindow input
            · split
              · exact parseProxyType_preservesTokenWindow
                  (typeExprWithFuel fuel) nestedWindow input
              · split
                · exact parseTupleType_preservesTokenWindow
                    (typeExprWithFuel fuel) nestedWindow input
                · split
                  · exact parseNamedType_preservesTokenWindow
                      (typeExprWithFuel fuel) nestedWindow input
                  · exact rejectAt_preservesTokenWindow input _ _
      · intro input value next result
        simp only [typeExprWithFuel] at result
        split at result
        · exact parseFunctionType_preservesTokensOnSuccess
            (typeExprWithFuel fuel) nestedTokens input value next result
        · split at result
          · exact parseComptimeType_preservesTokensOnSuccess
              (typeExprWithFuel fuel) nestedTokens input value next result
          · split at result
            · exact parseMappingType_preservesTokensOnSuccess
                (typeExprWithFuel fuel) nestedTokens input value next result
            · split at result
              · exact parseProxyType_preservesTokensOnSuccess
                  (typeExprWithFuel fuel) nestedTokens input value next result
              · split at result
                · exact parseTupleType_preservesTokensOnSuccess
                    (typeExprWithFuel fuel) nestedTokens input value next result
                · split at result
                  · exact parseNamedType_preservesTokensOnSuccess
                      (typeExprWithFuel fuel) nestedTokens input value next result
                  · unfold rejectAt at result
                    contradiction
      · intro input value next result
        simp only [typeExprWithFuel] at result
        split at result
        · exact parseFunctionType_cursorMonotoneOnSuccess
            (typeExprWithFuel fuel) input value next result
        · split at result
          · exact parseComptimeType_cursorMonotoneOnSuccess
              (typeExprWithFuel fuel) nestedCursor input value next result
          · split at result
            · exact parseMappingType_cursorMonotoneOnSuccess
                (typeExprWithFuel fuel) nestedCursor input value next result
            · split at result
              · exact parseProxyType_cursorMonotoneOnSuccess
                  (typeExprWithFuel fuel) nestedCursor input value next result
              · split at result
                · exact parseTupleType_cursorMonotoneOnSuccess
                    (typeExprWithFuel fuel) input value next result
                · split at result
                  · exact parseNamedType_cursorMonotoneOnSuccess
                      (typeExprWithFuel fuel) input value next result
                  · unfold rejectAt at result
                    contradiction
      · intro input value next result
        simp only [typeExprWithFuel] at result
        split at result
        · exact parseFunctionType_startsAtCurrentTokenOnSuccess
            (typeExprWithFuel fuel) input value next result
        · split at result
          · exact parseComptimeType_startsAtCurrentTokenOnSuccess
              (typeExprWithFuel fuel) input value next result
          · split at result
            · exact parseMappingType_startsAtCurrentTokenOnSuccess
                (typeExprWithFuel fuel) input value next result
            · split at result
              · exact parseProxyType_startsAtCurrentTokenOnSuccess
                  (typeExprWithFuel fuel) input value next result
              · split at result
                · exact parseTupleType_startsAtCurrentTokenOnSuccess
                    (typeExprWithFuel fuel) input value next result
                · split at result
                  · exact parseNamedType_startsAtCurrentTokenOnSuccess
                      (typeExprWithFuel fuel) input value next result
                  · unfold rejectAt at result
                    contradiction

/-- Every fuel-bounded recursive type parse retains source provenance. -/
theorem typeExprWithFuel_validFor (fuel : Nat) :
    (typeExprWithFuel fuel).ValidFor TypeExpr.ValidFor :=
  (typeExprWithFuel_contracts fuel).1

/-- Every successful fuel-bounded type parse retains the token carrier. -/
theorem typeExprWithFuel_preservesTokensOnSuccess (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (typeExprWithFuel fuel) :=
  (typeExprWithFuel_contracts fuel).2.2.1

/-- Every fuel-bounded recursive type reply retains its active token window. -/
theorem typeExprWithFuel_preservesTokenWindow (fuel : Nat) :
    Parser.PreservesTokenWindow (typeExprWithFuel fuel) :=
  (typeExprWithFuel_contracts fuel).2.1

/-- Every successful fuel-bounded type parse is cursor-monotone. -/
theorem typeExprWithFuel_cursorMonotoneOnSuccess (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess (typeExprWithFuel fuel) :=
  (typeExprWithFuel_contracts fuel).2.2.2.1

/-- Every successful fuel-bounded type starts at its current token. -/
theorem typeExprWithFuel_startsAtCurrentTokenOnSuccess (fuel : Nat) :
    Parser.StartsAtCurrentTokenOnSuccess
      (typeExprWithFuel fuel) (·.span) :=
  (typeExprWithFuel_contracts fuel).2.2.2.2

/-- Public recursive type parsing retains source provenance at computed fuel. -/
theorem typeExpr_validFor : typeExpr.ValidFor TypeExpr.ValidFor := by
  intro input inputValid
  unfold typeExpr
  exact typeExprWithFuel_validFor (input.remainingCount + 1)
    input inputValid

/-- Public recursive type success retains the immutable token carrier. -/
theorem typeExpr_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess typeExpr := by
  intro input value next result
  unfold typeExpr at result
  exact typeExprWithFuel_preservesTokensOnSuccess
    (input.remainingCount + 1) input value next result

/-- Public recursive type parsing preserves every ordinary token window. -/
theorem typeExpr_preservesTokenWindow :
    Parser.PreservesTokenWindow typeExpr := by
  intro input
  unfold typeExpr
  exact typeExprWithFuel_preservesTokenWindow
    (input.remainingCount + 1) input

/-- Public recursive type success never rewinds the parser cursor. -/
theorem typeExpr_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess typeExpr := by
  intro input value next result
  unfold typeExpr at result
  exact typeExprWithFuel_cursorMonotoneOnSuccess
    (input.remainingCount + 1) input value next result

/-- Public recursive type success starts at the current input token. -/
theorem typeExpr_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess typeExpr (·.span) := by
  intro input value next result
  unfold typeExpr at result
  exact typeExprWithFuel_startsAtCurrentTokenOnSuccess
    (input.remainingCount + 1) input value next result

end Solcore.Syntax.Parser
end
