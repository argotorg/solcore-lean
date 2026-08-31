import Solcore.Syntax.Parser.Expression.Atom
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.ExpressionValidity

/-! Provenance and state contracts for canonical Core expression atoms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ExpressionAtomInternals

private theorem atomBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
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

/-- Expression names retain the ordinary or Boolean builtin token range. -/
theorem expressionName_validFor :
    expressionName.ValidFor Located.ValidFor := by
  intro input inputValid
  unfold expressionName
  split
  · exact booleanIdentifier_validFor input inputValid
  · exact identifier_validFor .expression input inputValid

/-- Expression-name parsing preserves every ordinary token window. -/
theorem expressionName_preservesTokenWindow :
    Parser.PreservesTokenWindow expressionName := by
  intro input
  unfold expressionName
  split
  · exact booleanIdentifier_preservesTokenWindow input
  · exact identifier_preservesTokenWindow .expression input

theorem expressionName_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess expressionName :=
  expressionName_preservesTokenWindow.preservesTokensOnSuccess

/-- A successful expression name consumes exactly its current token. -/
theorem expressionName_ok_state_shape {input next : State}
    {name : Identifier} (parsed : expressionName input = .ok name next) :
    ∃ token, input.peek? = some token ∧ token.span = name.span ∧
      next.tokens = input.tokens ∧ next.cursor = input.cursor + 1 := by
  unfold expressionName at parsed
  split at parsed
  · unfold booleanIdentifier at parsed
    cases found : input.peek? with
    | none => simp [found, rejectAt] at parsed
    | some token =>
        rcases token with ⟨span, kind⟩
        cases kind <;> simp only [found] at parsed
        all_goals try { unfold rejectAt at parsed; contradiction }
        case keyword keyword =>
          cases keyword <;> simp only at parsed
          all_goals try { unfold rejectAt at parsed; contradiction }
          all_goals cases parsed
          all_goals exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact identifier_ok_state_shape .expression parsed

/-- Successful expression-name parsing never rewinds the cursor. -/
theorem expressionName_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess expressionName := by
  intro input name next parsed
  unfold expressionName at parsed
  split at parsed
  · exact booleanIdentifier_cursorMonotoneOnSuccess
      input name next parsed
  · exact identifier_cursorMonotoneOnSuccess .expression
      input name next parsed

theorem expressionName_cursor_lt_onSuccess {input next : State}
    {name : Identifier} (parsed : expressionName input = .ok name next) :
    input.cursor < next.cursor := by
  rw [(expressionName_ok_state_shape parsed).choose_spec.2.2.2]
  simp

/-- An expression name starts at its ordinary or Boolean name token. -/
theorem expressionName_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess expressionName (·.span) := by
  intro input name next parsed
  unfold expressionName at parsed
  split at parsed
  · exact booleanIdentifier_startsAtCurrentTokenOnSuccess
      input name next parsed
  · rcases identifier_ok_state_shape .expression parsed with
      ⟨token, found, span, _tokens, _cursor⟩
    exact ⟨token, found, congrArg SourceSpan.startByte span⟩

/-- Literal-expression parsing retains both equal literal ranges. -/
theorem literalExpression_validFor
    (statementValid : SourceFile → Statement → Prop) :
    literalExpression.ValidFor (Expr.ValidFor statementValid) := by
  unfold literalExpression
  apply Parser.bind_validFor_of_value coreLiteral_validFor
  intro literal input inputValid literalValid
  exact ⟨Expr.ValidFor.literal literalValid literalValid, inputValid, rfl⟩

/-- Literal expressions preserve every ordinary token window. -/
theorem literalExpression_preservesTokenWindow :
    Parser.PreservesTokenWindow literalExpression := by
  unfold literalExpression
  apply Parser.bind_preservesTokenWindow coreLiteral_preservesTokenWindow
  intro literal
  exact Parser.pure_preservesTokenWindow _

theorem literalExpression_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess literalExpression :=
  literalExpression_preservesTokenWindow.preservesTokensOnSuccess

/-- Literal-expression parsing never rewinds the cursor. -/
theorem literalExpression_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess literalExpression := by
  unfold literalExpression
  apply Parser.bind_cursorMonotoneOnSuccess
    coreLiteral_cursorMonotoneOnSuccess
  intro literal
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A literal expression starts at its literal token. -/
theorem literalExpression_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess literalExpression (·.span) := by
  unfold literalExpression
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    coreLiteral_startsAtCurrentTokenOnSuccess
  intro literal input value final parsed
  cases parsed
  rfl

/-- Identifier-expression parsing retains both equal name ranges. -/
theorem identifierExpression_validFor
    (statementValid : SourceFile → Statement → Prop) :
    identifierExpression.ValidFor (Expr.ValidFor statementValid) := by
  unfold identifierExpression
  apply Parser.bind_validFor_of_value expressionName_validFor
  intro name input inputValid nameValid
  exact ⟨Expr.ValidFor.identifier nameValid nameValid, inputValid, rfl⟩

/-- Identifier expressions preserve every ordinary token window. -/
theorem identifierExpression_preservesTokenWindow :
    Parser.PreservesTokenWindow identifierExpression := by
  unfold identifierExpression
  apply Parser.bind_preservesTokenWindow expressionName_preservesTokenWindow
  intro name
  exact Parser.pure_preservesTokenWindow _

theorem identifierExpression_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess identifierExpression :=
  identifierExpression_preservesTokenWindow.preservesTokensOnSuccess

/-- Identifier-expression parsing never rewinds the cursor. -/
theorem identifierExpression_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess identifierExpression := by
  unfold identifierExpression
  apply Parser.bind_cursorMonotoneOnSuccess
    expressionName_cursorMonotoneOnSuccess
  intro name
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- An identifier expression starts at its name token. -/
theorem identifierExpression_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess identifierExpression (·.span) := by
  unfold identifierExpression
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    expressionName_startsAtCurrentTokenOnSuccess
  intro name input value final parsed
  cases parsed
  rfl

/-- Proxy expressions retain their marker, inner type, and outer cover. -/
theorem proxyExpression_validFor
    (statementValid : SourceFile → Statement → Prop) :
    proxyExpression.ValidFor (Expr.ValidFor statementValid) := by
  have weak : proxyExpression.ValidFor (fun _ _ => True) := by
    unfold proxyExpression
    apply Parser.bind_validFor (symbol_validFor .at .expression)
    intro marker
    apply Parser.bind_validFor typeExpr_validFor
    intro type
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : proxyExpression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok expression final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold proxyExpression at stages
      rcases atomBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases atomBind_ok_components rest with
        ⟨type, afterType, typeResult, finished⟩
      have markerContract := symbol_validFor .at .expression input inputValid
      rw [markerResult] at markerContract
      have typeContract := typeExpr_validFor afterMarker markerContract.2.1
      rw [typeResult] at typeContract
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerContract.1
      have typeValidInput : TypeExpr.ValidFor input.file type := by
        simpa [markerContract.2.2] using typeContract.1
      rcases typeExpr_startsAtCurrentTokenOnSuccess
          afterMarker type afterType typeResult with
        ⟨typeToken, typeFound, typeStart⟩
      have markerShape :=
        symbol_ok_state_shape .at .expression markerResult
      have advanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      have markerBeforeType :
          marker.span.endByte ≤ type.span.startByte := by
        rw [← typeStart]
        exact inputValid.consumed_end_le_peek_start_after_advance
          advanced typeFound
      have outerValid :
          (SourceSpan.cover marker.span type.span).ValidFor input.file := by
        apply SourceSpan.cover_validFor markerSpanValid
          typeValidInput.span_valid
        exact Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeType typeValidInput.span_valid.2.1)
      cases finished
      exact ⟨Expr.ValidFor.proxy outerValid markerSpanValid typeValidInput,
        weakResult.2.1, weakResult.2.2⟩

/-- Proxy-expression parsing preserves every ordinary token window. -/
theorem proxyExpression_preservesTokenWindow :
    Parser.PreservesTokenWindow proxyExpression := by
  unfold proxyExpression
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .at .expression)
  intro marker
  apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
  intro type
  exact Parser.pure_preservesTokenWindow _

theorem proxyExpression_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess proxyExpression :=
  proxyExpression_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful proxy-expression parsing never rewinds the cursor. -/
theorem proxyExpression_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess proxyExpression := by
  unfold proxyExpression
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .at .expression)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    typeExpr_cursorMonotoneOnSuccess
  intro type
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A proxy expression starts at its current `@` token. -/
theorem proxyExpression_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess proxyExpression (·.span) := by
  unfold proxyExpression
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (symbol_startsAtCurrentTokenOnSuccess .at .expression)
  intro marker input expression final parsed
  rcases atomBind_ok_components parsed with
    ⟨type, afterType, typeResult, finished⟩
  cases finished
  rfl

private theorem optionalDotConstructorArguments_validFor
    (nested : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (optionalDotConstructorArguments nested).ValidFor
      (Option.ValidFor
        (DelimitedList.ValidFor (Expr.ValidFor statementValid))) := by
  unfold optionalDotConstructorArguments
  apply Parser.bind_validFor getState_validFor
  intro observed
  split
  · apply Parser.bind_validFor_of_value
      (delimitedNoTrailing_validFor (Expr.ValidFor statementValid)
        .leftParen .rightParen true nested .expression .expression
        nestedValid nestedPreserves)
    intro values input inputValid valuesValid
    exact ⟨by simpa only [Option.ValidFor] using valuesValid,
      inputValid, rfl⟩
  · exact Parser.pure_validFor none _ (fun _ => trivial)

private theorem optionalDotConstructorArguments_preservesTokenWindow
    (nested : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow
      (optionalDotConstructorArguments nested) := by
  unfold optionalDotConstructorArguments
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  split
  · apply Parser.bind_preservesTokenWindow
      (delimitedWithPolicy_preservesTokenWindow .leftParen .rightParen
        true false nested .expression .expression nestedPreserves)
    intro values
    exact Parser.pure_preservesTokenWindow _
  · exact Parser.pure_preservesTokenWindow none

private theorem optionalDotConstructorArguments_cursorMonotoneOnSuccess
    (nested : Parser Expr) :
    Parser.CursorMonotoneOnSuccess
      (optionalDotConstructorArguments nested) := by
  unfold optionalDotConstructorArguments
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      (delimitedNoTrailing_cursorMonotoneOnSuccess .leftParen .rightParen
        true nested .expression .expression)
    intro values
    exact Parser.pure_cursorMonotoneOnSuccess _
  · exact Parser.pure_cursorMonotoneOnSuccess none

private theorem optionalDotConstructorArguments_some_starts
    (nested : Parser Expr) {input next : State}
    {values : DelimitedList Expr}
    (parsed : optionalDotConstructorArguments nested input =
      .ok (some values) next) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = values.span.startByte := by
  unfold optionalDotConstructorArguments at parsed
  rcases atomBind_ok_components parsed with
    ⟨observed, afterState, stateResult, rest⟩
  unfold getState at stateResult
  cases stateResult
  split at rest
  · rcases atomBind_ok_components rest with
      ⟨arguments, afterArguments, argumentsResult, finished⟩
    have starts := delimitedNoTrailing_startsAtCurrentTokenOnSuccess
      .leftParen .rightParen true nested .expression .expression
      input arguments afterArguments argumentsResult
    cases finished
    exact starts
  · cases rest

private theorem dotConstructor_weakValidFor (nested : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (dotConstructor nested).ValidFor (fun _ _ => True) := by
  have argumentsWeak :=
    (optionalDotConstructorArguments_validFor nested statementValid
      nestedValid nestedPreserves).mono (fun _ _ _ => trivial)
  unfold dotConstructor
  apply Parser.bind_validFor (symbol_validFor .dot .expression)
  intro dot
  apply Parser.bind_validFor expressionName_validFor
  intro name
  apply Parser.bind_validFor argumentsWeak
  intro arguments
  exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/-- Leading-dot expressions retain their name, arguments, and outer cover. -/
theorem dotConstructor_validFor (nested : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (dotConstructor nested).ValidFor (Expr.ValidFor statementValid) := by
  intro input inputValid
  have weak := dotConstructor_weakValidFor nested statementValid
    nestedValid nestedPreserves input inputValid
  cases parsed : dotConstructor nested input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weak; exact weak
  | ok result final =>
      rw [parsed] at weak
      have stages := parsed
      unfold dotConstructor at stages
      rcases atomBind_ok_components stages with
        ⟨dot, afterDot, dotResult, rest⟩
      rcases atomBind_ok_components rest with
        ⟨name, afterName, nameResult, rest⟩
      rcases atomBind_ok_components rest with
        ⟨arguments, afterArguments, argumentsResult, finished⟩
      have dotReply := symbol_validFor .dot .expression input inputValid
      rw [dotResult] at dotReply
      have nameReply := expressionName_validFor afterDot dotReply.2.1
      rw [nameResult] at nameReply
      have argumentsReply := optionalDotConstructorArguments_validFor
        nested statementValid nestedValid nestedPreserves
        afterName nameReply.2.1
      rw [argumentsResult] at argumentsReply
      have dotSpanValid : dot.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using dotReply.1
      have nameSpanValid : name.span.ValidFor input.file := by
        simpa only [Located.ValidFor, dotReply.2.2] using nameReply.1
      have argumentsValid : Option.ValidFor
          (DelimitedList.ValidFor (Expr.ValidFor statementValid))
          input.file arguments := by
        simpa [nameReply.2.2, dotReply.2.2] using argumentsReply.1
      have dotShape := symbol_ok_state_shape .dot .expression dotResult
      rcases expressionName_ok_state_shape nameResult with
        ⟨nameToken, nameFound, nameTokenSpan, nameTokens, nameCursor⟩
      have dotAdvanced : input.advance? = some (dot, afterDot) := by
        unfold State.advance?
        rw [dotShape.1, dotShape.2]
        rfl
      have dotBeforeName :=
        inputValid.consumed_end_le_peek_start_after_advance
          dotAdvanced nameFound
      have orderedName : dot.span.startByte ≤ name.span.endByte :=
        Nat.le_trans dotSpanValid.2.1 (Nat.le_trans
          (by simpa [nameTokenSpan] using dotBeforeName)
          nameSpanValid.2.1)
      cases arguments with
      | none =>
          cases finished
          exact ⟨Expr.ValidFor.dotConstructor
            (SourceSpan.cover_validFor dotSpanValid nameSpanValid orderedName)
            dotSpanValid nameSpanValid (by simp) (by simp),
            weak.2.1, weak.2.2⟩
      | some values =>
          have valuesValid : DelimitedList.ValidFor
              (Expr.ValidFor statementValid) input.file values := by
            simpa only [Option.ValidFor] using argumentsValid
          rcases optionalDotConstructorArguments_some_starts nested
              argumentsResult with ⟨opening, openingFound, valuesStart⟩
          have nameAtAfterName :
              afterName.tokens[afterDot.cursor]? = some nameToken := by
            rw [nameTokens]
            exact State.getElem?_eq_some_of_peek?_eq_some nameFound
          have openingAt :=
            State.getElem?_eq_some_of_peek?_eq_some openingFound
          have nameBeforeValues :=
            nameReply.2.1.token_end_le_token_start_of_getElem?_lt
              nameAtAfterName openingAt (by rw [nameCursor]; simp)
          have orderedValues : dot.span.startByte ≤ values.span.endByte :=
            Nat.le_trans orderedName (Nat.le_trans
              (by simpa [nameTokenSpan, valuesStart] using nameBeforeValues)
              valuesValid.1.2.1)
          cases finished
          refine ⟨Expr.ValidFor.dotConstructor
            (SourceSpan.cover_validFor dotSpanValid valuesValid.1
              orderedValues) dotSpanValid nameSpanValid ?_ ?_,
            weak.2.1, weak.2.2⟩
          · intro retained member
            simp at member
            subst retained
            exact valuesValid.1
          · intro retained retainedMember argument argumentMember
            simp at retainedMember
            subst retained
            exact valuesValid.2 argument argumentMember

/-- Leading-dot expression parsing preserves every ordinary token window. -/
theorem dotConstructor_preservesTokenWindow (nested : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (dotConstructor nested) := by
  unfold dotConstructor
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .dot .expression)
  intro dot
  apply Parser.bind_preservesTokenWindow expressionName_preservesTokenWindow
  intro name
  apply Parser.bind_preservesTokenWindow
    (optionalDotConstructorArguments_preservesTokenWindow
      nested nestedPreserves)
  intro arguments
  exact Parser.pure_preservesTokenWindow _

theorem dotConstructor_preservesTokensOnSuccess (nested : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokensOnSuccess (dotConstructor nested) :=
  (dotConstructor_preservesTokenWindow nested
    nestedPreserves).preservesTokensOnSuccess

/-- Leading-dot expression parsing never rewinds the cursor. -/
theorem dotConstructor_cursorMonotoneOnSuccess (nested : Parser Expr) :
    Parser.CursorMonotoneOnSuccess (dotConstructor nested) := by
  unfold dotConstructor
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .dot .expression)
  intro dot
  apply Parser.bind_cursorMonotoneOnSuccess
    expressionName_cursorMonotoneOnSuccess
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalDotConstructorArguments_cursorMonotoneOnSuccess nested)
  intro arguments
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A leading-dot expression starts at its dot token. -/
theorem dotConstructor_startsAtCurrentTokenOnSuccess
    (nested : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (dotConstructor nested) (·.span) := by
  unfold dotConstructor
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (symbol_startsAtCurrentTokenOnSuccess .dot .expression)
  intro dot input value final parsed
  rcases atomBind_ok_components parsed with
    ⟨name, afterName, nameResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  rfl

/-- Closing a tuple retains its opening token and accumulated expressions. -/
theorem closeTuple_validFor
    (statementValid : SourceFile → Statement → Prop)
    (opening : Token) (elementsRev : List Expr) {input : State}
    {openingIndex : Nat} (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (elementsValid : List.ValidFor (Expr.ValidFor statementValid)
      input.file elementsRev) :
    (closeTuple opening elementsRev input).ValidFor input
      (Expr.ValidFor statementValid) := by
  unfold closeTuple
  simp only [bind]
  cases closingResult : symbol .rightParen .expression input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .rightParen .expression input inputValid
      rw [closingResult] at valid
      exact valid
  | ok closing afterClosing =>
      have closingValid := symbol_validFor .rightParen .expression
        input inputValid
      rw [closingResult] at closingValid
      have closingShape := symbol_ok_state_shape .rightParen .expression
        closingResult
      have closingFound :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingValid :=
        inputValid.token_span_validFor_of_getElem?_eq_some openingFound
      have closingSpanValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using closingValid.1
      have openingBeforeClosing :=
        inputValid.token_end_le_token_start_of_getElem?_lt openingFound
          closingFound openingBefore
      have outerValid := SourceSpan.cover_validFor openingValid
        closingSpanValid (Nat.le_trans openingValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1))
      cases elementsRev with
      | nil =>
          exact ⟨Expr.ValidFor.tuple outerValid outerValid
            (by simp), closingValid.2.1, closingValid.2.2⟩
      | cons only tail =>
          cases tail with
          | nil =>
              exact ⟨Expr.ValidFor.group outerValid
                (elementsValid only (by simp)), closingValid.2.1,
                closingValid.2.2⟩
          | cons second rest =>
              exact ⟨Expr.ValidFor.tuple outerValid outerValid
                (by
                  intro element member
                  exact elementsValid element (by
                    simpa only [List.mem_reverse] using member)),
                closingValid.2.1, closingValid.2.2⟩

/-- Closing an expression tuple preserves every ordinary token window. -/
theorem closeTuple_preservesTokenWindow (opening : Token)
    (elementsRev : List Expr) :
    Parser.PreservesTokenWindow (closeTuple opening elementsRev) := by
  unfold closeTuple
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightParen .expression)
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_preservesTokenWindow _
  | cons only tail =>
      cases tail <;> exact Parser.pure_preservesTokenWindow _

theorem closeTuple_preservesTokensOnSuccess (opening : Token)
    (elementsRev : List Expr) :
    Parser.PreservesTokensOnSuccess (closeTuple opening elementsRev) :=
  (closeTuple_preservesTokenWindow opening
    elementsRev).preservesTokensOnSuccess

/-- Closing an expression tuple never rewinds the cursor. -/
theorem closeTuple_cursorMonotoneOnSuccess (opening : Token)
    (elementsRev : List Expr) :
    Parser.CursorMonotoneOnSuccess (closeTuple opening elementsRev) := by
  unfold closeTuple
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .expression)
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_cursorMonotoneOnSuccess _
  | cons only tail =>
      cases tail <;> exact Parser.pure_cursorMonotoneOnSuccess _

/-- Closing retains the opening parenthesis as the result start. -/
theorem closeTuple_preservesOpeningStartOnSuccess
    (opening : Token) (elementsRev : List Expr)
    {input final : State} {expression : Expr}
    (parsed : closeTuple opening elementsRev input =
      .ok expression final) :
    expression.span.startByte = opening.span.startByte := by
  unfold closeTuple at parsed
  rcases atomBind_ok_components parsed with
    ⟨closing, afterClosing, _closingResult, finished⟩
  cases elementsRev with
  | nil => cases finished; rfl
  | cons only tail =>
      cases tail with
      | nil => cases finished; rfl
      | cons second rest => cases finished; rfl

/-- The result ends at the current closing-parenthesis token. -/
theorem closeTuple_endsAtCurrentTokenOnSuccess
    (opening : Token) (elementsRev : List Expr)
    {input final : State} {expression : Expr}
    (parsed : closeTuple opening elementsRev input =
      .ok expression final) :
    ∃ closing, input.peek? = some closing ∧
      closing.span.endByte = expression.span.endByte := by
  unfold closeTuple at parsed
  rcases atomBind_ok_components parsed with
    ⟨closing, afterClosing, closingResult, finished⟩
  have found :=
    (symbol_ok_state_shape .rightParen .expression closingResult).1
  cases elementsRev with
  | nil => cases finished; exact ⟨closing, found, rfl⟩
  | cons only tail =>
      cases tail with
      | nil => cases finished; exact ⟨closing, found, rfl⟩
      | cons second rest =>
          cases finished
          exact ⟨closing, found, rfl⟩

/-- The closing parenthesis is the final consumed token. -/
theorem closeTuple_endsAtLastConsumedTokenOnSuccess
    (opening : Token) (elementsRev : List Expr)
    {input final : State} {expression : Expr}
    (parsed : closeTuple opening elementsRev input =
      .ok expression final) :
    ∃ closing, final.tokens[final.cursor - 1]? = some closing ∧
      closing.span.endByte = expression.span.endByte := by
  unfold closeTuple at parsed
  rcases atomBind_ok_components parsed with
    ⟨closing, afterClosing, closingResult, finished⟩
  have shape := symbol_ok_state_shape .rightParen .expression closingResult
  have indexed := State.getElem?_eq_some_of_peek?_eq_some shape.1
  cases elementsRev with
  | nil => cases finished; exact ⟨closing, by simpa [shape.2] using indexed, rfl⟩
  | cons only tail =>
      cases tail with
      | nil => cases finished; exact ⟨closing, by simpa [shape.2] using indexed, rfl⟩
      | cons second rest =>
          cases finished
          exact ⟨closing, by simpa [shape.2] using indexed, rfl⟩

/-- The tuple-tail loop retains its opening and accumulated expressions. -/
theorem tupleTail_validFor (nested : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (opening : Token) : ∀ fuel elementsRev input openingIndex,
    input.ValidFor →
    input.tokens[openingIndex]? = some opening →
    openingIndex < input.cursor →
    List.ValidFor (Expr.ValidFor statementValid) input.file elementsRev →
    (tupleTail nested opening fuel elementsRev input).ValidFor input
      (Expr.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro elementsRev input openingIndex inputValid openingFound
        openingBefore elementsValid
      unfold tupleTail
      cases commaResult : symbol .comma .expression input with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := symbol_validFor .comma .expression input inputValid
          rw [commaResult] at valid
          exact valid
      | ok comma afterComma =>
          have commaValid := symbol_validFor .comma .expression input
            inputValid
          rw [commaResult] at commaValid
          have commaShape := symbol_ok_state_shape .comma .expression
            commaResult
          have openingFoundAfter :
              afterComma.tokens[openingIndex]? = some opening := by
            simpa [commaShape.2] using openingFound
          have openingBeforeAfter : openingIndex < afterComma.cursor := by
            simpa [commaShape.2] using Nat.lt_succ_of_lt openingBefore
          have elementsValidAfter : List.ValidFor
              (Expr.ValidFor statementValid) afterComma.file
              elementsRev := by
            simpa [commaValid.2.2] using elementsValid
          simp only
          split
          · exact (closeTuple_validFor statementValid opening elementsRev
                commaValid.2.1 openingFoundAfter openingBeforeAfter
                elementsValidAfter).of_file_eq commaValid.2.2
          · cases nestedResult : nested afterComma with
            | invariant error => trivial
            | reject failure rejected =>
                have valid := nestedValid afterComma commaValid.2.1
                rw [nestedResult] at valid
                exact valid.of_file_eq commaValid.2.2
            | ok value next =>
                have valueValid := nestedValid afterComma commaValid.2.1
                rw [nestedResult] at valueValid
                simp only
                split
                · have tokensEq := nestedPreserves afterComma value next
                      nestedResult
                  have openingFoundNext :
                      next.tokens[openingIndex]? = some opening := by
                    simpa [tokensEq] using openingFoundAfter
                  have openingBeforeNext : openingIndex < next.cursor :=
                    Nat.lt_trans openingBeforeAfter (by omega)
                  have accumulatedValid : List.ValidFor
                      (Expr.ValidFor statementValid) next.file
                      (value :: elementsRev) := by
                    intro retained member
                    rcases List.mem_cons.mp member with rfl | member
                    · simpa [valueValid.2.2] using valueValid.1
                    · simpa [valueValid.2.2] using
                        elementsValidAfter retained member
                  split
                  · exact (inductionHypothesis (value :: elementsRev) next
                        openingIndex valueValid.2.1 openingFoundNext
                        openingBeforeNext accumulatedValid).of_file_eq
                          (valueValid.2.2.trans commaValid.2.2)
                  · exact (closeTuple_validFor statementValid opening
                        (value :: elementsRev) valueValid.2.1
                        openingFoundNext openingBeforeNext
                        accumulatedValid).of_file_eq
                          (valueValid.2.2.trans commaValid.2.2)
                · trivial

/-- The tuple-tail loop preserves the nested parser's token window. -/
theorem tupleTail_preservesTokenWindow (nested : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (opening : Token) : ∀ fuel elementsRev,
    Parser.PreservesTokenWindow
      (tupleTail nested opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro elementsRev input
      unfold tupleTail
      have commaShape := symbol_preservesTokenWindow .comma .expression input
      cases commaResult : symbol .comma .expression input with
      | invariant error => trivial
      | reject failure rejected =>
          rw [commaResult] at commaShape
          exact commaShape
      | ok comma afterComma =>
          rw [commaResult] at commaShape
          simp only
          split
          · exact (closeTuple_preservesTokenWindow opening elementsRev
                afterComma).trans commaShape
          · have nestedShape := nestedPreserves afterComma
            cases nestedResult : nested afterComma with
            | invariant error => trivial
            | reject failure rejected =>
                rw [nestedResult] at nestedShape
                exact nestedShape.trans commaShape
            | ok value next =>
                rw [nestedResult] at nestedShape
                simp only
                split
                · split
                  · exact (inductionHypothesis (value :: elementsRev)
                        next).trans (nestedShape.trans commaShape)
                  · exact (closeTuple_preservesTokenWindow opening
                        (value :: elementsRev) next).trans
                          (nestedShape.trans commaShape)
                · trivial

theorem tupleTail_preservesTokensOnSuccess (nested : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (opening : Token) (fuel : Nat) (elementsRev : List Expr) :
    Parser.PreservesTokensOnSuccess
      (tupleTail nested opening fuel elementsRev) :=
  (tupleTail_preservesTokenWindow nested nestedPreserves opening
    fuel elementsRev).preservesTokensOnSuccess

/-- The tuple-tail loop never rewinds the parser cursor. -/
theorem tupleTail_cursorMonotoneOnSuccess (nested : Parser Expr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (opening : Token) : ∀ fuel elementsRev,
    Parser.CursorMonotoneOnSuccess
      (tupleTail nested opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input expression final parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input expression final parsed
      unfold tupleTail at parsed
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at parsed
      | reject failure rejected => simp [commaResult] at parsed
      | ok comma afterComma =>
          simp only [commaResult] at parsed
          have commaMonotone := symbol_cursorMonotoneOnSuccess .comma
            .expression input comma afterComma commaResult
          split at parsed
          · exact Nat.le_trans commaMonotone
              (closeTuple_cursorMonotoneOnSuccess opening elementsRev
                afterComma expression final parsed)
          · cases nestedResult : nested afterComma with
            | invariant error => simp [nestedResult] at parsed
            | reject failure rejected => simp [nestedResult] at parsed
            | ok value next =>
                simp only [nestedResult] at parsed
                have valueMonotone := nestedMonotone afterComma value next
                  nestedResult
                split at parsed
                · split at parsed
                  · exact Nat.le_trans commaMonotone
                      (Nat.le_trans valueMonotone
                        (inductionHypothesis (value :: elementsRev)
                          next expression final parsed))
                  · exact Nat.le_trans commaMonotone
                      (Nat.le_trans valueMonotone
                        (closeTuple_cursorMonotoneOnSuccess opening
                          (value :: elementsRev) next expression final parsed))
                · contradiction

/-- Every successful tuple-tail result keeps its opening-parenthesis start. -/
theorem tupleTail_preservesOpeningStartOnSuccess
    (nested : Parser Expr) (opening : Token) :
    ∀ fuel elementsRev input expression final,
      tupleTail nested opening fuel elementsRev input =
        .ok expression final →
      expression.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input expression final parsed
      unfold tupleTail at parsed
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at parsed
      | reject failure rejected => simp [commaResult] at parsed
      | ok comma afterComma =>
          simp only [commaResult] at parsed
          split at parsed
          · exact closeTuple_preservesOpeningStartOnSuccess opening
              elementsRev parsed
          · cases nestedResult : nested afterComma with
            | invariant error => simp [nestedResult] at parsed
            | reject failure rejected => simp [nestedResult] at parsed
            | ok value next =>
                simp only [nestedResult] at parsed
                split at parsed
                · split at parsed
                  · exact inductionHypothesis (value :: elementsRev)
                      next expression final parsed
                  · exact closeTuple_preservesOpeningStartOnSuccess
                      opening (value :: elementsRev) parsed
                · contradiction

/-- A successful tuple tail ends at its final consumed parenthesis. -/
theorem tupleTail_endsAtLastConsumedTokenOnSuccess
    (nested : Parser Expr) (opening : Token) :
    ∀ fuel elementsRev input expression final,
      tupleTail nested opening fuel elementsRev input =
        .ok expression final →
      ∃ closing, final.tokens[final.cursor - 1]? = some closing ∧
        closing.span.endByte = expression.span.endByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input expression final parsed
      unfold tupleTail at parsed
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at parsed
      | reject failure rejected => simp [commaResult] at parsed
      | ok comma afterComma =>
          simp only [commaResult] at parsed
          split at parsed
          · exact closeTuple_endsAtLastConsumedTokenOnSuccess opening
              elementsRev parsed
          · cases nestedResult : nested afterComma with
            | invariant error => simp [nestedResult] at parsed
            | reject failure rejected => simp [nestedResult] at parsed
            | ok value next =>
                simp only [nestedResult] at parsed
                split at parsed
                · split at parsed
                  · exact inductionHypothesis (value :: elementsRev)
                      next expression final parsed
                  · exact closeTuple_endsAtLastConsumedTokenOnSuccess
                      opening (value :: elementsRev) parsed
                · contradiction

/-- Parenthesized expressions retain delimiters and every nested range. -/
theorem parenthesized_validFor (nested : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parenthesized nested).ValidFor (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold parenthesized
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .leftParen .expression input inputValid
      rw [openingResult] at valid
      exact valid
  | ok opening afterOpening =>
      have openingValid := symbol_validFor .leftParen .expression input
        inputValid
      rw [openingResult] at openingValid
      have openingShape := symbol_ok_state_shape .leftParen .expression
        openingResult
      have openingFound :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have openingFoundAfter :
          afterOpening.tokens[input.cursor]? = some opening := by
        simpa [openingShape.2] using openingFound
      have openingBeforeAfter : input.cursor < afterOpening.cursor := by
        rw [openingShape.2]
        simp
      simp only
      split
      · exact (closeTuple_validFor statementValid opening []
            openingValid.2.1 openingFoundAfter openingBeforeAfter
            (by simp [List.ValidFor])).of_file_eq openingValid.2.2
      · cases nestedResult : nested afterOpening with
        | invariant error => trivial
        | reject failure rejected =>
            have valid := nestedValid afterOpening openingValid.2.1
            rw [nestedResult] at valid
            exact valid.of_file_eq openingValid.2.2
        | ok first next =>
            have firstValid := nestedValid afterOpening openingValid.2.1
            rw [nestedResult] at firstValid
            simp only
            split
            · trivial
            · have tokensEq := nestedPreserves afterOpening first next
                  nestedResult
              have openingFoundNext :
                  next.tokens[input.cursor]? = some opening := by
                simpa [tokensEq] using openingFoundAfter
              have openingBeforeNext : input.cursor < next.cursor :=
                Nat.lt_trans openingBeforeAfter (by omega)
              have accumulatedValid : List.ValidFor
                  (Expr.ValidFor statementValid) next.file [first] := by
                intro retained member
                simp only [List.mem_singleton] at member
                subst retained
                simpa [firstValid.2.2] using firstValid.1
              split
              · exact (tupleTail_validFor nested statementValid nestedValid
                    nestedPreserves opening (next.remainingCount + 1)
                    [first] next input.cursor firstValid.2.1
                    openingFoundNext openingBeforeNext accumulatedValid
                  ).of_file_eq (firstValid.2.2.trans openingValid.2.2)
              · exact (closeTuple_validFor statementValid opening [first]
                    firstValid.2.1 openingFoundNext openingBeforeNext
                    accumulatedValid).of_file_eq
                      (firstValid.2.2.trans openingValid.2.2)

/-- Parenthesized parsing preserves every ordinary token window. -/
theorem parenthesized_preservesTokenWindow (nested : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parenthesized nested) := by
  intro input
  unfold parenthesized
  have openingShape := symbol_preservesTokenWindow .leftParen .expression input
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [openingResult] at openingShape
      exact openingShape
  | ok opening afterOpening =>
      rw [openingResult] at openingShape
      simp only
      split
      · exact (closeTuple_preservesTokenWindow opening []
            afterOpening).trans openingShape
      · have nestedShape := nestedPreserves afterOpening
        cases nestedResult : nested afterOpening with
        | invariant error => trivial
        | reject failure rejected =>
            rw [nestedResult] at nestedShape
            exact nestedShape.trans openingShape
        | ok first next =>
            rw [nestedResult] at nestedShape
            simp only
            split
            · trivial
            · split
              · exact (tupleTail_preservesTokenWindow nested
                    nestedPreserves opening (next.remainingCount + 1)
                    [first] next).trans (nestedShape.trans openingShape)
              · exact (closeTuple_preservesTokenWindow opening
                    [first] next).trans (nestedShape.trans openingShape)

theorem parenthesized_preservesTokensOnSuccess (nested : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokensOnSuccess (parenthesized nested) :=
  (parenthesized_preservesTokenWindow nested
    nestedPreserves).preservesTokensOnSuccess

/-- Parenthesized parsing never rewinds the parser cursor. -/
theorem parenthesized_cursorMonotoneOnSuccess (nested : Parser Expr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parenthesized nested) := by
  intro input expression final parsed
  unfold parenthesized at parsed
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      have openingMonotone := symbol_cursorMonotoneOnSuccess .leftParen
        .expression input opening afterOpening openingResult
      split at parsed
      · exact Nat.le_trans openingMonotone
          (closeTuple_cursorMonotoneOnSuccess opening []
            afterOpening expression final parsed)
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
              · exact Nat.le_trans openingMonotone
                  (Nat.le_trans firstMonotone
                    (tupleTail_cursorMonotoneOnSuccess nested
                      nestedMonotone opening (next.remainingCount + 1)
                      [first] next expression final parsed))
              · exact Nat.le_trans openingMonotone
                  (Nat.le_trans firstMonotone
                    (closeTuple_cursorMonotoneOnSuccess opening
                      [first] next expression final parsed))

/-- A parenthesized expression starts at its opening parenthesis. -/
theorem parenthesized_startsAtCurrentTokenOnSuccess (nested : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parenthesized nested) (fun expression => expression.span) := by
  intro input expression final parsed
  unfold parenthesized at parsed
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      have found :=
        (symbol_ok_state_shape .leftParen .expression openingResult).1
      split at parsed
      · have start := closeTuple_preservesOpeningStartOnSuccess
            opening [] parsed
        exact ⟨opening, found, start.symm⟩
      · cases nestedResult : nested afterOpening with
        | invariant error => simp [nestedResult] at parsed
        | reject failure rejected => simp [nestedResult] at parsed
        | ok first next =>
            simp only [nestedResult] at parsed
            split at parsed
            · contradiction
            · split at parsed
              · have start := tupleTail_preservesOpeningStartOnSuccess
                    nested opening (next.remainingCount + 1) [first]
                    next expression final parsed
                exact ⟨opening, found, start.symm⟩
              · have start := closeTuple_preservesOpeningStartOnSuccess
                    opening [first] parsed
                exact ⟨opening, found, start.symm⟩

/-- A parenthesized expression ends at its final consumed parenthesis. -/
theorem parenthesized_endsAtLastConsumedTokenOnSuccess
    (nested : Parser Expr) {input final : State} {expression : Expr}
    (parsed : parenthesized nested input = .ok expression final) :
    ∃ closing, final.tokens[final.cursor - 1]? = some closing ∧
      closing.span.endByte = expression.span.endByte := by
  unfold parenthesized at parsed
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      split at parsed
      · exact closeTuple_endsAtLastConsumedTokenOnSuccess opening [] parsed
      · cases nestedResult : nested afterOpening with
        | invariant error => simp [nestedResult] at parsed
        | reject failure rejected => simp [nestedResult] at parsed
        | ok first next =>
            simp only [nestedResult] at parsed
            split at parsed
            · contradiction
            · split at parsed
              · exact tupleTail_endsAtLastConsumedTokenOnSuccess nested
                  opening (next.remainingCount + 1) [first]
                  next expression final parsed
              · exact closeTuple_endsAtLastConsumedTokenOnSuccess
                  opening [first] parsed

/-- Array literals retain their delimiters and every nested expression. -/
theorem arrayLiteral_validFor (nested : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (arrayLiteral nested).ValidFor (Expr.ValidFor statementValid) := by
  unfold arrayLiteral
  apply Parser.bind_validFor_of_value
    (delimitedNoTrailing_validFor (Expr.ValidFor statementValid)
      .leftBracket .rightBracket true nested .expression .expression
      nestedValid nestedPreserves)
  intro values input inputValid valuesValid
  exact ⟨Expr.ValidFor.array valuesValid.1 valuesValid.1 valuesValid.2,
    inputValid, rfl⟩

/-- Array-literal parsing preserves every ordinary token window. -/
theorem arrayLiteral_preservesTokenWindow (nested : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (arrayLiteral nested) := by
  have valuesWindow : Parser.PreservesTokenWindow
      (delimitedNoTrailing .leftBracket .rightBracket true nested
        .expression .expression) := by
    exact delimitedWithPolicy_preservesTokenWindow .leftBracket .rightBracket
      true false nested .expression .expression nestedPreserves
  unfold arrayLiteral
  apply Parser.bind_preservesTokenWindow valuesWindow
  intro values
  exact Parser.pure_preservesTokenWindow _

theorem arrayLiteral_preservesTokensOnSuccess (nested : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokensOnSuccess (arrayLiteral nested) :=
  (arrayLiteral_preservesTokenWindow nested
    nestedPreserves).preservesTokensOnSuccess

/-- Array-literal parsing never rewinds the parser cursor. -/
theorem arrayLiteral_cursorMonotoneOnSuccess (nested : Parser Expr) :
    Parser.CursorMonotoneOnSuccess (arrayLiteral nested) := by
  unfold arrayLiteral
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimitedNoTrailing_cursorMonotoneOnSuccess .leftBracket .rightBracket
      true nested .expression .expression)
  intro values
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- An array literal starts at its current opening bracket. -/
theorem arrayLiteral_startsAtCurrentTokenOnSuccess (nested : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (arrayLiteral nested) (fun expression => expression.span) := by
  unfold arrayLiteral
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimitedNoTrailing_startsAtCurrentTokenOnSuccess .leftBracket
      .rightBracket true nested .expression .expression)
  intro values input expression final parsed
  cases parsed
  rfl

/-- The array expression retains the complete delimited-list endpoint. -/
theorem arrayLiteral_retainsDelimitedEndOnSuccess (nested : Parser Expr)
    {input final : State} {expression : Expr}
    (parsed : arrayLiteral nested input = .ok expression final) :
    ∃ values, expression.value = .array values ∧
      expression.span.endByte = values.span.endByte := by
  unfold arrayLiteral at parsed
  rcases atomBind_ok_components parsed with
    ⟨values, afterValues, _valuesResult, finished⟩
  cases finished
  exact ⟨values, rfl, rfl⟩

end ExpressionAtomInternals
end Solcore.Syntax.Parser
