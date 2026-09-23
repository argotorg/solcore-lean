import Solcore.Syntax.Parser.Literal
import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.ExpressionValidity
import Solcore.Syntax.Parser.LiteralTotalityProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties
import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.InvariantFreeProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExpressionAtomInternals

/-- Parse an ordinary identifier or Boolean builtin as an expression name. -/
def expressionName : Parser Identifier := fun state =>
  if isBooleanValue state then booleanIdentifier state
  else identifier .expression state

/-- Parse one canonical literal expression leaf. -/
def literalExpression : Parser Expr := do
  let literal ← coreLiteral
  pure {
    span := literal.span
    value := .literal literal
  }

/-- Parse one canonical identifier expression leaf. -/
def identifierExpression : Parser Expr := do
  let name ← expressionName
  pure {
    span := name.span
    value := .identifier name
  }

/-- Parse a proxy expression whose outer range begins at its `@` marker. -/
def proxyExpression : Parser Expr := do
  let marker ← symbol .at .expression
  let type ← typeExpr
  pure {
    span := SourceSpan.cover marker.span type.span
    value := .proxy marker.span type
  }

/-- Parse the optional argument list of a leading-dot constructor. -/
def optionalDotConstructorArguments (nested : Parser Expr) :
    Parser (Option (DelimitedList Expr)) := do
  let state ← getState
  if isSymbol state .leftParen then
    pure (some (← delimitedNoTrailing .leftParen .rightParen true
      nested .expression .expression))
  else
    pure none

/-- Parse a leading-dot constructor expression. -/
def dotConstructor (nested : Parser Expr) : Parser Expr := do
  let dot ← symbol .dot .expression
  let name ← expressionName
  let arguments ← optionalDotConstructorArguments nested
  let endSpan := arguments.map (fun values => values.span) |>.getD name.span
  pure {
    span := SourceSpan.cover dot.span endSpan
    value := .dotConstructor dot.span name arguments
  }

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Close a parenthesized expression after its elements have been accumulated. -/
def closeTuple (opening : Token) (elementsRev : List Expr) :
    Parser Expr := do
  let closing ← symbol .rightParen .expression
  let span := SourceSpan.cover opening.span closing.span
  match elementsRev with
  | [only] => pure { span, value := .group only }
  | _ => pure {
      span
      value := .tuple { span, elements := elementsRev.reverse }
    }

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Continue a parenthesized expression after its first comma. -/
def tupleTail (nested : Parser Expr) (opening : Token) :
    Nat → List Expr → State → Reply Expr
  | 0, _, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, elementsRev, state =>
      match symbol .comma .expression state with
      | .ok _ afterComma =>
          if isSymbol afterComma .rightParen then
            ExpressionAtomInternals.closeTuple opening elementsRev afterComma
          else
            let before := afterComma.cursor
            match nested afterComma with
            | .ok value next =>
                if next.cursor > before then
                  if isSymbol next .comma then
                    ExpressionAtomInternals.tupleTail nested opening fuel
                      (value :: elementsRev) next
                  else
                    ExpressionAtomInternals.closeTuple opening
                      (value :: elementsRev) next
                else
                  .invariant (.noProgress .expression next.currentSpan)
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Parse a grouped expression or tuple after an opening parenthesis. -/
def parenthesized (nested : Parser Expr) : Parser Expr := fun state =>
  match symbol .leftParen .expression state with
  | .ok opening afterOpening =>
      if isSymbol afterOpening .rightParen then
        ExpressionAtomInternals.closeTuple opening [] afterOpening
      else
        let before := afterOpening.cursor
        match nested afterOpening with
        | .ok first next =>
            if next.cursor ≤ before then
              .invariant (.noProgress .expression next.currentSpan)
            else if isSymbol next .comma then
              ExpressionAtomInternals.tupleTail nested opening
                (next.remainingCount + 1) [first] next
            else
              ExpressionAtomInternals.closeTuple opening [first] next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Parse a bracketed array literal. -/
def arrayLiteral (nested : Parser Expr) : Parser Expr := do
  let values ← delimitedNoTrailing .leftBracket .rightBracket true nested
    .expression .expression
  pure { span := values.span, value := .array values }

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Parse an optional lambda return type introduced by `->`. -/
def optionalLambdaReturnType : Parser (Option TypeExpr) := do
  let state ← getState
  if isSymbol state .arrow then
    let _ ← symbol .arrow .typeExpr
    pure (some (← typeExpr))
  else
    pure none

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Parse a lambda expression using the supplied recursive block parser. -/
def lambdaExpression (block : Parser Block) : Parser Expr := do
  let marker ← keyword .lamKw .expression
  let parameters ← delimited .leftParen .rightParen true
    lambdaParameter .parameter .expression
  let returnType ← ExpressionAtomInternals.optionalLambdaReturnType
  let body ← block
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .lambda marker.span parameters returnType body
  }

end ExpressionAtomInternals

namespace ExpressionAtomInternals

def expressionAtomCore (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  if isCoreLiteral state then
    ExpressionAtomInternals.literalExpression state
  else if isBooleanValue state || isIdentifier state then
    ExpressionAtomInternals.identifierExpression state
  else if isSymbol state .dot then
    ExpressionAtomInternals.dotConstructor nested state
  else if isSymbol state .at then
    ExpressionAtomInternals.proxyExpression state
  else if isSymbol state .leftParen then
    ExpressionAtomInternals.parenthesized nested state
  else if isSymbol state .leftBracket then
    ExpressionAtomInternals.arrayLiteral nested state
  else if isKeyword state .lamKw then
    ExpressionAtomInternals.lambdaExpression block state
  else rejectAt state { head := .expression, tail := [] } .expression

def isAtomBoundary (state : State) : Bool :=
  state.atEnd ||
    [.semicolon, .comma, .rightParen, .rightBracket, .rightBrace,
      .question, .colon, .fatArrow, .pipe].any (isSymbol state) ||
    isKeyword state .elseKw

def finishRecoveredAtom (first last : SourceSpan)
    (state : State) : Reply Expr :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .expressionAtom
  })

def recoverAtomAux (first last : SourceSpan) :
    Nat → State → Reply Expr
  | 0, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, state =>
      if isAtomBoundary state then
        finishRecoveredAtom first last state
      else
        match state.advance? with
        | some (token, next) => recoverAtomAux first token.span fuel next
        | none => finishRecoveredAtom first last state

def recoverAtom (state : State) : Reply Expr :=
  match state.advance? with
  | some (token, next) =>
      recoverAtomAux token.span token.span (next.remainingCount + 1) next
  | none => rejectAt state { head := .expression, tail := [] } .expression

end ExpressionAtomInternals

/-- Parse one recoverable expression atom. -/
def expressionAtom (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  match ExpressionAtomInternals.expressionAtomCore nested block state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if ExpressionAtomInternals.isAtomBoundary rewound then
        .reject failure rewound
      else
        ExpressionAtomInternals.recoverAtom
          (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

namespace ExpressionAtomInternals

/-- Extend one atom through every following index, call, and field suffix. -/
def postfixTail (nested : Parser Expr) (block : Parser Block) :
    Nat → Expr → State → Reply Expr
  | 0, _, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, base, state =>
      if isSymbol state .leftBracket then
        match symbol .leftBracket .expression state with
        | .ok opening afterOpening =>
            match nested afterOpening with
            | .ok index next =>
                match symbol .rightBracket .expression next with
                | .ok closing afterClosing =>
                    let brackets := SourceSpan.cover opening.span closing.span
                    ExpressionAtomInternals.postfixTail nested block fuel {
                      span := SourceSpan.cover base.span closing.span
                      value := .index base brackets index
                    } afterClosing
                | .reject failure failed => .reject failure failed
                | .invariant error => .invariant error
            | .reject failure failed => .reject failure failed
            | .invariant error => .invariant error
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
      else if isSymbol state .leftParen then
        match delimitedNoTrailing .leftParen .rightParen true nested
            .expression .expression state with
        | .ok arguments next =>
            ExpressionAtomInternals.postfixTail nested block fuel {
              span := SourceSpan.cover base.span arguments.span
              value := .call base arguments
            } next
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
      else if isSymbol state .dot then
        match symbol .dot .expression state with
        | .ok dot afterDot =>
            match identifier .expression afterDot with
            | .ok name next =>
                ExpressionAtomInternals.postfixTail nested block fuel {
                  span := SourceSpan.cover base.span name.span
                  value := .field base dot.span name
                } next
            | .reject failure failed => .reject failure failed
            | .invariant error => .invariant error
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
      else
        .ok base state

end ExpressionAtomInternals

/-- Parse an atom followed by all canonical postfix operations. -/
def expressionPostfix (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  match expressionAtom nested block state with
  | .ok base next =>
      ExpressionAtomInternals.postfixTail nested block
        (next.remainingCount + 1) base next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.Expression.AtomProperties`
-/

/-! Provenance and state contracts for canonical Core expression atoms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ExpressionAtomInternals

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

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

/-- Optional lambda return types retain their arrow-following type syntax. -/
theorem optionalLambdaReturnType_validFor :
    optionalLambdaReturnType.ValidFor
      (Option.ValidFor TypeExpr.ValidFor) := by
  unfold optionalLambdaReturnType
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_validFor (symbol_validFor .arrow .typeExpr)
    intro arrow
    apply Parser.bind_validFor_of_value typeExpr_validFor
    intro type input inputValid typeValid
    exact ⟨by simpa only [Option.ValidFor] using typeValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional lambda return types preserve every ordinary token window. -/
theorem optionalLambdaReturnType_preservesTokenWindow :
    Parser.PreservesTokenWindow optionalLambdaReturnType := by
  unfold optionalLambdaReturnType
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .arrow .typeExpr)
    intro arrow
    apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
    intro type
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem optionalLambdaReturnType_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess optionalLambdaReturnType :=
  optionalLambdaReturnType_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional lambda return-type parsing never rewinds the cursor. -/
theorem optionalLambdaReturnType_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess optionalLambdaReturnType := by
  unfold optionalLambdaReturnType
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .arrow .typeExpr)
    intro arrow
    apply Parser.bind_cursorMonotoneOnSuccess
      typeExpr_cursorMonotoneOnSuccess
    intro type
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present lambda return type starts at the token after its arrow. -/
theorem optionalLambdaReturnType_some_startsAfterArrow
    {input final : State} {type : TypeExpr}
    (parsed : optionalLambdaReturnType input = .ok (some type) final) :
    ∃ arrow afterArrow first,
      symbol .arrow .typeExpr input = .ok arrow afterArrow ∧
      afterArrow.peek? = some first ∧
      first.span.startByte = type.span.startByte := by
  unfold optionalLambdaReturnType getState at parsed
  simp only [bind] at parsed
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at parsed
    rcases atomBind_ok_components parsed with
      ⟨arrow, afterArrow, arrowResult, rest⟩
    rcases atomBind_ok_components rest with
      ⟨parsedType, afterType, typeResult, finished⟩
    have typeEq : parsedType = type := by cases finished; rfl
    subst parsedType
    rcases typeExpr_startsAtCurrentTokenOnSuccess
        afterArrow type afterType typeResult with
      ⟨first, firstFound, firstStart⟩
    exact ⟨arrow, afterArrow, first, arrowResult, firstFound, firstStart⟩
  · simp only [present] at parsed
    change Reply.ok none input = .ok (some type) final at parsed
    cases parsed

/-- Lambda parsing preserves token windows when its recursive leaves do. -/
theorem lambdaExpression_preservesTokenWindow (block : Parser Block)
    (parameterWindow : Parser.PreservesTokenWindow lambdaParameter)
    (blockWindow : Parser.PreservesTokenWindow block) :
    Parser.PreservesTokenWindow (lambdaExpression block) := by
  unfold lambdaExpression
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .lamKw .expression)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftParen .rightParen true
      lambdaParameter .parameter .expression parameterWindow)
  intro parameters
  apply Parser.bind_preservesTokenWindow
    optionalLambdaReturnType_preservesTokenWindow
  intro returnType
  apply Parser.bind_preservesTokenWindow blockWindow
  intro body
  exact Parser.pure_preservesTokenWindow _

theorem lambdaExpression_preservesTokensOnSuccess (block : Parser Block)
    (parameterWindow : Parser.PreservesTokenWindow lambdaParameter)
    (blockWindow : Parser.PreservesTokenWindow block) :
    Parser.PreservesTokensOnSuccess (lambdaExpression block) :=
  (lambdaExpression_preservesTokenWindow block parameterWindow
    blockWindow).preservesTokensOnSuccess

/-- Lambda parsing never rewinds when its body parser is monotone. -/
theorem lambdaExpression_cursorMonotoneOnSuccess (block : Parser Block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block) :
    Parser.CursorMonotoneOnSuccess (lambdaExpression block) := by
  unfold lambdaExpression
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .lamKw .expression)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
      lambdaParameter .parameter .expression)
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalLambdaReturnType_cursorMonotoneOnSuccess
  intro returnType
  apply Parser.bind_cursorMonotoneOnSuccess blockCursor
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A lambda expression starts at its `lam` keyword token. -/
theorem lambdaExpression_startsAtCurrentTokenOnSuccess
    (block : Parser Block) :
    Parser.StartsAtCurrentTokenOnSuccess
      (lambdaExpression block) (fun expression => expression.span) := by
  unfold lambdaExpression
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .lamKw)
      .expression (· == .keyword .lamKw))
  intro marker input expression final parsed
  rcases atomBind_ok_components parsed with
    ⟨parameters, afterParameters, _parametersResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨returnType, afterReturnType, _returnTypeResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  rfl

/-- A lambda expression retains its parsed body's final endpoint. -/
theorem lambdaExpression_retainsBodyEndOnSuccess (block : Parser Block)
    {input final : State} {expression : Expr}
    (parsed : lambdaExpression block input = .ok expression final) :
    ∃ (marker : Token) (parameters : DelimitedList LambdaParameter)
      (returnType : Option TypeExpr) (body : Block),
      expression.value = .lambda marker.span parameters returnType body ∧
      expression.span.endByte = body.span.endByte := by
  unfold lambdaExpression at parsed
  rcases atomBind_ok_components parsed with
    ⟨marker, afterMarker, _markerResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨parameters, afterParameters, _parametersResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨returnType, afterReturnType, _returnTypeResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  exact ⟨marker, parameters, returnType, body, rfl, rfl⟩

private theorem lambdaExpression_weakValidFor (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : block.ValidFor (Block.ValidFor statementValid)) :
    (lambdaExpression block).ValidFor (fun _ _ => True) := by
  unfold lambdaExpression
  apply Parser.bind_validFor (keyword_validFor .lamKw .expression)
  intro marker
  apply Parser.bind_validFor
    ((delimited_validFor LambdaParameter.ValidFor .leftParen .rightParen true
      lambdaParameter .parameter .expression lambdaParameter_validFor
      lambdaParameter_preservesTokensOnSuccess).mono (fun _ _ _ => trivial))
  intro parameters
  apply Parser.bind_validFor
    (optionalLambdaReturnType_validFor.mono (fun _ _ _ => trivial))
  intro returnType
  apply Parser.bind_validFor (blockValid.mono (fun _ _ _ => trivial))
  intro body
  exact Parser.pure_validFor _ _ (fun _ => trivial)

/-- Lambda parsing retains parameters, return type, body, and outer range. -/
theorem lambdaExpression_validFor (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span)) :
    (lambdaExpression block).ValidFor (Expr.ValidFor statementValid) := by
  intro input inputValid
  have weak := lambdaExpression_weakValidFor block statementValid blockValid
    input inputValid
  cases parsed : lambdaExpression block input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weak; exact weak
  | ok expression final =>
      rw [parsed] at weak
      have stages := parsed
      unfold lambdaExpression at stages
      rcases atomBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases atomBind_ok_components rest with
        ⟨parameters, afterParameters, parametersResult, rest⟩
      rcases atomBind_ok_components rest with
        ⟨returnType, afterReturnType, returnTypeResult, rest⟩
      rcases atomBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerReply := keyword_validFor .lamKw .expression input inputValid
      rw [markerResult] at markerReply
      have parametersContract := delimited_validFor LambdaParameter.ValidFor
        .leftParen .rightParen true lambdaParameter .parameter .expression
        lambdaParameter_validFor lambdaParameter_preservesTokensOnSuccess
      have parametersReply := parametersContract afterMarker markerReply.2.1
      rw [parametersResult] at parametersReply
      have returnTypeReply := optionalLambdaReturnType_validFor
        afterParameters parametersReply.2.1
      rw [returnTypeResult] at returnTypeReply
      have bodyReply := blockValid afterReturnType returnTypeReply.2.1
      rw [bodyResult] at bodyReply
      have markerValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerReply.1
      have parametersValid : DelimitedList.ValidFor LambdaParameter.ValidFor
          input.file parameters := by
        simpa [markerReply.2.2] using parametersReply.1
      have returnTypeValid : Option.ValidFor TypeExpr.ValidFor input.file
          returnType := by
        simpa [parametersReply.2.2, markerReply.2.2] using returnTypeReply.1
      have bodyValid : Block.ValidFor statementValid input.file body := by
        simpa [returnTypeReply.2.2, parametersReply.2.2,
          markerReply.2.2] using bodyReply.1
      have markerShape := acceptToken_ok_state_shape (.keyword .lamKw)
        .expression (· == .keyword .lamKw) markerResult
      have parametersTokens := delimited_preservesTokensOnSuccess
        .leftParen .rightParen true lambdaParameter .parameter .expression
          lambdaParameter_preservesTokensOnSuccess afterMarker parameters
            afterParameters parametersResult
      have returnTypeTokens := optionalLambdaReturnType_preservesTokensOnSuccess
        afterParameters returnType afterReturnType returnTypeResult
      rcases blockStarts afterReturnType body afterBody bodyResult with
        ⟨bodyToken, bodyFound, bodyStart⟩
      have markerAt : afterReturnType.tokens[input.cursor]? = some marker := by
        simpa [returnTypeTokens, parametersTokens, markerShape.2] using
          State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      have bodyAt := State.getElem?_eq_some_of_peek?_eq_some bodyFound
      have markerBeforeBody :=
        returnTypeReply.2.1.token_end_le_token_start_of_getElem?_lt
          markerAt bodyAt (by
            have parametersCursor := delimited_cursorMonotoneOnSuccess
              .leftParen .rightParen true lambdaParameter .parameter .expression
                afterMarker parameters afterParameters parametersResult
            have returnTypeCursor := optionalLambdaReturnType_cursorMonotoneOnSuccess
              afterParameters returnType afterReturnType returnTypeResult
            simp [markerShape.2] at parametersCursor
            omega)
      have ordered : marker.span.startByte ≤ body.span.endByte :=
        Nat.le_trans markerValid.2.1 (Nat.le_trans markerBeforeBody
          (by rw [bodyStart]; exact bodyValid.1.2.1))
      cases finished
      refine ⟨Expr.ValidFor.lambda
        (SourceSpan.cover_validFor markerValid bodyValid.1 ordered)
        markerValid parametersValid.1 parametersValid.2 ?_ bodyValid,
        weak.2.1, weak.2.2⟩
      intro type member
      cases returnType with
      | none => simp at member
      | some retained =>
          simp at member
          subst type
          simpa [Option.ValidFor] using returnTypeValid

/-- Literal atoms consume their literal token. -/
theorem literalExpression_cursor_lt_onSuccess {input next : State}
    {expression : Expr}
    (parsed : literalExpression input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold literalExpression at parsed
  rcases atomBind_ok_components parsed with
    ⟨literal, afterLiteral, literalResult, finished⟩
  cases finished
  exact coreLiteral_cursor_lt_onSuccess literalResult

/-- Identifier atoms consume their name token. -/
theorem identifierExpression_cursor_lt_onSuccess {input next : State}
    {expression : Expr}
    (parsed : identifierExpression input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold identifierExpression at parsed
  rcases atomBind_ok_components parsed with
    ⟨name, afterName, nameResult, finished⟩
  cases finished
  exact expressionName_cursor_lt_onSuccess nameResult

/-- Proxy atoms consume `@` before parsing their type. -/
theorem proxyExpression_cursor_lt_onSuccess {input next : State}
    {expression : Expr}
    (parsed : proxyExpression input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold proxyExpression at parsed
  rcases atomBind_ok_components parsed with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨type, afterType, typeResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (acceptToken_cursor_lt_onSuccess (.symbol .at) .expression
      (· == .symbol .at) markerResult)
    (typeExpr_cursorMonotoneOnSuccess afterMarker type next typeResult)

/-- Leading-dot atoms consume their dot before all optional arguments. -/
theorem dotConstructor_cursor_lt_onSuccess (nested : Parser Expr)
    {input next : State} {expression : Expr}
    (parsed : dotConstructor nested input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold dotConstructor at parsed
  rcases atomBind_ok_components parsed with
    ⟨dot, afterDot, dotResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (acceptToken_cursor_lt_onSuccess (.symbol .dot) .expression
      (· == .symbol .dot) dotResult)
    (Nat.le_trans (expressionName_cursorMonotoneOnSuccess afterDot name
      afterName nameResult)
      (optionalDotConstructorArguments_cursorMonotoneOnSuccess nested
        afterName arguments next argumentsResult))

/-- Parenthesized atoms consume their opening parenthesis. -/
theorem parenthesized_cursor_lt_onSuccess (nested : Parser Expr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input next : State} {expression : Expr}
    (parsed : parenthesized nested input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold parenthesized at parsed
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      have openingStrict := acceptToken_cursor_lt_onSuccess
        (.symbol .leftParen) .expression (· == .symbol .leftParen)
          openingResult
      split at parsed
      · exact Nat.lt_of_lt_of_le openingStrict
          (closeTuple_cursorMonotoneOnSuccess opening []
            afterOpening expression next parsed)
      · cases nestedResult : nested afterOpening with
        | invariant error => simp [nestedResult] at parsed
        | reject failure rejected => simp [nestedResult] at parsed
        | ok first afterFirst =>
            simp only [nestedResult] at parsed
            have firstMonotone := nestedMonotone afterOpening first afterFirst
              nestedResult
            split at parsed
            · contradiction
            · split at parsed
              · exact Nat.lt_of_lt_of_le openingStrict
                  (Nat.le_trans firstMonotone
                    (tupleTail_cursorMonotoneOnSuccess nested nestedMonotone
                      opening (afterFirst.remainingCount + 1) [first]
                        afterFirst expression next parsed))
              · exact Nat.lt_of_lt_of_le openingStrict
                  (Nat.le_trans firstMonotone
                    (closeTuple_cursorMonotoneOnSuccess opening [first]
                      afterFirst expression next parsed))

/-- Array atoms consume their complete bracketed list. -/
theorem arrayLiteral_cursor_lt_onSuccess (nested : Parser Expr)
    {input next : State} {expression : Expr}
    (parsed : arrayLiteral nested input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold arrayLiteral at parsed
  rcases atomBind_ok_components parsed with
    ⟨values, afterValues, valuesResult, finished⟩
  cases finished
  exact delimitedWithPolicy_cursor_lt_onSuccess .leftBracket .rightBracket
    true false nested .expression .expression valuesResult

/-- Lambda atoms consume `lam` before their remaining syntax. -/
theorem lambdaExpression_cursor_lt_onSuccess (block : Parser Block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    {input next : State} {expression : Expr}
    (parsed : lambdaExpression block input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold lambdaExpression at parsed
  rcases atomBind_ok_components parsed with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨returnType, afterReturnType, returnTypeResult, rest⟩
  rcases atomBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (acceptToken_cursor_lt_onSuccess (.keyword .lamKw) .expression
      (· == .keyword .lamKw) markerResult)
    (Nat.le_trans (delimited_cursorMonotoneOnSuccess .leftParen .rightParen
      true lambdaParameter .parameter .expression afterMarker parameters
        afterParameters parametersResult)
      (Nat.le_trans (optionalLambdaReturnType_cursorMonotoneOnSuccess
        afterParameters returnType afterReturnType returnTypeResult)
        (blockCursor afterReturnType body next bodyResult)))

/-- Atom dispatch preserves recursive source provenance in every branch. -/
theorem expressionAtomCore_validFor
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedTokens : Parser.PreservesTokensOnSuccess nested)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span)) :
    (expressionAtomCore nested block).ValidFor
      (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold expressionAtomCore
  split
  · exact literalExpression_validFor statementValid input inputValid
  · split
    · exact identifierExpression_validFor statementValid input inputValid
    · split
      · exact dotConstructor_validFor nested statementValid nestedValid
          nestedTokens input inputValid
      · split
        · exact proxyExpression_validFor statementValid input inputValid
        · split
          · exact parenthesized_validFor nested statementValid nestedValid
              nestedTokens input inputValid
          · split
            · exact arrayLiteral_validFor nested statementValid nestedValid
                nestedTokens input inputValid
            · split
              · exact lambdaExpression_validFor block statementValid
                  blockValid blockStarts input inputValid
              · unfold rejectAt Reply.ValidFor
                exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩

/-- Atom dispatch preserves token windows when its recursive leaves do. -/
theorem expressionAtomCore_preservesTokenWindow
    (nested : Parser Expr) (block : Parser Block)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (blockWindow : Parser.PreservesTokenWindow block) :
    Parser.PreservesTokenWindow (expressionAtomCore nested block) := by
  intro input
  unfold expressionAtomCore
  split
  · exact literalExpression_preservesTokenWindow input
  · split
    · exact identifierExpression_preservesTokenWindow input
    · split
      · exact dotConstructor_preservesTokenWindow nested nestedWindow input
      · split
        · exact proxyExpression_preservesTokenWindow input
        · split
          · exact parenthesized_preservesTokenWindow nested nestedWindow input
          · split
            · exact arrayLiteral_preservesTokenWindow nested nestedWindow input
            · split
              · exact lambdaExpression_preservesTokenWindow block
                  lambdaParameter_preservesTokenWindow blockWindow input
              · exact rejectAt_preservesTokenWindow input _ _

/-- Successful atom dispatch never rewinds recursive leaves. -/
theorem expressionAtomCore_cursorMonotoneOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (blockCursor : Parser.CursorMonotoneOnSuccess block) :
    Parser.CursorMonotoneOnSuccess (expressionAtomCore nested block) := by
  intro input value next result
  unfold expressionAtomCore at result
  split at result
  · exact literalExpression_cursorMonotoneOnSuccess input value next result
  · split at result
    · exact identifierExpression_cursorMonotoneOnSuccess input value next result
    · split at result
      · exact dotConstructor_cursorMonotoneOnSuccess nested
          input value next result
      · split at result
        · exact proxyExpression_cursorMonotoneOnSuccess input value next result
        · split at result
          · exact parenthesized_cursorMonotoneOnSuccess nested nestedCursor
              input value next result
          · split at result
            · exact arrayLiteral_cursorMonotoneOnSuccess nested
                input value next result
            · split at result
              · exact lambdaExpression_cursorMonotoneOnSuccess block blockCursor
                  input value next result
              · simp [rejectAt] at result

/-- Every successful dispatched atom consumes at least one token. -/
theorem expressionAtomCore_cursor_lt_onSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    {input next : State} {value : Expr}
    (parsed : expressionAtomCore nested block input = .ok value next) :
    input.cursor < next.cursor := by
  unfold expressionAtomCore at parsed
  split at parsed
  · exact literalExpression_cursor_lt_onSuccess parsed
  · split at parsed
    · exact identifierExpression_cursor_lt_onSuccess parsed
    · split at parsed
      · exact dotConstructor_cursor_lt_onSuccess nested parsed
      · split at parsed
        · exact proxyExpression_cursor_lt_onSuccess parsed
        · split at parsed
          · exact parenthesized_cursor_lt_onSuccess nested nestedMonotone parsed
          · split at parsed
            · exact arrayLiteral_cursor_lt_onSuccess nested parsed
            · split at parsed
              · exact lambdaExpression_cursor_lt_onSuccess block blockCursor
                  parsed
              · simp [rejectAt] at parsed

/-- Every successful atom branch starts at the dispatch input token. -/
theorem expressionAtomCore_startsAtCurrentTokenOnSuccess
    (nested : Parser Expr) (block : Parser Block) :
    Parser.StartsAtCurrentTokenOnSuccess
      (expressionAtomCore nested block) (·.span) := by
  intro input value next result
  unfold expressionAtomCore at result
  split at result
  · exact literalExpression_startsAtCurrentTokenOnSuccess input value next result
  · split at result
    · exact identifierExpression_startsAtCurrentTokenOnSuccess
        input value next result
    · split at result
      · exact dotConstructor_startsAtCurrentTokenOnSuccess nested
          input value next result
      · split at result
        · exact proxyExpression_startsAtCurrentTokenOnSuccess
            input value next result
        · split at result
          · exact parenthesized_startsAtCurrentTokenOnSuccess nested
              input value next result
          · split at result
            · exact arrayLiteral_startsAtCurrentTokenOnSuccess nested
                input value next result
            · split at result
              · exact lambdaExpression_startsAtCurrentTokenOnSuccess block
                  input value next result
              · simp [rejectAt] at result

/-- Finishing atom recovery retains one source-valid error expression. -/
theorem finishRecoveredAtom_validFor
    (statementValid : SourceFile → Statement → Prop)
    (first last : SourceSpan) (state : State)
    (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredAtom first last state).ValidFor state
      (Expr.ValidFor statementValid) := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredAtom Reply.ValidFor
  exact ⟨.error spanValid, stateValid.emit_validFor _ spanValid, rfl⟩

/-- Fuel-bounded atom recovery preserves source provenance. -/
theorem recoverAtomAux_validFor
    (statementValid : SourceFile → Statement → Prop)
    (first : SourceSpan) : ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverAtomAux first last fuel state).ValidFor state
        (Expr.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverAtomAux
      split
      · exact finishRecoveredAtom_validFor statementValid first last state
          stateValid firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredAtom_validFor statementValid first last state
              stateValid firstValid lastValid ordered
        | some pair =>
            rcases pair with ⟨token, next⟩
            have shape := advance?_state_shape advanced
            have nextValid := stateValid.advance?_validFor advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                currentFound lastBefore
            exact (inductionHypothesis token.span next state.cursor token
              nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl
              (by simp [shape.2])).of_file_eq (by simp [shape.2])

/-- Complete atom recovery preserves source provenance. -/
theorem recoverAtom_validFor
    (statementValid : SourceFile → Statement → Prop) :
    Parser.ValidFor recoverAtom (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold recoverAtom
  cases advanced : input.advance? with
  | none =>
      unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      have shape := advance?_state_shape advanced
      have nextValid := inputValid.advance?_validFor advanced
      have tokenValid := inputValid.peek?_span_validFor shape.1
      have currentFound := State.getElem?_eq_some_of_peek?_eq_some shape.1
      exact (recoverAtomAux_validFor statementValid token.span
        (next.remainingCount + 1) token.span next input.cursor token nextValid
        (by simpa [shape.2] using tokenValid)
        (by simpa [shape.2] using tokenValid) tokenValid.2.1
        (by simpa [shape.2] using currentFound) rfl
        (by simp [shape.2])).of_file_eq (by simp [shape.2])

/-- Fuel-bounded atom recovery preserves every ordinary token window. -/
theorem recoverAtomAux_preservesTokenWindow (first last : SourceSpan)
    (fuel : Nat) :
    Parser.PreservesTokenWindow (recoverAtomAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverAtomAux
      split
      · unfold finishRecoveredAtom Reply.PreservesTokenWindow State.emit
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecoveredAtom Reply.PreservesTokenWindow State.emit
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            exact (inductionHypothesis token.span afterToken).trans (by
              simp [(advance?_state_shape advanced).2])

/-- Successful fuel-bounded recovery records cursor and first-token shape. -/
theorem recoverAtomAux_ok_state_shape (first last : SourceSpan) :
    ∀ fuel, ∀ {input final : State} {value : Expr},
      recoverAtomAux first last fuel input = .ok value final →
      input.cursor ≤ final.cursor ∧
        first.startByte = value.span.startByte := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverAtomAux]
  | succ fuel inductionHypothesis =>
      intro input final value parsed
      unfold recoverAtomAux at parsed
      split at parsed
      · unfold finishRecoveredAtom at parsed
        cases parsed
        exact ⟨Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredAtom at parsed
            cases parsed
            exact ⟨Nat.le_refl _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at parsed
            have recursive := inductionHypothesis token.span parsed
            exact ⟨Nat.le_trans (by
              simp [(advance?_state_shape advanced).2]) recursive.1,
              recursive.2⟩

/-- Complete atom recovery preserves the ordinary token window. -/
theorem recoverAtom_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverAtom := by
  intro input
  unfold recoverAtom
  cases advanced : input.advance? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      exact (recoverAtomAux_preservesTokenWindow token.span token.span
        (afterToken.remainingCount + 1) afterToken).trans (by
          simp [(advance?_state_shape advanced).2])

/-- Complete recovery is cursor-monotone and begins at its consumed token. -/
theorem recoverAtom_ok_state_shape {input final : State} {value : Expr}
    (parsed : recoverAtom input = .ok value final) :
    input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = value.span.startByte := by
  unfold recoverAtom at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at parsed
      have recovered := recoverAtomAux_ok_state_shape token.span token.span
        (afterToken.remainingCount + 1) parsed
      exact ⟨Nat.le_trans (by simp [(advance?_state_shape advanced).2])
        recovered.1, token, (advance?_state_shape advanced).1, recovered.2⟩

/-- Successful recovery strictly consumes its first malformed token. -/
theorem recoverAtom_cursor_lt_onSuccess {input final : State} {value : Expr}
    (parsed : recoverAtom input = .ok value final) :
    input.cursor < final.cursor := by
  unfold recoverAtom at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at parsed
      exact Nat.lt_of_lt_of_le (by simp [(advance?_state_shape advanced).2])
        (recoverAtomAux_ok_state_shape token.span token.span
          (afterToken.remainingCount + 1) parsed).1

/-- Public atom parsing preserves token windows through dispatch and recovery. -/
theorem expressionAtom_preservesTokenWindow
    (nested : Parser Expr) (block : Parser Block)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (blockWindow : Parser.PreservesTokenWindow block) :
    Parser.PreservesTokenWindow (expressionAtom nested block) := by
  intro input
  unfold expressionAtom
  have coreShape := expressionAtomCore_preservesTokenWindow nested block
    nestedWindow blockWindow input
  cases coreResult : expressionAtomCore nested block input with
  | ok value next => rw [coreResult] at coreShape; exact coreShape
  | invariant error => trivial
  | reject failure failedState =>
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using coreShape
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := by simpa [rewound] using failedShape
      change Reply.PreservesTokenWindow
        (if isAtomBoundary rewound then Reply.reject failure rewound
        else recoverAtom (rewound.emit failure.toDiagnostic)) input
      split
      · exact rewoundShape
      · exact (recoverAtom_preservesTokenWindow
          (rewound.emit failure.toDiagnostic)).trans (by
            simpa [State.emit] using rewoundShape)

theorem expressionAtom_preservesTokensOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (blockWindow : Parser.PreservesTokenWindow block) :
    Parser.PreservesTokensOnSuccess (expressionAtom nested block) :=
  (expressionAtom_preservesTokenWindow nested block nestedWindow
    blockWindow).preservesTokensOnSuccess

/-- Public atom parsing preserves recursive source provenance through recovery. -/
theorem expressionAtom_validFor
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span))
    (blockWindow : Parser.PreservesTokenWindow block) :
    (expressionAtom nested block).ValidFor (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold expressionAtom
  have coreValid := expressionAtomCore_validFor nested block statementValid
    nestedValid nestedWindow.preservesTokensOnSuccess blockValid blockStarts
      input inputValid
  cases coreResult : expressionAtomCore nested block input with
  | ok value next => rw [coreResult] at coreValid; exact coreValid
  | invariant error => trivial
  | reject failure failedState =>
      rw [coreResult] at coreValid
      have coreShape := expressionAtomCore_preservesTokenWindow nested block
        nestedWindow blockWindow input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := coreValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, coreShape.2] using inputValid.cursor_le_endIndex
        endIndex_le_size := coreValid.2.1.endIndex_le_size
        endByte_le_source := coreValid.2.1.endByte_le_source
        endByte_boundary := coreValid.2.1.endByte_boundary
        diagnosticsRev := coreValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using coreValid.2.2
      have failureValid : failure.span.ValidFor rewound.file := by
        simpa [rewound, coreValid.2.2] using coreValid.1
      change (if isAtomBoundary rewound then Reply.reject failure rewound
        else recoverAtom (rewound.emit failure.toDiagnostic)).ValidFor input
          (Expr.ValidFor statementValid)
      split
      · exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
      · have emittedValid := rewoundValid.emit_validFor failure.toDiagnostic
          (failure.toDiagnostic_span_validFor failureValid)
        exact (recoverAtom_validFor statementValid
          (rewound.emit failure.toDiagnostic) emittedValid).of_file_eq
            (by simpa [State.emit] using rewoundFile)

/-- Public atom successes never rewind through either parsing path. -/
theorem expressionAtom_cursorMonotoneOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (blockCursor : Parser.CursorMonotoneOnSuccess block) :
    Parser.CursorMonotoneOnSuccess (expressionAtom nested block) := by
  intro input value next result
  unfold expressionAtom at result
  cases coreResult : expressionAtomCore nested block input with
  | invariant error => simp [coreResult] at result
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      have monotone := expressionAtomCore_cursorMonotoneOnSuccess nested block
        nestedCursor blockCursor input coreValue afterCore coreResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isAtomBoundary rewound then Reply.reject failure rewound
        else recoverAtom (rewound.emit failure.toDiagnostic)) =
          .ok value next at result
      split at result
      · contradiction
      · exact (by simpa [rewound, State.emit] using
          (recoverAtom_ok_state_shape result).1)

/-- Every successful public atom parse consumes at least one token. -/
theorem expressionAtom_cursor_lt_onSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    {input next : State} {value : Expr}
    (parsed : expressionAtom nested block input = .ok value next) :
    input.cursor < next.cursor := by
  unfold expressionAtom at parsed
  cases coreResult : expressionAtomCore nested block input with
  | invariant error => simp [coreResult] at parsed
  | ok coreValue afterCore =>
      simp only [coreResult] at parsed
      have strict := expressionAtomCore_cursor_lt_onSuccess nested block
        nestedMonotone blockCursor coreResult
      cases parsed
      exact strict
  | reject failure failedState =>
      simp only [coreResult] at parsed
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isAtomBoundary rewound then Reply.reject failure rewound
        else recoverAtom (rewound.emit failure.toDiagnostic)) =
          .ok value next at parsed
      split at parsed
      · contradiction
      · simpa [rewound, State.emit] using
          recoverAtom_cursor_lt_onSuccess parsed

/-- Public atom success starts at its caller's current token. -/
theorem expressionAtom_startsAtCurrentTokenOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (blockWindow : Parser.PreservesTokenWindow block) :
    Parser.StartsAtCurrentTokenOnSuccess
      (expressionAtom nested block) (·.span) := by
  intro input value next result
  unfold expressionAtom at result
  cases coreResult : expressionAtomCore nested block input with
  | invariant error => simp [coreResult] at result
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      have starts := expressionAtomCore_startsAtCurrentTokenOnSuccess
        nested block input coreValue afterCore coreResult
      cases result
      exact starts
  | reject failure failedState =>
      simp only [coreResult] at result
      have coreShape := expressionAtomCore_preservesTokenWindow nested block
        nestedWindow blockWindow input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isAtomBoundary rewound then Reply.reject failure rewound
        else recoverAtom (rewound.emit failure.toDiagnostic)) =
          .ok value next at result
      split at result
      · contradiction
      · rcases (recoverAtom_ok_state_shape result).2 with
          ⟨token, found, starts⟩
        refine ⟨token, ?_, starts⟩
        unfold State.peek? at found ⊢
        simpa [rewound, State.emit, coreShape.1, coreShape.2] using found

/-- The postfix loop preserves every ordinary token window. -/
theorem postfixTail_preservesTokenWindow
    (nested : Parser Expr) (block : Parser Block)
    (nestedWindow : Parser.PreservesTokenWindow nested) :
    ∀ fuel base,
      Parser.PreservesTokenWindow (postfixTail nested block fuel base) := by
  intro fuel
  induction fuel with
  | zero => intro base input; trivial
  | succ fuel inductionHypothesis =>
      intro base input
      unfold postfixTail
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true]
        have openingShape :=
          symbol_preservesTokenWindow .leftBracket .expression input
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [openingResult] at openingShape
            exact openingShape
        | ok opening afterOpening =>
            rw [openingResult] at openingShape
            simp only
            have indexShape := nestedWindow afterOpening
            cases indexResult : nested afterOpening with
            | invariant error => trivial
            | reject failure rejected =>
                rw [indexResult] at indexShape
                exact indexShape.trans openingShape
            | ok index next =>
                rw [indexResult] at indexShape
                simp only
                have closingShape :=
                  symbol_preservesTokenWindow .rightBracket .expression next
                cases closingResult : symbol .rightBracket .expression next with
                | invariant error => trivial
                | reject failure rejected =>
                    rw [closingResult] at closingShape
                    exact (closingShape.trans indexShape).trans openingShape
                | ok closing afterClosing =>
                    rw [closingResult] at closingShape
                    exact (((inductionHypothesis {
                        span := SourceSpan.cover base.span closing.span
                        value := .index base
                          (SourceSpan.cover opening.span closing.span) index
                      } afterClosing).trans closingShape).trans
                        indexShape).trans openingShape
      · simp only [indexed, Bool.false_eq_true, if_false]
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true]
          have argumentsShape :
              ((delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression) input).PreservesTokenWindow input := by
            simpa only [delimitedNoTrailing] using
              (delimitedWithPolicy_preservesTokenWindow .leftParen .rightParen
                true false nested .expression .expression nestedWindow input)
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => trivial
          | reject failure rejected =>
              rw [argumentsResult] at argumentsShape
              exact argumentsShape
          | ok arguments next =>
              rw [argumentsResult] at argumentsShape
              exact (inductionHypothesis {
                span := SourceSpan.cover base.span arguments.span
                value := .call base arguments
              } next).trans argumentsShape
        · simp only [called, Bool.false_eq_true, if_false]
          by_cases field : isSymbol input .dot
          · simp only [field, if_true]
            have dotShape := symbol_preservesTokenWindow .dot .expression input
            cases dotResult : symbol .dot .expression input with
            | invariant error => trivial
            | reject failure rejected =>
                rw [dotResult] at dotShape
                exact dotShape
            | ok dot afterDot =>
                rw [dotResult] at dotShape
                simp only
                have nameShape := identifier_preservesTokenWindow
                  .expression afterDot
                cases nameResult : identifier .expression afterDot with
                | invariant error => trivial
                | reject failure rejected =>
                    rw [nameResult] at nameShape
                    exact nameShape.trans dotShape
                | ok name next =>
                    rw [nameResult] at nameShape
                    exact ((inductionHypothesis {
                      span := SourceSpan.cover base.span name.span
                      value := .field base dot.span name
                    } next).trans nameShape).trans dotShape
          · simp only [field]
            exact ⟨rfl, rfl⟩

theorem postfixTail_preservesTokensOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (fuel : Nat) (base : Expr) :
    Parser.PreservesTokensOnSuccess (postfixTail nested block fuel base) :=
  (postfixTail_preservesTokenWindow nested block nestedWindow fuel
    base).preservesTokensOnSuccess

/-- Successful postfix parsing never rewinds its caller. -/
theorem postfixTail_cursorMonotoneOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested) :
    ∀ fuel base,
      Parser.CursorMonotoneOnSuccess (postfixTail nested block fuel base) := by
  intro fuel
  induction fuel with
  | zero =>
      intro base input expression final parsed
      unfold postfixTail at parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro base input expression final parsed
      unfold postfixTail at parsed
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at parsed
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at parsed
        | reject failure rejected => simp [openingResult] at parsed
        | ok opening afterOpening =>
            simp only [openingResult] at parsed
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at parsed
            | reject failure rejected => simp [indexResult] at parsed
            | ok index next =>
                simp only [indexResult] at parsed
                cases closingResult : symbol .rightBracket .expression next with
                | invariant error => simp [closingResult] at parsed
                | reject failure rejected => simp [closingResult] at parsed
                | ok closing afterClosing =>
                    simp only [closingResult] at parsed
                    exact Nat.le_trans
                      (symbol_cursorMonotoneOnSuccess .leftBracket .expression
                        input opening afterOpening openingResult)
                      (Nat.le_trans
                        (nestedCursor afterOpening index next indexResult)
                        (Nat.le_trans
                          (symbol_cursorMonotoneOnSuccess .rightBracket
                            .expression next closing afterClosing closingResult)
                          (inductionHypothesis _ afterClosing expression final
                            parsed)))
      · simp only [indexed, Bool.false_eq_true, if_false] at parsed
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at parsed
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at parsed
          | reject failure rejected => simp [argumentsResult] at parsed
          | ok arguments next =>
              simp only [argumentsResult] at parsed
              exact Nat.le_trans
                (delimitedNoTrailing_cursorMonotoneOnSuccess .leftParen
                  .rightParen true nested .expression .expression input
                    arguments next argumentsResult)
                (inductionHypothesis _ next expression final parsed)
        · simp only [called, Bool.false_eq_true, if_false] at parsed
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at parsed
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at parsed
            | reject failure rejected => simp [dotResult] at parsed
            | ok dot afterDot =>
                simp only [dotResult] at parsed
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at parsed
                | reject failure rejected => simp [nameResult] at parsed
                | ok name next =>
                    simp only [nameResult] at parsed
                    exact Nat.le_trans
                      (symbol_cursorMonotoneOnSuccess .dot .expression input dot
                        afterDot dotResult)
                      (Nat.le_trans
                        (identifier_cursorMonotoneOnSuccess .expression afterDot
                          name next nameResult)
                        (inductionHypothesis _ next expression final parsed))
          · simp only [field] at parsed
            cases parsed
            exact Nat.le_refl _

/-- Every successful postfix tail retains its original base's left edge. -/
theorem postfixTail_preservesBaseStartOnSuccess
    (nested : Parser Expr) (block : Parser Block) :
    ∀ fuel base input expression final,
      postfixTail nested block fuel base input = .ok expression final →
      expression.span.startByte = base.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro base input expression final parsed
      unfold postfixTail at parsed
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at parsed
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at parsed
        | reject failure rejected => simp [openingResult] at parsed
        | ok opening afterOpening =>
            simp only [openingResult] at parsed
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at parsed
            | reject failure rejected => simp [indexResult] at parsed
            | ok index next =>
                simp only [indexResult] at parsed
                cases closingResult : symbol .rightBracket .expression next with
                | invariant error => simp [closingResult] at parsed
                | reject failure rejected => simp [closingResult] at parsed
                | ok closing afterClosing =>
                    simp only [closingResult] at parsed
                    calc
                      expression.span.startByte =
                          (SourceSpan.cover base.span closing.span).startByte :=
                        inductionHypothesis {
                          span := SourceSpan.cover base.span closing.span
                          value := .index base
                            (SourceSpan.cover opening.span closing.span) index
                        } afterClosing expression final parsed
                      _ = base.span.startByte := rfl
      · simp only [indexed, Bool.false_eq_true, if_false] at parsed
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at parsed
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at parsed
          | reject failure rejected => simp [argumentsResult] at parsed
          | ok arguments next =>
              simp only [argumentsResult] at parsed
              calc
                expression.span.startByte =
                    (SourceSpan.cover base.span arguments.span).startByte :=
                  inductionHypothesis {
                    span := SourceSpan.cover base.span arguments.span
                    value := .call base arguments
                  } next expression final parsed
                _ = base.span.startByte := rfl
        · simp only [called, Bool.false_eq_true, if_false] at parsed
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at parsed
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at parsed
            | reject failure rejected => simp [dotResult] at parsed
            | ok dot afterDot =>
                simp only [dotResult] at parsed
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at parsed
                | reject failure rejected => simp [nameResult] at parsed
                | ok name next =>
                    simp only [nameResult] at parsed
                    calc
                      expression.span.startByte =
                          (SourceSpan.cover base.span name.span).startByte :=
                        inductionHypothesis {
                          span := SourceSpan.cover base.span name.span
                          value := .field base dot.span name
                        } next expression final parsed
                      _ = base.span.startByte := rfl
          · simp only [field] at parsed
            cases parsed
            rfl

/-- Postfix parsing preserves token windows when its atom and leaves do. -/
theorem expressionPostfix_preservesTokenWindow
    (nested : Parser Expr) (block : Parser Block)
    (atomWindow : Parser.PreservesTokenWindow (expressionAtom nested block))
    (nestedWindow : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (expressionPostfix nested block) := by
  intro input
  unfold expressionPostfix
  have atomShape := atomWindow input
  cases atomResult : expressionAtom nested block input with
  | invariant error => trivial
  | reject failure rejected => rw [atomResult] at atomShape; exact atomShape
  | ok base next =>
      rw [atomResult] at atomShape
      exact (postfixTail_preservesTokenWindow nested block nestedWindow
        (next.remainingCount + 1) base next).trans atomShape

theorem expressionPostfix_preservesTokensOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (atomWindow : Parser.PreservesTokenWindow (expressionAtom nested block))
    (nestedWindow : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokensOnSuccess (expressionPostfix nested block) :=
  (expressionPostfix_preservesTokenWindow nested block atomWindow
    nestedWindow).preservesTokensOnSuccess

/-- Postfix parsing never rewinds when its atom and recursive leaves do not. -/
theorem expressionPostfix_cursorMonotoneOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (atomCursor : Parser.CursorMonotoneOnSuccess (expressionAtom nested block))
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (expressionPostfix nested block) := by
  intro input expression final parsed
  unfold expressionPostfix at parsed
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at parsed
  | reject failure rejected => simp [atomResult] at parsed
  | ok base next =>
      simp only [atomResult] at parsed
      exact Nat.le_trans (atomCursor input base next atomResult)
        (postfixTail_cursorMonotoneOnSuccess nested block nestedCursor
          (next.remainingCount + 1) base next expression final parsed)

/-- Concrete postfix success is strict because its atom is strict. -/
theorem expressionPostfix_cursor_lt_onSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    {input final : State} {expression : Expr}
    (parsed : expressionPostfix nested block input = .ok expression final) :
    input.cursor < final.cursor := by
  unfold expressionPostfix at parsed
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at parsed
  | reject failure rejected => simp [atomResult] at parsed
  | ok base next =>
      simp only [atomResult] at parsed
      exact Nat.lt_of_lt_of_le
        (expressionAtom_cursor_lt_onSuccess nested block nestedCursor
          blockCursor atomResult)
        (postfixTail_cursorMonotoneOnSuccess nested block nestedCursor
          (next.remainingCount + 1) base next expression final parsed)

/-- A postfix expression starts at the same token as its atom. -/
theorem expressionPostfix_startsAtCurrentTokenOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (atomStarts : Parser.StartsAtCurrentTokenOnSuccess
      (expressionAtom nested block) (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (expressionPostfix nested block) (·.span) := by
  intro input expression final parsed
  unfold expressionPostfix at parsed
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at parsed
  | reject failure rejected => simp [atomResult] at parsed
  | ok base next =>
      simp only [atomResult] at parsed
      rcases atomStarts input base next atomResult with
        ⟨token, found, starts⟩
      have retained := postfixTail_preservesBaseStartOnSuccess nested block
        (next.remainingCount + 1) base next expression final parsed
      exact ⟨token, found, starts.trans retained.symm⟩

/-- The postfix loop retains its base and every suffix source range. -/
theorem postfixTail_validFor
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedTokens : Parser.PreservesTokensOnSuccess nested)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested) :
    ∀ fuel base input,
      input.ValidFor →
      Expr.ValidFor statementValid input.file base →
      (∀ token, input.peek? = some token →
        base.span.startByte ≤ token.span.startByte) →
      (postfixTail nested block fuel base input).ValidFor input
        (Expr.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro base input inputValid baseValid baseBefore
      unfold postfixTail
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true]
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => trivial
        | reject failure rejected =>
            have reply := symbol_validFor .leftBracket .expression input inputValid
            rw [openingResult] at reply
            exact reply
        | ok opening afterOpening =>
            have openingReply := symbol_validFor .leftBracket .expression input
              inputValid
            rw [openingResult] at openingReply
            simp only
            cases indexResult : nested afterOpening with
            | invariant error => trivial
            | reject failure rejected =>
                have reply := nestedValid afterOpening openingReply.2.1
                rw [indexResult] at reply
                exact reply.of_file_eq openingReply.2.2
            | ok index next =>
                have indexReply := nestedValid afterOpening openingReply.2.1
                rw [indexResult] at indexReply
                simp only
                cases closingResult : symbol .rightBracket .expression next with
                | invariant error => trivial
                | reject failure rejected =>
                    have reply := symbol_validFor .rightBracket .expression next
                      indexReply.2.1
                    rw [closingResult] at reply
                    exact reply.of_file_eq
                      (indexReply.2.2.trans openingReply.2.2)
                | ok closing afterClosing =>
                    have closingReply := symbol_validFor .rightBracket
                      .expression next indexReply.2.1
                    rw [closingResult] at closingReply
                    have openingShape := symbol_ok_state_shape .leftBracket
                      .expression openingResult
                    have closingShape := symbol_ok_state_shape .rightBracket
                      .expression closingResult
                    have openingAt :=
                      State.getElem?_eq_some_of_peek?_eq_some openingShape.1
                    have closingAtNext :=
                      State.getElem?_eq_some_of_peek?_eq_some closingShape.1
                    have openingTokens := symbol_preservesTokensOnSuccess
                      .leftBracket .expression input opening afterOpening
                        openingResult
                    have indexTokens := nestedTokens afterOpening index next
                      indexResult
                    have closingAt : input.tokens[next.cursor]? = some closing := by
                      simpa [indexTokens, openingTokens] using closingAtNext
                    have separated :=
                      inputValid.token_end_le_token_start_of_getElem?_lt
                        openingAt closingAt
                        (Nat.lt_of_lt_of_le
                          (acceptToken_cursor_lt_onSuccess
                            (.symbol .leftBracket) .expression
                            (· == .symbol .leftBracket) openingResult)
                          (nestedCursor afterOpening index next indexResult))
                    have openingSpan : opening.span.ValidFor input.file := by
                      simpa only [Located.ValidFor] using openingReply.1
                    have closingSpan : closing.span.ValidFor input.file := by
                      simpa only [Located.ValidFor, indexReply.2.2,
                        openingReply.2.2] using closingReply.1
                    have indexValid : Expr.ValidFor statementValid input.file
                        index := by
                      simpa [openingReply.2.2] using indexReply.1
                    have bracketsValid := SourceSpan.cover_validFor openingSpan
                      closingSpan (Nat.le_trans openingSpan.2.1
                        (Nat.le_trans separated closingSpan.2.1))
                    have baseToClosing : base.span.startByte ≤
                        closing.span.endByte := Nat.le_trans
                      (baseBefore opening openingShape.1)
                      (Nat.le_trans openingSpan.2.1
                        (Nat.le_trans separated closingSpan.2.1))
                    let combined : Expr := {
                      span := SourceSpan.cover base.span closing.span
                      value := .index base
                        (SourceSpan.cover opening.span closing.span) index
                    }
                    have combinedValid : Expr.ValidFor statementValid input.file
                        combined := Expr.ValidFor.index
                      (SourceSpan.cover_validFor baseValid.span_valid closingSpan
                        baseToClosing) baseValid bracketsValid indexValid
                    have resultFileEq : afterClosing.file = input.file :=
                      closingReply.2.2.trans
                        (indexReply.2.2.trans openingReply.2.2)
                    have closingTokens := symbol_preservesTokensOnSuccess
                      .rightBracket .expression next closing afterClosing
                        closingResult
                    have combinedBefore : ∀ future,
                        afterClosing.peek? = some future →
                        combined.span.startByte ≤ future.span.startByte := by
                      intro future futureFound
                      have futureAtAfter :=
                        State.getElem?_eq_some_of_peek?_eq_some futureFound
                      have futureAt : input.tokens[afterClosing.cursor]? =
                          some future := by
                        simpa [closingTokens, indexTokens, openingTokens] using
                          futureAtAfter
                      have beforeFuture :=
                        inputValid.token_end_le_token_start_of_getElem?_lt
                          openingAt futureAt (Nat.lt_of_lt_of_le
                            (acceptToken_cursor_lt_onSuccess
                              (.symbol .leftBracket) .expression
                              (· == .symbol .leftBracket) openingResult)
                            (Nat.le_trans
                              (nestedCursor afterOpening index next indexResult)
                              (symbol_cursorMonotoneOnSuccess .rightBracket
                                .expression next closing afterClosing
                                  closingResult)))
                      exact Nat.le_trans (baseBefore opening openingShape.1)
                        (Nat.le_trans openingSpan.2.1 beforeFuture)
                    exact (inductionHypothesis combined afterClosing
                      closingReply.2.1 (by simpa [resultFileEq] using
                        combinedValid) combinedBefore).of_file_eq resultFileEq
      · simp only [indexed, Bool.false_eq_true, if_false]
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true]
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => trivial
          | reject failure rejected =>
              have reply := delimitedNoTrailing_validFor
                (Expr.ValidFor statementValid) .leftParen .rightParen true
                  nested .expression .expression nestedValid nestedTokens input
                    inputValid
              rw [argumentsResult] at reply
              exact reply
          | ok arguments next =>
              have argumentsReply := delimitedNoTrailing_validFor
                (Expr.ValidFor statementValid) .leftParen .rightParen true
                  nested .expression .expression nestedValid nestedTokens input
                    inputValid
              rw [argumentsResult] at argumentsReply
              rcases delimitedNoTrailing_startsAtCurrentTokenOnSuccess
                  .leftParen .rightParen true nested .expression .expression
                    input arguments next argumentsResult with
                ⟨opening, openingFound, argumentsStart⟩
              have argumentsValid := argumentsReply.1
              have ordered : base.span.startByte ≤ arguments.span.endByte :=
                Nat.le_trans (baseBefore opening openingFound)
                  (by rw [argumentsStart]; exact argumentsValid.1.2.1)
              let combined : Expr := {
                span := SourceSpan.cover base.span arguments.span
                value := .call base arguments
              }
              have combinedValid : Expr.ValidFor statementValid input.file
                  combined := Expr.ValidFor.call
                (SourceSpan.cover_validFor baseValid.span_valid argumentsValid.1
                  ordered) baseValid argumentsValid.1 argumentsValid.2
              have argumentsTokens :=
                delimitedNoTrailing_preservesTokensOnSuccess .leftParen
                  .rightParen true nested .expression .expression nestedTokens
                    input arguments next argumentsResult
              have combinedBefore : ∀ future, next.peek? = some future →
                  combined.span.startByte ≤ future.span.startByte := by
                intro future futureFound
                have openingAt :=
                  State.getElem?_eq_some_of_peek?_eq_some openingFound
                have futureAtNext :=
                  State.getElem?_eq_some_of_peek?_eq_some futureFound
                have futureAt : input.tokens[next.cursor]? = some future := by
                  simpa [argumentsTokens] using futureAtNext
                have beforeFuture :=
                  inputValid.token_end_le_token_start_of_getElem?_lt openingAt
                    futureAt (by
                      apply delimitedWithPolicy_cursor_lt_onSuccess .leftParen
                        .rightParen true false nested .expression .expression
                      simpa only [delimitedNoTrailing] using argumentsResult)
                exact Nat.le_trans (baseBefore opening openingFound)
                  (Nat.le_trans (inputValid.peek?_span_validFor openingFound).2.1
                    beforeFuture)
              exact (inductionHypothesis combined next argumentsReply.2.1
                (by simpa [argumentsReply.2.2] using combinedValid)
                  combinedBefore).of_file_eq argumentsReply.2.2
        · simp only [called, Bool.false_eq_true, if_false]
          by_cases field : isSymbol input .dot
          · simp only [field, if_true]
            cases dotResult : symbol .dot .expression input with
            | invariant error => trivial
            | reject failure rejected =>
                have reply := symbol_validFor .dot .expression input inputValid
                rw [dotResult] at reply
                exact reply
            | ok dot afterDot =>
                have dotReply := symbol_validFor .dot .expression input inputValid
                rw [dotResult] at dotReply
                simp only
                cases nameResult : identifier .expression afterDot with
                | invariant error => trivial
                | reject failure rejected =>
                    have reply := identifier_validFor .expression afterDot
                      dotReply.2.1
                    rw [nameResult] at reply
                    exact reply.of_file_eq dotReply.2.2
                | ok name next =>
                    have nameReply := identifier_validFor .expression afterDot
                      dotReply.2.1
                    rw [nameResult] at nameReply
                    rcases identifier_ok_state_shape .expression nameResult with
                      ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
                    have dotShape := symbol_ok_state_shape .dot .expression
                      dotResult
                    have dotAt := State.getElem?_eq_some_of_peek?_eq_some
                      dotShape.1
                    have nameAtAfter :=
                      State.getElem?_eq_some_of_peek?_eq_some nameFound
                    have nameAt : input.tokens[afterDot.cursor]? =
                        some nameToken := by
                      simpa [dotShape.2] using nameAtAfter
                    have separated :=
                      inputValid.token_end_le_token_start_of_getElem?_lt dotAt
                        nameAt (by simp [dotShape.2])
                    have dotSpan : dot.span.ValidFor input.file := by
                      simpa only [Located.ValidFor] using dotReply.1
                    have nameValid : name.span.ValidFor input.file := by
                      simpa only [Located.ValidFor, dotReply.2.2] using
                        nameReply.1
                    have ordered : base.span.startByte ≤ name.span.endByte :=
                      Nat.le_trans (baseBefore dot dotShape.1)
                        (Nat.le_trans dotSpan.2.1 (Nat.le_trans separated
                          (by simpa [nameSpan] using nameValid.2.1)))
                    let combined : Expr := {
                      span := SourceSpan.cover base.span name.span
                      value := .field base dot.span name
                    }
                    have combinedValid : Expr.ValidFor statementValid input.file
                        combined := Expr.ValidFor.field
                      (SourceSpan.cover_validFor baseValid.span_valid nameValid
                        ordered) baseValid dotSpan nameValid
                    have resultFileEq := nameReply.2.2.trans dotReply.2.2
                    have combinedBefore : ∀ future, next.peek? = some future →
                        combined.span.startByte ≤ future.span.startByte := by
                      intro future futureFound
                      have futureAtNext :=
                        State.getElem?_eq_some_of_peek?_eq_some futureFound
                      have futureAt : input.tokens[next.cursor]? = some future := by
                        simpa [nameTokens, dotShape.2] using futureAtNext
                      have dotProgress : input.cursor < afterDot.cursor := by
                        rw [dotShape.2]
                        simp
                      have nameProgress : afterDot.cursor < next.cursor := by
                        rw [nameCursor]
                        simp
                      have beforeFuture :=
                        inputValid.token_end_le_token_start_of_getElem?_lt dotAt
                          futureAt (Nat.lt_trans dotProgress nameProgress)
                      exact Nat.le_trans (baseBefore dot dotShape.1)
                        (Nat.le_trans dotSpan.2.1 beforeFuture)
                    exact (inductionHypothesis combined next nameReply.2.1
                      (by simpa [resultFileEq] using combinedValid)
                        combinedBefore).of_file_eq resultFileEq
          · simp only [field]
            exact ⟨baseValid, inputValid, rfl⟩

/-- A complete postfix parser retains its atom and every suffix source range. -/
theorem expressionPostfix_validFor
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (atomValid : (expressionAtom nested block).ValidFor
      (Expr.ValidFor statementValid))
    (atomTokens : Parser.PreservesTokensOnSuccess
      (expressionAtom nested block))
    (atomCursorLt : ∀ {input next : State} {value : Expr},
      expressionAtom nested block input = .ok value next →
        input.cursor < next.cursor)
    (atomStarts : Parser.StartsAtCurrentTokenOnSuccess
      (expressionAtom nested block) (·.span))
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedTokens : Parser.PreservesTokensOnSuccess nested)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested) :
    (expressionPostfix nested block).ValidFor
      (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold expressionPostfix
  cases atomResult : expressionAtom nested block input with
  | invariant error => trivial
  | reject failure rejected =>
      have reply := atomValid input inputValid
      rw [atomResult] at reply
      exact reply
  | ok base next =>
      have atomReply := atomValid input inputValid
      rw [atomResult] at atomReply
      rcases atomStarts input base next atomResult with
        ⟨first, firstFound, baseStart⟩
      have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
      have carrier := atomTokens input base next atomResult
      have baseBefore : ∀ future, next.peek? = some future →
          base.span.startByte ≤ future.span.startByte := by
        intro future futureFound
        have futureAtNext :=
          State.getElem?_eq_some_of_peek?_eq_some futureFound
        have futureAt : input.tokens[next.cursor]? = some future := by
          simpa [carrier] using futureAtNext
        have separated := inputValid.token_end_le_token_start_of_getElem?_lt
          firstAt futureAt (atomCursorLt atomResult)
        calc
          base.span.startByte = first.span.startByte := baseStart.symm
          _ ≤ first.span.endByte :=
            (inputValid.peek?_span_validFor firstFound).2.1
          _ ≤ future.span.startByte := separated
      have recursive := postfixTail_validFor nested block statementValid
        nestedValid nestedTokens nestedCursor (next.remainingCount + 1) base
          next atomReply.2.1
            (by simpa [atomReply.2.2] using atomReply.1) baseBefore
      exact recursive.of_file_eq atomReply.2.2

end ExpressionAtomInternals
end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.Expression.AtomLeafTotalityProperties`
-/

/-! Totality for the non-recursive expression-atom leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem expressionName_ordinary : Parser.Ordinary expressionName := by
  intro input
  unfold expressionName
  split
  · exact booleanIdentifier_ordinary input
  · exact (identifier_ordinary .expression) input

theorem expressionName_invariantFreeOnValid :
    Parser.InvariantFreeOnValid expressionName :=
  expressionName_ordinary.invariantFreeOnValid

theorem expressionName_ne_invariant (input : State)
    (error : ParserInvariantError) :
    expressionName input ≠ .invariant error :=
  expressionName_ordinary.ne_invariant input error

theorem expressionName_elementTotalityContract :
    ElementTotalityContract expressionName := {
  validFor := expressionName_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := expressionName_preservesTokenWindow
  cursorLtOnSuccess := expressionName_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    expressionName_ne_invariant input error
}

theorem literalExpression_invariantFreeOnValid :
    Parser.InvariantFreeOnValid literalExpression := by
  unfold literalExpression
  apply Parser.bind_invariantFreeOnValid coreLiteral_validFor
    coreLiteral_ordinary.invariantFreeOnValid
  intro literal
  exact Parser.pure_invariantFreeOnValid ({
    span := literal.span
    value := .literal literal
  } : Expr)

theorem literalExpression_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    literalExpression input ≠ .invariant error :=
  literalExpression_invariantFreeOnValid.ne_invariant
    input inputValid error

theorem identifierExpression_invariantFreeOnValid :
    Parser.InvariantFreeOnValid identifierExpression := by
  unfold identifierExpression
  apply Parser.bind_invariantFreeOnValid expressionName_validFor
    expressionName_invariantFreeOnValid
  intro name
  exact Parser.pure_invariantFreeOnValid ({
    span := name.span
    value := .identifier name
  } : Expr)

theorem identifierExpression_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    identifierExpression input ≠ .invariant error :=
  identifierExpression_invariantFreeOnValid.ne_invariant
    input inputValid error

theorem proxyExpression_invariantFreeOnValid :
    Parser.InvariantFreeOnValid proxyExpression := by
  unfold proxyExpression
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .at .expression)
    (symbol_ordinary .at .expression).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid typeExpr_validFor
    typeExpr_invariantFreeOnValid
  intro type
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span type.span
    value := .proxy marker.span type
  } : Expr)

theorem proxyExpression_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    proxyExpression input ≠ .invariant error :=
  proxyExpression_invariantFreeOnValid.ne_invariant
    input inputValid error

theorem optionalLambdaReturnType_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalLambdaReturnType := by
  unfold optionalLambdaReturnType
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro state
  split
  · apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .arrow .typeExpr)
      (symbol_ordinary .arrow .typeExpr).invariantFreeOnValid
    intro marker
    apply Parser.bind_invariantFreeOnValid typeExpr_validFor
      typeExpr_invariantFreeOnValid
    intro type
    exact Parser.pure_invariantFreeOnValid (some type)
  · exact Parser.pure_invariantFreeOnValid none

theorem optionalLambdaReturnType_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    optionalLambdaReturnType input ≠ .invariant error :=
  optionalLambdaReturnType_invariantFreeOnValid.ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.ExpressionAtomInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.Expression.AtomDelimitedFuelTotalityProperties`
-/

/-! Fuel-aware totality for recursive delimited expression atoms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Optional leading-dot arguments inherit bounded delimited totality. -/
theorem optionalDotConstructorArguments_ordinary_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next,
      optionalDotConstructorArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      optionalDotConstructorArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .leftParen
  · rcases delimitedWithPolicy_ordinary_of_elementFuel .leftParen .rightParen
        true false nested .expression .expression nestedFuel contract input
        inputValid adequate with
      ⟨values, next, valuesResult⟩ | ⟨failure, rejected, valuesResult⟩
    · exact Or.inl ⟨some values, next, by
        simp only [optionalDotConstructorArguments, getState, bind, present,
          ↓reduceIte, delimitedNoTrailing, valuesResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalDotConstructorArguments, getState, bind, present,
          ↓reduceIte, delimitedNoTrailing, valuesResult]⟩
  · have absent : isSymbol input .leftParen = false := by
      cases found : isSymbol input .leftParen with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalDotConstructorArguments, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalDotConstructorArguments_ne_invariant_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    optionalDotConstructorArguments nested input ≠ .invariant error := by
  intro failed
  rcases optionalDotConstructorArguments_ordinary_of_elementFuel nested
      nestedFuel contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- A leading-dot constructor spends its outer fuel before recursive arguments. -/
theorem dotConstructor_ordinary_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next, dotConstructor nested input = .ok expression next) ∨
    (∃ failure next, dotConstructor nested input = .reject failure next) := by
  rcases (symbol_ordinary .dot .expression) input with
    ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
  · have dotValid := symbol_validFor .dot .expression input inputValid
    rw [dotResult] at dotValid
    have dotWindow := symbol_preservesTokenWindow .dot .expression input
    rw [dotResult] at dotWindow
    have afterDotAdequate : afterDot.remainingCount < nestedFuel :=
      remainingCount_lt_after_strict_progress dotValid.2.1 dotWindow.2
        (acceptToken_cursor_lt_onSuccess (.symbol .dot) .expression
          (· == .symbol .dot) dotResult) adequate
    rcases expressionName_ordinary afterDot with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameValid := expressionName_validFor afterDot dotValid.2.1
      rw [nameResult] at nameValid
      have nameWindow := expressionName_preservesTokenWindow afterDot
      rw [nameResult] at nameWindow
      have afterNameAdequate : afterName.remainingCount < nestedFuel :=
        remainingCount_lt_of_cursor_le nameWindow.2
          (Nat.le_of_lt (expressionName_cursor_lt_onSuccess nameResult))
          afterDotAdequate
      rcases optionalDotConstructorArguments_ordinary_of_elementFuel nested
          nestedFuel contract afterName nameValid.2.1 (by omega) with
        ⟨arguments, final, argumentsResult⟩ |
        ⟨failure, rejected, argumentsResult⟩
      · let endSpan := arguments.map (fun values => values.span) |>.getD name.span
        exact Or.inl ⟨{
            span := SourceSpan.cover dot.span endSpan
            value := .dotConstructor dot.span name arguments
          }, final, by
            simp only [dotConstructor, bind, dotResult, nameResult,
              argumentsResult, pure]
            rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [dotConstructor, bind, dotResult, nameResult,
            argumentsResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [dotConstructor, bind, dotResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [dotConstructor, bind, dotResult]⟩

theorem dotConstructor_ne_invariant_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    dotConstructor nested input ≠ .invariant error := by
  intro failed
  rcases dotConstructor_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Array literals inherit bounded no-trailing delimited totality. -/
theorem arrayLiteral_ordinary_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next, arrayLiteral nested input = .ok expression next) ∨
    (∃ failure next, arrayLiteral nested input = .reject failure next) := by
  rcases delimitedWithPolicy_ordinary_of_elementFuel .leftBracket .rightBracket
      true false nested .expression .expression nestedFuel contract input
      inputValid adequate with
    ⟨values, next, valuesResult⟩ | ⟨failure, rejected, valuesResult⟩
  · exact Or.inl ⟨{
        span := values.span
        value := .array values
      }, next, by
        unfold arrayLiteral
        simp only [delimitedNoTrailing, valuesResult, bind, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold arrayLiteral
      simp only [delimitedNoTrailing, valuesResult, bind]⟩

theorem arrayLiteral_ne_invariant_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    arrayLiteral nested input ≠ .invariant error := by
  intro failed
  rcases arrayLiteral_ordinary_of_elementFuel nested nestedFuel contract input
      inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.Expression.AtomRecoveryTotalityProperties`
-/

/-! Production-fuel adequacy for malformed expression-atom recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- More fuel than remaining tokens makes atom recovery terminate. -/
theorem recoverAtomAux_exists_ok_of_remainingCount_lt
    (first : SourceSpan) :
    ∀ fuel last state, state.remainingCount < fuel →
      ∃ value final,
        recoverAtomAux first last fuel state = .ok value final := by
  intro fuel last
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverAtomAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : state.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ value final,
              recoverAtomAux first token.span fuel next = .ok value final
            apply inductionHypothesis token.span next
            unfold State.advance? at advanced
            cases found : state.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at adequate ⊢
                omega

/-- The production recovery fuel is always adequate. -/
theorem recoverAtomAux_production_exists_ok
    (first last : SourceSpan) (state : State) :
    ∃ value final,
      recoverAtomAux first last (state.remainingCount + 1) state =
        .ok value final :=
  recoverAtomAux_exists_ok_of_remainingCount_lt first
    (state.remainingCount + 1) last state (by omega)

theorem recoverAtomAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverAtomAux first last fuel state ≠ .invariant error := by
  intro failed
  rcases recoverAtomAux_exists_ok_of_remainingCount_lt first fuel last state
      adequate with ⟨value, final, result⟩
  rw [result] at failed
  contradiction

/-- Complete atom recovery has an ordinary result on every input. -/
theorem recoverAtom_ordinary : Parser.Ordinary recoverAtom := by
  intro input
  unfold recoverAtom
  cases advanced : input.advance? with
  | none => exact Or.inr ⟨_, _, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      exact Or.inl (recoverAtomAux_production_exists_ok
        token.span token.span next)

theorem recoverAtom_invariantFreeOnValid :
    Parser.InvariantFreeOnValid recoverAtom :=
  recoverAtom_ordinary.invariantFreeOnValid

theorem recoverAtom_ne_invariant (input : State)
    (error : ParserInvariantError) :
    recoverAtom input ≠ .invariant error :=
  recoverAtom_ordinary.ne_invariant input error

end Solcore.Syntax.Parser.ExpressionAtomInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.Expression.AtomTupleTotalityProperties`
-/

/-! Fuel-aware totality for grouped expressions and expression tuples. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Closing a grouped expression or tuple is invariant-free on valid input. -/
theorem closeTuple_invariantFreeOnValid (opening : Token)
    (elementsRev : List Expr) :
    Parser.InvariantFreeOnValid (closeTuple opening elementsRev) := by
  unfold closeTuple
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .rightParen .expression)
    (symbol_ordinary .rightParen .expression).invariantFreeOnValid
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_invariantFreeOnValid _
  | cons only tail =>
      cases tail <;> exact Parser.pure_invariantFreeOnValid _

/--
The tuple-tail loop is ordinary when its own loop fuel and the nested parser's
fixed recursive-fuel bound are both adequate.
-/
theorem tupleTail_ordinary_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) :
    ∀ loopFuel elementsRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < nestedFuel + 1 →
      (∃ value next,
        tupleTail nested opening loopFuel elementsRev input = .ok value next) ∨
      (∃ failure next,
        tupleTail nested opening loopFuel elementsRev input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro elementsRev input inputValid loopAdequate nestedAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro elementsRev input inputValid loopAdequate nestedAdequate
      unfold tupleTail
      cases commaResult : symbol .comma .expression input with
      | invariant error =>
          exact False.elim
            (symbol_ne_invariant .comma .expression input error commaResult)
      | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
      | ok comma afterComma =>
          have commaValid := symbol_validFor .comma .expression input inputValid
          rw [commaResult] at commaValid
          have commaWindow := symbol_preservesTokenWindow .comma .expression input
          rw [commaResult] at commaWindow
          have commaProgress : input.cursor < afterComma.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .comma) .expression
              (· == .symbol .comma) commaResult
          have afterCommaNestedAdequate :
              afterComma.remainingCount < nestedFuel :=
            remainingCount_lt_after_strict_progress commaValid.2.1
              commaWindow.2 commaProgress nestedAdequate
          simp only
          split
          · exact closeTuple_invariantFreeOnValid opening elementsRev
              afterComma commaValid.2.1
          · cases nestedResult : nested afterComma with
            | invariant error =>
                exact False.elim (contract.ne_invariant afterComma
                  commaValid.2.1 afterCommaNestedAdequate error nestedResult)
            | reject failure rejected =>
                exact Or.inr ⟨failure, rejected, rfl⟩
            | ok value next =>
                have valueValid := contract.validFor afterComma commaValid.2.1
                rw [nestedResult] at valueValid
                have valueWindow := contract.preservesTokenWindow afterComma
                rw [nestedResult] at valueWindow
                have valueProgress := contract.cursorLtOnSuccess nestedResult
                dsimp only
                split
                · split
                  · have nextWindow : next.window = input.window :=
                      valueWindow.2.trans commaWindow.2
                    have nextLoopAdequate :
                        next.remainingCount < loopFuel :=
                      remainingCount_lt_after_strict_progress valueValid.2.1
                        nextWindow (Nat.lt_trans commaProgress valueProgress)
                        (by simpa [Nat.succ_eq_add_one] using loopAdequate)
                    have nextNestedAdequate :
                        next.remainingCount < nestedFuel + 1 := by
                      have preserved : next.remainingCount < nestedFuel :=
                        remainingCount_lt_of_cursor_le valueWindow.2
                          (Nat.le_of_lt valueProgress)
                          afterCommaNestedAdequate
                      omega
                    exact inductionHypothesis (value :: elementsRev) next
                      valueValid.2.1 nextLoopAdequate nextNestedAdequate
                  · exact closeTuple_invariantFreeOnValid opening
                      (value :: elementsRev) next valueValid.2.1
                · omega

theorem tupleTail_ne_invariant_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) (loopFuel : Nat) (elementsRev : List Expr)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    tupleTail nested opening loopFuel elementsRev input ≠ .invariant error := by
  intro failed
  rcases tupleTail_ordinary_of_elementFuel nested nestedFuel contract opening
      loopFuel elementsRev input inputValid loopAdequate nestedAdequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The production tuple-loop fuel is adequate on every valid bounded input. -/
theorem tupleTail_production_ordinary_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) (elementsRev : List Expr)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next,
      tupleTail nested opening (input.remainingCount + 1) elementsRev input =
        .ok value next) ∨
    (∃ failure next,
      tupleTail nested opening (input.remainingCount + 1) elementsRev input =
        .reject failure next) :=
  tupleTail_ordinary_of_elementFuel nested nestedFuel contract opening
    (input.remainingCount + 1) elementsRev input inputValid (by omega)
      nestedAdequate

theorem tupleTail_production_ne_invariant_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) (elementsRev : List Expr)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    tupleTail nested opening (input.remainingCount + 1) elementsRev input ≠
      .invariant error :=
  tupleTail_ne_invariant_of_elementFuel nested nestedFuel contract opening
    (input.remainingCount + 1) elementsRev input inputValid (by omega)
      nestedAdequate error

/--
Parenthesized parsing is ordinary with one fuel unit beyond its nested parser.
The opening parenthesis spends that unit before the first nested invocation.
-/
theorem parenthesized_ordinary_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, parenthesized nested input = .ok value next) ∨
      (∃ failure next,
        parenthesized nested input = .reject failure next) := by
  unfold parenthesized
  cases openingResult : symbol .leftParen .expression input with
  | invariant error =>
      exact False.elim
        (symbol_ne_invariant .leftParen .expression input error openingResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok opening afterOpening =>
      have openingValid := symbol_validFor .leftParen .expression input inputValid
      rw [openingResult] at openingValid
      have openingWindow :=
        symbol_preservesTokenWindow .leftParen .expression input
      rw [openingResult] at openingWindow
      have openingProgress : input.cursor < afterOpening.cursor :=
        acceptToken_cursor_lt_onSuccess (.symbol .leftParen) .expression
          (· == .symbol .leftParen) openingResult
      have afterOpeningAdequate :
          afterOpening.remainingCount < nestedFuel :=
        remainingCount_lt_after_strict_progress openingValid.2.1
          openingWindow.2 openingProgress adequate
      simp only
      split
      · exact closeTuple_invariantFreeOnValid opening [] afterOpening
          openingValid.2.1
      · cases nestedResult : nested afterOpening with
        | invariant error =>
            exact False.elim (contract.ne_invariant afterOpening
              openingValid.2.1 afterOpeningAdequate error nestedResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok first next =>
            have firstValid := contract.validFor afterOpening openingValid.2.1
            rw [nestedResult] at firstValid
            have firstWindow := contract.preservesTokenWindow afterOpening
            rw [nestedResult] at firstWindow
            have firstProgress := contract.cursorLtOnSuccess nestedResult
            dsimp only
            split
            · omega
            · split
              · have nextAdequate :
                    next.remainingCount < nestedFuel + 1 := by
                  have preserved : next.remainingCount < nestedFuel :=
                    remainingCount_lt_of_cursor_le firstWindow.2
                      (Nat.le_of_lt firstProgress) afterOpeningAdequate
                  omega
                exact tupleTail_production_ordinary_of_elementFuel nested
                  nestedFuel contract opening [first] next firstValid.2.1
                    nextAdequate
              · exact closeTuple_invariantFreeOnValid opening [first] next
                  firstValid.2.1

theorem parenthesized_ne_invariant_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    parenthesized nested input ≠ .invariant error := by
  intro failed
  rcases parenthesized_ordinary_of_elementFuel nested nestedFuel contract input
      inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.Expression.AtomCoreTotalityProperties`
-/

/-! Fuel-aware totality for expression-atom dispatch and recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem expressionAtomCore_ordinary_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      expressionAtomCore nested block input = .ok expression next) ∨
    (∃ failure next,
      expressionAtomCore nested block input = .reject failure next) := by
  unfold expressionAtomCore
  split
  · exact literalExpression_invariantFreeOnValid input inputValid
  · split
    · exact identifierExpression_invariantFreeOnValid input inputValid
    · split
      · exact dotConstructor_ordinary_of_elementFuel nested nestedFuel
          nestedContract input inputValid adequate
      · split
        · exact proxyExpression_invariantFreeOnValid input inputValid
        · split
          · exact parenthesized_ordinary_of_elementFuel nested nestedFuel
              nestedContract input inputValid adequate
          · split
            · exact arrayLiteral_ordinary_of_elementFuel nested nestedFuel
                nestedContract input inputValid adequate
            · split
              · exact lambdaFree input inputValid
              · exact Parser.rejectAt_invariantFreeOnValid
                  { head := .expression, tail := [] } .expression
                    input inputValid

theorem expressionAtomCore_ne_invariant_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    expressionAtomCore nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtomCore_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Recovery adds no invariant after an ordinary atom-core rejection. -/
theorem expressionAtom_ordinary_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      expressionAtom nested block input = .ok expression next) ∨
    (∃ failure next,
      expressionAtom nested block input = .reject failure next) := by
  rcases expressionAtomCore_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree input inputValid adequate with
    ⟨value, next, coreResult⟩ | ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [expressionAtom, coreResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : isAtomBoundary rewound
    · exact Or.inr ⟨failure, rewound, by
        simp only [expressionAtom, coreResult, rewound, boundary, ↓reduceIte]⟩
    · have boundaryFalse : isAtomBoundary rewound = false := by
        cases found : isAtomBoundary rewound with
        | false => rfl
        | true => exact False.elim (boundary found)
      rcases recoverAtom_ordinary
          (rewound.emit failure.toDiagnostic) with
        ⟨recovered, final, recoveryResult⟩ |
        ⟨recoveryFailure, rejected, recoveryResult⟩
      · exact Or.inl ⟨recovered, final, by
          simp only [expressionAtom, coreResult, rewound, boundaryFalse,
            Bool.false_eq_true, ↓reduceIte, recoveryResult]⟩
      · exact Or.inr ⟨recoveryFailure, rejected, by
          simp only [expressionAtom, coreResult, rewound, boundaryFalse,
            Bool.false_eq_true, ↓reduceIte, recoveryResult]⟩

theorem expressionAtom_ne_invariant_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    expressionAtom nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtom_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
