import Solcore.Syntax.Parser.Expression
import Solcore.Syntax.Unicode.Lowercase

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def patternName : Parser Identifier := fun state =>
  if isBooleanValue state then booleanIdentifier state
  else identifier .pattern state

private def requirePatternArguments (values : DelimitedList Pattern) :
    Parser (NonemptyDelimitedList Pattern) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .pattern values.span)

private def constructorArguments
    (nested : Parser Pattern) : Parser (NonemptyDelimitedList Pattern) := do
  let values ← delimitedNoTrailing .leftParen .rightParen false nested
    .pattern .pattern
  requirePatternArguments values

private def optionalConstructorArguments
    (nested : Parser Pattern) : Parser (Option (NonemptyDelimitedList Pattern)) :=
    fun state =>
  if isSymbol state .leftParen then
    orElse
      (do pure (some (← constructorArguments nested)))
      (pure none) state
  else
    .ok none state

private def closePatternTuple (opening : Token)
    (elementsRev : List Pattern) : Parser Pattern := do
  let closing ← symbol .rightParen .pattern
  let span := SourceSpan.cover opening.span closing.span
  match elementsRev with
  | [only] => pure { span, value := .group only }
  | _ => pure {
      span
      value := .tuple { span, elements := elementsRev.reverse }
    }

private def patternTupleTail (nested : Parser Pattern) (opening : Token) :
    Nat → List Pattern → State → Reply Pattern
  | 0, _, state => .invariant (.fuelExhausted .pattern state.currentSpan)
  | fuel + 1, elementsRev, state =>
      match symbol .comma .pattern state with
      | .ok _ afterComma =>
          if isSymbol afterComma .rightParen then
            closePatternTuple opening elementsRev afterComma
          else
            let before := afterComma.cursor
            match nested afterComma with
            | .ok value next =>
                if next.cursor ≤ before then
                  .invariant (.noProgress .pattern next.currentSpan)
                else if isSymbol next .comma then
                  patternTupleTail nested opening fuel
                    (value :: elementsRev) next
                else
                  closePatternTuple opening (value :: elementsRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error

private def parenthesizedPattern (nested : Parser Pattern) : Parser Pattern :=
    fun state =>
  match symbol .leftParen .pattern state with
  | .ok opening afterOpening =>
      if isSymbol afterOpening .rightParen then
        closePatternTuple opening [] afterOpening
      else
        let before := afterOpening.cursor
        match nested afterOpening with
        | .ok first next =>
            if next.cursor ≤ before then
              .invariant (.noProgress .pattern next.currentSpan)
            else if isSymbol next .comma then
              patternTupleTail nested opening (next.remainingCount + 1)
                [first] next
            else
              match symbol .rightParen .pattern next with
              | .ok closing afterClosing => .ok {
                  span := SourceSpan.cover opening.span closing.span
                  value := .group first
                } afterClosing
              | .reject failure failed => .reject failure failed
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

private def dotConstructorPattern
    (nested : Parser Pattern) : Parser Pattern := do
  let dot ← symbol .dot .pattern
  let name ← patternName
  let arguments ← optionalConstructorArguments nested
  let endSpan := arguments.map (fun values => values.span) |>.getD name.span
  pure {
    span := SourceSpan.cover dot.span endSpan
    value := .constructor (some dot.span) [] name arguments
  }

private def startsWithLowercase (name : Identifier) : Bool :=
  match name.value.toList with
  | first :: _ => Unicode.isLowercase first
  | [] => true

private def qualifiedPattern (nested : Parser Pattern) : Parser Pattern := do
  let path ← qualifiedName .pattern .pattern
  let arguments ← optionalConstructorArguments nested
  let components := path.value.components.toList
  match components.reverse with
  | [] => fun _ => .invariant (.noProgress .pattern path.span)
  | name :: qualifiersRev =>
      if qualifiersRev.isEmpty && arguments.isNone &&
          startsWithLowercase name then
        pure { span := path.span, value := .binder name }
      else
        let endSpan := arguments.map (fun values => values.span) |>.getD path.span
        pure {
          span := SourceSpan.cover path.span endSpan
          value := .constructor none qualifiersRev.reverse name arguments
        }

private def patternCore (nested : Parser Pattern)
    (expression : Parser Expr) : Parser Pattern := fun state =>
  if isSymbol state .underscore then
    match symbol .underscore .pattern state with
    | .ok marker next => .ok {
        span := marker.span
        value := .wildcard marker.span
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isCoreLiteral state then
    match coreLiteral state with
    | .ok literal next => .ok {
        span := literal.span
        value := .literal literal
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isBooleanValue state then
    match booleanIdentifier state with
    | .ok name next => .ok { span := name.span, value := .binder name } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isSymbol state .leftParen then parenthesizedPattern nested state
  else if isSymbol state .dot then dotConstructorPattern nested state
  else if isContextual state .comptime then
    match contextual .comptime .pattern state with
    | .ok marker afterMarker =>
        match expression afterMarker with
        | .ok value next => .ok {
            span := SourceSpan.cover marker.span value.span
            value := .comptime marker.span value
          } next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isIdentifier state then qualifiedPattern nested state
  else rejectAt state { head := .pattern, tail := [] } .pattern

private def isPatternBoundary (state : State) : Bool :=
  state.atEnd ||
    [.comma, .rightParen, .fatArrow, .pipe, .rightBrace].any
      (isSymbol state)

private def finishRecoveredPattern (first last : SourceSpan)
    (state : State) : Reply Pattern :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .pattern
  })

private def recoverPatternAux (first last : SourceSpan) :
    Nat → State → Reply Pattern
  | 0, state => .invariant (.fuelExhausted .pattern state.currentSpan)
  | fuel + 1, state =>
      if isPatternBoundary state then
        finishRecoveredPattern first last state
      else
        match state.advance? with
        | some (token, next) => recoverPatternAux first token.span fuel next
        | none => finishRecoveredPattern first last state

/-- Build one pattern recursion layer with a supplied comptime expression. -/
def patternLayer (nested : Parser Pattern)
    (expression : Parser Expr) : Parser Pattern := fun state =>
  match patternCore nested expression state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if isPatternBoundary rewound then
        .reject failure rewound
      else
        match rewound.advance? with
        | some (token, next) =>
            recoverPatternAux token.span token.span
              (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
        | none => .reject failure rewound
  | .invariant error => .invariant error

/-- Whether the current token may begin a canonical pattern. -/
def startsPattern (state : State) : Bool :=
  isSymbol state .underscore || isCoreLiteral state ||
    isBooleanValue state || isSymbol state .leftParen ||
    isSymbol state .dot || isIdentifier state

end Solcore.Syntax.Parser
