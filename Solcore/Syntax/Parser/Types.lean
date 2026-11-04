import Solcore.Syntax.Parser.State
import Solcore.Syntax.Type
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.Foundation
import Solcore.Syntax.Source
import Solcore.Syntax.Token
import Solcore.Syntax.Parser.Tokens

/-!
Parsers for type expressions, predicates and parameters.

Main declarations: `typeExpr`, `predicate`, `whereClause`, `namedParameter`,
`lambdaParameter`.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Type
set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

/-- Parse a parenthesized tuple type using the supplied recursive parser. -/
def parseTupleType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let tuple ← delimited .leftParen .rightParen true nested
    .typeExpr .typeExpr
  pure {
    span := tuple.span
    value := .tuple tuple.elements
  }

namespace TypeFunctionInternals

/-- Parse the optional return list of a function type. -/
def parseFunctionReturns (nested : Parser TypeExpr) :
    Parser (Option (DelimitedList TypeExpr)) := do
  let state ← getState
  if isContextual state .returns then
    let _ ← contextual .returns .typeExpr
    let values ← delimited .leftParen .rightParen true nested .typeExpr .typeExpr
    pure (some values)
  else
    pure none

end TypeFunctionInternals

open TypeFunctionInternals

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
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Predicate
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse one trait predicate `subject: Trait<arguments...>`. -/
def predicate : Parser Predicate := do
  let subject ← typeExpr
  let _ ← symbol .colon .typeExpr
  let traitName ← identifier .typeExpr
  let arguments ← parseNamedTypeArguments typeExpr
  let endSpan := match arguments with
    | some values => values.span
    | none => traitName.span
  pure {
    span := SourceSpan.cover subject.span endSpan
    subject
    traitName
    arguments
  }

namespace PredicateInternals

abbrev PredicateSequence := NonemptyDelimitedList Predicate

def barePredicatesTail (first : Predicate) :
    Nat → Predicate → List Predicate → State → Reply PredicateSequence
  | 0, _, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .comma then
        match symbol .comma .typeExpr state with
        | .ok comma afterComma =>
            if startsTypeExpr afterComma then
              match predicate afterComma with
              | .ok value next =>
                  barePredicatesTail first fuel value
                    (value :: tailRev) next
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
            else
              .ok {
                span := SourceSpan.cover first.span comma.span
                elements := { head := first, tail := tailRev.reverse }
              } afterComma
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok {
          span := SourceSpan.cover first.span last.span
          elements := { head := first, tail := tailRev.reverse }
        } state

def barePredicates : Parser PredicateSequence := fun state =>
  match predicate state with
  | .ok first next =>
      barePredicatesTail first (next.remainingCount + 1) first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

def groupedPredicates : Parser PredicateSequence := do
  let values ← delimited .leftParen .rightParen false predicate
    .typeExpr .topLevel
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

def predicateSequence : Parser PredicateSequence := fun state =>
  if isSymbol state .leftParen then
    orElse groupedPredicates barePredicates state
  else
    barePredicates state

end PredicateInternals

/-- Optional nonempty `where` predicate sequence. -/
def whereClause : Parser (Option WhereClause) := do
  let state ← getState
  if isContextual state .where then
    let whereToken ← contextual .where .typeExpr
    let predicates ← PredicateInternals.predicateSequence
    pure (some {
      span := SourceSpan.cover whereToken.span predicates.span
      predicates := predicates.elements
    })
  else
    pure none

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Parameter
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FunctionParameterInternals

def finishTypedParameter (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) : Parser FunctionParameter := do
  match type.value with
  | .comptime .. =>
      let _ ← emitDiagnostic {
        span := type.span
        kind := .constraintViolation .comptimeTypeInParameter
      }
  | _ => pure ()
  pure {
    span := SourceSpan.cover start type.span
    value := .typed comptimeMarker name type
  }

def errorParameter (span : SourceSpan)
    (constraint : ParseConstraint) : Parser FunctionParameter := do
  let _ ← emitDiagnostic {
    span
    kind := .constraintViolation constraint
  }
  pure { span, value := .error }

def namedParameterTail (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) : Parser FunctionParameter := do
  let state ← getState
  if isSymbol state .colon then
    let _ ← symbol .colon .parameter
    let type ← typeExpr
    finishTypedParameter start comptimeMarker name type
  else
    errorParameter errorSpan .namedParameterRequiresType

def ordinaryNamedParameter : Parser FunctionParameter := do
  let name ← identifier .parameter
  if name.value == ContextualKeyword.comptime.spelling then
    let _ ← emitDiagnostic {
      span := name.span
      kind := .constraintViolation .comptimeUsedAsParameterName
    }
  else
    pure ()
  namedParameterTail name.span none name name.span

def comptimeNamedParameter : Parser FunctionParameter := do
  let marker ← contextual .comptime .parameter
  let name ← identifier .parameter
  namedParameterTail marker.span (some marker.span) name
    (SourceSpan.cover marker.span name.span)

def namedParameterCore : Parser FunctionParameter := fun state =>
  if isContextual state .comptime &&
      match state.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false then
    comptimeNamedParameter state
  else
    ordinaryNamedParameter state

def finishRecoveredParameter (first last : SourceSpan)
    (state : State) : Reply FunctionParameter :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .functionParameter
  })

def recoverParameterAux (first last : SourceSpan) :
    Nat → State → Reply FunctionParameter
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || isSymbol state .comma ||
          isSymbol state .rightParen then
        finishRecoveredParameter first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverParameterAux first token.span fuel next
        | none => finishRecoveredParameter first last state

def recoverParameter (state : State) : Reply FunctionParameter :=
  match state.advance? with
  | some (token, next) =>
      recoverParameterAux token.span token.span
        (next.remainingCount + 1) next
  | none => rejectAt state { head := .identifier, tail := [] } .parameter

end FunctionParameterInternals

/-- Named function-like parameter with comma/right-paren recovery. -/
def namedParameter : Parser FunctionParameter := fun state =>
  match FunctionParameterInternals.namedParameterCore state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then
        .reject failure rewound
      else
        FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

namespace LambdaParameterInternals

/-- Retag a named-function parameter while preserving every retained range. -/
def ofFunctionParameter (parameter : FunctionParameter) : LambdaParameter := {
  span := parameter.span
  value := match parameter.value with
    | .typed comptime name type => .typed comptime name type
    | .error => .error
}

def ordinaryLambdaParameterTail (name : Identifier) : Parser LambdaParameter := do
  let state ← getState
  if isSymbol state .colon then
    let parameter ← FunctionParameterInternals.namedParameterTail
      name.span none name name.span
    pure (ofFunctionParameter parameter)
  else
    pure { span := name.span, value := .inferred name }

def ordinaryLambdaParameter : Parser LambdaParameter := do
  let name ← identifier .parameter
  if name.value == ContextualKeyword.comptime.spelling then
    let _ ← emitDiagnostic {
      span := name.span
      kind := .constraintViolation .comptimeUsedAsParameterName
    }
  else
    pure ()
  ordinaryLambdaParameterTail name

def comptimeLambdaParameterTail (marker : Token)
    (name : Identifier) : Parser LambdaParameter := do
  let state ← getState
  if isSymbol state .colon then
    let parameter ← FunctionParameterInternals.namedParameterTail
      marker.span (some marker.span) name
      (SourceSpan.cover marker.span name.span)
    pure (ofFunctionParameter parameter)
  else
    let span := SourceSpan.cover marker.span name.span
    let parameter ← FunctionParameterInternals.errorParameter span
      .comptimeParameterRequiresType
    pure (ofFunctionParameter parameter)

def comptimeLambdaParameter : Parser LambdaParameter := do
  let marker ← contextual .comptime .parameter
  let name ← identifier .parameter
  comptimeLambdaParameterTail marker name

def lambdaParameterCore : Parser LambdaParameter := fun state =>
  if isContextual state .comptime &&
      match state.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false then
    comptimeLambdaParameter state
  else
    ordinaryLambdaParameter state

def recoverLambdaParameter (state : State) : Reply LambdaParameter :=
  match FunctionParameterInternals.recoverParameter state with
  | .ok recovered next => .ok {
      span := recovered.span
      value := .error
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end LambdaParameterInternals

/-- Lambda parameter, retaining inference only for ordinary unmodified names. -/
def lambdaParameter : Parser LambdaParameter := fun state =>
  match LambdaParameterInternals.lambdaParameterCore state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then
        .reject failure rewound
      else
        LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
end
