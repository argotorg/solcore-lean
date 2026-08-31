import Solcore.Syntax.Parser.Signature

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace EnumInternals

/-- Parse the optional tuple payload of one enum constructor. -/
def enumConstructorFields : Parser (Option (DelimitedList TypeExpr)) := do
  let state ← getState
  if isSymbol state .leftParen then
    pure (some (← delimitedNoTrailing .leftParen .rightParen true typeExpr
      .typeExpr .topLevel))
  else
    pure none

/-- Parse one enum constructor and its optional tuple payload. -/
def enumConstructor : Parser EnumConstructor := do
  let name ← identifier .topItem
  let fields ← enumConstructorFields
  let endSpan := fields.map (fun values => values.span) |>.getD name.span
  pure {
    span := SourceSpan.cover name.span endSpan
    value := { leadingComments := [], name, fields }
  }

structure EnumBody where
  span : SourceSpan
  constructors : List EnumConstructor

def closeEnumBody (opening : Token)
    (constructorsRev : List EnumConstructor) : Parser EnumBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    constructors := constructorsRev.reverse
  }

def enumConstructors (opening : Token) :
    Nat → List EnumConstructor → State → Reply EnumBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, constructorsRev, state =>
      if isSymbol state .comma then
        match symbol .comma .topItem state with
        | .ok _ afterComma =>
            if isSymbol afterComma .rightBrace then
              closeEnumBody opening constructorsRev afterComma
            else
              let before := afterComma.cursor
              match enumConstructor afterComma with
              | .ok value next =>
                  if next.cursor > before then
                    enumConstructors opening fuel (value :: constructorsRev) next
                  else
                    .invariant (.noProgress .topLevel next.currentSpan)
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        closeEnumBody opening constructorsRev state

def enumBody : Parser EnumBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      if isSymbol next .rightBrace then
        closeEnumBody opening [] next
      else
        match enumConstructor next with
        | .ok first afterFirst =>
            enumConstructors opening (afterFirst.remainingCount + 1)
              [first] afterFirst
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end EnumInternals

/-- Parse a canonical algebraic `enum` declaration. -/
def enumDecl
    (deriveAttribute : Option DeriveAttribute) : Parser EnumDecl := do
  let marker ← contextual .enum .topItem
  let name ← identifier .topItem
  let parameters ← optionalGenericParameters
  let body ← EnumInternals.enumBody
  let startSpan := deriveAttribute.map (fun derive => derive.span)
    |>.getD marker.span
  pure {
    span := SourceSpan.cover startSpan body.span
    value := {
      deriveAttribute
      name
      parameters
      bodySpan := body.span
      constructors := body.constructors
    }
  }

end Solcore.Syntax.Parser
