import Solcore.Syntax.Parser.Function

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/- Proof-visible implementation-body parser components. -/
namespace ImplInternals

/-- Require at least one implementation head argument. -/
def requireImplArguments (values : DelimitedList TypeExpr) :
    Parser (NonemptyDelimitedList TypeExpr) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

/-- Parse one function member of an implementation body. -/
def implMethod : Parser ImplMethod := do
  let declaration ← functionDecl .module
  pure {
    span := declaration.span
    value := { leadingComments := [], declaration }
  }

/-- The brace range and methods accumulated by implementation-body parsing. -/
structure ImplBody where
  span : SourceSpan
  methods : List ImplMethod

/-- Close an implementation body and restore source order. -/
def closeImplBody (opening : Token)
    (methodsRev : List ImplMethod) : Parser ImplBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    methods := methodsRev.reverse
  }

/-- Parse implementation methods with explicit fuel and progress checks. -/
def implMethods (opening : Token) :
    Nat → List ImplMethod → State → Reply ImplBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, methodsRev, state =>
      if isSymbol state .rightBrace then
        closeImplBody opening methodsRev state
      else if isKeyword state .functionKw then
        let before := state.cursor
        match implMethod state with
        | .ok value next =>
            if next.cursor > before then
              implMethods opening fuel (value :: methodsRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        rejectAt state {
          head := .keyword .functionKw
          tail := [.symbol .rightBrace]
        } .topItem

/-- Parse a complete brace-delimited implementation body. -/
def implBody : Parser ImplBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      implMethods opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end ImplInternals

open ImplInternals

/-- Parse a canonical optional-default trait implementation. -/
def implDecl : Parser ImplDecl := do
  let state ← getState
  let defaultMarker ←
    if isKeyword state .defaultKw then
      pure (some (← keyword .defaultKw .topItem).span)
    else
      pure none
  let marker ← contextual .impl .topItem
  let genericParameters ← optionalGenericParameters
  let traitName ← identifier .topItem
  let arguments ← delimited .less .greater false typeExpr
    .typeExpr .topLevel
  let headArguments ← requireImplArguments arguments
  let whereClause ← whereClause
  let body ← implBody
  let startSpan := defaultMarker.getD marker.span
  pure {
    span := SourceSpan.cover startSpan body.span
    value := {
      defaultMarker
      genericParameters
      traitName
      headArguments
      whereClause
      bodySpan := body.span
      methods := body.methods
    }
  }

end Solcore.Syntax.Parser
