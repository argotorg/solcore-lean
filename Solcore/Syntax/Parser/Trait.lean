import Solcore.Syntax.Parser.Signature

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def traitMethod : Parser TraitMethod := do
  let signature ← functionSignature .module
  let semicolon ← symbol .semicolon .topItem
  pure {
    span := SourceSpan.cover signature.span semicolon.span
    value := {
      leadingComments := []
      signature
      semicolon := semicolon.span
    }
  }

private structure TraitBody where
  span : SourceSpan
  methods : List TraitMethod

private def closeTraitBody (opening : Token)
    (methodsRev : List TraitMethod) : Parser TraitBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    methods := methodsRev.reverse
  }

private def traitMethods (opening : Token) :
    Nat → List TraitMethod → State → Reply TraitBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, methodsRev, state =>
      if isSymbol state .rightBrace then
        closeTraitBody opening methodsRev state
      else if isKeyword state .functionKw then
        let before := state.cursor
        match traitMethod state with
        | .ok value next =>
            if next.cursor > before then
              traitMethods opening fuel (value :: methodsRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        rejectAt state {
          head := .keyword .functionKw
          tail := [.symbol .rightBrace]
        } .topItem

private def traitBody : Parser TraitBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      traitMethods opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Parse a canonical trait declaration and signature-only methods. -/
def traitDecl : Parser TraitDecl := do
  let marker ← contextual .trait .topItem
  let name ← identifier .topItem
  let genericParameters ← genericParameters
  let whereClause ← whereClause
  let body ← traitBody
  pure {
    span := SourceSpan.cover marker.span body.span
    value := {
      name
      genericParameters
      whereClause
      bodySpan := body.span
      methods := body.methods
    }
  }

end Solcore.Syntax.Parser
