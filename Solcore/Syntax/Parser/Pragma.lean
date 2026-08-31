import Solcore.Syntax.Parser.Primitive

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def pragmaItemsTail :
    Nat → List Identifier → State → Reply (List Identifier)
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, itemsRev, state =>
      if isSymbol state .comma then
        match symbol .comma .pragmaDecl state with
        | .ok _ afterComma =>
            if isSymbol afterComma .semicolon then
              .ok itemsRev.reverse afterComma
            else
              match identifier .pragmaDecl afterComma with
              | .ok item next =>
                  pragmaItemsTail fuel (item :: itemsRev) next
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok itemsRev.reverse state

private def pragmaItems : Parser (List Identifier) := fun state =>
  if isSymbol state .semicolon then
    .ok [] state
  else
    match identifier .pragmaDecl state with
    | .ok item next =>
        pragmaItemsTail (next.remainingCount + 1) [item] next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

/-- Parse one canonical provisional pragma declaration. -/
def pragmaDecl : Parser PragmaDecl := do
  let pragmaKeyword ← keyword .pragmaKw .pragmaDecl
  -- The pragma name deliberately omits the ordinary hyphen diagnostic.
  let name ← rawIdentifier .pragmaDecl
  let items ← pragmaItems
  let semicolon ← symbol .semicolon .pragmaDecl
  pure {
    span := SourceSpan.cover pragmaKeyword.span semicolon.span
    value := { name, items }
  }

end Solcore.Syntax.Parser
