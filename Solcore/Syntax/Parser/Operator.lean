import Solcore.Syntax.Parser.Primitive

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Exact operator-token subset accepted inside import/export parentheses. -/
def operatorPart? : TokenKind → Option String
  | .symbol .colonEqual => some ":="
  | .symbol .arrow => some "->"
  | .symbol .fatArrow => some "=>"
  | .symbol .equalEqual => some "=="
  | .symbol .notEqual => some "!="
  | .symbol .greaterEqual => some ">="
  | .symbol .lessEqual => some "<="
  | .symbol .logicalAnd => some "&&"
  | .symbol .logicalOr => some "||"
  | .symbol .plusEqual => some "+="
  | .symbol .minusEqual => some "-="
  | .symbol .starEqual => some "*="
  | .symbol .slashEqual => some "/="
  | .symbol .caretEqual => some "^="
  | .symbol .ampEqual => some "&="
  | .symbol .pipeEqual => some "|="
  | .symbol .percentEqual => some "%="
  | .symbol .tildeEqual => some "~="
  | .symbol .plus => some "+"
  | .symbol .minus => some "-"
  | .symbol .star => some "*"
  | .symbol .slash => some "/"
  | .symbol .percent => some "%"
  | .symbol .bang => some "!"
  | .symbol .tilde => some "~"
  | .symbol .less => some "<"
  | .symbol .greater => some ">"
  | .symbol .equal => some "="
  | .symbol .pipe => some "|"
  | .symbol .amp => some "&"
  | .symbol .caret => some "^"
  | .symbol .colon => some ":"
  | _ => none

def isOperatorPart (kind : TokenKind) : Bool :=
  (operatorPart? kind).isSome

private def operatorParts (context : ParseContext) :
    Nat → List String → State → Reply (List String)
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, partsRev, state =>
      match state.peek? with
      | some token =>
          match operatorPart? token.value with
          | some spelling =>
              operatorParts context fuel (spelling :: partsRev)
                { state with cursor := state.cursor + 1 }
          | none =>
              if partsRev.isEmpty then
                rejectAt state { head := .selectorName, tail := [] } context
              else
                .ok partsRev.reverse state
      | none =>
          if partsRev.isEmpty then
            rejectAt state { head := .selectorName, tail := [] } context
          else
            .ok partsRev.reverse state

/-- Parse a nonempty parenthesized operator selector. -/
def operatorSelector (context : ParseContext) : Parser SelectorName := do
  let opening ← symbol .leftParen context
  let parts ← fun state =>
    operatorParts context (state.remainingCount + 1) [] state
  let closing ← symbol .rightParen context
  let span := SourceSpan.cover opening.span closing.span
  pure {
    span
    value := .operator (String.join parts)
  }

/-- Parse either an ordinary identifier or a parenthesized operator. -/
def selectorName (context : ParseContext) : Parser SelectorName := fun state =>
  if isSymbol state .leftParen then
    operatorSelector context state
  else
    match identifier context state with
    | .ok name next => .ok {
        span := name.span
        value := .identifier name
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

end Solcore.Syntax.Parser
