import Solcore.Syntax.Parser.Primitive

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Synchronization starts shared with the pinned Rust top-level grammar. -/
def isTopItemStartKind : TokenKind → Bool
  | .keyword .importKw | .keyword .exportKw | .keyword .pragmaKw |
      .keyword .typeKw | .keyword .contractKw | .keyword .functionKw |
      .keyword .defaultKw | .symbol .hash => true
  | kind => kind.isContextual .enum || kind.isContextual .trait ||
      kind.isContextual .impl

def atTopItemStart (state : State) : Bool :=
  match state.peekKind? with
  | some kind => isTopItemStartKind kind
  | none => false

end Solcore.Syntax.Parser
