import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.Term

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse an ordinary named function and its root-tail-enabled body. -/
def functionDecl
    (location : FunctionLocation) : Parser FunctionDecl := do
  let signature ← functionSignature location
  let body ← isolateBlock (block .allow)
  pure {
    span := SourceSpan.cover signature.span body.span
    value := { signature, body }
  }

end Solcore.Syntax.Parser
