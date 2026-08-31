import Solcore.Syntax.Lexer

set_option autoImplicit false

namespace Solcore.Syntax

/--
Whether `text` is one ordinary Solcore source identifier.

The check follows the canonical lexer and consumes the complete input. Hard
keywords, Yul-only names, pragma-only hyphenated names, and token sequences are
not ordinary identifiers. Contextual keywords remain valid identifiers.
-/
def isValidIdentifier (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: rest =>
      if !Lexer.isCoreIdentifierStart first then
        false
      else
        let scanned := Lexer.scanLetterIdentifier first rest
        scanned.remaining.isEmpty &&
          scanned.kind == .identifier text &&
          !text.toList.contains '-'

end Solcore.Syntax
