import Solcore.Syntax.Foundation

set_option autoImplicit false

namespace Solcore.Syntax

/-- Raw Core literal payload retained by the canonical parser. -/
inductive CoreLiteralValue where
  | decimal (spelling : String)
  | hexadecimal (spelling : String)
  | string (spelling : String)
  deriving Repr, BEq, DecidableEq

/-- One Core literal paired with the exact range of its written spelling. -/
abbrev CoreLiteral := Located CoreLiteralValue

/-- Raw inline-Yul literal payload. Only Yul admits boolean literals. -/
inductive YulLiteralValue where
  | decimal (spelling : String)
  | hexadecimal (spelling : String)
  | string (spelling : String)
  | boolean (value : Bool)
  deriving Repr, BEq, DecidableEq

/-- One inline-Yul literal paired with its exact source range. -/
abbrev YulLiteral := Located YulLiteralValue

end Solcore.Syntax
