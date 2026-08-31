import Solcore.Syntax.Foundation

set_option autoImplicit false

namespace Solcore.Syntax

/-- Literal payload shared by Core expressions, patterns, and inline Yul. -/
inductive LiteralValue where
  | decimal (spelling : String)
  | hexadecimal (spelling : String)
  | string (spelling : String) (decoded : String)
  | boolean (value : Bool)
  deriving Repr, BEq, DecidableEq

/-- One literal paired with the exact range of its written spelling. -/
abbrev Literal := Located LiteralValue

end Solcore.Syntax
