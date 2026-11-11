import Solcore.Syntax.Foundation

/-!
Literals: `CoreLiteral`, `YulLiteral`.
-/

set_option autoImplicit false

namespace Solcore.Syntax

/-- Raw Core literal payload retained by the canonical parser. -/
inductive CoreLiteralValue where
  | decimal (spelling : String)
  | hexadecimal (spelling : String)
  | string (spelling : String)
  deriving Repr, BEq, DecidableEq

namespace CoreLiteralValue

/-- Whether the literal is a number. -/
def isNumeric : CoreLiteralValue → Bool
  | .decimal _ | .hexadecimal _ => true
  | .string _ => false

/-- A spelling with its sign flipped: a leading `-` is removed or added. -/
def flipSign (spelling : String) : String :=
  match spelling.toList with
  | '-' :: rest => String.ofList rest
  | characters => String.ofList ('-' :: characters)

/-- A numeric literal with its sign flipped. The parser never writes a `-`
into a literal: `Syntax.Unchecked.mark` does, when it folds a prefix `-` into
the literal under it. -/
def negated : CoreLiteralValue → CoreLiteralValue
  | .decimal spelling => .decimal (flipSign spelling)
  | .hexadecimal spelling => .hexadecimal (flipSign spelling)
  | .string spelling => .string spelling

end CoreLiteralValue

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
