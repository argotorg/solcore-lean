import Solcore.Frontend.NumericDigits
import Solcore.Syntax.Literal
import Solcore.Core.Syntax

/-!
Standalone mathematical numeric meaning and an explicitly strict Word projection.
These operations do not assign a general source type or extend expression checking.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Decode a complete numeric payload, validating even manually constructed ASTs. -/
def numericLiteralValue? : Syntax.CoreLiteralValue → Option Nat
  | .decimal spelling =>
      match spelling.toList with
      | [] => none
      | first :: rest => numericDigitsValue? .decimal (first :: rest) 0
  | .hexadecimal spelling =>
      match spelling.toList with
      | '0' :: 'x' :: first :: rest =>
          numericDigitsValue? .hexadecimal (first :: rest) 0
      | _ => none
  | .string _ => none

/-- Whole numeric spelling has its natural value, independently of decoding. -/
inductive NumericLiteralDenotes : Syntax.CoreLiteralValue → Nat → Prop where
  | decimal {spelling : String} {value : Nat}
      (nonempty : spelling.toList ≠ [])
      (digits : NumericDigitsDenote .decimal spelling.toList 0 value) :
      NumericLiteralDenotes (.decimal spelling) value
  | hexadecimal {spelling : String} {characters : List Char} {value : Nat}
      (spellingEq : spelling.toList = '0' :: 'x' :: characters)
      (nonempty : characters ≠ [])
      (digits : NumericDigitsDenote .hexadecimal characters 0 value) :
      NumericLiteralDenotes (.hexadecimal spelling) value

/-- Convert a numeric literal only when its natural value fits a 256-bit Word. -/
def interpretWordLiteral? (literal : Syntax.CoreLiteral) : Option Core.Word :=
  (numericLiteralValue? literal.value).bind Core.Word.ofNat?

/-- Strict Word meaning retains exactly the independent natural value. -/
def WordLiteralDenotes (literal : Syntax.CoreLiteral) (word : Core.Word) : Prop :=
  NumericLiteralDenotes literal.value word.val

end Solcore.Frontend
