import Solcore.Syntax.Unicode.LowercaseRanges0
import Solcore.Syntax.Unicode.LowercaseRanges1
import Solcore.Syntax.Unicode.LowercaseRanges2

set_option autoImplicit false

namespace Solcore.Syntax.Unicode

/--
Unicode lowercase-property ranges, matching Rust 1.97.0's
`char::is_lowercase()` classification.
-/
def lowercaseRanges : Array ScalarRange :=
  lowercaseRanges0 ++ lowercaseRanges1 ++ lowercaseRanges2

/-- Recognize exactly the characters accepted by Rust 1.97.0 as lowercase. -/
def isLowercase (character : Char) : Bool :=
  inScalarRanges lowercaseRanges character

end Solcore.Syntax.Unicode
