import Solcore.Syntax.Unicode.LetterRanges0
import Solcore.Syntax.Unicode.LetterRanges1
import Solcore.Syntax.Unicode.LetterRanges2

set_option autoImplicit false

namespace Solcore.Syntax.Unicode

/--
Unicode 16.0 general-category Letter ranges, matching
regex-syntax 0.8.11's general_category::LETTER table.
-/
def letterRanges : Array ScalarRange :=
  letterRanges0 ++ letterRanges1 ++ letterRanges2

/-- Recognize exactly the Unicode 16.0 characters in general category Letter. -/
def isLetter (character : Char) : Bool :=
  inScalarRanges letterRanges character

end Solcore.Syntax.Unicode
