import Solcore

/-! External compile consumers for canonical source-span composition laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example (file : SourceFile) (first last : SourceSpan)
    (firstValid : first.ValidFor file) (lastValid : last.ValidFor file)
    (ordered : first.startByte ≤ last.endByte) :
    (SourceSpan.cover first last).ValidFor file :=
  SourceSpan.cover_validFor firstValid lastValid ordered

example (file : SourceFile) (first last : SourceSpan)
    (firstValid : first.ValidFor file)
    (endOrdered : first.endByte ≤ last.endByte) :
    (SourceSpan.cover first last).Contains first :=
  SourceSpan.cover_contains_first firstValid endOrdered

example (file : SourceFile) (first last : SourceSpan)
    (firstValid : first.ValidFor file) (lastValid : last.ValidFor file)
    (startOrdered : first.startByte ≤ last.startByte) :
    (SourceSpan.cover first last).Contains last :=
  SourceSpan.cover_contains_last firstValid lastValid startOrdered

end Tests
