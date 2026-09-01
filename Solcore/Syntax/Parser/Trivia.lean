import Solcore.Syntax.Parser.Result
import Solcore.Syntax.TriviaAttachment

/-!
Compatibility façade for the pure syntax-level trivia implementation.

The established parser namespace remains available to existing consumers,
while declarative grammar can depend directly on `Solcore.Syntax.Trivia`
without importing parser state or replies.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

abbrev isRustWhitespace := Solcore.Syntax.Trivia.isRustWhitespace

abbrev utf8Slice? := Solcore.Syntax.Trivia.utf8Slice?

abbrev lineBreakCount := Solcore.Syntax.Trivia.lineBreakCount

abbrev commentsDirectlyBefore :=
  Solcore.Syntax.Trivia.commentsDirectlyBefore

namespace TriviaInternals

abbrev attachEnumConstructorComments :=
  Solcore.Syntax.Trivia.Internals.attachEnumConstructorComments

abbrev attachEnumConstructors :=
  Solcore.Syntax.Trivia.Internals.attachEnumConstructors

abbrev attachEnumComments :=
  Solcore.Syntax.Trivia.Internals.attachEnumComments

abbrev attachTraitMethodComments :=
  Solcore.Syntax.Trivia.Internals.attachTraitMethodComments

abbrev attachTraitComments :=
  Solcore.Syntax.Trivia.Internals.attachTraitComments

abbrev attachImplMethodComments :=
  Solcore.Syntax.Trivia.Internals.attachImplMethodComments

abbrev attachImplComments :=
  Solcore.Syntax.Trivia.Internals.attachImplComments

abbrev attachContractMemberComments :=
  Solcore.Syntax.Trivia.Internals.attachContractMemberComments

abbrev attachContractComments :=
  Solcore.Syntax.Trivia.Internals.attachContractComments

end TriviaInternals

abbrev attachTopItemComments :=
  Solcore.Syntax.Trivia.attachTopItemComments

theorem commentsDirectlyBefore_mem (source : String)
    (comments : List Comment) (declarationStart : Nat)
    {comment : Comment}
    (member : comment ∈ commentsDirectlyBefore source comments
      declarationStart) :
    comment ∈ comments := by
  exact Solcore.Syntax.Trivia.commentsDirectlyBefore_mem source comments
    declarationStart member

theorem TriviaInternals.attachEnumConstructorComments_mem
    (file : SourceFile) (comments : List Comment)
    (introducer : SourceSpan) (constructor : EnumConstructor)
    {comment : Comment}
    (member : comment ∈
      (attachEnumConstructorComments file comments introducer
        constructor).value.leadingComments) :
    comment ∈ comments := by
  exact Solcore.Syntax.Trivia.Internals.attachEnumConstructorComments_mem
    file comments introducer constructor member

end Solcore.Syntax.Parser
