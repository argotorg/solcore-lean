import Solcore.Frontend.WordLiteral
import Solcore.Syntax.Term

/-! Ordered source-level literal selection is independent of checking, stores
and Core lowering. Only the selected original body is returned. -/

set_option autoImplicit false

namespace Solcore.Frontend

def WordMatchPatternDenotes (pattern : Syntax.Pattern) (word : Core.Word) : Prop :=
  ∃ literal, pattern.value = .literal literal ∧ WordLiteralDenotes literal word

/-- Empty cases perform no Word comparison. Nonempty cases compare actual
Words, and a hit never inspects later cases. Tests count original visited cases. -/
inductive WordMatchChooses :
    Core.Value → List Syntax.MatchCase → Syntax.Block → Syntax.Block → Nat → Prop where
  | fallback {value : Core.Value} {defaultBody : Syntax.Block} :
      WordMatchChooses value [] defaultBody defaultBody 0
  | hit {word : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Syntax.Block}
      (meaning : WordMatchPatternDenotes first.value.pattern word) :
      WordMatchChooses (.word word) (first :: rest) defaultBody first.value.body 1
  | miss {word literal : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody selected : Syntax.Block} {tests : Nat}
      (meaning : WordMatchPatternDenotes first.value.pattern literal)
      (different : word ≠ literal)
      (tail : WordMatchChooses (.word word) rest defaultBody selected tests) :
      WordMatchChooses (.word word) (first :: rest) defaultBody selected (tests + 1)

end Solcore.Frontend
