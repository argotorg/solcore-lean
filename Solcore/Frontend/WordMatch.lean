import Solcore.Frontend.WordLiteral
import Solcore.Syntax.Term

/-! Ordered source-level case selection is independent of checking, stores
and Core lowering. Only the selected original body is returned. -/

set_option autoImplicit false

namespace Solcore.Frontend

def WordMatchPatternDenotes (pattern : Syntax.Pattern) (word : Core.Word) : Prop :=
  ∃ literal, pattern.value = .literal literal ∧ WordLiteralDenotes literal word

def interpretWordMatchPattern? (pattern : Syntax.Pattern) : Option (Option Core.Word) :=
  match pattern with
  | ⟨_, .literal literal⟩ => (interpretWordLiteral? literal).map some
  | ⟨_, .wildcard _⟩ => some none
  | ⟨_, .group inner⟩ => interpretWordMatchPattern? inner
  | _ => none
termination_by sizeOf pattern

inductive WordMatchPatternClassifies : Syntax.Pattern → Option Core.Word → Prop where
  | literal {pattern : Syntax.Pattern} {word : Core.Word}
      (meaning : WordMatchPatternDenotes pattern word) :
      WordMatchPatternClassifies pattern (some word)
  | wildcard {pattern : Syntax.Pattern} {marker : Syntax.SourceSpan}
      (shape : pattern.value = .wildcard marker) :
      WordMatchPatternClassifies pattern none
  | group {span : Syntax.SourceSpan} {inner : Syntax.Pattern} {tag : Option Core.Word}
      (child : WordMatchPatternClassifies inner tag) :
      WordMatchPatternClassifies ⟨span, .group inner⟩ tag

/-- Only literal cases compare actual Words. A wildcard or literal hit ignores
later cases; fallback requires an original default. Tests count literal comparisons. -/
inductive WordMatchChooses :
    Core.Value → List Syntax.MatchCase → Option Syntax.Block → Syntax.Block → Nat → Prop where
  | fallback {value : Core.Value} {defaultBody : Syntax.Block} :
      WordMatchChooses value [] (some defaultBody) defaultBody 0
  | wildcard {value : Core.Value} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (meaning : WordMatchPatternClassifies first.value.pattern none) :
      WordMatchChooses value (first :: rest) defaultBody first.value.body 0
  | hit {word : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (meaning : WordMatchPatternClassifies first.value.pattern (some word)) :
      WordMatchChooses (.word word) (first :: rest) defaultBody first.value.body 1
  | miss {word literal : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
      (meaning : WordMatchPatternClassifies first.value.pattern (some literal))
      (different : word ≠ literal)
      (tail : WordMatchChooses (.word word) rest defaultBody selected tests) :
      WordMatchChooses (.word word) (first :: rest) defaultBody selected (tests + 1)

end Solcore.Frontend
