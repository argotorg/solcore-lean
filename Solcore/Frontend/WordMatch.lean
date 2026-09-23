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

/-!
## Consolidated module: `Solcore.Frontend.WordMatchProperties`
-/

/-! Independent pattern meaning and original ordered choice are deterministic.
No checker, lowering, typing or Core execution assumption is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem WordMatchPatternDenotes.value_unique {pattern : Syntax.Pattern} {left right : Core.Word}
    (first : WordMatchPatternDenotes pattern left)
    (second : WordMatchPatternDenotes pattern right) : left = right := by
  obtain ⟨leftLiteral, leftShape, leftMeaning⟩ := first
  obtain ⟨rightLiteral, rightShape, rightMeaning⟩ := second
  have literals := Syntax.PatternValue.literal.inj (leftShape.symm.trans rightShape)
  subst rightLiteral
  exact leftMeaning.value_unique rightMeaning

theorem WordMatchPatternClassifies.tag_unique
    {pattern : Syntax.Pattern} {left right : Option Core.Word}
    (first : WordMatchPatternClassifies pattern left)
    (second : WordMatchPatternClassifies pattern right) : left = right := by
  induction first generalizing right with
  | @literal pattern word meaning =>
      cases second with
      | literal other => exact congrArg some (meaning.value_unique other)
      | wildcard shape =>
          obtain ⟨literal, literalShape, _⟩ := meaning
          rw [shape] at literalShape
          cases literalShape
      | group _ => obtain ⟨literal, shape, _⟩ := meaning; cases shape
  | wildcard shape =>
      cases second with
      | literal meaning =>
          obtain ⟨literal, literalShape, _⟩ := meaning
          rw [shape] at literalShape
          cases literalShape
      | wildcard _ => rfl
      | group _ => cases shape
  | group _ ih =>
      cases second with
      | literal meaning => obtain ⟨literal, shape, _⟩ := meaning; cases shape
      | wildcard shape => cases shape
      | group other => exact ih other

theorem WordMatchPatternClassifies.value_unique
    {pattern : Syntax.Pattern} {left right : Core.Word}
    (first : WordMatchPatternClassifies pattern (some left))
    (second : WordMatchPatternClassifies pattern (some right)) : left = right :=
  Option.some.inj (first.tag_unique second)

private theorem classified_checks {pattern : Syntax.Pattern} {tag : Option Core.Word}
    (meaning : WordMatchPatternClassifies pattern tag) :
    interpretWordMatchPattern? pattern = some tag := by
  induction meaning with
  | @literal pattern word meaning =>
      obtain ⟨literal, shape, denotes⟩ := meaning
      rcases pattern with ⟨span, value⟩
      change value = .literal literal at shape
      subst value
      simp [interpretWordMatchPattern?, interpretWordLiteral?_iff.mpr denotes]
  | @wildcard pattern marker shape =>
      rcases pattern with ⟨span, value⟩
      change value = .wildcard marker at shape
      subst value
      simp only [interpretWordMatchPattern?]
  | group _ ih => simpa only [interpretWordMatchPattern?] using ih

private theorem checked_classifies (pattern : Syntax.Pattern) (tag : Option Core.Word)
    (checked : interpretWordMatchPattern? pattern = some tag) :
    WordMatchPatternClassifies pattern tag := by
  cases pattern with
  | mk span value =>
      cases value <;> simp only [interpretWordMatchPattern?] at checked
      all_goals try cases checked
      case literal literal =>
        obtain ⟨word, found, rfl⟩ := Option.map_eq_some_iff.mp checked
        exact .literal ⟨literal, rfl, interpretWordLiteral?_iff.mp found⟩
      case wildcard.refl marker => exact .wildcard rfl
      case group inner => exact .group (checked_classifies inner tag checked)
termination_by sizeOf pattern

theorem interpretWordMatchPattern?_iff {pattern : Syntax.Pattern} {tag : Option Core.Word} :
    interpretWordMatchPattern? pattern = some tag ↔ WordMatchPatternClassifies pattern tag :=
  ⟨checked_classifies pattern tag, classified_checks⟩

theorem WordMatchChooses.deterministic
    {value : Core.Value} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
    {left right : Syntax.Block}
    {leftTests rightTests : Nat}
    (first : WordMatchChooses value cases defaultBody left leftTests)
    (second : WordMatchChooses value cases defaultBody right rightTests) :
    left = right ∧ leftTests = rightTests := by
  induction first generalizing right rightTests with
  | fallback => cases second; exact ⟨rfl, rfl⟩
  | wildcard shape =>
      cases second with
      | wildcard _ => exact ⟨rfl, rfl⟩
      | hit meaning => cases shape.tag_unique meaning
      | miss meaning _ _ => cases shape.tag_unique meaning
  | hit meaning =>
      cases second with
      | wildcard shape => cases meaning.tag_unique shape
      | hit _ => exact ⟨rfl, rfl⟩
      | miss other different _ => exact False.elim (different (meaning.value_unique other))
  | miss meaning different _ ih =>
      cases second with
      | wildcard shape => cases meaning.tag_unique shape
      | hit other => exact False.elim (different (other.value_unique meaning))
      | miss _ _ tail =>
          obtain ⟨rfl, rfl⟩ := ih tail
          exact ⟨rfl, rfl⟩

end Solcore.Frontend
