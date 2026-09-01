import Solcore.Syntax.DeclarativeCoreLiteralOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeGrammar

/-! Deterministic ordinary outcomes of the three infallible selected leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Wildcard success has one output remainder. -/
theorem WildcardPatternOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : WildcardPatternOrdinaryParses input left afterLeft)
    (rightParsed : WildcardPatternOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed _ leftMarker =>
      cases rightParsed with
      | parsed _ rightMarker => rw [leftMarker.2, rightMarker.2]

/-- Wildcard rejection excludes wildcard success. -/
theorem WildcardPatternRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : WildcardPatternRejects input rejected) :
    ¬ ∃ pattern output, WildcardPatternOrdinaryParses input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | absent markerAbsent =>
      cases successful with
      | parsed span markerParsed => exact markerAbsent ⟨span, markerParsed.1⟩

/-- Wildcard leaves have deterministic ordinary outcomes. -/
theorem wildcardPatternDeterministicOutcomeSpec :
    DeterministicOutcomeSpec WildcardPatternOrdinaryParses
      WildcardPatternRejects where
  successOutputUnique := WildcardPatternOrdinaryParses.output_unique
  successRejectDisjoint := WildcardPatternRejects.disjointOrdinary

/-- Literal-pattern success has one output remainder. -/
theorem LiteralPatternOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : LiteralPatternOrdinaryParses input left afterLeft)
    (rightParsed : LiteralPatternOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftLiteral =>
      cases rightParsed with
      | parsed rightLiteral =>
          exact CoreLiteralOrdinaryParses.output_unique leftLiteral
            rightLiteral

/-- Literal-pattern rejection excludes literal-pattern success. -/
theorem LiteralPatternRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : LiteralPatternRejects input rejected) :
    ¬ ∃ pattern output, LiteralPatternOrdinaryParses input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | absent literalAbsent =>
      cases successful with
      | parsed parsed =>
          cases parsed with
          | decimal token => exact literalAbsent.1 ⟨_, _, token⟩
          | hexadecimal token => exact literalAbsent.2.1 ⟨_, _, token⟩
          | string token => exact literalAbsent.2.2 ⟨_, _, token⟩

/-- Literal-pattern leaves have deterministic ordinary outcomes. -/
theorem literalPatternDeterministicOutcomeSpec :
    DeterministicOutcomeSpec LiteralPatternOrdinaryParses
      LiteralPatternRejects where
  successOutputUnique := LiteralPatternOrdinaryParses.output_unique
  successRejectDisjoint := LiteralPatternRejects.disjointOrdinary

/-- Boolean-binder success has one output remainder. -/
theorem BooleanBinderPatternOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : BooleanBinderPatternOrdinaryParses input left afterLeft)
    (rightParsed : BooleanBinderPatternOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName => cases leftName <;> cases rightName <;> rfl

/-- Boolean-binder rejection excludes Boolean-binder success. -/
theorem BooleanBinderPatternRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : BooleanBinderPatternRejects input rejected) :
    ¬ ∃ pattern output,
      BooleanBinderPatternOrdinaryParses input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | absent booleanAbsent =>
      cases successful with
      | parsed parsed =>
          cases parsed with
          | trueKeyword token => exact booleanAbsent.1 ⟨_, token⟩
          | falseKeyword token => exact booleanAbsent.2 ⟨_, token⟩

/-- Boolean-binder leaves have deterministic ordinary outcomes. -/
theorem booleanBinderPatternDeterministicOutcomeSpec :
    DeterministicOutcomeSpec BooleanBinderPatternOrdinaryParses
      BooleanBinderPatternRejects where
  successOutputUnique := BooleanBinderPatternOrdinaryParses.output_unique
  successRejectDisjoint := BooleanBinderPatternRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
