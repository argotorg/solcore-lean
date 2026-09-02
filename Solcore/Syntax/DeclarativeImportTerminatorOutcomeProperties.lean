import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeImportTerminatorOutcomeGrammar

/-! Deterministic and exclusive broad ordinary import-terminator outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem topItemStart_conflicts_absent {input : Remainder}
    (starts : ImportTerminatorTopItemStartsAt input)
    (absent : TopItemKindsAbsentAt input
      ImportTerminatorTopItemStartKinds) : False := by
  rcases starts with ⟨kind, member, span, token⟩
  exact absent kind member ⟨span, token⟩

/-- Ordinary import terminators have one final remainder. -/
theorem ImportTerminatorOrdinaryParses.output_unique (lastSpan : SourceSpan)
    {input : Remainder} {left right : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImportTerminatorOrdinaryParses lastSpan input left afterLeft)
    (rightParsed :
      ImportTerminatorOrdinaryParses lastSpan input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | semicolon leftSpan leftSemicolon =>
      cases rightParsed with
      | semicolon rightSpan rightSemicolon =>
          exact exactToken_output_unique leftSemicolon rightSemicolon
      | recovered rightAbsent rightStarts =>
          exact False.elim
            (absent_conflicts_exact rightAbsent leftSemicolon)
  | recovered leftAbsent leftStarts =>
      cases rightParsed with
      | semicolon rightSpan rightSemicolon =>
          exact False.elim
            (absent_conflicts_exact leftAbsent rightSemicolon)
      | recovered rightAbsent rightStarts => rfl

/-- Missing import-terminator rejection excludes every ordinary success. -/
theorem ImportTerminatorRejects.disjointOrdinary (lastSpan : SourceSpan)
    {input rejected : Remainder}
    (rejection : ImportTerminatorRejects input rejected) :
    ¬ ∃ span output,
      ImportTerminatorOrdinaryParses lastSpan input span output := by
  rintro ⟨span, output, successful⟩
  cases rejection with
  | missing semicolonAbsent topItemStartAbsent =>
      cases successful with
      | semicolon semicolonSpan semicolonParsed =>
          exact absent_conflicts_exact semicolonAbsent semicolonParsed
      | recovered otherSemicolonAbsent topItemStarts =>
          exact topItemStart_conflicts_absent topItemStarts
            topItemStartAbsent

/-- Import terminators have deterministic and exclusive broad ordinary
outcomes for each fixed preceding span. -/
theorem importTerminatorDeterministicOutcomeSpec (lastSpan : SourceSpan) :
    DeterministicOutcomeSpec (ImportTerminatorOrdinaryParses lastSpan)
      ImportTerminatorRejects where
  successOutputUnique :=
    ImportTerminatorOrdinaryParses.output_unique lastSpan
  successRejectDisjoint :=
    ImportTerminatorRejects.disjointOrdinary lastSpan

end Solcore.Syntax.DeclarativeGrammar
