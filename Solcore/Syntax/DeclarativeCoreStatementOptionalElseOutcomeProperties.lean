import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementIfOutcomeGrammar

/-! Deterministic diagnostic-inclusive outcomes for optional Core `else`. -/

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

/-- Optional `else` success has one output remainder. -/
theorem OptionalElseBodyOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalElseBodyOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : OptionalElseBodyOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent rightAbsent => rfl
      | present rightMarkerSpan rightMarker rightBody =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftBody =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact leftBody.output_unique statementOutcomes rightBody

/-- Exact optional `else` rejection excludes success. -/
theorem OptionalElseBodyRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : OptionalElseBodyRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ body output,
      OptionalElseBodyOrdinaryParses statementOrdinary input body output := by
  rintro ⟨body, output, successful⟩
  cases rejection with
  | bodyRejected rejectedMarkerSpan rejectedMarker rejectedBody =>
      cases successful with
      | absent elseAbsent =>
          exact absent_conflicts_exact elseAbsent rejectedMarker
      | present successfulMarkerSpan successfulMarker successfulBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact rejectedBody.disjointOrdinary statementOutcomes
            ⟨_, _, successfulBody⟩

/-- Lift recursive statement outcomes through prioritized optional `else`. -/
theorem optionalElseBodyDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (OptionalElseBodyOrdinaryParses statementOrdinary)
      (OptionalElseBodyRejects statementOrdinary statementRejects) where
  successOutputUnique := OptionalElseBodyOrdinaryParses.output_unique
    statementOutcomes
  successRejectDisjoint := OptionalElseBodyRejects.disjointOrdinary
    statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
