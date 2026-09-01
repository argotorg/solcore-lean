import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchComponentOutcomeGrammar

/-! Deterministic diagnostic-inclusive outcomes for optional Core default. -/

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

/-- Optional default success has one output remainder. -/
theorem OptionalDefaultBodyOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      right afterRight) : afterLeft = afterRight := by
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
          cases afterMarkerEq
          exact leftBody.output_unique statementOutcomes rightBody

/-- Exact optional-default rejection excludes ordinary success. -/
theorem OptionalDefaultBodyRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : OptionalDefaultBodyRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ body output,
      OptionalDefaultBodyOrdinaryParses statementOrdinary input body output := by
  rintro ⟨body, output, successful⟩
  cases rejection with
  | bodyRejected rejectedMarkerSpan rejectedMarker rejectedBody =>
      cases successful with
      | absent defaultAbsent =>
          exact absent_conflicts_exact defaultAbsent rejectedMarker
      | present successfulMarkerSpan successfulMarker successfulBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact rejectedBody.disjointOrdinary statementOutcomes
            ⟨_, _, successfulBody⟩

/-- Lift recursive statement outcomes through prioritized optional default. -/
theorem optionalDefaultBodyDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (OptionalDefaultBodyOrdinaryParses statementOrdinary)
      (OptionalDefaultBodyRejects statementOrdinary statementRejects) where
  successOutputUnique := OptionalDefaultBodyOrdinaryParses.output_unique
    statementOutcomes
  successRejectDisjoint := OptionalDefaultBodyRejects.disjointOrdinary
    statementOutcomes

/-- Every clean optional-default derivation embeds into the ordinary
relation. -/
theorem OptionalDefaultBodyParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    (statementToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {body : Option Syntax.Block}
    (parsed : OptionalDefaultBodyParses statementClean input body output) :
    OptionalDefaultBodyOrdinaryParses statementOrdinary input body output := by
  cases parsed with
  | absent defaultAbsent => exact .absent defaultAbsent
  | present markerSpan markerParsed bodyParsed =>
      exact .present markerSpan markerParsed
        (bodyParsed.toOrdinary statementToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
