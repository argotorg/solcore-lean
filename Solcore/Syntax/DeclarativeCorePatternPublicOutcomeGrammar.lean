import Solcore.Syntax.DeclarativeCorePatternRecoveryOutcomeGrammar

/-!
Parser-independent ordinary outcomes at the public Core pattern rewind and
recovery boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming boundaries checked before public pattern recovery. -/
inductive PatternBoundaryStops : Remainder → Prop where
  | windowEnd {input : Remainder} (atEnd : input.endIndex ≤ input.cursor) :
      PatternBoundaryStops input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      PatternBoundaryStops input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      PatternBoundaryStops input
  | fatArrow {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .fatArrow }) :
      PatternBoundaryStops input
  | pipe {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .pipe }) :
      PatternBoundaryStops input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      PatternBoundaryStops input

/-- A Core-pattern rejection retains its failed cursor while preserving the
token carrier and active window needed for the public cursor rewind. -/
def PatternCoreRejectsWithPreservedWindow
    (coreRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ failed, coreRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Ordinary public pattern success is a direct Core success or recovery from
the original cursor after a window-preserving Core rejection. -/
inductive PatternLayerOrdinaryParses
    (coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (coreRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | core {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : coreOrdinary input pattern output) :
      PatternLayerOrdinaryParses coreOrdinary coreRejects input pattern output
  | recovered {input output : Remainder} {pattern : Syntax.Pattern}
      (coreRejected : PatternCoreRejectsWithPreservedWindow coreRejects input)
      (continues : ¬ PatternBoundaryStops input)
      (recovered : PatternRecoveryParses input pattern output) :
      PatternLayerOrdinaryParses coreOrdinary coreRejects input pattern output

/-- Exact public pattern rejection after the Core failure is rewound. -/
inductive PatternLayerRejects
    (coreRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (coreRejected : PatternCoreRejectsWithPreservedWindow coreRejects input)
      (stops : PatternBoundaryStops input) :
      PatternLayerRejects coreRejects input input
  | recovery {input rejected : Remainder}
      (coreRejected : PatternCoreRejectsWithPreservedWindow coreRejects input)
      (continues : ¬ PatternBoundaryStops input)
      (recoveryRejected : PatternRecoveryRejects input rejected) :
      PatternLayerRejects coreRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
