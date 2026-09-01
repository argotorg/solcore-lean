import Solcore.Syntax.DeclarativeCoreAssemblyStatementOutcomeGrammar

/-! Deterministic ordinary outcomes for Core `assembly`. -/

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

/-- Ordinary Core assembly success has one final remainder. -/
theorem AssemblyStatementOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssemblyStatementOrdinaryParses input left afterLeft)
    (rightParsed : AssemblyStatementOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact leftBody.output_unique
            yulStatementPublicDeterministicOutcomeSpec rightBody

/-- Exact Core assembly rejection excludes ordinary success. -/
theorem AssemblyStatementRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : AssemblyStatementRejects input rejected) :
    ¬ ∃ statement output,
      AssemblyStatementOrdinaryParses input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact rejectedBody.disjointOrdinary
            yulStatementPublicDeterministicOutcomeSpec
              ⟨_, _, _, successfulBody⟩

/-- Public Yul body outcomes lift through the Core assembly wrapper. -/
theorem assemblyStatementDeterministicOutcomeSpec :
    DeterministicOutcomeSpec AssemblyStatementOrdinaryParses
      AssemblyStatementRejects where
  successOutputUnique := AssemblyStatementOrdinaryParses.output_unique
  successRejectDisjoint := AssemblyStatementRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
