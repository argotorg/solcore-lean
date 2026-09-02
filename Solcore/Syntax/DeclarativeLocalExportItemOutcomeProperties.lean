import Solcore.Syntax.DeclarativeExportNameOutcomeProperties
import Solcore.Syntax.DeclarativeExportPathOutcomeProperties
import Solcore.Syntax.DeclarativeLocalExportItemOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem qualifiedStart_conflicts_absent {input : Remainder}
    (present : LocalExportItemQualifiedStartAt input)
    (absent : IdentifierDotAbsentAt input.tokens input.endIndex input.cursor) :
    False := by
  rcases present with ⟨identifierSpan, dotSpan, text, identifierToken,
    dotToken⟩
  exact absent ⟨identifierSpan, dotSpan, text, identifierToken, dotToken⟩

private theorem initial_dot_of_path_tail
    {tokens : Array Token} {endIndex cursor finish : Nat}
    {components : List Syntax.Identifier} {dotSpan : SourceSpan}
    (tail : ExportPathTailParses tokens endIndex cursor components finish)
    (finishDot : TokenAt tokens endIndex finish {
      span := dotSpan
      value := .symbol .dot
    }) :
    ∃ firstDotSpan, TokenAt tokens endIndex cursor {
      span := firstDotSpan
      value := .symbol .dot
    } := by
  cases tail with
  | done cursor stopped =>
      exact ⟨dotSpan, finishDot⟩
  | next firstDotSpan firstDot componentToken rest =>
      exact ⟨firstDotSpan, firstDot⟩

private theorem qualifiedStart_of_path_dot
    {input afterPath : Remainder} {path : Syntax.QualifiedName}
    {dotSpan : SourceSpan}
    (pathParsed : ExportPathOrdinaryParses input path afterPath)
    (dotToken : TokenAt afterPath.tokens afterPath.endIndex afterPath.cursor {
      span := dotSpan
      value := .symbol .dot
    }) : LocalExportItemQualifiedStartAt input := by
  unfold ExportPathOrdinaryParses ExportPathParses at pathParsed
  rcases pathParsed with ⟨tokensEq, endIndexEq, firstToken, tail, spanEq⟩
  have finishDot : TokenAt input.tokens input.endIndex afterPath.cursor {
      span := dotSpan
      value := .symbol .dot
    } := by
    simpa only [tokensEq, endIndexEq] using dotToken
  rcases initial_dot_of_path_tail tail finishDot with
    ⟨firstDotSpan, firstDot⟩
  exact ⟨_, firstDotSpan, _, firstToken, firstDot⟩

/-- Prioritized local-export-item success has one final remainder. -/
theorem LocalExportItemOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.LocalExportItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportItemOrdinaryParses input left afterLeft)
    (rightParsed : LocalExportItemOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | moduleWildcard leftDotSpan leftMarkerSpan leftPath leftDot leftMarker =>
      cases rightParsed with
      | moduleWildcard rightDotSpan rightMarkerSpan rightPath rightDot
          rightMarker =>
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique leftPath rightPath
          subst afterPathEq
          rfl
      | name rightQualifiedAbsent rightName =>
          exact False.elim (qualifiedStart_conflicts_absent
            (qualifiedStart_of_path_dot leftPath leftDot)
            rightQualifiedAbsent)
  | name leftQualifiedAbsent leftName =>
      cases rightParsed with
      | moduleWildcard rightDotSpan rightMarkerSpan rightPath rightDot
          rightMarker =>
          exact False.elim (qualifiedStart_conflicts_absent
            (qualifiedStart_of_path_dot rightPath rightDot)
            leftQualifiedAbsent)
      | name rightQualifiedAbsent rightName =>
          exact exportNameDeterministicOutcomeSpec.successOutputUnique
            leftName rightName

/-- Exact first-stage local-export-item rejection excludes ordinary success. -/
theorem LocalExportItemRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : LocalExportItemRejects input rejected) :
    ¬ ∃ item output, LocalExportItemOrdinaryParses input item output := by
  rintro ⟨item, output, successful⟩
  cases rejection with
  | moduleDotMissing qualifiedStart rejectedPath dotAbsent =>
      cases successful with
      | moduleWildcard dotSpan markerSpan successfulPath dotToken
          markerToken =>
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath successfulPath
          subst afterPathEq
          exact dotAbsent ⟨dotSpan, dotToken⟩
      | name qualifiedAbsent nameParsed =>
          exact qualifiedStart_conflicts_absent qualifiedStart
            qualifiedAbsent
  | moduleStarMissing qualifiedStart rejectedPath dotSpan dotParsed
      starAbsent =>
      cases successful with
      | moduleWildcard successfulDotSpan markerSpan successfulPath dotToken
          markerToken =>
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath successfulPath
          subst afterPathEq
          rw [dotParsed.2] at starAbsent
          exact starAbsent ⟨markerSpan, by simpa using markerToken⟩
      | name qualifiedAbsent nameParsed =>
          exact qualifiedStart_conflicts_absent qualifiedStart
            qualifiedAbsent
  | nameRejected qualifiedAbsent nameRejected =>
      cases successful with
      | moduleWildcard dotSpan markerSpan pathParsed dotToken markerToken =>
          exact qualifiedStart_conflicts_absent
            (qualifiedStart_of_path_dot pathParsed dotToken)
            qualifiedAbsent
      | name successfulQualifiedAbsent nameParsed =>
          exact exportNameDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, nameParsed⟩

/-- Local export items have deterministic and exclusive broad outcomes. -/
theorem localExportItemDeterministicOutcomeSpec :
    DeterministicOutcomeSpec LocalExportItemOrdinaryParses
      LocalExportItemRejects where
  successOutputUnique := LocalExportItemOrdinaryParses.output_unique
  successRejectDisjoint := LocalExportItemRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
