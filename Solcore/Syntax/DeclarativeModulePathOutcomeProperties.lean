import Solcore.Syntax.DeclarativeCoreTypeNameOutcomeProperties
import Solcore.Syntax.DeclarativeCoreTypePrimitiveProperties
import Solcore.Syntax.DeclarativeModulePathOutcomeGrammar

/-! Deterministic and exclusive broad ordinary outcomes for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem at_conflicts_identifier {input : Remainder}
    {markerSpan : SourceSpan} {name : Syntax.Identifier}
    (markerToken : TokenAt input.tokens input.endIndex input.cursor {
      span := markerSpan
      value := .symbol .at
    })
    (nameToken : TokenAt input.tokens input.endIndex input.cursor {
      span := name.span
      value := .identifier name.value
    }) : False := by
  have kindEq : (.symbol .at : TokenKind) = .identifier name.value :=
    typeTokenAt_kind_eq markerToken nameToken
  cases kindEq

/-- Ordinary module paths have one final remainder. -/
theorem ModulePathOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ModulePath}
    {afterLeft afterRight : Remainder}
    (leftParsed : ModulePathOrdinaryParses input left afterLeft)
    (rightParsed : ModulePathOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | «local» leftName =>
      cases rightParsed with
      | «local» rightName =>
          exact QualifiedNameParses.output_unique leftName rightName
      | externalPackage markerSpan markerToken rightName =>
          rcases leftName with
            ⟨tokensEq, endIndexEq, firstToken, tail, spanEq⟩
          exact False.elim (at_conflicts_identifier markerToken firstToken)
  | externalPackage markerSpan markerToken leftName =>
      cases rightParsed with
      | «local» rightName =>
          rcases rightName with
            ⟨tokensEq, endIndexEq, firstToken, tail, spanEq⟩
          exact False.elim (at_conflicts_identifier markerToken firstToken)
      | externalPackage rightMarkerSpan rightMarkerToken rightName =>
          exact QualifiedNameParses.output_unique leftName rightName

/-- Exact module-path rejection excludes every ordinary success. -/
theorem ModulePathRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ModulePathRejects input rejected) :
    ¬ ∃ path output, ModulePathOrdinaryParses input path output := by
  rintro ⟨path, output, successful⟩
  cases rejection with
  | localRejected markerAbsent nameRejected =>
      cases successful with
      | «local» nameParsed =>
          exact nameRejected.disjointQualified ⟨_, _, nameParsed⟩
      | externalPackage markerSpan markerToken nameParsed =>
          exact typeTokenAbsent_conflicts_token markerAbsent markerToken
  | externalRejected markerSpan markerParsed nameRejected =>
      cases successful with
      | «local» nameParsed =>
          rcases nameParsed with
            ⟨tokensEq, endIndexEq, firstToken, tail, spanEq⟩
          exact at_conflicts_identifier markerParsed.1 firstToken
      | externalPackage successfulMarkerSpan successfulMarker nameParsed =>
          rw [markerParsed.2] at nameRejected
          exact nameRejected.disjointQualified ⟨_, _, nameParsed⟩

/-- Module paths have deterministic and exclusive broad ordinary outcomes. -/
theorem modulePathDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ModulePathOrdinaryParses ModulePathRejects where
  successOutputUnique := ModulePathOrdinaryParses.output_unique
  successRejectDisjoint := ModulePathRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
