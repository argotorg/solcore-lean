import Solcore.Syntax.DeclarativeWildcardImportOutcomeProperties
import Solcore.Syntax.DeclarativeModulePathExactnessProperties
import Solcore.Syntax.DeclarativeHidingClauseExactnessProperties
import Solcore.Syntax.DeclarativeImportTerminatorExactnessProperties

/-! Exact wildcard imports, including optional hiding and recovered terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- The fixed outer start and exact optional hiding fix the complete wildcard AST. -/
theorem WildcardImportOrdinaryParses.value_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : WildcardImportOrdinaryParses start input left afterLeft)
    (rightParsed : WildcardImportOrdinaryParses start input right afterRight) : left = right := by
  cases leftParsed with
  | parsed _ _ leftStar leftFrom leftPath leftHiding leftTerminator =>
      cases rightParsed with
      | parsed _ _ rightStar rightFrom rightPath rightHiding rightTerminator =>
          have afterStarEq := leftStar.output_unique rightStar
          subst afterStarEq
          have afterFromEq := leftFrom.output_unique rightFrom
          subst afterFromEq
          rcases modulePathExactOutcomeSpec.successResultUnique leftPath rightPath with
            ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          rcases optionalHidingExactOutcomeSpec.successResultUnique leftHiding rightHiding with
            ⟨hidingEq, afterHidingEq⟩
          subst hidingEq
          subst afterHidingEq
          have endEq := (importTerminatorExactOutcomeSpec _).successValueUnique
            leftTerminator rightTerminator
          cases endEq
          rfl

/-- Wildcard-import success fixes the full located AST and remainder. -/
theorem WildcardImportOrdinaryParses.result_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : WildcardImportOrdinaryParses start input left afterLeft)
    (rightParsed : WildcardImportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique start rightParsed, leftParsed.output_unique start rightParsed⟩

/-- A wildcard payload fixes the first failing path, hiding, or terminator endpoint. -/
theorem WildcardImportRejects.output_unique {input left right : Remainder}
    (leftRejected : WildcardImportRejects input left)
    (rightRejected : WildcardImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [absent_conflicts_exact, ExactTokenParses.output_unique,
      modulePathExactOutcomeSpec.successOutputUnique,
      modulePathExactOutcomeSpec.rejectOutputUnique,
      modulePathExactOutcomeSpec.successRejectDisjoint,
      optionalHidingExactOutcomeSpec.successOutputUnique,
      optionalHidingExactOutcomeSpec.rejectOutputUnique,
      optionalHidingExactOutcomeSpec.successRejectDisjoint,
      ImportTerminatorRejects.output_unique]

/-- Wildcard-import payload outcomes are fully exact at a fixed outer start. -/
theorem wildcardImportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (WildcardImportOrdinaryParses start)
      WildcardImportRejects where
  toDeterministicOutcomeSpec := wildcardImportDeterministicOutcomeSpec start
  successValueUnique := WildcardImportOrdinaryParses.value_unique start
  rejectOutputUnique := WildcardImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
