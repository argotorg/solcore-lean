import Solcore.Syntax.DeclarativeNamespaceImportOutcomeProperties
import Solcore.Syntax.DeclarativeModulePathExactnessProperties
import Solcore.Syntax.DeclarativeImportTerminatorExactnessProperties

/-! Exact namespace-import aliases, paths, spans, and first-failure endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A namespace payload fixes its alias, module path, and complete covered span. -/
theorem NamespaceImportOrdinaryParses.value_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : NamespaceImportOrdinaryParses start input left afterLeft)
    (rightParsed : NamespaceImportOrdinaryParses start input right afterRight) : left = right := by
  cases leftParsed with
  | parsed _ _ _ _ leftStar leftAs leftAlias leftFrom leftPath leftTerminator =>
      cases rightParsed with
      | parsed _ _ _ _ rightStar rightAs rightAlias rightFrom rightPath rightTerminator =>
          have afterStarEq := leftStar.output_unique rightStar
          subst afterStarEq
          have afterAsEq := leftAs.output_unique rightAs
          subst afterAsEq
          rcases leftAlias.result_unique rightAlias with ⟨aliasEq, afterAliasEq⟩
          subst aliasEq
          subst afterAliasEq
          have afterFromEq := leftFrom.output_unique rightFrom
          subst afterFromEq
          rcases modulePathExactOutcomeSpec.successResultUnique leftPath rightPath with
            ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          have endEq := (importTerminatorExactOutcomeSpec _).successValueUnique
            leftTerminator rightTerminator
          cases endEq
          rfl

/-- Namespace-import success fixes the full located AST and remainder. -/
theorem NamespaceImportOrdinaryParses.result_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : NamespaceImportOrdinaryParses start input left afterLeft)
    (rightParsed : NamespaceImportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique start rightParsed, leftParsed.output_unique start rightParsed⟩

/-- Namespace-import rejection fixes the first unsuccessful stage's endpoint. -/
theorem NamespaceImportRejects.output_unique {input left right : Remainder}
    (leftRejected : NamespaceImportRejects input left)
    (rightRejected : NamespaceImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [absent_conflicts_exact, ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.rejectOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      modulePathExactOutcomeSpec.successOutputUnique,
      modulePathExactOutcomeSpec.rejectOutputUnique,
      modulePathExactOutcomeSpec.successRejectDisjoint,
      ImportTerminatorRejects.output_unique]

/-- Namespace-import payload outcomes are fully exact at a fixed outer start. -/
theorem namespaceImportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (NamespaceImportOrdinaryParses start)
      NamespaceImportRejects where
  toDeterministicOutcomeSpec := namespaceImportDeterministicOutcomeSpec start
  successValueUnique := NamespaceImportOrdinaryParses.value_unique start
  rejectOutputUnique := NamespaceImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
