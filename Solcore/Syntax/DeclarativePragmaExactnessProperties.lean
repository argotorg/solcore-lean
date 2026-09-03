import Solcore.Syntax.DeclarativePragmaItemsExactnessProperties
import Solcore.Syntax.DeclarativePragmaOutcomeProperties

/-! Exact pragma declarations, including located names and ordered items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem pragma_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Broad pragma success fixes its marker-to-semicolon span, located name,
and complete source-order item list. -/
theorem PragmaDeclOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.PragmaDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaDeclOrdinaryParses input left afterLeft)
    (rightParsed : PragmaDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ExactTokenParses.result_unique,
      identifierExactOutcomeSpec.successResultUnique,
      pragmaItemsExactOutcomeSpec.successResultUnique]

/-- Broad pragma success fixes its complete AST and final remainder. -/
theorem PragmaDeclOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.PragmaDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaDeclOrdinaryParses input left afterLeft)
    (rightParsed : PragmaDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The prioritized first rejected pragma stage fixes its exact endpoint. -/
theorem PragmaDeclRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PragmaDeclRejects input left)
    (rightRejected : PragmaDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [pragma_absent_conflicts_exact, ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      pragmaItemsExactOutcomeSpec.successOutputUnique,
      pragmaItemsExactOutcomeSpec.successRejectDisjoint,
      pragmaItemsExactOutcomeSpec.rejectOutputUnique]

/-- Complete pragmas have unconditional exact AST, remainder, and rejection
endpoint outcomes; no diagnostic payload equality is asserted. -/
theorem pragmaDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PragmaDeclOrdinaryParses
      PragmaDeclRejects where
  toDeterministicOutcomeSpec := pragmaDeclDeterministicOutcomeSpec
  successValueUnique := PragmaDeclOrdinaryParses.value_unique
  rejectOutputUnique := PragmaDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
