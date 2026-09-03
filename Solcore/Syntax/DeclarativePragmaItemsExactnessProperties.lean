import Solcore.Syntax.DeclarativePragmaItemsOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact values and rejection endpoints for forward-order pragma items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem pragmaItems_present_conflicts_absent {input : Remainder}
    {kind : TokenKind}
    (present : PragmaItemsTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent present

/-- One pragma-item suffix fixes its complete source-order identifier list. -/
theorem PragmaItemsTailOrdinaryParses.value_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsTailOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsTailOrdinaryParses input right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | done leftCommaAbsent =>
      cases rightParsed <;>
        grind [pragmaItems_present_conflicts_absent]
  | trailing leftCommaSpan leftCommaPresent leftComma leftSemicolon =>
      cases rightParsed <;>
        grind [pragmaItems_present_conflicts_absent,
          ExactTokenParses.output_unique]
  | next leftCommaSpan leftCommaPresent leftComma leftSemicolonAbsent
      leftItem leftTail inductionHypothesis =>
      cases rightParsed <;>
        grind [pragmaItems_present_conflicts_absent,
          ExactTokenParses.output_unique,
          identifierExactOutcomeSpec.successResultUnique]

/-- One pragma-item suffix fixes its identifiers and final remainder. -/
theorem PragmaItemsTailOrdinaryParses.result_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsTailOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsTailOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The first rejecting pragma-item suffix stage fixes its exact endpoint. -/
theorem PragmaItemsTailRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PragmaItemsTailRejects input left)
    (rightRejected : PragmaItemsTailRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | identifierRejected leftCommaSpan leftCommaPresent leftComma
      leftSemicolonAbsent leftItem =>
      cases rightRejected <;>
        grind [ExactTokenParses.output_unique,
          identifierExactOutcomeSpec.rejectOutputUnique,
          identifierExactOutcomeSpec.successRejectDisjoint]
  | laterRejected leftCommaSpan leftCommaPresent leftComma
      leftSemicolonAbsent leftItem leftTail inductionHypothesis =>
      cases rightRejected <;>
        grind [ExactTokenParses.output_unique,
          identifierExactOutcomeSpec.successOutputUnique,
          identifierExactOutcomeSpec.successRejectDisjoint]

/-- Pragma-item suffixes have unconditionally exact ordinary outcomes. -/
theorem pragmaItemsTailExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PragmaItemsTailOrdinaryParses
      PragmaItemsTailRejects where
  toDeterministicOutcomeSpec := pragmaItemsTailDeterministicOutcomeSpec
  successValueUnique := PragmaItemsTailOrdinaryParses.value_unique
  rejectOutputUnique := PragmaItemsTailRejects.output_unique

/-- A complete pragma-item scan fixes its source-order identifier list. -/
theorem PragmaItemsOrdinaryParses.value_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [pragmaItems_present_conflicts_absent,
      identifierExactOutcomeSpec.successResultUnique,
      pragmaItemsTailExactOutcomeSpec.successValueUnique]

/-- A complete pragma-item scan fixes its identifiers and final remainder. -/
theorem PragmaItemsOrdinaryParses.result_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Complete pragma-item rejection fixes its exact first failed endpoint. -/
theorem PragmaItemsRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PragmaItemsRejects input left)
    (rightRejected : PragmaItemsRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      pragmaItemsTailExactOutcomeSpec.rejectOutputUnique]

/-- Complete pragma-item scans have unconditionally exact ordinary outcomes. -/
theorem pragmaItemsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PragmaItemsOrdinaryParses
      PragmaItemsRejects where
  toDeterministicOutcomeSpec := pragmaItemsDeterministicOutcomeSpec
  successValueUnique := PragmaItemsOrdinaryParses.value_unique
  rejectOutputUnique := PragmaItemsRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
