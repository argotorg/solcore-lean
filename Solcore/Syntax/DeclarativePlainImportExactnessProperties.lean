import Solcore.Syntax.DeclarativePlainImportOutcomeProperties
import Solcore.Syntax.DeclarativeModulePathExactnessProperties
import Solcore.Syntax.DeclarativeImportTerminatorExactnessProperties

/-! Exact plain-import payloads with explicit and recovered terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A fixed outer start span determines the complete plain-import AST. -/
theorem PlainImportOrdinaryParses.value_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : PlainImportOrdinaryParses start input left afterLeft)
    (rightParsed : PlainImportOrdinaryParses start input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftPath leftTerminator =>
      cases rightParsed with
      | parsed rightPath rightTerminator =>
          rcases modulePathExactOutcomeSpec.successResultUnique leftPath rightPath with
            ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          have endEq := (importTerminatorExactOutcomeSpec _).successValueUnique
            leftTerminator rightTerminator
          cases endEq
          rfl

/-- Plain-import payload success fixes the full located AST and remainder. -/
theorem PlainImportOrdinaryParses.result_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : PlainImportOrdinaryParses start input left afterLeft)
    (rightParsed : PlainImportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique start rightParsed, leftParsed.output_unique start rightParsed⟩

/-- A plain-import payload has one exact first rejecting endpoint. -/
theorem PlainImportRejects.output_unique {input left right : Remainder}
    (leftRejected : PlainImportRejects input left)
    (rightRejected : PlainImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [modulePathExactOutcomeSpec.successOutputUnique,
      modulePathExactOutcomeSpec.rejectOutputUnique,
      modulePathExactOutcomeSpec.successRejectDisjoint,
      ImportTerminatorRejects.output_unique]

/-- Plain-import payload outcomes are fully exact at a fixed outer start. -/
theorem plainImportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (PlainImportOrdinaryParses start) PlainImportRejects where
  toDeterministicOutcomeSpec := plainImportDeterministicOutcomeSpec start
  successValueUnique := PlainImportOrdinaryParses.value_unique start
  rejectOutputUnique := PlainImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
