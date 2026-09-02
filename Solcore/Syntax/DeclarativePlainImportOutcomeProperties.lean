import Solcore.Syntax.DeclarativeImportTerminatorOutcomeProperties
import Solcore.Syntax.DeclarativeModulePathOutcomeProperties
import Solcore.Syntax.DeclarativePlainImportOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem importTerminator_output_unique_anyLast
    {leftLast rightLast : SourceSpan}
    {input afterLeft afterRight : Remainder}
    {leftEnd rightEnd : SourceSpan}
    (leftParsed : ImportTerminatorOrdinaryParses leftLast input leftEnd
      afterLeft)
    (rightParsed : ImportTerminatorOrdinaryParses rightLast input rightEnd
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | semicolon leftSpan leftSemicolon =>
      cases rightParsed with
      | semicolon rightSpan rightSemicolon =>
          rw [leftSemicolon.2, rightSemicolon.2]
      | recovered rightAbsent rightStarts =>
          exact False.elim (rightAbsent ⟨leftEnd, leftSemicolon.1⟩)
  | recovered leftAbsent leftStarts =>
      cases rightParsed with
      | semicolon rightSpan rightSemicolon =>
          exact False.elim (leftAbsent ⟨rightEnd, rightSemicolon.1⟩)
      | recovered rightAbsent rightStarts => rfl

/-- Ordinary plain-import payloads have one final remainder. -/
theorem PlainImportOrdinaryParses.output_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder}
    {left right : Syntax.ImportDecl}
    (leftParsed : PlainImportOrdinaryParses start input left afterLeft)
    (rightParsed : PlainImportOrdinaryParses start input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftPath leftTerminator =>
      cases rightParsed with
      | parsed rightPath rightTerminator =>
          have afterPathEq :=
            modulePathDeterministicOutcomeSpec.successOutputUnique leftPath
              rightPath
          subst afterPathEq
          exact importTerminator_output_unique_anyLast leftTerminator
            rightTerminator

/-- Exact plain-import rejection excludes every ordinary success. -/
theorem PlainImportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : PlainImportRejects input rejected) :
    ¬ ∃ declaration output,
      PlainImportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulPath successfulTerminator =>
      cases rejection with
      | pathRejected pathRejected =>
          exact modulePathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, successfulPath⟩
      | terminatorRejected rejectedPath terminatorRejected =>
          have afterPathEq :=
            modulePathDeterministicOutcomeSpec.successOutputUnique
              rejectedPath successfulPath
          subst afterPathEq
          exact (importTerminatorDeterministicOutcomeSpec _)
            |>.successRejectDisjoint terminatorRejected
              ⟨_, _, successfulTerminator⟩

/-- Plain import payloads have deterministic and exclusive broad ordinary
outcomes for each fixed outer start span. -/
theorem plainImportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (PlainImportOrdinaryParses start)
      PlainImportRejects where
  successOutputUnique := PlainImportOrdinaryParses.output_unique start
  successRejectDisjoint := PlainImportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
