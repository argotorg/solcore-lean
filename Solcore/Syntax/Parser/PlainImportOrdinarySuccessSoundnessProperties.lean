import Solcore.Syntax.DeclarativePlainImportOutcomeGrammar
import Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.ModulePathOrdinarySuccessSoundnessProperties

/-! Broad ordinary-success reflection for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable plain-import success preserves its exact module path,
ordinary terminator outcome, AST span, and final remainder. -/
theorem plainImport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ImportDecl}
    (result : ImportInternals.plainImport start input =
      .ok declaration output) :
    DeclarativeGrammar.PlainImportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold ImportInternals.plainImport at result
  cases pathResult : modulePath .importDecl input with
  | invariant error => simp [bind, pathResult] at result
  | reject failure rejected => simp [bind, pathResult] at result
  | ok path afterPath =>
      simp only [bind, pathResult] at result
      have pathParsed :=
        modulePath_success_ordinaryOutcome_sound .importDecl pathResult
      unfold ImportInternals.finish at result
      cases terminatorResult :
          ImportInternals.terminator path.span afterPath with
      | invariant error => simp [bind, terminatorResult] at result
      | reject failure rejected => simp [bind, terminatorResult] at result
      | ok endSpan afterEnd =>
          simp only [bind, terminatorResult] at result
          cases result
          exact .parsed pathParsed
            (importTerminator_success_ordinaryOutcome_sound path.span
              terminatorResult)

end Solcore.Syntax.Parser
