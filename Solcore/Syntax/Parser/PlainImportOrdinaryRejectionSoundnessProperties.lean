import Solcore.Syntax.DeclarativePlainImportOutcomeGrammar
import Solcore.Syntax.Parser.ImportTerminatorOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ModulePath

/-! Exact executable rejection reflection for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable plain-import rejection occurs first in its module path,
or after an exact path success in its import terminator. -/
theorem plainImport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.plainImport start input =
      .reject failure rejected) :
    DeclarativeGrammar.PlainImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.plainImport at result
  cases pathResult : modulePath .importDecl input with
  | invariant error => simp [bind, pathResult] at result
  | reject pathFailure pathRejected =>
      simp only [bind, pathResult] at result
      cases result
      exact .pathRejected
        (modulePath_reject_ordinaryOutcome_sound .importDecl pathResult)
  | ok path afterPath =>
      simp only [bind, pathResult] at result
      have pathParsed :=
        modulePath_success_ordinaryOutcome_sound .importDecl pathResult
      unfold ImportInternals.finish at result
      cases terminatorResult :
          ImportInternals.terminator path.span afterPath with
      | invariant error => simp [bind, terminatorResult] at result
      | reject terminatorFailure terminatorRejected =>
          simp only [bind, terminatorResult] at result
          cases result
          exact .terminatorRejected pathParsed
            (importTerminator_reject_ordinaryOutcome_sound path.span
              terminatorResult)
      | ok endSpan afterEnd => simp [bind, terminatorResult, pure] at result

end Solcore.Syntax.Parser
