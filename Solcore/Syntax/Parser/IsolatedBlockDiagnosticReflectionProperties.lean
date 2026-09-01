import Solcore.Syntax.Parser.Block
import Solcore.Syntax.Parser.DiagnosticReflectionProperties

/-! Backward diagnostic reflection through balanced block isolation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Block isolation cannot hide an incoming diagnostic.  In the direct branch this
follows from the nested parser contract.  In the captured branch the child
starts with an empty accumulator, its diagnostics are appended to the parent
accumulator, and rejection recovery emits a fresh diagnostic.
-/
theorem isolateBlock_reflectsDiagnosticFreeOnSuccess
    (parser : Parser Block)
    (parserReflects : Parser.ReflectsDiagnosticFreeOnSuccess parser) :
    Parser.ReflectsDiagnosticFreeOnSuccess (isolateBlock parser) := by
  intro input body next result diagnosticFree
  unfold isolateBlock at result
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact parserReflects input body next result diagnosticFree
  | some captured =>
      simp only [captureResult] at result
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | ok childBody childAfter =>
          simp only [childResult] at result
          cases result
          simp [State.mergeDiagnostics] at diagnosticFree
          exact diagnosticFree.2
      | reject failure childAfter =>
          simp only [childResult] at result
          cases result
          simp [State.emit] at diagnosticFree
      | invariant error =>
          simp [childResult] at result

end Solcore.Syntax.Parser
