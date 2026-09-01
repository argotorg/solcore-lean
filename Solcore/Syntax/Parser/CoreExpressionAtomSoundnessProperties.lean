import Solcore.Syntax.Parser.CoreExpressionAtomCoreSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionAtomRecoveryDiagnosticProperties

/-!
Exact diagnostic-free soundness at the public recoverable Core atom boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public atom parsing reflects diagnostic freedom through the exact ordered
Core dispatcher. -/
theorem coreExpressionAtom_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtom nested block) :=
  expressionAtom_reflectsDiagnosticFreeOnSuccess nested block
    (ExpressionAtomInternals.expressionAtomCore_reflectsDiagnosticFreeOnSuccess
      nested block nestedReflects blockReflects)

/-- Every diagnostic-free public atom success follows the exact seven-way
Core atom grammar; recovery successes are excluded. -/
theorem expressionAtom_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block)
    (blockSound : ∀ {input next : State} {value : Block},
      next.diagnosticsRev = [] → block input = .ok value next →
      blockParses input.declarativeRemainder value next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionAtom nested block input = .ok value next) :
    DeclarativeGrammar.ExpressionAtomCoreParses nestedParses blockParses
      input.declarativeRemainder value next.declarativeRemainder := by
  exact ExpressionAtomInternals.expressionAtomCore_success_sound nested block
    nestedParses blockParses nestedReflects nestedSound nestedShape
      blockReflects blockSound diagnosticFree
        (expressionAtomCore_of_diagnosticFree_success nested block result
          diagnosticFree)

end Solcore.Syntax.Parser
