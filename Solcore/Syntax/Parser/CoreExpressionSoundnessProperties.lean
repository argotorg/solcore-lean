import Solcore.Syntax.DeclarativeCoreExpressionGrammar
import Solcore.Syntax.Parser.CoreExpressionAtomSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionStepSoundnessProperties

/-!
Aggregate diagnostic reflection and exact declarative soundness for one
concrete Core expression recursion layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A concrete Core expression layer reflects through its supplied recursive
expression and block parsers. -/
theorem coreExpressionStep_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block) :
    Parser.ReflectsDiagnosticFreeOnSuccess (expressionLayer nested block) :=
  expressionStep_reflectsDiagnosticFreeOnSuccess nested block
    (coreExpressionAtom_reflectsDiagnosticFreeOnSuccess nested block
      nestedReflects blockReflects)
    nestedReflects

/-- Every diagnostic-free success of one concrete Core expression layer
follows the exact atom, postfix, precedence, and conditional grammar. -/
theorem coreExpressionStep_success_sound
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
    (result : expressionLayer nested block input = .ok value next) :
    DeclarativeGrammar.CoreExpressionStepWithBlockParses nestedParses
      blockParses input.declarativeRemainder value
        next.declarativeRemainder := by
  apply expressionStep_success_sound nested block
    (DeclarativeGrammar.ExpressionAtomCoreParses nestedParses blockParses)
    nestedParses
    (coreExpressionAtom_reflectsDiagnosticFreeOnSuccess nested block
      nestedReflects blockReflects)
    (fun atomFree atomResult =>
      expressionAtom_success_sound nested block nestedParses blockParses
        nestedReflects nestedSound nestedShape blockReflects blockSound
          atomFree atomResult)
    nestedReflects nestedSound nestedShape diagnosticFree result

end Solcore.Syntax.Parser
