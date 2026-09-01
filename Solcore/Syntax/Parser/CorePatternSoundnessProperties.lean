import Solcore.Syntax.Parser.CorePatternCoreSoundnessProperties
import Solcore.Syntax.Parser.CorePatternRecoveryDiagnosticProperties

/-!
Public diagnostic reflection and exact diagnostic-free soundness for one Core
pattern recursion layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public pattern reflection follows from the two recursive components. -/
theorem patternLayer_reflectsDiagnosticFreeOnSuccess_of_components
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (patternLayer nested expression) :=
  patternLayer_reflectsDiagnosticFreeOnSuccess nested expression
    (PatternInternals.patternCore_reflectsDiagnosticFreeOnSuccess nested
      expression nestedReflects expressionReflects)

/--
Every diagnostic-free public pattern success is the unchanged Core success
and therefore follows the exact ordered independent grammar.
-/
theorem patternLayer_success_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.ConstructorArgumentsFallbackSpec nestedParses)
    (argumentsRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      PatternInternals.constructorArguments nested input =
          .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : patternLayer nested expression input = .ok value next) :
    DeclarativeGrammar.PatternLayerParses nestedParses expressionParses
      fallback input.declarativeRemainder value next.declarativeRemainder :=
  PatternInternals.patternCore_success_sound nested expression nestedParses
    expressionParses fallback argumentsRejectionSound nestedReflects
      nestedSound nestedShape expressionSound diagnosticFree
        (patternCore_of_diagnosticFree_success nested expression result
          diagnosticFree)

end Solcore.Syntax.Parser
