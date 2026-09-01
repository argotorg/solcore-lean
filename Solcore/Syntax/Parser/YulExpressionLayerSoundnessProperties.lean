import Solcore.Syntax.Parser.YulExpressionCoreSoundnessProperties

/-!
Public diagnostic-free declarative bridge for the recoverable inline-Yul
expression layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The public recoverable Yul layer reflects diagnostic freedom whenever its
recursive expression parser does. -/
theorem yulExpressionLayer_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (YulExpressionInternals.layer nested) :=
  YulExpressionInternals.layer_reflectsDiagnosticFreeOnSuccess nested
    (yulExpressionCore_reflectsDiagnosticFreeOnSuccess nested nestedReflects)

/-- Every diagnostic-free public-layer success is the unchanged core success
and follows the exact literal-before-name inline-Yul grammar. -/
theorem yulExpressionLayer_success_sound
    (nested : Parser YulExpr)
    (nestedParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback : DeclarativeGrammar.YulCallArgumentsFallbackSpec nestedParses)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (rejectSound : ∀ {input failed : State} {failure : Failure},
      delimited .leftParen .rightParen true nested .yulExpression .yul input =
          .reject failure failed →
        fallback.rejects input.declarativeRemainder)
    {input next : State} {expression : YulExpr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : YulExpressionInternals.layer nested input =
      .ok expression next) :
    DeclarativeGrammar.YulExpressionCoreParses nestedParses fallback
      input.declarativeRemainder expression next.declarativeRemainder :=
  yulExpressionCore_success_sound nested nestedParses fallback nestedReflects
    nestedSound nestedShape rejectSound diagnosticFree
      (YulExpressionInternals.layer_core_of_diagnosticFree_success nested
        result diagnosticFree)

end Solcore.Syntax.Parser
