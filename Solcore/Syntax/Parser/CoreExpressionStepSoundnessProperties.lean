import Solcore.Syntax.DeclarativeCoreExpressionStepGrammar
import Solcore.Syntax.Parser.CoreExpressionLayerSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionPostfixSoundnessProperties

/-!
Aggregate diagnostic reflection and exact soundness for one complete Core
expression recursion step.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- One complete expression step reflects diagnostic freedom through its
supplied atom and recursive expression parsers. -/
theorem expressionStep_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (atomReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtom nested block))
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionLayer nested block) :=
  expressionLayer_reflectsDiagnosticFreeOnSuccess nested block
    nestedReflects
    (expressionPostfix_reflectsDiagnosticFreeOnSuccess nested block
      atomReflects nestedReflects)

/-- Diagnostic-free success of one complete expression step follows the
parser-independent atom/postfix/precedence/conditional composition. -/
theorem expressionStep_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomParses nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtom nested block))
    (atomSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] →
      expressionAtom nested block input = .ok value next →
      atomParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionLayer nested block input =
      .ok value next) :
    DeclarativeGrammar.CoreExpressionStepParses atomParses nestedParses
      input.declarativeRemainder value next.declarativeRemainder := by
  let postfixParses :=
    DeclarativeGrammar.ExpressionPostfixParses atomParses nestedParses
  have postfixReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block) :=
    expressionPostfix_reflectsDiagnosticFreeOnSuccess nested block
      atomReflects nestedReflects
  have postfixSound : ∀ {postfixInput postfixNext : State}
      {expression : Expr},
      postfixNext.diagnosticsRev = [] →
      expressionPostfix nested block postfixInput =
        .ok expression postfixNext →
      postfixParses postfixInput.declarativeRemainder expression
        postfixNext.declarativeRemainder := by
    intro postfixInput postfixNext expression postfixFree postfixResult
    exact expressionPostfix_success_sound nested block atomParses nestedParses
      atomSound nestedReflects nestedSound nestedShape postfixFree
        postfixResult
  exact expressionLayer_success_sound nested block nestedParses postfixParses
    nestedReflects nestedSound postfixReflects postfixSound diagnosticFree
      result

end Solcore.Syntax.Parser
