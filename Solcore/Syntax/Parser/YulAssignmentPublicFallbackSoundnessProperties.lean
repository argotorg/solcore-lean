import Solcore.Syntax.DeclarativeYulAssignmentPublicFallbackProperties
import Solcore.Syntax.Parser.YulAssignmentRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties
import Solcore.Syntax.Parser.YulStatementBasicSoundnessProperties
import Solcore.Syntax.Parser.YulStatementCoreSoundnessProperties

/-!
Executable bridges for the concrete public inline-Yul assignment fallback.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable assignment rejection supplies the concrete unary
fallback consumed by the public Yul statement dispatcher. -/
theorem yulAssignment_publicFallback_reject_sound
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    DeclarativeGrammar.yulAssignmentPublicFallbackSpec.rejects
      input.declarativeRemainder := by
  simpa only [DeclarativeGrammar.yulAssignmentPublicFallbackSpec] using
    yulAssignment_fallback_reject_sound
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionParses
      DeclarativeGrammar.YulExpressionRejects
      DeclarativeGrammar.yulExpressionPublicDeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionParses.toOrdinary
      yulExpression_reject_sound result

/-- Every diagnostic-free executable assignment success follows the concrete
public recursive expression grammar. -/
theorem yulAssignment_success_public_sound
    {input output : State} {statement : YulStmt}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulAssignment input = .ok statement output) :
    DeclarativeGrammar.YulAssignmentParses
      DeclarativeGrammar.YulExpressionParses input.declarativeRemainder
        statement output.declarativeRemainder :=
  yulAssignment_success_sound DeclarativeGrammar.YulExpressionParses
    yulExpression_success_clean_sound diagnosticFree result

/-- Specialize the clean core statement dispatcher to the complete public
expression grammar and its concrete transactional assignment fallback. -/
theorem yulStatementCore_success_publicExpression_sound
    (nested : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input output : State} {statement : YulStmt},
      output.diagnosticsRev = [] →
        nested input = .ok statement output →
        statementParses input.declarativeRemainder statement
          output.declarativeRemainder)
    {input output : State} {statement : YulStmt}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulStatementCore nested input = .ok statement output) :
    DeclarativeGrammar.YulStatementCoreParses statementParses
      DeclarativeGrammar.YulExpressionParses
      DeclarativeGrammar.yulAssignmentPublicFallbackSpec
      input.declarativeRemainder statement output.declarativeRemainder :=
  yulStatementCore_success_sound nested statementParses
    DeclarativeGrammar.YulExpressionParses
    DeclarativeGrammar.yulAssignmentPublicFallbackSpec
    yulAssignment_publicFallback_reject_sound nestedReflects nestedSound
    yulExpression_success_clean_sound diagnosticFree result

end Solcore.Syntax.Parser
