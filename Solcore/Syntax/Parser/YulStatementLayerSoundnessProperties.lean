import Solcore.Syntax.Parser.YulStatementCoreSoundnessProperties

/-! Exact soundness for Yul semicolon and recovery statement layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Clean concrete terminated success is exact core plus optional semicolon. -/
theorem yulStatementTerminated_success_sound_of_core
    (nested : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.YulAssignmentFallbackSpec expressionParses)
    (assignmentRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      yulAssignment input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → nested input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulStatementTerminated nested input = .ok value next) :
    DeclarativeGrammar.YulStatementTerminatedLayerParses statementParses
      expressionParses fallback input.declarativeRemainder value
        next.declarativeRemainder := by
  unfold yulStatementTerminated at result
  exact yulStatementTerminated_success_sound (yulStatementCore nested)
    (DeclarativeGrammar.YulStatementCoreParses statementParses
      expressionParses fallback)
    (fun outputFree coreResult => yulStatementCore_success_sound nested
      statementParses expressionParses fallback assignmentRejectionSound
        nestedReflects nestedSound expressionSound outputFree coreResult)
    diagnosticFree result

/-- A clean recovering-layer success is the unchanged terminated derivation. -/
theorem yulStatementLayer_success_sound
    (nested : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.YulAssignmentFallbackSpec expressionParses)
    (assignmentRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      yulAssignment input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → nested input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulStatementLayer nested input = .ok value next) :
    DeclarativeGrammar.YulStatementLayerParses statementParses
      expressionParses fallback input.declarativeRemainder value
        next.declarativeRemainder :=
  yulStatementTerminated_success_sound_of_core nested statementParses
    expressionParses fallback assignmentRejectionSound nestedReflects
      nestedSound expressionSound diagnosticFree
        (yulStatementTerminated_of_diagnosticFree_layer_success nested result
          diagnosticFree)

end Solcore.Syntax.Parser
