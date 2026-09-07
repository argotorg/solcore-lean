import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar
import Solcore.Syntax.Term

/-! Parser-independent expression trace assumptions for compositional laws.
Existence is separate from exactness; neither asserts a concrete implementation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

structure ExpressionTraceExactOutcomeSpec
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (expressionRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop where
  successResultUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    expressionTrace source endByte input left afterLeft leftTrace →
    expressionTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace
  rejectResultUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    expressionRejects source endByte input afterLeft leftReport leftTrace →
    expressionRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace
  successRejectDisjoint : ∀ {input rejected diagnostic trace},
    expressionRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, expressionTrace source endByte input value output events

def ExpressionTraceOutcomeExists
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (expressionRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop :=
  ∀ input, (∃ value output trace, expressionTrace source endByte input value output trace) ∨
    (∃ rejected diagnostic trace, expressionRejects source endByte input rejected diagnostic trace)

end Solcore.Syntax.DeclarativeGrammar
