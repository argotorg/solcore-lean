import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementHead

/-! Authentication of the production absent-RHS callback. The original
binary policy is deliberately separate so existing extraction APIs are unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

abbrev Policy (policy : SourceCoreLoops.Policy) (values : ValuesContext)
    (invalidProjection invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) : Prop :=
  policy.assignBitNotWithExpression = some (fun expression fuel source scope site assignment output next reasonAt =>
    lower values values.checked.signatures expression fuel source scope site assignment .equal none output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root)
      (missingDefault site assignment.target.root))
end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
