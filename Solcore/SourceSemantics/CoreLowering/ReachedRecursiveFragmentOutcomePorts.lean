import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursiveMeaning
import Solcore.SourceSemantics.CoreLowering.ReachedScalarFragmentOutcomePorts

/-! Recursive support derives its literal, read and Members providers internally.
The same existing support induction retains the actual primitive fault path. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedRecursiveFragmentOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

include extension in
theorem recursive_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionRecursive.preserves_with_literals_and_post functions extension program evidence unique
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.preserves functions program context evidence valid unique)
    (ReachedScalarFragmentOutcomePorts.read_preserves functions extension program evidence policies unique)
    ⟨tree, tree.literalSites⟩

include extension in
theorem recursive_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionRecursive.reflects_with_literals_and_post functions extension program evidence
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.reflects functions program context evidence valid)
    (ReachedScalarFragmentOutcomePorts.read_reflects functions extension program evidence policies unique)
    ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.ReachedRecursiveFragmentOutcomePorts
