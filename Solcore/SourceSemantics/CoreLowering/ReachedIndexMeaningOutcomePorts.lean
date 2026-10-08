import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexMeaning

/-! Concrete finite terminal and Source joins are derived internally. The
fragment retains its genuine independent meaning until its original fold is
connected to the same reached post family. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedIndexMeaningOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts IndexFaultPostContracts

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

theorem scalar_preserves_with_reached_diagnostics
    (unique : NodeOccurrencesUnique source)
    (fragment : TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry))
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionIndices.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  exact CompatibleExpressionIndices.preserves_with_post (functions := functions) (program := program)
    (evidence := evidence) (unique := unique) fragment
    (model_scalar_terminal functions registry program context evidence reasonAt policies)
    (model_index_joins functions registry program context evidence)

theorem scalar_reflects_with_reached_diagnostics
    (fragment : TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry))
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionIndices.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  exact CompatibleExpressionIndices.reflects_with_post (functions := functions) (program := program)
    (evidence := evidence) fragment
    (model_scalar_terminal functions registry program context evidence reasonAt policies)
    (model_index_joins functions registry program context evidence)

theorem general_preserves_with_reached_diagnostics
    (unique : NodeOccurrencesUnique source)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (fragment : TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionTyped.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry))
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleGeneralIndex.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  exact CompatibleGeneralIndex.preserves_with_post (functions := functions) (program := program)
    (evidence := evidence) (unique := unique) fragment
    (model_general_terminal functions registry program context evidence reasonAt faithful functionLeaves functionTypes policies)
    (model_index_joins functions registry program context evidence)

theorem general_reflects_with_reached_diagnostics
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (fragment : TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionTyped.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry))
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleGeneralIndex.Tree fuel values source context solved reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  exact CompatibleGeneralIndex.reflects_with_post (functions := functions) (program := program)
    (evidence := evidence) fragment
    (model_general_terminal functions registry program context evidence reasonAt faithful functionLeaves functionTypes policies)
    (model_index_joins functions registry program context evidence)

end Solcore.SourceSemantics.CoreLowering.ReachedIndexMeaningOutcomePorts
