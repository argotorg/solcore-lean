import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexMeaning
import Solcore.SourceSemantics.CoreLowering.ReachedScalarExpressionFaultPaths
import Solcore.SourceSemantics.CoreLowering.ReachedLiteralOutcomePorts

/-! The scalar fragment derives its literal and reached read providers
internally. The existing index core receives that same richer path family. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedScalarFragmentOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

include extension in
theorem read_preserves
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals agrees trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    ReachedLoweredReadOutcomePorts.lowered_read_preserves_with_post functions extension program context evidence
      reasonAt policies unique generated found environments heaps locals agrees trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, ReachedScalarExpressionFaultPaths.prior_outcomePost retained⟩

include extension in
theorem read_reflects
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals agrees evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    ReachedLoweredReadOutcomePorts.lowered_read_reflects_with_post functions extension program context evidence
      reasonAt policies unique generated found environments heaps locals agrees evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, ReachedScalarExpressionFaultPaths.prior_outcomePost retained⟩

include extension in
theorem members_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionMembers.preserves_with_literals_and_post functions extension program evidence unique
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.preserves functions program context evidence valid unique)
    (read_preserves functions extension program evidence policies unique) ⟨tree, tree.literalSites⟩

include extension in
theorem members_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionMembers.reflects_with_literals_and_post functions extension program evidence
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.reflects functions program context evidence valid)
    (read_reflects functions extension program evidence policies unique) ⟨tree, tree.literalSites⟩

theorem scalar_terminal
    (policies : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt CompatibleExpressionIndices.SourceScalar faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, retained⟩ :=
    IndexFaultPostContracts.model_scalar_terminal functions registry program context evidence reasonAt policies
      header sourceType profile baseRep keyRep actualTyped heaps keyFound form baseTrace keyTrace
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, ReachedScalarExpressionFaultPaths.prior_outcomePost retained⟩

include extension in
theorem scalar_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionIndices.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) :=
  CompatibleExpressionIndices.preserves_with_post (functions := functions) (program := program)
    (evidence := evidence) (unique := unique)
    (ReachedLoweredReadOutcomePorts.typed_preserves_of_unrestricted
      (members_preserves functions extension program evidence valid reads unique))
    (scalar_terminal functions program evidence missing)
    (ReachedScalarExpressionFaultPaths.index_joins values functions registry program context evidence source)

include extension in
theorem scalar_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionIndices.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) :=
  CompatibleExpressionIndices.reflects_with_post (functions := functions) (program := program)
    (evidence := evidence)
    (ReachedLoweredReadOutcomePorts.typed_reflects_of_unrestricted
      (members_reflects functions extension program evidence valid reads unique))
    (scalar_terminal functions program evidence missing)
    (ReachedScalarExpressionFaultPaths.index_joins values functions registry program context evidence source)

end Solcore.SourceSemantics.CoreLowering.ReachedScalarFragmentOutcomePorts
