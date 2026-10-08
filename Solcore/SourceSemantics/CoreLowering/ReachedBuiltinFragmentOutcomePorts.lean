import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinMeaning
import Solcore.SourceSemantics.CoreLowering.ReachedBuiltinExpressionFaultPaths
import Solcore.SourceSemantics.CoreLowering.ReachedGeneralFragmentOutcomePorts

/-! Builtin fragment providers retain the same reached primitive packet through
ordered argument faults. Literal, read, proxy and terminal providers come from
their genuine existing certificates; the support core is used once. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedBuiltinFragmentOutcomePorts
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
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals agrees trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    ReachedScalarFragmentOutcomePorts.read_preserves functions extension program evidence policies unique generated found environments heaps locals agrees trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, ReachedBuiltinExpressionFaultPaths.prior_outcomePost retained⟩

include extension in
theorem read_reflects
    (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals agrees evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    ReachedScalarFragmentOutcomePorts.read_reflects functions extension program evidence policies unique generated found environments heaps locals agrees evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, ReachedBuiltinExpressionFaultPaths.prior_outcomePost retained⟩

variable {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include faithful functionLeaves functionTypes in
theorem general_terminal
    (policies : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, retained⟩ :=
    ReachedGeneralFragmentOutcomePorts.general_terminal functions program evidence faithful functionLeaves functionTypes policies
      header sourceType profile baseRep keyRep actualTyped heaps keyFound form baseTrace keyTrace
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, ReachedBuiltinExpressionFaultPaths.prior_outcomePost retained⟩

include extension faithful functionLeaves functionTypes in
theorem builtin_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionBuiltins.preserves_with_literals_and_post functions extension functionLeaves program evidence unique
    (ReachedBuiltinExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.index_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.builtin_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.preserves functions program context evidence valid unique)
    (read_preserves functions extension program evidence reads unique)
    (ReachedGeneralFragmentOutcomePorts.proxy_preserves functions extension program evidence unique)
    (general_terminal functions program evidence faithful functionLeaves functionTypes missing)
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes in
theorem builtin_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionBuiltins.reflects_with_literals_and_post functions extension functionLeaves program evidence
    (ReachedBuiltinExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.index_joins values functions registry program context evidence source)
    (ReachedBuiltinExpressionFaultPaths.builtin_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.reflects functions program context evidence valid)
    (read_reflects functions extension program evidence reads unique)
    (ReachedGeneralFragmentOutcomePorts.proxy_reflects functions extension program evidence)
    (general_terminal functions program evidence faithful functionLeaves functionTypes missing)
    ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.ReachedBuiltinFragmentOutcomePorts
