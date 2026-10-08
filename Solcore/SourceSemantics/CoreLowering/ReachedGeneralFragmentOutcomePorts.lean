import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralMeaning
import Solcore.SourceSemantics.CoreLowering.ReachedRecursiveFragmentOutcomePorts

/-! The General fragment obtains every primitive provider from the actual
read, proxy, Recursive and index certificates. The existing support fold carries
the same fault post through its ordered children. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedGeneralFragmentOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

include extension in
/-- The original proxy meaning with a false fault relation excludes only the
actual impossible alternative. Its full value tuple is kept. -/
theorem proxy_preserves (unique : NodeOccurrencesUnique source) {post : ExpressionFaultPost} :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionProxies.Certificate values source) faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata⟩ :=
    CompatibleExpressionProxies.preserves functions extension program context evidence unique
      (fun _ _ => False) generated found environments heaps locals agrees actualTyped trace
  cases represented with
  | value related =>
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .value related,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault impossible => exact False.elim impossible

include extension in
/-- Proxy completion retains the original independent Source trace. No Source
uniqueness premise is added to the generic reflection core. -/
theorem proxy_reflects {post : ExpressionFaultPost} :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionProxies.Certificate values source) faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata⟩ :=
    CompatibleExpressionProxies.reflects functions extension program context evidence
      (fun _ _ => False) generated found environments heaps locals agrees actualTyped evaluated
  cases represented with
  | value related =>
    exact ⟨_, after, finalMap, finalWorld, trace, .value related,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault impossible => exact False.elim impossible

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
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, retained⟩ :=
    IndexFaultPostContracts.model_general_terminal functions registry program context evidence reasonAt
      faithful functionLeaves functionTypes policies header sourceType profile baseRep keyRep
      actualTyped heaps keyFound form baseTrace keyTrace
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps,
    worlds, frame, functional, trace, ReachedScalarExpressionFaultPaths.prior_outcomePost retained⟩

include extension faithful functionLeaves functionTypes in
theorem general_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionGeneral.preserves_with_literals_and_post functions extension program evidence unique
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.index_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.preserves functions program context evidence valid unique)
    (ReachedScalarFragmentOutcomePorts.read_preserves functions extension program evidence reads unique)
    (proxy_preserves functions extension program evidence unique)
    (general_terminal functions program evidence faithful functionLeaves functionTypes missing)
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes in
theorem general_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry
      program context evidence reasonAt faults) :
    TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt) faults
      (ReachedScalarExpressionFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered tree
  exact CompatibleExpressionGeneral.reflects_with_literals_and_post functions extension program evidence
    (ReachedScalarExpressionFaultPaths.sequence_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.composition_joins values.checked functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.constructor_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.member_joins values functions registry program context evidence source)
    (ReachedScalarExpressionFaultPaths.index_joins values functions registry program context evidence source)
    (ReachedLiteralOutcomePorts.reflects functions program context evidence valid)
    (ReachedScalarFragmentOutcomePorts.read_reflects functions extension program evidence reads unique)
    (proxy_reflects functions extension program evidence)
    (general_terminal functions program evidence faithful functionLeaves functionTypes missing)
    ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.ReachedGeneralFragmentOutcomePorts
