import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads
import Solcore.SourceSemantics.CoreLowering.ReachedBuiltinFragmentOutcomePorts

/-! The existing builtin producer retains its primitive path at one actual
reached caller. The state post keeps the same native fault evaluation, since
the generic Calls head post does not contain the returned native value. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBuiltinFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ExpressionFailurePostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)

/-- This packet names the actual parent evaluation and the same reached heap,
map, world and store. The original Source fault reason remains unchanged. -/
def NativeFaultAt (post : ExpressionFaultPost)
    {initialIndex : ProtectedStateTransition.Index} (_initial : callerProtocol.State initialIndex)
    (environment : Dynamic.Environment) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (actual : Environment) (ξ : Renaming) (outcome : Dynamic.ExpressionOutcome)
    {index : ProtectedStateTransition.Index} (_reached : callerProtocol.State index) : Prop :=
  match outcome with
  | .value _ => True
  | .fault reason => ∃ token,
      Evaluates actual initialIndex.store (lowered.expression.rename ξ)
        (.inLeft lowered.type (.word token)) index.store ∧
      post program context evidence source environment initialIndex.heap id reason
        index.heap token index.mapping index.world index.store

/-- Admission and the actual fault packet observe the identical returned state. -/
def StatePost (post : ExpressionFaultPost)
    {initialIndex : ProtectedStateTransition.Index} (initial : callerProtocol.State initialIndex)
    (environment : Dynamic.Environment) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (actual : Environment) (ξ : Renaming) (node : ExpressionNode) (outcome : Dynamic.ExpressionOutcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop :=
  PostAdmission bridge context node.type outcome reached ∧
  NativeFaultAt (program := program) (source := source) (context := context) evidence post initial environment id lowered actual ξ outcome reached

variable {bridge functions evidence}

/-- Determinism aligns the packet's token with a separately retained actual
parent completion. It does not infer a path from the category FaultRep. -/
theorem NativeFaultAt.at_fault {post : ExpressionFaultPost}
    {initialIndex : ProtectedStateTransition.Index} {initial : callerProtocol.State initialIndex}
    {environment : Dynamic.Environment} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {actual : Environment} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index} {value : Value}
    (packet : NativeFaultAt (program := program) (source := source) (context := context) evidence post
      initial environment id lowered actual ξ (.fault reason) reached)
    (evaluated : Evaluates actual initialIndex.store (lowered.expression.rename ξ) value index.store) :
    ∃ token, value = .inLeft lowered.type (.word token) ∧
      post program context evidence source environment initialIndex.heap id reason
        index.heap token index.mapping index.world index.store := by
  obtain ⟨token, faultEvaluation, retained⟩ := packet
  exact ⟨token, (evaluation_deterministic evaluated faultEvaluation).1, retained⟩

variable (bridge functions evidence)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked) source context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) source functions registry
    program context evidence reasonAt faults)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers transport in
/-- One builtin producer returns its complete semantic tuple and primitive path.
The actual Source trace supplies admission at the same protected transition. -/
theorem preserves
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (tree : CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked) source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (sourceTyped : ExpressionHasType source context id node.type)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ProtectedStateExpressionCallsHeads.WithFacts.PreservesResult (registry := registry) (faults := faults)
      functions callerProtocol
      (StatePost (program := program) (source := source) (context := context) bridge evidence
        (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
        initial environment id lowered actual ξ)
      initial node lowered actual ξ outcome after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ :=
    ReachedBuiltinFragmentOutcomePorts.builtin_preserves
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions extension program evidence faithful observations functionTypes
      valid reads unique missing tree found environments heaps locals agrees typed trace.sound
  obtain ⟨reached, related⟩ :=
    ProtectedStateTransition.AdministrativeTransport.transition callerProtocol transport initial maps worlds frame metadata
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame, ?_⟩
  cases outcome with
  | value sourceValue => trivial
  | fault reason =>
    obtain ⟨token, sameValue, origin⟩ := retained
    exact ⟨token, sameValue ▸ evaluated, origin⟩

include extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers transport in
/-- Native completion retains the same fault packet and reached state. Its
Source grade is reconstructed from the genuine returned Source trace. -/
theorem reflects
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (tree : CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked) source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (sourceTyped : ExpressionHasType source context id node.type)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {size : Nat} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ProtectedStateExpressionCallsHeads.WithFacts.ReflectsResult (registry := registry) (faults := faults)
      (program := program) (source := source) (context := context) functions evidence callerProtocol
      (StatePost (program := program) (source := source) (context := context) bridge evidence
        (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
        initial environment id lowered actual ξ)
      initial node id lowered environment value finalStore := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ :=
    ReachedBuiltinFragmentOutcomePorts.builtin_reflects
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions extension program evidence faithful observations functionTypes
      valid reads unique missing tree found environments heaps locals agrees typed completed.sound
  obtain ⟨sourceSize, sourceTrace⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  obtain ⟨reached, related⟩ :=
    ProtectedStateTransition.AdministrativeTransport.transition callerProtocol transport initial maps worlds frame metadata
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped sourceTrace frame, ?_⟩
  cases outcome with
  | value sourceValue => trivial
  | fault reason =>
    obtain ⟨token, sameValue, origin⟩ := retained
    exact ⟨token, sameValue ▸ completed.sound, origin⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBuiltinFaultBounds
