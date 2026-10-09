import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyFaultBounds

/-! One actual absent local allocation precedes the supported discard/return
suffix. Static constructor receipts build the whole lexical Tree; the original
Tree and finish producers supply allocation, readiness and fault provenance. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedLexicalNamedBodyFaultBounds
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedIndirectExpressionHeads
open RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {expressionSyntax : ExpressionId → Prop}
  {id : StatementId} {node : StatementNode} {binder : TypedBinder}
  {nextContext : SourceSemantics.Context} {rest : List StatementId} {payload : Ty} {suffixFlow : Expr}
  (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts header.owner header.active
    (GenericLexicalStatements.absentRequest header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) binder payload))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame
    header.globals (compiled.indexed.layouts.allocatorAt header.owner header.active header.onError)
    (GenericLexicalStatements.absentRequest header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) binder payload))
  (validity : SourceSemantics.Context → Prop)

/-- Every field refers to the same Header, binder and actual allocator layout.
The suffix has static certificates; no expression or body semantics is supplied. -/
structure AbsentInputs : Prop where
  body : header.function.body = id :: rest
  found : header.function.source.lookupStatement? id = some node
  form : node.form = .letDecl binder none
  declaration : SourceCoreDataPlaces.rootBinder header.function.source binder.id = .ok binder
  monomorphic : binder.scheme.quantified = []
  extended : BinderExtends header.function.source.owner header.context binder nextContext
  ordinary : header.function.source.inputs.any (fun input => decide (input.id = binder.id)) = false
  projected : compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload
  same : annotation.original = allocation.expression
  suffixProfile : DiscardReturnProfile header.function.source rest
  suffixSyntax : GenericLexicalStatements.Syntax header.function.source expressionSyntax nextContext true
    rest header.function.resultType
  suffixTree : GenericLexicalStatements.Tree compiled.indexed.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source certificates nextContext
    ((binder.id, payload) :: header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
    rest header.function.resultType header.output suffixFlow
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok (.letE annotation.expression suffixFlow)
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output
  valid : validity header.context
  contexts : ∀ context, validity context → StaticContext (compiled := compiled) (program := program)
    (registry := registry) (faults := faults) (source := header.function.source) (certificates := certificates)
    functions header.function.evidence context
  extend : ∀ {context nextContext binder}, validity context →
    BinderExtends header.function.source.owner context binder nextContext → validity nextContext

variable (inputs : AbsentInputs (functions := functions) (registry := registry) (faults := faults)
  (certificates := certificates) (expressionSyntax := expressionSyntax) (id := id) (node := node)
  (nextContext := nextContext) (rest := rest) (suffixFlow := suffixFlow) allocation annotation validity)

include inputs in
/-- Only the genuine absent-let constructors are added to the static suffix.
Its real accepted flow remains indexed by the actual annotation expression. -/
theorem static_inputs :
    StaticBodyInputs (functions := functions) (header := header) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (flow := .letE annotation.expression suffixFlow) validity := by
  refine {
    syntaxTree := ?_
    tree := ?_
    accepted := inputs.accepted
    generated := inputs.generated
    projection := inputs.projection
    valid := inputs.valid
    contexts := inputs.contexts
    extend := inputs.extend }
  · rw [inputs.body]
    exact .uninitialized inputs.found inputs.form inputs.declaration inputs.monomorphic inputs.extended
      inputs.ordinary inputs.suffixSyntax
  · rw [inputs.body]
    exact .uninitialized inputs.found inputs.form inputs.monomorphic inputs.extended inputs.ordinary
      inputs.projected allocation annotation inputs.same inputs.suffixTree

variable
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) (wellFormed : ProgramWellFormed program)
  {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (sourceReceipt : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- The original lexical allocation/readiness and finish producers run once.
The genuine fault post stays at the returned bodyStore. -/
theorem source_body_with_post (size : Nat) :
    SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size :=
  CallableIndexedOwnedLexicalNamedBodyFaultBounds.source_body_with_post.with_static functions validity entry reached
    extension faithful observations functionTypes wellFormed sourceReceipt rows stable
    (static_inputs functions allocation annotation validity inputs) size

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Native reflection selects the actual allocation suffix completion; its
Source grade is reconstructed independently by the shared lexical producer. -/
theorem native_body_with_post (size : Nat) :
    NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size :=
  CallableIndexedOwnedLexicalNamedBodyFaultBounds.native_body_with_post.with_static functions validity entry reached
    extension faithful observations functionTypes wellFormed sourceReceipt rows stable
    (static_inputs functions allocation annotation validity inputs) size

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
theorem source_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions allocation annotation validity inputs extension faithful observations
    functionTypes wellFormed entry reached sourceReceipt rows stable child

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
theorem native_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions allocation annotation validity inputs extension faithful observations
    functionTypes wellFormed entry reached sourceReceipt rows stable child

section Parameters
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {parameterArguments : List Dynamic.Value}
  (parameters : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    functions owner argumentsPool header parameterArguments)

include inputs parameters extension faithful observations functionTypes wellFormed in
/-- The actual parameter receipt supplies native frame/read facts, deep Source
admission, all live rows and its stable hook at this same body entry. -/
theorem source_at_parameters (size : Nat) :
    SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) parameters.body parameters.reached size :=
  source_body_with_post functions allocation annotation validity inputs extension faithful observations
    functionTypes wellFormed parameters.body parameters.reached
    (parameters.source wellFormed) parameters.rows parameters.stable_owner size

include inputs parameters extension faithful observations functionTypes wellFormed in
theorem native_at_parameters (size : Nat) :
    NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) parameters.body parameters.reached size :=
  native_body_with_post functions allocation annotation validity inputs extension faithful observations
    functionTypes wellFormed parameters.body parameters.reached
    (parameters.source wellFormed) parameters.rows parameters.stable_owner size
end Parameters

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds
