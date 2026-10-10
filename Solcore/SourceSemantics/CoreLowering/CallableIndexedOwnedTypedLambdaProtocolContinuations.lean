import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaBodyContinuations

/-! Typed finish consumes flow under the actual caller protocol carried by its
parameter packet. A packet adds only authentic static canonical authority to
that same Entry/Prefix and base pool. Source and native finish each use one
strict flow child and the original SourceReceipt; their real returned pool is
projected forward. No arbitrary base environment acquires a canonical packet.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaProtocolContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open RecursiveNamedCatalogInvocationBounds (Below)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedOwnedTypedLambdaStaticBody.Body code program expressionSyntax certificates)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {bodyProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) bodyProtocol)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

/-- The only new packet fields are genuine states over the original parameter
indices, with a literal forward base-pool equation. No execution or grade field
is present. Concrete ordinary/Principal constructors supply these states. -/
structure Packets where
  source : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment), added.length = code.receipt.loweredParameters.length →
      entry.entry.canonical = added ++ captured.canonical →
    ∀ reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      { actual : bodyProtocol.State
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ //
        bridge.pool actual = reached }
  native : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current),
    ∀ reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      { actual : bodyProtocol.State
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ //
        bridge.pool actual = reached }

/-- Flow is indexed by the protocol which contains actual canonical authority,
rather than by every arbitrary bare base-pool environment. The retained tree,
Source/context/scope, body flow and validity remain exactly the original ones. -/
def FlowPreserves (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    bodyProtocol (readiness bridge)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
    functions program function.evidence (Validity (program := program) captured code)
    (source := function.source) (context := body.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := captured.administrative) size
    (scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    true function.body function.resultType code.receipt.resultCore body.flow

def FlowReflects (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    bodyProtocol (readiness bridge)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
    functions program function.evidence (Validity (program := program) captured code)
    (source := function.source) (context := body.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := captured.administrative) size
    (scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    true function.body function.resultType code.receipt.resultCore body.flow

private theorem project_transition {initial final : ProtectedStateTransition.Index}
    {base : State headers keys initial} {actual : bodyProtocol.State initial}
    (same : bridge.pool actual = base)
    (transition : ProtectedStateTransition.Transition bodyProtocol actual final) :
    ProtectedStateTransition.Transition (protocol headers keys) base final := by
  obtain ⟨returned, related⟩ := transition
  refine ⟨bridge.pool returned, ?_⟩
  change CallableIndexedOwnedFunctionState.Relates base (bridge.pool returned)
  simpa only [same] using bridge.related related

variable (packets : Packets (registry := registry) (arguments := arguments)
    (nativeArguments := nativeArguments) captured code history body functions bridge owner caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed program)

include stable in
private theorem parameter_rows {next : NativeFrame} {nextGhost : GhostFrame} {metadata : Option MetadataState}
    {final : ProtectedStateTransition.Index}
    (reached : State headers keys final)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost metadata)
    (parameters : AdministrativePreserved mapping
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))
      final.mapping final.store) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached :=
  CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (install caller owner.position (.stable carried)) reached
    (CallableIndexedOwnedAdmittedBodyEntries.stable_rows_install caller stable owner.position carried) parameters

private theorem body_facts {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program function body.context environment heap) :
    ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source)
      body.context true function.body function.resultType := by
  obtain ⟨final, facts, typed, _⟩ := receipt.bodyTyped
  exact ⟨body.syntaxTree, { returnType := function.resultType }, final, facts, typed⟩

include beforeTyped argumentsTyped stable wellFormed packets in
/-- The authentic Source parameter Entry acquires its real canonical packet,
then one protocol-indexed strict flow child supplies original typed finish.
Only that same returned state projects to the low-level base continuation. -/
theorem source_continuation (budget : Nat)
    (below : Below budget (FlowPreserves captured code body functions bridge
      (registry := registry) (faults := faults))) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history body.toContext functions owner caller budget := by
  intro entry added length spine reached child strict outcome after trace
  let selected := packets.source entry added length spine reached
  have source := CallableIndexedOwnedTypedLambdaBodyContinuations.source_receipt
    captured code history body functions owner caller beforeTyped argumentsTyped entry
  have admitted : Admission bridge body.context selected.val := by
    refine ⟨source.heapTyped, ?_⟩
    rw [selected.property]
    exact parameter_rows owner caller stable reached entry.nextHistory entry.entry.frame
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.preserves_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := body.tree)
      (projection := body.projection) (unique := body.unique)
      bodyProtocol (readiness bridge) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
      body.emitted (Validity (program := program) captured code) child (below child strict) ⟨body.valid, source.runtime⟩
      (body_facts captured code body source)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped selected.val gate admitted source wellFormed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, project_transition bridge selected.property post.forget⟩

include beforeTyped argumentsTyped stable wellFormed packets in
/-- The independent native Prefix has its own authentic canonical packet and
SourceReceipt. One strict native flow family feeds finish; the original reached
base pool and independent Source grade survive the forward projection. -/
theorem native_continuation (budget : Nat)
    (below : Below budget (FlowReflects captured code body functions bridge
      (registry := registry) (faults := faults))) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      captured code history body.toContext functions owner caller budget := by
  intro entry reached child strict value finalStore completed
  let selected := Packets.native (registry := registry) (arguments := arguments)
    (nativeArguments := nativeArguments) packets entry reached
  have source := CallableIndexedOwnedTypedLambdaBodyContinuations.native_receipt
    captured code history body functions owner caller beforeTyped argumentsTyped entry
  have admitted : Admission bridge body.context selected.val := by
    refine ⟨source.heapTyped, ?_⟩
    rw [selected.property]
    exact parameter_rows owner caller stable reached entry.nextHistory entry.frame
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.reflects_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := body.tree)
      (projection := body.projection) (unique := body.unique)
      bodyProtocol (readiness bridge) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
      body.emitted (Validity (program := program) captured code) budget child (Nat.le_of_lt strict) below ⟨body.valid, source.runtime⟩
      (body_facts captured code body source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      entry.reference entry.read entry.unmapped selected.val gate admitted source wellFormed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, project_transition bridge selected.property post.forget⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaProtocolContinuations
