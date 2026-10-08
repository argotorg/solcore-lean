import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaEntryBodyContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaStaticBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedParameterReadyContinuations

/-! Genuine lambda parameter entries supply independent Source admission.
Strict members of the same flow family feed typed finish at those exact
entries; direct control transfers require no escaped token. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaBodyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
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
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed program)

/-- Runtime validity includes the original full ledger and independent Source validity. -/
def Validity (context : SourceSemantics.Context) : Prop :=
  CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence ∧
    Dynamic.SourceRuntimeValid program context function.source

/-- This is the strict flow member consumed by the original typed finish core. -/
def FlowPreserves (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (protocol headers keys) (readiness (bridge (headers := headers) (keys := keys)))
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
    (protocol headers keys) (readiness (bridge (headers := headers) (keys := keys)))
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
    functions program function.evidence (Validity (program := program) captured code)
    (source := function.source) (context := body.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := captured.administrative) size
    (scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    true function.body function.resultType code.receipt.resultCore body.flow

include beforeTyped argumentsTyped in
/-- Source allocation supplies typing at its actual parameter heap. -/
theorem source_receipt
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost) :
    SourceReceipt program function body.context entry.entry.environment entry.entry.heap :=
  SourceReceipt.of_lambda captured code history body.toContext functions entry body.frame beforeTyped argumentsTyped

include beforeTyped argumentsTyped in
/-- The native prefix retains its real raw allocation. Source typing is derived
from that allocation and the complete original ClosureFrame. -/
theorem native_receipt
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current) :
    SourceReceipt program function body.context entry.environment entry.heap := by
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq body.extended] using argumentsTyped
  have allocated := entry.allocation.preservesHeapTyping beforeTyped rawArguments
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields body.extended
  have heapTyped : Dynamic.HeapWellTyped body.context entry.heap :=
    allocated.transportClosed fields.signatures body.frame.code.closed (fields.targetClosed body.frame.code.closed)
      body.frame.code.variables_closed (fields.targetResidualVariablesOpen body.frame.code.residual_variables_open)
  have runtime := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended
  have typed := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters body.frame body.extended
  exact ⟨runtime.1, runtime.2, heapTyped, entry.locals, typed⟩

include stable in
private theorem parameter_rows {next : NativeFrame} {nextGhost : GhostFrame} {metadata : Option MetadataState}
    {final : ProtectedStateTransition.Index}
    (reached : State headers keys final)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost metadata)
    (parameters : AdministrativePreserved mapping
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))
      final.mapping final.store) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached := by
  exact CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (install caller owner.position (.stable carried)) reached
    (CallableIndexedOwnedAdmittedBodyEntries.stable_rows_install caller stable owner.position carried) parameters

private theorem body_facts {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (receipt : SourceReceipt program function body.context environment heap) :
    ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source)
      body.context true function.body function.resultType := by
  obtain ⟨final, facts, typed, _⟩ := receipt.bodyTyped
  exact ⟨body.syntaxTree, { returnType := function.resultType }, final, facts, typed⟩

include beforeTyped argumentsTyped stable wellFormed in
/-- The strict same-family flow child supplies body meaning at the actual
Source parameter entry. Typed finish closes direct transfers internally. -/
theorem source_continuation (budget : Nat)
    (below : Below budget (FlowPreserves captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys))) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history body.toContext functions owner caller budget := by
  intro entry _added _length _spine reached child strict outcome after trace
  have source := source_receipt captured code history body functions owner caller beforeTyped argumentsTyped entry
  have admitted : Admission (bridge (headers := headers) (keys := keys)) body.context reached :=
    ⟨source.heapTyped, parameter_rows owner caller stable reached entry.nextHistory entry.entry.frame⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.preserves_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := body.tree)
      (projection := body.projection) (unique := body.unique)
      (protocol headers keys) (readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
      body.emitted (Validity (program := program) captured code) child (below child strict) ⟨body.valid, source.runtime⟩
      (body_facts captured code body source)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped reached gate admitted source wellFormed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, post.forget⟩

include beforeTyped argumentsTyped stable wellFormed in
/-- Native finish consumes only strict flow members, preserving its original
measured input and independently reconstructed Source grade. -/
theorem native_continuation (budget : Nat)
    (below : Below budget (FlowReflects captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys))) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      captured code history body.toContext functions owner caller budget := by
  intro entry reached child strict value finalStore completed
  have source := native_receipt captured code history body functions owner caller beforeTyped argumentsTyped entry
  have admitted : Admission (bridge (headers := headers) (keys := keys)) body.context reached :=
    ⟨source.heapTyped, parameter_rows owner caller stable reached entry.nextHistory entry.frame⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.reflects_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (tree := body.tree)
      (projection := body.projection) (unique := body.unique)
      (protocol headers keys) (readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts function.source (expressionSyntax function.source))
      body.emitted (Validity (program := program) captured code) budget child (Nat.le_of_lt strict) below ⟨body.valid, source.runtime⟩
      (body_facts captured code body source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      entry.reference entry.read entry.unmapped reached gate admitted source wellFormed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, post.forget⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaBodyContinuations
