import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedCatalogBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds

/-! A genuine public parameter entry supplies the original Source receipt and
its chosen compiler flow. The existing finish proofs retain that same reached
pool, while successful Source body typing supplies its exact PostAdmission. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame GhostFrame)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedPublicPreparedSourceSites (Validity)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {protocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (issued : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}









variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends ((SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer protocol header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)}
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.original.prepared.compilation.own.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.original.prepared.compilation.own.assignments reason token → faults reason token)


open RecursiveNamedCatalogInvocationBounds (BodyState)
open RecursiveNamedCatalogNativeContexts (Complete)
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : Complete (prepared := compiled.indexed.ancestry) (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked))
    (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked))
    (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) headers owner.key.locations 0 functions registry header arguments before initialStore
    mapping world administrative actualContext actual ξ frameLocation current ghost)
  (sourceReceipt : SourceReceipt (Program.ofChecked compiled.sourceProgram) header.function header.context entry.environment entry.heap)
  (children : CallableIndexedOwnedNamedTokenProfileExtraction.Children
    (header := header) (headers := headers) (expressionSyntax := expressionSyntax) compilation (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (initial : protocol.State ⟨(RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (stable : StableRows (bridge.pool initial))
  (gate : condition frameLocation current)
  (escapedFault : faults .controlEscapedFunction header.escaped)

/-- Every clause describes this body's actual returned state. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld header.function.resultType header.output faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
    AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
    TypedMixedNamedBody.ReachedExit compiled.compatible.checked ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      (Program.ofChecked compiled.sourceProgram) header.function header.context (RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header) entry.environment entry.heap after outcome ∧
    ∃ reached : protocol.State ⟨(RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header), finalMap, finalWorld, after, finalStore, entry.canonical⟩,
      protocol.Relates initial reached ∧ PostAdmission bridge header.context header.function.resultType outcome reached

variable (interpretations : ∀ receipt : CallableIndexedOwnedPublicCatalogPreparedReceipts.CatalogReceipt
    (headers := headers) (compilation := compilation) (expressionSyntax := expressionSyntax)
    (administrative := administrative) issued,
  ∀ context, Validity header context →
    CallableIndexedOwnedPublicPreparedAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (factory := AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)
      (faults := faults) (registry := registry) header bridge issued functions table)

include extension faithful observations producer acquire transport bindings wellFormed diagnosticsFound rebuilt
  operandIncluded unaryIncluded complete sourceReceipt children stable gate escapedFault interpretations in
theorem preserves_at_entry (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ context, Validity header context → RecursiveNamedHeaderContracts.AtMost budget
      (fun child => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults child))
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size header.function header.context
      entry.environment entry.heap outcome after) :
    ∃ value finalStore,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      ResultAt (faults := faults) header bridge functions owner entry initial outcome after value finalStore := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPublicCatalogPreparedReceipts.at_entry
    functions owner complete entry issued wellFormed children
  have flow := CallableIndexedOwnedPublicPreparedCatalogBounds.preserves_flow
    (header := header) (bridge := bridge) (issued := issued) (functions := functions)
    (extension := extension) (faithful := faithful) (observations := observations) (condition := condition)
    (producer := producer) (acquire := acquire) (transport := transport) (bindings := bindings)
    (wellFormed := wellFormed) (sourceRuntime := sourceReceipt.runtime) (diagnosticsFound := diagnosticsFound)
    (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded)
    (receipt := receipt) (interprets := interpretations receipt) budget meaning
  have admitted : Admission bridge header.context initial := ⟨sourceReceipt.heapTyped, stable⟩
  have reference : entry.canonical[(RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
    simpa only [RecursiveNamedCatalogNativeContexts.bodyScope, List.length_map, List.length_reverse] using entry.reference
  have unmapped : frameLocation ∉ entry.mapping :=
    Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame) entry.catalog.authority.unmapped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, lexical, reached, related, _post⟩ :=
    RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when
      (functions := functions) (program := (Program.ofChecked compiled.sourceProgram)) (tree := receipt.extracted.original.original.original.original.tree)
      (projection := issued.original.aligned.projection) (unique := header.unique) (escapedFault := escapedFault)
      protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
      receipt.finished (Validity header) size (flow size within)
      (CallableIndexedOwnedPublicPreparedSourceSites.validity_at header sourceReceipt.runtime)
      (CallableIndexedOwnedPublicPreparedSourceSites.body_facts header sourceReceipt children.syntaxTree)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped reference entry.state.read unmapped initial gate admitted trace
  refine ⟨value, finalStore, evaluated, finalMap, finalWorld, represented, heaps, maps, worlds, frame, metadata, lexical, reached, related, ?_⟩
  exact ⟨StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) stable frame,
    sourceReceipt.after_body_values wellFormed trace⟩

include extension faithful observations producer acquire transport bindings wellFormed diagnosticsFound rebuilt
  operandIncluded unaryIncluded complete sourceReceipt children stable gate escapedFault interpretations in
theorem reflects_at_entry (budget size : Nat) (within : size ≤ budget)
    (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity header context → RecursiveNamedBoundedContracts.Below budget
      (fun child => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults child))
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      ResultAt (faults := faults) header bridge functions owner entry initial outcome after value finalStore := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPublicCatalogPreparedReceipts.at_entry
    functions owner complete entry issued wellFormed children
  have flow := CallableIndexedOwnedPublicPreparedCatalogBounds.reflects_flow
    (header := header) (bridge := bridge) (issued := issued) (functions := functions)
    (extension := extension) (faithful := faithful) (observations := observations) (condition := condition)
    (producer := producer) (acquire := acquire) (transport := transport) (bindings := bindings)
    (wellFormed := wellFormed) (sourceRuntime := sourceReceipt.runtime) (diagnosticsFound := diagnosticsFound)
    (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded)
    (receipt := receipt) (interprets := interpretations receipt) budget functionTypes reflection
  have admitted : Admission bridge header.context initial := ⟨sourceReceipt.heapTyped, stable⟩
  have reference : entry.canonical[(RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
    simpa only [RecursiveNamedCatalogNativeContexts.bodyScope, List.length_map, List.length_reverse] using entry.reference
  have unmapped : frameLocation ∉ entry.mapping :=
    Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame) entry.catalog.authority.unmapped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, lexical, reached, related, _post⟩ :=
    RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when
      (functions := functions) (program := (Program.ofChecked compiled.sourceProgram)) (tree := receipt.extracted.original.original.original.original.tree)
      (projection := issued.original.aligned.projection) (unique := header.unique) (escapedFault := escapedFault)
      protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
      receipt.finished (Validity header) budget size within flow
      (CallableIndexedOwnedPublicPreparedSourceSites.validity_at header sourceReceipt.runtime)
      (CallableIndexedOwnedPublicPreparedSourceSites.body_facts header sourceReceipt children.syntaxTree)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped reference entry.state.read unmapped initial gate admitted completed
  refine ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, represented, heaps, maps, worlds, frame, metadata, lexical, reached, related, ?_⟩
  exact ⟨StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) stable frame,
    sourceReceipt.after_body_values wellFormed trace⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedBodyBounds
