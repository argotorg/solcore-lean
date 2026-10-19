import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingSourceBodyLifting

/-! Original Source bodies are lifted from the actual marked parameter entry.
The resulting public invocation includes the real earlier stage stop when a
guard rejects, retaining its reached heap and the saved caller restoration. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedSourceInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header whole (Program.ofChecked whole.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan header.named.signature.key = .ok header.named.specialized)
  (sameLayouts : header.layouts = whole.indexed.layouts)
  (sameGlobals : header.globals = whole.indexed.base.globals.length)
  (sameBindings : header.bindings = header.named.inputs)
  (sameBody : header.body = generation.body)
  (sameSolved : header.solved = header.named.specialized.function.solvedRequirements)
  {invocation : Staging.Recursive.Scope}
  (selected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function invocation)
  (authority : CellAwareNamedCallPorts.Authority (compiled := whole) header.named invocation)
  (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named (diagnostics.reasonAt header.named.signature.key))
  (body : CellAwareFaultingNamedBodySupport.Body generation (CellAwareNamedBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
    header.context header.function.resultType)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  {arguments : List Dynamic.Value} {payloads : List Value}

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "instances" => GeneralizedLocalInstanceValues.model whole.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "bridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

private theorem reindex_physical
    {named : SourceCoreGeneralFunctions.Function} {context : SourceSemantics.Context}
    {first second : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    (physical : CellAwareScopePhysical.Physical whole named context first canonical mapping world before store environment)
    (same : first = second) :
    ∃ next : CellAwareScopePhysical.Physical whole named context second canonical mapping world before store environment,
      next.location = physical.location ∧ next.native = physical.native := by
  cases same
  exact ⟨physical, rfl, rfl⟩

private theorem statements : generation.statements = header.function.body := by
  have same := (RecursiveNamedPreparedSourceFrames.compiled_roots_eq generation).symm.trans
    (header.agreement.source ▸ header.agreement.roots)
  exact (List.map_inj_right (fun _ _ same => NodeId.statement.inj same)).mp same


include body record receiver extension sameLayouts sameGlobals sameBindings sameSolved selected authority issuer wellFormed in
theorem lift
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context invocation.evidence invocation.source environment bound header.function.body finalContext outcome after) :
    ∃ stagedSize stagedContext stagedOutcome reached,
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages stagedSize invocation
        header.context environment bound header.function.body stagedContext stagedOutcome reached ∧
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached := by
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      _prefixFrame, _prefixEffect, lexical, reached, _related, rows, physical, frameEq, _wrap, _unwrap⟩ :=
    CellAwareNamedEntry.prepare owner caller header capture sameLayouts sameGlobals record wellFormed
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements := by
    exact header.valid.ledger.trans sameSolved
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements := by
    obtain ⟨final, facts, typed, _completes⟩ := sourceReceipt.bodyTyped
    exact ⟨_, final, facts, by simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source] using typed⟩
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys cells
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
  rw [← statements header generation] at trace
  obtain ⟨bodyPhysical, sameLocation, sameNative⟩ := reindex_physical physical
    (show header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      CellAwareFaultingNamedBodySupport.scope header.named by rw [sameBindings]; rfl)
  have bodyReady : ProtectedStateTransition.CellAllocation.ReadyAt producer bodyPhysical.location bodyPhysical.native := by
    intro index state read
    rw [sameLocation, sameNative] at read ⊢
    exact ready state read
  have meaning := CellAwareFaultingSourceBodyLifting.lifts bridge generation record profile receiver extension authority
    wellFormed producer (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body issuer
    (size := size) (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareFaultingNamedBodySupport.scope, ← sameBindings] at meaning
  obtain ⟨stagedContext, stagedOutcome, reachedHeap, lifted, adapted⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed
      reached ⟨sourceReceipt.heapTyped, rows⟩ lexical bodyPhysical owner (sameLocation.trans frameEq).symm bodyReady trace
  have actual : Staging.Recursive.Statements (Program.ofChecked whole.sourceProgram) stages invocation
      header.context environment bound header.function.body stagedContext stagedOutcome reachedHeap := by
    simpa only [sameEnvironment, sameHeap, statements header generation] using lifted
  obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Statements.of_trace actual
  exact ⟨stagedSize, stagedContext, stagedOutcome, reachedHeap, measured, adapted⟩

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer wellFormed in
theorem preserves
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context invocation.evidence invocation.source environment bound header.function.body finalContext outcome after) :
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld reached finalStore := by
  obtain ⟨stageSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    lift profile receiver extension owner caller header capture generation record sameLayouts sameGlobals sameBindings
      sameSolved selected authority issuer body wellFormed stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨value, finalStore, finalMap, finalWorld, result, effect⟩ :=
    CellAwareFaultingNamedInvocation.preserves profile receiver extension owner caller header capture generation record sameLayouts
      sameGlobals sameBindings sameBody sameSolved selected authority issuer body wellFormed stable heapTyped argumentsTyped
      represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, adapted, result, effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedSourceInvocation
