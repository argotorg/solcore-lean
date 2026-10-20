import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedEntry
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwareOwnedBodyRestoration
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames

/-! One genuine named invocation joins marked parameters, the actual bounded
compiler body and restoration of the saved physical caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedInvocation
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
  (body : CellAwareNamedBodySupport.Body generation (CellAwareNamedBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
    header.context header.function.resultType)
  (support : SelectedCompilationNamedSupport.Support whole)
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

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer support in
/-- The Source allocation and body trace are independent inputs. Every native
entry, body step and saved-caller restoration is constructed from the compiler. -/
theorem preserves_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
      header.context environment bound header.function.body finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, lexical, reached, related, rows, physical, frameEq, wrap, _unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record (support.certified header)
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
      CellAwareNamedBodySupport.scope header.named by rw [sameBindings]; rfl)
  have bodyReady : ProtectedStateTransition.CellAllocation.ReadyAt producer bodyPhysical.location bodyPhysical.native := by
    intro index state read
    rw [sameLocation, sameNative] at read ⊢
    exact ready state read
  have meaning := CellAwareNamedBodyMeaning.preserves_selected bridge (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    generation record profile receiver extension authority support.registryBodies producer
    (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body issuer (Nat.le_refl size)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareNamedBodySupport.scope, ← sameBindings] at meaning
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, bodyHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      lexical bodyPhysical owner (sameLocation.trans frameEq).symm bodyReady trace
  have evaluatedHeader : Evaluates entryActual entryStore (header.body.rename entryEmbedding) value bodyStore := by
    simpa only [sameBody] using evaluated
  have fullEffect := prefixEffect.trans bodyEffect
  have bodyCaller : Relates caller bodyState := related.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps fullEffect.worlds
      (prefixFrame.trans bodyFrame) bodyCaller
  have restoredEffect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState owner.position instances fullEffect
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, ⟨wrap evaluatedHeader, ?_⟩, restoredEffect⟩
  exact ⟨by simpa only [header.resultType] using result, restoredHeaps, fullEffect.maps, fullEffect.worlds,
    restoredFrame, fullEffect.metadata, returned, restoredRelated, post⟩

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer support in
/-- Actual native completion is unwrapped through the same named entry. Its
independent Source grade and concrete saved-caller post are returned together. -/
theorem reflects_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
        header.context environment bound header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, lexical, reached, related, rows, physical, frameEq, _wrap, unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record (support.certified header)
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨bodyStore, bodyEvaluation, finalEq⟩ := unwrap completed
  have compiledEvaluation : Evaluates entryActual entryStore (generation.body.rename entryEmbedding) value bodyStore := by
    simpa only [sameBody] using bodyEvaluation
  obtain ⟨nativeSize, nativeTrace⟩ := evaluation_has_size compiledEvaluation
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
  obtain ⟨bodyPhysical, sameLocation, sameNative⟩ := reindex_physical physical
    (show header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      CellAwareNamedBodySupport.scope header.named by rw [sameBindings]; rfl)
  have bodyReady : ProtectedStateTransition.CellAllocation.ReadyAt producer bodyPhysical.location bodyPhysical.native := by
    intro index state read
    rw [sameLocation, sameNative] at read ⊢
    exact ready state read
  have meaning := CellAwareNamedBodyMeaning.reflects_selected bridge (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    generation record profile receiver extension authority support.registryBodies producer
    (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body issuer (Nat.le_refl nativeSize)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareNamedBodySupport.scope, ← sameBindings] at meaning
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, matched, result, bodyHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      lexical bodyPhysical owner (sameLocation.trans frameEq).symm bodyReady nativeTrace
  have fullEffect := prefixEffect.trans bodyEffect
  have bodyCaller : Relates caller bodyState := related.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps fullEffect.worlds
      (prefixFrame.trans bodyFrame) bodyCaller
  have restoredEffect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState owner.position instances fullEffect
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨sourceSize, entryEnvironment, entryHeap, finalContext, outcome, after, finalMap, finalWorld,
    entryAllocated, ?_, matched, ?_, ?_⟩
  · simpa only [statements header generation] using trace
  · refine ⟨completed, ?_⟩
    rw [finalEq]
    exact ⟨by simpa only [header.resultType] using result, restoredHeaps, fullEffect.maps, fullEffect.worlds,
      restoredFrame, fullEffect.metadata, returned, restoredRelated, post⟩
  · rw [finalEq]
    exact restoredEffect

/- Compatibility adapters for callers with a whole-program receipt. -/
include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer wellFormed in
theorem preserves
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
      header.context environment bound header.function.body finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  apply preserves_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) <;> assumption

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer wellFormed in
theorem reflects
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
        header.context environment bound header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  apply reflects_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedInvocation
