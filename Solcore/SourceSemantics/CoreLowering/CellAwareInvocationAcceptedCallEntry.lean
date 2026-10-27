import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedApplication

/-! The entry of a call-containing named row at the public root. It is the
body-trace counterpart of `CellAwareInvocationAcceptedNamedApplication`: the
named entry over the caller's accepted cells, the body on the slot-retaining
protocol with the body's accepted-expression meaning as input, and the restored
caller with its post-admission, packaged as the root's `NamedResultAt`, as
`CellAwareInvocationAcceptedNamedInvocation.preserves_selected` does for
first-subset rows on the plain caller protocol. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)

private theorem monomorphic_context {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context parameters types final)
    (initial : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    ∀ id scheme, (id, scheme) ∈ final.locals → scheme.quantified = [] := by
  induction extended with
  | nil => exact initial
  | @cons context binder next rest types final payload mono head tail ih =>
    apply ih
    cases head
    intro id scheme member
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [mono, TypeSystem.Scheme.mono]
    · exact initial id scheme member

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}

private theorem statements (header : Header whole (Program.ofChecked whole.sourceProgram))
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named diagnostics code) :
    generation.statements = header.function.body := by
  have same := (RecursiveNamedPreparedSourceFrames.compiled_roots_eq generation).symm.trans
    (header.agreement.source ▸ header.agreement.roots)
  exact (List.map_inj_right (fun _ _ same => NodeId.statement.inj same)).mp same

/-- Post-admission on the slot-retaining protocol is post-admission of its
plain caller pool. -/
private theorem post_base {index : ProtectedStateTransition.Index}
    {state : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State index}
    (owner : OwnedKey keys) (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
      context type outcome state) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      CallableIndexedOwnedBodyRestorationAdmission.bridge context type outcome state.base.val := by
  cases outcome with
  | value value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, post.successful⟩
    | stage scope call reason => exact post

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (header : Header whole (Program.ofChecked whole.sourceProgram))
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (sameNamed : header.named = named)
  (sameLayouts : header.layouts = whole.indexed.layouts)
  (sameGlobals : header.globals = whole.indexed.base.globals.length)
  (sameBindings : header.bindings = named.inputs)
  (sameBody : header.body = generation.body)
  (sameSolved : header.solved = named.specialized.function.solvedRequirements)
  (projection : whole.compatible.checked.catalog.project header.function.resultType = .ok named.signature.resultType)
  (support : SelectedCompilationNamedSupport.Support whole)
  (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
  (assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments)
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (body : AcceptedNamedBodyFlow.Body (rowIndex generation record).policy (rowIndex generation record).fuel
    (rowIndex generation record).compilerSource (rowIndex generation record).scope
    (rowIndex generation record).statements (rowIndex generation record).result
    (rowIndex generation record).reasonAt (rowIndex generation record).fellThrough
    (rowIndex generation record).escaped (rowIndex generation record).body)
  (covered : CellAwareInvocationAcceptedFlow.Covered (rowIndex generation record).source header.function.resultType
    (CellAwareInvocationAcceptedMatches.Admitted (rowIndex generation record))
    (CellAwareInvocationAcceptedInputs.Generalized (rowIndex generation record)) body.tree)
  (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (rowIndex generation record).scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
    (rowIndex generation record).body nativeType whole.indexed.layouts.definitions)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" =>
  CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions
local notation "accepted" => GeneralizedLocalDescriptorHeap.cellModel model
  (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True))
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved projection support
  issued assignments artifact checked covered native in
/-- A staged Source trace of a call-containing row's body determines the
native entry, body and restoration from a reached caller pool with its
physical cache and capture: the body runs on the slot-retaining protocol, and
the result is the root's `NamedResultAt` over accepted cells. -/
theorem preserves_selected {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store : Store} {canonical : Environment} (owner : OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store)
    (cache : CallableIndexedOwnedPhysicalGlobals.Authority whole mapping store)
    (stable : StableRows caller) {arguments : List Dynamic.Value} {payloads : List Value}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents accepted mapping world before store)
    {child : Staging.Recursive.Scope} (selected : (stages).Closure header.function child)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (bodyTrace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size child
      header.context environment bound header.function.body finalContext bodyOutcome after)
    (expressions : ∀ (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex generation record) stages child faults size) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        rootFunctions accepted owner caller header capture.named payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result bodyOutcome) after value finalStore finalMap finalWorld
        faults := by
  subst sameNamed
  have certified := support.certified header
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped, spine,
      prefixFrame, prefixEffect, _lexical, reached, related, rows, physical, frameEq, wrap, _unwrap⟩ :=
    CellAwareInvocationAcceptedNamedEntry.prepare owner caller header capture.named sameLayouts sameGlobals record
      certified heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap, ← statements header generation] at bodyTrace
  have sourceEq : child.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : child.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements :=
    header.valid.ledger.trans sameSolved
  obtain ⟨typingFinal, typingFacts, originalTyped, _completes⟩ := sourceReceipt.bodyTyped
  have functionTyped : StatementsHaveType (CallableIndexedNamedGeneration.source header.named)
      {returnType := header.function.resultType} header.context generation.statements typingFinal typingFacts := by
    simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source]
      using originalTyped
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements :=
    ⟨_, typingFinal, typingFacts, functionTyped⟩
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ runtime.graph.nodeOccurrencesUnique
  obtain ⟨_facts, certificate⟩ := certified
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certificate.locals_empty
  have monomorphic := monomorphic_context header.extended
    (by intro id scheme member; rw [empty] at member; cases member)
  have prefixEq : RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header =
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative := by
    simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, CellAwareNamedPreparedReceipt.administrative capture,
      header.parameterType, List.cons_append]
  rw [prefixEq] at native
  obtain ⟨added, addedLength, canonicalEq⟩ := spine
  have rowLocation : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
    (caller.rows owner.position).frame_eq
  have frameRead : store.read? owner.key.frameLocation = some (SourceCoreCallableIndexedFrames.encode
      whole.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) := by
    simpa only [rowLocation] using (caller.rows owner.position).authority.frame.read
  have scopeLength : added.length = (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length := by
    simpa only [List.length_map, List.length_reverse] using addedLength
  let initial := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine cache frameRead _ prefixFrame reached
    capture.slots (DataPatternValues.packValues payloads) scopeLength canonicalEq
  let producer := CellAwareInvocationAcceptedGlobalSlots.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) (headers := headers) (keys := keys)
    1 accepted
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index state read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read state.base.val owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CellAwareInvocationAcceptedGlobalSlots.producer,
      CellAwareInvocationAcceptedGlobalSlots.slotsProducer, CallableIndexedOwnedCellAllocationProducer.producer,
      frameEq, OwnedKey.key] using result
  let frame : ActualBodyInvocation.Frame (rowIndex generation record) :=
    ⟨physical.native, .named physical.id, CallableIndexedNamedGeneration.state header.named, physical.carried,
      .named (CallableIndexedNamedGeneration.seed whole.indexed physical.selected record), rfl, rfl⟩
  let bodyPhysical : CellAwareInvocationPhysical.Physical (attachment := fun _ _ _ => True) whole
      (rowIndex generation record)
      header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entryCanonical entryMap entryWorld entryHeap entryStore entryEnvironment :=
    CellAwareInvocationPhysical.Physical.of_monomorphic (attachment := fun _ _ _ => True) frame physical.declarations
    physical.ownership physical.sourceDeclarations physical.location physical.reference physical.read physical.unmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  have scopeEq : (rowIndex generation record).scope =
      header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) := by
    rw [sameBindings]
    rfl
  have meaning := CellAwareInvocationAcceptedFlow.body_preserves (attachment := fun _ _ _ => True)
    (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 capture.keyPhysical.locations).forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
    (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1) (rowIndex generation record) producer
    (CallableIndexedAmbient.frame_registered whole.indexed) stages child faults
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative) size
    (expressions owner capture.keyPhysical selected)
    (CellAwareInvocationAcceptedNamedInvocation.writes profile generation record issued assignments receiver
      (protocol := CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1) sourceEq
      runtime.graph.nodeOccurrencesUnique)
    artifact checked sourceEq unique (control := {returnType := header.function.resultType})
    (expected := header.function.resultType) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    functionTyped projection body covered native (Nat.le_refl size)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  rw [scopeEq] at meaning
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, bodyHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, _bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed initial
      ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready bodyTrace
  have evaluatedHeader : Evaluates entryActual entryStore (header.body.rename entryEmbedding) value bodyStore := by
    rw [sameBody]
    exact evaluated
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState.base.val owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState.base.val owner.position stable (post_base owner capture.keyPhysical bodyPost) supports restoredFrame
  exact ⟨value, _, finalMap, finalWorld, wrap evaluatedHeader, result, restoredHeaps,
    prefixEffect.maps.trans bodyMaps, worlds, restoredFrame, prefixEffect.metadata.trans bodyMetadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState.base.val owner.position, restoredRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallEntry
