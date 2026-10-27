import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedEntry
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectCalls
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedGlobalSlots
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedPreparedReceipt

/-! The row lemma of direct calls: the application input of
`CellAwareInvocationAcceptedDirectCalls` comes from the callee's own accepted
body. The named entry runs over the caller's accepted cells
(`CellAwareInvocationAcceptedNamedEntry.prepare`); its parameter spine and the
caller's physical cache and capture slots give the body a state of the
slot-retaining protocol (`CallableIndexedOwnedPhysicalCanonicalState`), on
which the accepted flow runs with the cell producer of
`CellAwareInvocationAcceptedGlobalSlots`. The entry, body and restoration
effects compose. The body's accepted-expression meaning below the grade is the
only expression input; the size induction across bodies supplies it. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedApplication
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
  issued assignments artifact checked covered native wellFormed in
/-- The callee row's accepted body discharges the application input of the
direct-call head at a Source grade, given the meaning of the body's accepted
expressions below that grade on the slot-retaining protocol. -/
theorem preserves (size : Nat)
    (expressions : ∀ (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex generation record) stages child faults size) :
    CellAwareInvocationAcceptedDirectCalls.PreservesAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size := by
  subst sameNamed
  intro scope mapping world before store canonical owner caller capture cache _member stable context arguments
    payloads _supports heapTyped argumentsTyped represented heaps rawD function sourceAt invocation outcome after trace
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨bodySize, child, bodyEnvironment, bound, finalContext, bodyOutcome, selected, allocated, bodyTrace,
      converted, smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix sourceAt wellFormed arity trace
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
    functionTyped projection body covered native (Nat.le_of_lt smaller)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  rw [scopeEq] at meaning
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, bodyHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, _bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed initial
      ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready bodyTrace
  have evaluatedHeader : Evaluates entryActual entryStore (header.body.rename entryEmbedding) value bodyStore := by
    rw [sameBody]
    exact evaluated
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq, ← CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq converted] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState.base.val owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  have effect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState.base.val owner.position
    (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True)) (prefixEffect.trans bodyEffect)
  exact ⟨value, _, finalMap, finalWorld, wrap evaluatedHeader, result, restoredHeaps,
    prefixEffect.maps.trans bodyMaps, worlds, restoredFrame, prefixEffect.metadata.trans bodyMetadata, effect,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState.base.val owner.position, restoredRelated⟩

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved projection support
  issued assignments artifact checked covered native in
/-- Native completion of the callee row's closure body reconstructs the staged
application at an independent grade, given the native meaning of the body's
accepted expressions below the native grade of the closure body. The callee's
own registry scope is a row receipt. -/
theorem reflects (size : Nat) {bodyScope : Staging.Recursive.Scope}
    (bodySelected : (stages).Closure header.function bodyScope)
    (expressions : ∀ (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex generation record) stages child faults size) :
    CellAwareInvocationAcceptedDirectCalls.ReflectsAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size := by
  subst sameNamed
  intro scope mapping world before store canonical owner caller capture cache _member stable context arguments
    payloads _supports heapTyped argumentsTyped represented heaps rawD function sourceAt invocation value finalStore
    completed
  have certified := support.certified header
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped, spine,
      prefixFrame, prefixEffect, _lexical, reached, related, rows, physical, frameEq, _wrap, unwrap⟩ :=
    CellAwareInvocationAcceptedNamedEntry.prepare owner caller header capture.named sameLayouts sameGlobals record
      certified heapTyped argumentsTyped represented heaps stable
  obtain ⟨bodySize, reachedStore, bodyLess, bodyEvaluation, finalEq⟩ := unwrap completed
  have compiledEvaluation : EvaluationSize bodySize entryActual entryStore (generation.body.rename entryEmbedding)
      value reachedStore := by
    rw [← sameBody]
    exact bodyEvaluation
  have sourceEq : bodyScope.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source bodySelected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : bodyScope.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence bodySelected] using
      sourceReceipt.covers
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
  have unique : NodeOccurrencesUnique bodyScope.source := sourceEq ▸ runtime.graph.nodeOccurrencesUnique
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
  have meaning := CellAwareInvocationAcceptedFlow.body_reflects (attachment := fun _ _ _ => True)
    (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 capture.keyPhysical.locations).forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
    (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1) (rowIndex generation record) producer
    (CallableIndexedAmbient.frame_registered whole.indexed) stages bodyScope faults
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative) size
    (expressions owner capture.keyPhysical bodySelected)
    (CellAwareInvocationAcceptedNamedInvocation.writes profile generation record issued assignments receiver
      (protocol := CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1) sourceEq
      runtime.graph.nodeOccurrencesUnique)
    artifact checked sourceEq unique (control := {returnType := header.function.resultType})
    (expected := header.function.resultType) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    functionTyped projection body covered native (Nat.le_of_lt bodyLess)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  rw [scopeEq] at meaning
  obtain ⟨sourceSize, bodyContext, bodyOutcome, after, finalMap, finalWorld, trace, matched, result, bodyHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, _bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed initial
      ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready compiledEvaluation
  have bodyTrace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages sourceSize
      bodyScope header.context entryEnvironment entryHeap header.function.body bodyContext bodyOutcome after := by
    rw [← statements header generation]
    exact trace
  have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.applies (caller := invocation)
    (context := context) sourceAt (SelectedCompilationPhysicalProgramSupport.stagePrepared whole) bodySelected
    header.extended entryAllocated bodyTrace matched
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState.base.val owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  have effect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState.base.val owner.position
    (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True)) (prefixEffect.trans bodyEffect)
  rw [finalEq]
  exact ⟨_, _, after, finalMap, finalWorld, applied, result, restoredHeaps,
    prefixEffect.maps.trans bodyMaps, worlds, restoredFrame, prefixEffect.metadata.trans bodyMetadata, effect,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState.base.val owner.position, restoredRelated⟩

include profile receiver record sameNamed sameBindings sameBody sameSolved projection support in
/-- A callee row whose accepted expressions all lie in the first closed subset
has accepted-expression meaning on the slot-retaining protocol at every grade,
from the same receipts as the public named root. -/
theorem expressions_closed
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (closed : CellAwareInvocationAcceptedExpressions.Closed (rowIndex generation record)) (size : Nat) :
    ∀ (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex generation record) stages child faults size := by
  subst sameNamed
  intro owner keyPhysical child selected
  obtain ⟨_facts, certificate⟩ := support.certified header
  have functionUnique : NodeOccurrencesUnique header.function.source := by
    rw [header.frame.source]
    exact certificate.graph_closed.wellFormed.nodeOccurrencesUnique
  have unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using functionUnique
  exact CellAwareInvocationAcceptedExpressions.expressions (attachment := fun _ _ _ => True)
    (receiving := completion.result.context.registry) (functions := rootFunctions)
    (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
    (rowIndex generation record) stages child faults closed size
    (((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source)
    completion.result.extension
    (CellAwareInvocationAcceptedNamedInvocation.reads generation record issuer receiver unique)
    support.registryBodies

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved projection support
  issued assignments artifact checked covered native wellFormed in
/-- A closed-subset callee row discharges the application input of the
direct-call head at every Source grade, without the size induction. -/
theorem preserves_closed
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (closed : CellAwareInvocationAcceptedExpressions.Closed (rowIndex generation record)) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.PreservesAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  preserves profile receiver header generation record sameNamed sameLayouts sameGlobals sameBindings sameBody
    sameSolved projection support issued assignments artifact checked body covered native wellFormed size
    (expressions_closed profile receiver header generation record sameNamed sameBindings sameBody sameSolved
      projection support issuer closed size)

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved projection support
  issued assignments artifact checked covered native in
/-- A closed-subset callee row discharges the native application input of the
direct-call head at every native grade. -/
theorem reflects_closed
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (closed : CellAwareInvocationAcceptedExpressions.Closed (rowIndex generation record)) (size : Nat)
    {bodyScope : Staging.Recursive.Scope} (bodySelected : (stages).Closure header.function bodyScope) :
    CellAwareInvocationAcceptedDirectCalls.ReflectsAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  reflects profile receiver header generation record sameNamed sameLayouts sameGlobals sameBindings sameBody
    sameSolved projection support issued assignments artifact checked body covered native size bodySelected
    (expressions_closed profile receiver header generation record sameNamed sameBindings sameBody sameSolved
      projection support issuer closed size)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedApplication
