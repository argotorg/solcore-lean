import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedEntry
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.CellAwareOwnedBodyRestoration
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
import Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysicalExtension
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressions
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.PreparedBranchingAssignmentDiagnostics

/-! One genuine named invocation of an accepted body whose expressions lie in
the closed subset. The actual named parameter entry supplies the physical entry
state of the body's own accepted-body index, the accepted-body theorem relates
the compiled body to independent Source execution, and the saved physical
caller is restored. The read and write inputs of the accepted-body theorem come
from the issued compilation and the public receiver. The caller's heap is
represented with the profiled instance model of the older family; each of its
snapshots embeds in the accepted instance model, in which the result is
stated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)

section Instances
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
  {mapping : LocationMap} {world : StoreTyping}

private theorem rows_of_profiled {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {entries : List SourceCoreLocalPolymorphism.Instance} {values : List Core.Value}
    (rows : SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      ((GeneralizedLocalInstanceValues.model prepared).Represents mapping world function binding lexical)
      entries values) :
    SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      ((GeneralizedLocalAcceptedInstances.modelWith prepared (fun _ _ _ => True)).Represents
        mapping world function binding lexical) entries values := by
  induction rows with
  | nil => exact .nil
  | cons head _ ih =>
    obtain ⟨location, framed⟩ := GeneralizedLocalAcceptedInstances.of_profiled head
    exact .cons ⟨location, framed.forget_attachment⟩ ih

/-- A cell of the profiled instance model is a cell of the accepted instance
model with the trivial attachment: every snapshot keeps its packet, captures,
location and value, and its profiled body yields an accepted body receipt. -/
theorem cell_of_profiled {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : (GeneralizedLocalDescriptorHeap.cellModel ordinary
      (GeneralizedLocalInstanceValues.model prepared)).Represents mapping world cell value payload) :
    (GeneralizedLocalDescriptorHeap.cellModel ordinary
      (GeneralizedLocalAcceptedInstances.modelWith prepared (fun _ _ _ => True))).Represents
        mapping world cell value payload := by
  cases represented with
  | ordinary represented => exact .ordinary represented
  | generalized stored =>
    cases stored with
    | bundle binding lexical registered captures origin binder initializer rows =>
      exact .generalized (GeneralizedLocalDescriptorHeap.Stored.bundle
        (model := GeneralizedLocalAcceptedInstances.modelWith prepared (fun _ _ _ => True))
        binding lexical registered captures origin binder initializer (rows_of_profiled rows))

end Instances

/-- The accepted-body index of an actual named cache row. -/
abbrev rowIndex {compiled : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key =
      .ok named.specialized) :
    ActualBodyInvocation.Index compiled ActualBodyInvocation.ReachedView :=
  .named generation record

section Reads
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named (diagnostics.reasonAt named.signature.key))
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

include issuer receiver in
/-- The read-fault input of the accepted-body theorems at a named row. The
selected compiler row and the retained issuer fix the diagnostic of every
ordinary local read, as `CellAwareNamedReadDiagnostics.uninitialized` does for
the older named family. -/
theorem reads (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named)) :
    CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) := by
  intro id node name binder found form location
  change CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
    (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id)
  obtain ⟨issued, present, callback, own, ownFound⟩ := issuer
  have contains : ContainsExpression named.specialized.function.typedBody id node :=
    lookupExpression?_sound found
  obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
      record unique contains form ownFound
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  exact CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (by simpa only [callback, token] using decoded) (.readUninitialized location binder)

end Reads

section Writes
variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
  (assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

include profile issued assignments receiver in
/-- The write inputs of the accepted-body theorems at a named row. The issued
compilation, its prepared assignment table and the public receiver interpret
the operand, unary and place diagnostics of every typed assignment occurrence,
as `CallableIndexedOwnedIssuedAssignmentRecipes.operands` and
`CellAwareNamedAssignmentDiagnostics.ready` do for the older named family. The
registry extension is the receiver's own, and the identity and runtime views
are those of the physical function origins. -/
def writes {invocation : Staging.Recursive.Scope}
    (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named)) :
    CellAwareInvocationAcceptedInputs.Writes (receiving := completion.result.context.registry)
      (functions := CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile)
      (protocol := protocol) (rowIndex generation record) invocation
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) where
  extension := completion.result.extension
  operands := by
    intro context site assignment operator rhs origin typed
    obtain ⟨first, prepared⟩ := assignments
    rw [sourceEq] at origin typed
    have raw : operator = .equal ∨ assignment.target.type = .word := by
      cases typed with
      | equal => exact .inl rfl
      | wordCompound _ place _ _ =>
        cases place with
        | intro _ _ same => exact .inr same
    exact PreparedBranchingAssignmentDiagnostics.operands prepared
      (fun _ _ represented => CallableIndexedOwnedIssuedAssignmentRecipes.operands generation issued receiver represented)
      origin raw
  unary := by
    intro context site assignment origin typed
    obtain ⟨first, prepared⟩ := assignments
    rw [sourceEq] at origin typed
    cases typed with
    | intro place _ =>
      cases place with
      | intro _ _ word =>
        exact GenericAssignmentUnaryDiagnostics.prepared_unary_included prepared
          (fun _ _ represented => CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.compilation_unary
            generation issued receiver represented) origin word
  identities := CallableIndexedLambdaValues.Identity whole.indexed
  faithful := CallableIndexedLambdaValues.identity_faithful whole.indexed
  observations := CellAwarePhysicalFunctionOrigins.observations profile
  functionTypes := CellAwarePhysicalFunctionOrigins.runtime_views profile
  placeDiagnostics := by
    rw [sourceEq]
    exact CellAwareNamedAssignmentDiagnostics.ready record unique issued receiver _ protocol

end Writes

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
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}

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
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header whole (Program.ofChecked whole.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
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
  {invocation : Staging.Recursive.Scope}
  (selected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function invocation)
  (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
  (projection : whole.compatible.checked.catalog.project header.function.resultType = .ok named.signature.resultType)
  (support : SelectedCompilationNamedSupport.Support whole)
  {arguments : List Dynamic.Value} {payloads : List Value}

local notation "namedFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" =>
  CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry namedFunctions
local notation "profiled" =>
  GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)
local notation "accepted" => GeneralizedLocalDescriptorHeap.cellModel model
  (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True))
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "bridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

variable
  (closed : CellAwareInvocationAcceptedExpressions.Closed (rowIndex generation record))
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
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative))
    (rowIndex generation record).body nativeType whole.indexed.layouts.definitions)

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved selected issuer
  projection support closed issued assignments artifact checked covered native in
/-- The Source allocation and body trace are independent inputs. The native
entry, the accepted body and the saved-caller restoration are constructed from
the compiler; no body or expression execution law is assumed. -/
theorem preserves_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents profiled mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
      header.context environment bound header.function.body finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        namedFunctions accepted owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  subst sameNamed
  have certified := support.certified header
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, _lexical, reached, related, rows, physical, frameEq, wrap, _unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record certified
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap, ← statements header generation] at trace
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
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
  have unique : NodeOccurrencesUnique invocation.source := sourceEq ▸ runtime.graph.nodeOccurrencesUnique
  obtain ⟨_facts, certificate⟩ := certified
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certificate.locals_empty
  have monomorphic := monomorphic_context header.extended
    (by intro id scheme member; rw [empty] at member; cases member)
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys accepted
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
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
  have meaning := CellAwareInvocationAcceptedExpressions.body_preserves (attachment := fun _ _ _ => True) bridge
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys) (rowIndex generation record) producer
    (CallableIndexedAmbient.frame_registered whole.indexed) stages invocation faults
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative) size closed
    (reads generation record issuer receiver runtime.graph.nodeOccurrencesUnique) support.registryBodies
    (writes profile generation record issued assignments receiver (protocol := protocol headers keys) sourceEq
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
    meaning environments (entryHeaps.includes cell_of_profiled) sourceReceipt.locals agrees actualTyped runtime
      covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready trace
  have evaluatedHeader : Evaluates entryActual entryStore (header.body.rename entryEmbedding) value bodyStore := by
    rw [sameBody]
    exact evaluated
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, wrap evaluatedHeader, ?_⟩
  exact ⟨result, restoredHeaps, prefixEffect.maps.trans bodyMaps, worlds,
    restoredFrame, prefixEffect.metadata.trans bodyMetadata, returned, restoredRelated, post⟩

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved selected issuer
  projection support closed issued assignments artifact checked covered native in
/-- Actual native completion is unwrapped through the same named entry and
reconstructs an independent Source execution with the restored caller. -/
theorem reflects_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents profiled mapping world before store)
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
        namedFunctions accepted owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  subst sameNamed
  have certified := support.certified header
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, _lexical, reached, related, rows, physical, frameEq, _wrap, unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record certified
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨bodyStore, bodyEvaluation, finalEq⟩ := unwrap completed
  have compiledEvaluation : Evaluates entryActual entryStore (generation.body.rename entryEmbedding) value bodyStore := by
    rw [← sameBody]
    exact bodyEvaluation
  obtain ⟨nativeSize, nativeTrace⟩ := evaluation_has_size compiledEvaluation
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
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
  have unique : NodeOccurrencesUnique invocation.source := sourceEq ▸ runtime.graph.nodeOccurrencesUnique
  obtain ⟨_facts, certificate⟩ := certified
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certificate.locals_empty
  have monomorphic := monomorphic_context header.extended
    (by intro id scheme member; rw [empty] at member; cases member)
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys accepted
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
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
  have meaning := CellAwareInvocationAcceptedExpressions.body_reflects (attachment := fun _ _ _ => True) bridge
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys) (rowIndex generation record) producer
    (CallableIndexedAmbient.frame_registered whole.indexed) stages invocation faults
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative) nativeSize closed
    (reads generation record issuer receiver runtime.graph.nodeOccurrencesUnique) support.registryBodies
    (writes profile generation record issued assignments receiver (protocol := protocol headers keys) sourceEq
      runtime.graph.nodeOccurrencesUnique)
    artifact checked sourceEq unique (control := {returnType := header.function.resultType})
    (expected := header.function.resultType) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    functionTyped projection body covered native (Nat.le_refl nativeSize)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  rw [scopeEq] at meaning
  obtain ⟨sourceSize, bodyContext, bodyOutcome, after, finalMap, finalWorld, trace, matched, result, bodyHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments (entryHeaps.includes cell_of_profiled) sourceReceipt.locals agrees actualTyped runtime
      covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready nativeTrace
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨sourceSize, entryEnvironment, entryHeap, bodyContext, bodyOutcome, after, finalMap, finalWorld,
    entryAllocated, ?_, matched, completed, ?_⟩
  · rw [← statements header generation]
    exact trace
  · rw [finalEq]
    exact ⟨result, restoredHeaps, prefixEffect.maps.trans bodyMaps, worlds,
      restoredFrame, prefixEffect.metadata.trans bodyMetadata, returned, restoredRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedInvocation
