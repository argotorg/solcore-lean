import Solcore.SourceSemantics.CoreLowering.Internal.Owned.DecodedCallFaults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyContinuations
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.ExpressionTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenOrdinaryCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenLambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries

/-!
# Owned callables: lambda receipts

Assignment recipes and provenance, read diagnostics and formation receipts of lambdas, and general method heads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentProvenance
/-! Exact cached compilation authenticates assignment inventories at the full
original method source, retaining its own selector rather than an ordinary header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentProvenance
open Core Frontend SourceInference
open CallablePreparedMethodSelection (Cached)
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallableIndexedOwnedPreparedStagedMethodTerminalSupport (DiagnosticAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}

/-- A genuine cached compiler and its diagnostic receipt select the same
member of the actual program inventory. -/
theorem cached_member (cached : Cached compiled row) (diagnostic : DiagnosticAt cached) :
    ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some issued ∧
      cached.compilation.own ∈ issued.program.base.functions := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  have sameBase : cached.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  have selected := cached.compilation.diagnostic
  rw [sameBase] at selected
  exact ⟨issued, present, List.mem_of_find?_eq_some selected⟩

/-- The original complete cached Source supplies the authentic preparation;
its assignment tokens are not regenerated from a subbody or native code. -/
theorem cached_assignments (cached : Cached compiled row) (diagnostic : DiagnosticAt cached) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare cached.named.specialized.function.typedBody first =
      .ok cached.compilation.own.assignments := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  have programAccepted := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base accepted
  have sameBase : cached.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  have selected := cached.compilation.diagnostic
  rw [sameBase] at selected
  exact SourceCoreProgramFaultSites.prepare_assignments_at programAccepted
    (CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook) selected

/-- The same inventory belongs to the method principal's complete Source
body, including its actual specialization and dictionary frame. -/
theorem method_assignments {method : ExecutableImplMethods.CheckedMethod}
    (principal : Principal compiled method) (diagnostic : DiagnosticAt principal.cached) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare principal.sourceBody.source first =
      .ok principal.cached.compilation.own.assignments := by
  rw [← principal.source_eq]
  exact cached_assignments principal.cached diagnostic

/-- Any genuine cached assignment operand is interpreted by the actual
public receiver, with all table inclusion obligations closed internally. -/
theorem cached_operands (cached : Cached compiled row) (diagnostic : DiagnosticAt cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : GenericAssignmentDiagnostics.OperandRep cached.compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ := cached_member cached diagnostic
  exact CallableIndexedOwnedPublicAssignmentDiagnostics.receiver_operands compiled receiver present member represented

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentProvenance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
/-! Exact public issuance turns a retained contextual compilation into its
original assignment preparation and receiver interpretation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaIssuedRecipes (IssuedAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}

/-- The existing named diagnostic receipt retains the genuine unchanged base. -/
theorem of_prepared {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (receipt : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared) :
    IssuedAt compiled.indexed prepared.diagnostics := by
  obtain ⟨issued, present, lowered⟩ := receipt.actual
  refine ⟨issued, present, ?_⟩
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> exact ⟨rfl, rfl⟩

/-- Actual method cache issuance has the same complete table provenance. -/
theorem of_cached {row : SourceSpecialization.SpecializedFunction}
    (cached : CallablePreparedMethodSelection.Cached compiled row)
    (receipt : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt cached) :
    IssuedAt compiled.indexed cached.diagnostics := by
  obtain ⟨issued, present, lowered⟩ := receipt.actual
  refine ⟨issued, present, ?_⟩
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> exact ⟨rfl, rfl⟩

/-- The exact same retained compilation selects its actual own table. -/
theorem compilation_member (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (receipt : IssuedAt compiled.indexed diagnostics) :
    ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some issued ∧
      compilation.own ∈ issued.program.base.functions := by
  obtain ⟨issued, present, sameBase, _samePlaces⟩ := receipt
  have selected := compilation.diagnostic
  rw [sameBase] at selected
  exact ⟨issued, present, List.mem_of_find?_eq_some selected⟩

/-- Full original-source preparation is preserved through closure-body views;
only authentic membership of the owning named cache is required. -/
theorem assignments_prepared {index : Nat}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (receipt : IssuedAt compiled.indexed diagnostics) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare (source named) first = .ok compilation.own.assignments := by
  obtain ⟨issued, present, sameBase, _samePlaces⟩ := receipt
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  have found := compilation.diagnostic
  rw [sameBase] at found
  exact SourceCoreProgramFaultSites.prepare_assignments_at
    (CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base accepted)
    (CallableIndexedActualNamedSourceReceipts.cached_record compiled selected compilation.hook) found

/-- The compilation used by the lowerer supplies the public operand relation. -/
theorem operands (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (receipt : IssuedAt compiled.indexed diagnostics)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : GenericAssignmentDiagnostics.OperandRep compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ := compilation_member compilation receipt
  exact CallableIndexedOwnedPublicAssignmentDiagnostics.receiver_operands compiled receiver present member represented

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
/-! Original lambda formation retains actual diagnostic issuer tokens on used
body expressions. The current public receiving table decodes that same issuer;
a captured read keeps the original binder, occurrence and source span. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance
open CallableIndexedOwnedPublicFaultReceiverTables

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}

/-- The real named callback gives its exact token provider before recapture. -/
theorem of_prepared {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (same : code.reasonAt = header.reasonAt) : BodyReasons code header.named := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  apply BodyReasons.of_issued present
  rw [same, aligned.reasonAt, aligned.named, lowered]
  cases compiled.indexed.base.callableContext <;> rfl

/-- An authentic original read token decodes in the actual receiving table. -/
theorem uninitialized
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
    (reasons : BodyReasons code support.caller.named)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {fuel : Nat} {context : SourceSemantics.Context} {readScope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression id))
    (receipt : CompatibleExpressionReads.LoweredRead fuel
      (.initial compiled.compatible.checked) function.source context code.reasonAt readScope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (code.reasonAt id) := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  obtain ⟨issued, present, token⟩ := reasons id reached
  obtain ⟨actual, namedCode, actualPresent, _cached, compiledCode⟩ :=
    NamedCalls.compiled_at compiled.indexed support.caller.selected
  have sameIssuer : actual = issued := Option.some.inj (actualPresent.symm.trans present)
  subst actual
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed compiledCode
  have ownFound : issued.program.base.find? support.caller.named.signature.key = some compilation.own := by
    have selected := compilation.diagnostic
    have sameBase : (match compiled.indexed.base.callableContext with
        | none => issued.program
        | some native => { issued.program with rootTable := native.diagnostics.rootTable }).base =
        issued.program.base := by cases compiled.indexed.base.callableContext <;> rfl
    exact (congrArg (fun base => base.find? support.caller.named.signature.key) sameBase).symm.trans selected
  have original : function.source = support.caller.named.specialized.function.typedBody := support.source
  have unique : NodeOccurrencesUnique support.caller.named.specialized.function.typedBody := original ▸ support.unique
  have contains : ContainsExpression support.caller.named.specialized.function.typedBody id certificate.node :=
    original ▸ lookupExpression?_sound certificate.metadata.found
  obtain ⟨read, _expression, _binder, _span, readToken, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
      (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)
      unique contains certificate.form ownFound
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (by simpa only [← readToken, ← token] using decoded)
  exact .readUninitialized location certificate.binder

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginAllocationReceipts
/-! A successful child keeps its positive payload and cells at its actual post.
The original owned initialized allocator consumes that post once under the
strong model and retains every original capture, environment and reached state.
An actual mapped write separately updates positive cells with the authenticated
replacement payload. Source heap typing and all-row stability belong to those
same returned states. Neither operation infers positive cells from a frame
receipt or converts an erased general-model closure into a positive member. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginAllocationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory TypedLexicalControl
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The bridge observes the original full owned pool without changing it. -/
def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

/-- Source admission and positive cells are attached to one actual caller
witness. Its scope and canonical slots remain independent of cell payloads. -/
structure AdmissionWithOrigins (context : SourceSemantics.Context)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {index : ProtectedStateTransition.Index} (reached : State headers keys index) : Prop where
  admission : Admission bridge context reached
  cells : CellOrigins headers keys bodyRegistry registry faults profile
    index.mapping index.world index.heap index.store

section InitializedAllocation
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {source : TypedSource} {context nextContext : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
  (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)

include registered in
/-- Consume the actual initializer child post and run the original owned
marked allocator once. The original full tuple is retained; admission and
positive cells stay inside its same reached existential. -/
theorem allocate_initialized_from_post
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active
      (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
      compiled.indexed.ancestry.layout.frame globals
      (compiled.indexed.layouts.allocatorAt owner active onError)
      (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (reference : canonical[scope.length + 1 + globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : CallableIndexedOwnedAllocationProducer.Ready initial contextLocation native)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry)
      (faults := faults) bridge context profile binder.scheme.body payload
      (.value sourceValue) (.inRight .word value) initial) :
    ∃ captured,
      CallableIndexedAllocationCompletion.Captures (value :: canonical)
        (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope)
        compiled.indexed.layouts.definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [compiled.indexed.ancestry.layout.frame.type,
        allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        nextMap nextWorld administrative ((binder.id, payload) :: scope)
        ((binder.id, location) :: environment) (nextRef :: canonical) compiled.indexed.layouts.definitions ∧
      CellOrigins headers keys bodyRegistry registry faults profile nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
        (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) compiled.indexed.layouts.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation) ∧
      nextStore.read? contextLocation =
        some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ∃ reached : State headers keys
          ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        Relates initial reached ∧
        AdmissionWithOrigins (bodyRegistry := bodyRegistry) (registry := registry)
          (faults := faults) nextContext profile reached := by
  obtain ⟨admitted, valueTyped, represented⟩ := post.at_value
  let producer := (CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))).toOrdinary
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextCells, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related, nextAdmission⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      rfl registered producer mono extended ordinary allocation annotation same
      valueTyped represented environments post.cells locals agrees actualTyped reference read
      allocated initial ready admitted
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextCells, nextLocals,
    nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related,
    ⟨nextAdmission, nextCells⟩⟩

end InitializedAllocation

section WrittenAllocationCell
variable {context : SourceSemantics.Context}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store} {canonical : Environment}
  {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell}
  {payload : Ty} {sourceValue : Dynamic.Value} {value : Value}

/-- A true assignment replacement updates the jointly indexed cells. Raw
typing comes from the actual successful RHS post at the retained cell type;
the real write preserves deep heap typing. The owned pool is extended only
after those independent write facts are available, retaining all records. -/
theorem write_initialized_from_post
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry)
      (faults := faults) bridge context profile cell.type payload
      (.value sourceValue) (.inRight .word value) initial)
    (reference : ReferenceRepresents mapping world location target payload)
    (read : Dynamic.Heap.Reads before location cell)
    (written : Dynamic.Heap.Writes before location (some sourceValue) after) :
    ∃ updated,
      store.write? target (.inRight .unit value) = some updated ∧
      AdministrativePreserved mapping store mapping updated ∧
      ∃ reached : State headers keys ⟨scope, mapping, world, after, updated, canonical⟩,
        Relates initial reached ∧ records reached = records initial ∧
        AdmissionWithOrigins (bodyRegistry := bodyRegistry) (registry := registry)
          (faults := faults) context profile reached := by
  obtain ⟨admitted, valueTyped, represented⟩ := post.at_value
  obtain ⟨updated, nativeWrite, nextCells, preservation⟩ :=
    CallableIndexedOwnedContextualCellOrigins.CellOrigins.write_initialized profile
      post.cells reference read represented written
  have heapTyped := Dynamic.HeapWellTyped.write admitted.heap read (.some valueTyped) written
  have metadata := Dynamic.HeapMetadataExtend.of_write written
  let transport := administrativeTransport headers keys
  let reached := transport.extend initial (LocationMap.Extends.refl mapping)
    (WorldExtends.refl world) preservation metadata
  have nextAdmission : Admission bridge context reached :=
    ⟨heapTyped, StableRows.after_administrative initial reached admitted.rows preservation⟩
  exact ⟨updated, nativeWrite, preservation, reached,
    transport.related initial (LocationMap.Extends.refl mapping) (WorldExtends.refl world)
      preservation metadata,
    transport.records_eq initial (LocationMap.Extends.refl mapping) (WorldExtends.refl world)
      preservation metadata,
    ⟨nextAdmission, nextCells⟩⟩

end WrittenAllocationCell
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginAllocationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureFormationReceipts
/-! Genuine ordinary and principal formation heads create a positive closure
leaf directly from the retained static receipt. Each direction invokes the
original factory once over the incoming positive cells, with its General
representation. Formation copies the captured cells, so the positive cells and
the caller's packet are transported to the formed state; the actual Source
trace establishes admission in that transported packet. No escaped diagnostic,
selected caller code, reverse General inclusion or body meaning is required by
formation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualTypedClosureReceipts (StaticMember)
open CallableIndexedOwnedContextualCellOrigins (PayloadOrigins CellOrigins PostWithOrigins post_at_same_state)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry faults)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

/-- The full head result retains the original effects and the same packet
witness, transported to the formed state that holds the copies of the captured
cells, with the positive heap there. The static member of the formed closure is
inside that returned existential beside the actual positive post. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
      PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        function.context profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
          (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
        StaticMember headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

/-- The legacy full-head projection has one registry. Its explicit equality
is needed only by this compatibility port; formation keeps the body and
receiving registries independent with the same result and reached caller. -/
theorem ResultAt.forget {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {result : Core.Value} {finalStore : Store}
    (sameRegistry : registry = bodyRegistry)
    (returned : ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore) :
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.ResultAt (registry := bodyRegistry) captured code support owner initial packet
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) outcome after result finalStore := by
  cases sameRegistry
  obtain ⟨nativeTrace, finalMap, finalWorld, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post, _member⟩ := returned
  exact ⟨nativeTrace, finalMap, finalWorld, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post.admission⟩

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include prefixContext observed provenance cells copied ordinary coercions in
/-- The original ordinary factory runs once over the incoming positive cells.
Its General representation supplies the static member of the formed closure
over the copies of its captured cells; no escaped-control row is used. -/
private theorem formation_member :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation initial owner captured code
      (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) rfl profile cells copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) represented
  exact ⟨formed, sourceTrace, nativeTrace, determined,
    ⟨.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.provenance_recapture provenance formed.captured)⟩⟩

include sourceType admitted wellFormed runtime covers locals typed in
/-- Pure attachment uses the trace and member already returned by one factory.
The caller is the same packet used by formation, transported to the formed
state; its actual Source trace supplies admission there, beside the formed
positive cells. -/
private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
      (history_at captured code support owner initial packet) heap store owner.key.frameLocation)
    (sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured heap code.id (.closure formed.closure)
      formed.finalHeap)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore)
    (member : StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) :
    ResultAt (registry := registry) captured code owner profile support initial packet (.value (.closure formed.closure))
      formed.finalHeap
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore := by
  have payload : PayloadOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
      code.sourceNode.type (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.lowered.type := by
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := registry) profile member
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding
        (history_at captured code support owner initial packet).native formed.closureActual)) := .value payload
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨nativeTrace, formed.finalMap, formed.finalWorld, represented, formed.heaps, formed.maps, formed.worlds,
    formed.frame, formed.copy.metadata_extends, reached, related,
    post_at_same_state (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      profile reached post formed.heaps represented, formed, member⟩

include prefixContext observed provenance cells sourceType copied ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Invert the actual Source head and form its closure over the copies of its
captured cells once. The genuine metadata, syntax, capture history and positive
cells all describe this original head; no accepted-call selection or body
continuation is assumed. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, sourceTrace, nativeTrace, _determined, member⟩ :=
      formation_member captured code owner profile cells support initial packet prefixContext observed provenance
        copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    exact ⟨_, formed.finalStore, result_at_formation captured code owner profile support initial packet
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace nativeTrace member⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include prefixContext observed provenance cells sourceType copied ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Compare the supplied native completion with one genuine formation. Its
independent Source grade and positive post use that same factory trace directly;
reflection does not invoke preservation and form the closure a second time. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, determined, member⟩ :=
    formation_member captured code owner profile cells support initial packet prefixContext observed provenance
      copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation captured code owner profile support initial packet
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace nativeTrace member⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code bodyRegistry faults)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code support)

open CallableIndexedOwnedMethodLambdaFormationReceipts (history_at source_origin leading reference_index)

/-- The full head result retains the original effects and the same packet
witness, transported to the formed state that holds the copies of the captured
cells, with the positive heap there. The static member of the formed closure is
inside that returned existential beside the actual positive post. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
        ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
      (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
      PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        function.context profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
          (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
        StaticMember headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

/-- The legacy full-head projection has one registry. Its explicit equality
is needed only by this compatibility port; formation keeps the body and
receiving registries independent with the same result and reached caller. -/
theorem ResultAt.forget {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {result : Core.Value} {finalStore : Store}
    (sameRegistry : registry = bodyRegistry)
    (returned : ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore) :
    CallableIndexedOwnedAdmittedPrincipalLambdaFormation.ResultAt (registry := bodyRegistry) captured code support owner initial packet
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) outcome after result finalStore := by
  cases sameRegistry
  obtain ⟨nativeTrace, finalMap, finalWorld, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post, _member⟩ := returned
  exact ⟨nativeTrace, finalMap, finalWorld, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post.admission⟩

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include packet provenance cells copied ordinary coercions in
/-- The original principal factory runs once over the incoming positive cells.
Its General representation, actual leading bundle and history supply the static
member of the formed closure over the copies of its captured cells; no
escaped-control row is used. -/
private theorem formation_member :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedAdmittedPrincipalLambdaFormation.principal_representation captured code support owner
      initial packet profile cells copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) represented
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    leading captured code support owner initial packet
  exact ⟨formed, sourceTrace, nativeTrace, determined,
    ⟨.principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin (source_origin captured code support owner initial packet)
        formed.captured)
      (packet.observed.of_slots formed.slots) leadingFormed (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.provenance_recapture provenance formed.captured)⟩⟩

include sourceType admitted wellFormed runtime covers locals typed in
/-- Pure attachment uses the trace and member already returned by one factory.
The caller is the same packet used by formation, transported to the formed
state; its actual Source trace supplies admission there, beside the formed
positive cells. -/
private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
      (history_at captured code support owner initial packet) heap store owner.key.frameLocation)
    (sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured heap code.id (.closure formed.closure)
      formed.finalHeap)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore)
    (member : StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) :
    ResultAt (registry := registry) captured code owner profile support initial packet (.value (.closure formed.closure))
      formed.finalHeap
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore := by
  have payload : PayloadOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
      code.sourceNode.type (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.lowered.type := by
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := registry) profile member
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding
        (history_at captured code support owner initial packet).native formed.closureActual)) := .value payload
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
    (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨nativeTrace, formed.finalMap, formed.finalWorld, represented, formed.heaps, formed.maps, formed.worlds,
    formed.frame, formed.copy.metadata_extends, reached, related,
    post_at_same_state (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      profile reached post formed.heaps represented, formed, member⟩

include packet provenance cells sourceType copied ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Invert the actual Source head and form its closure over the copies of its
captured cells once. The genuine metadata, syntax, capture history and positive
cells all describe this original head; no accepted-call selection or body
continuation is assumed. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, sourceTrace, nativeTrace, _determined, member⟩ :=
      formation_member captured code owner profile cells support initial packet provenance
        copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    exact ⟨_, formed.finalStore, result_at_formation captured code owner profile support initial packet
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace nativeTrace member⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include packet provenance cells sourceType copied ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Compare the supplied native completion with one genuine formation. Its
independent Source grade and positive post use that same factory trace directly;
reflection does not invoke preservation and form the closure a second time. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, determined, member⟩ :=
    formation_member captured code owner profile cells support initial packet provenance
      copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation captured code owner profile support initial packet
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace nativeTrace member⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureFormationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionHeads
/-! The original finite named/method-lambda certificates share one actual
principal caller packet. Authentic lambda formation preserves its prefix and
leading bundle in the shared model, including through named/method expressions.
Original named entries and strict joint body children keep the same caller pool. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge)
open CallableIndexedOwnedMethodMixedExpressionHeads (named_caller)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context) (compilation : SourceCoreFunctions.Context)

/-- The exact original mixed certificate retains its authentic static heads. -/
abbrev Head (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodMixedExpressionHeads.Head
    (headers := headers) (registry := registry) (faults := faults) principal context compilation certificate

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

variable
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (prefixOne : compilation.administrativePrefix = 1)
  (prefixZero : owner.key.capturePrefix = 0)
  (globalCounts : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  {certificate : GenericExpressionMeaning.Certificate}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include inclusion prefixOne prefixZero globalCounts complete slots wellFormed runtime covers unique owners idsUnique
  sameLayouts escaped profiles syntaxTrees in
/-- Each selected finite branch runs at the same input and returned caller.
Its body obligation is the actual strict child of the extended shared family. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation certificate) faults size := by
  have named : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation (CallableIndexedNamedGeneration.source principal.named) context principal.dictionary certificate) faults size :=
    CallableIndexedOwnedAdmittedNamedExpressionHeads.preserves_at
    (functions := functions) (owner := owner) (runtime := true) principal.dictionary
    (named_caller principal compilation owner prefixOne) wellFormed runtime covers unique idsUnique
    sameLayouts escaped profiles owners budget size within children
    (fun header member => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.source_bodies
      (functions := functions) (owner := owner) (runtime := true) wellFormed prefixZero (globalCounts header member)
      member (syntaxTrees header member) (fun index => below (.namedNested index)))
  have methodLambda : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CallableIndexedOwnedMethodLambdaExpressionHeads.Head (registry := registry) (faults := faults) principal context certificate) faults size :=
    CallableIndexedOwnedPrincipalLambdaExpressionHeads.preserves_at
    principal context owner profile functions inclusion complete slots wellFormed runtime covers budget size within children below
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  cases head with
  | named head => exact named head found sourceTyped environments heaps locals agrees typed initial admitted trace
  | method_lambda head => exact methodLambda head found sourceTyped environments heaps locals agrees typed initial admitted trace

include inclusion prefixOne prefixZero globalCounts complete slots wellFormed runtime covers unique
  sameLayouts escaped profiles syntaxTrees in
/-- Native finite selection keeps the original measured children and restores
the same full caller while independently reconstructing the Source parent. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation certificate) faults size := by
  have named : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation (CallableIndexedNamedGeneration.source principal.named) context principal.dictionary certificate) faults size :=
    CallableIndexedOwnedAdmittedNamedExpressionHeads.reflects_at
    (functions := functions) (owner := owner) (runtime := true) principal.dictionary
    (named_caller principal compilation owner prefixOne) wellFormed runtime covers unique
    sameLayouts escaped profiles budget size within children
    (fun header member => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.native_bodies
      (functions := functions) (owner := owner) (runtime := true) wellFormed prefixZero (globalCounts header member)
      member (syntaxTrees header member) (fun index => below (.namedNested index)))
  have methodLambda : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CallableIndexedOwnedMethodLambdaExpressionHeads.Head (registry := registry) (faults := faults) principal context certificate) faults size :=
    CallableIndexedOwnedPrincipalLambdaExpressionHeads.reflects_at
    principal context owner profile functions inclusion complete slots wellFormed runtime covers budget size within children below
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  cases head with
  | named head => exact named head found sourceTyped environments heaps locals agrees typed initial admitted completed
  | method_lambda head => exact methodLambda head found sourceTyped environments heaps locals agrees typed initial admitted completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionRuntimeBounds
/-! Original mixed named/method certificates run with complete principal
lambda provenance under one supplied function model. The same expression Tree
fold and finite dispatcher consume authentic heads and internally constructed
runtime literals. Strict original family children supply only the body IH. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge)
open CallableIndexedOwnedGeneralMethodMixedExpressionHeads (Head)
open CallableIndexedOwnedPrincipalLambdaExpressionHeads (model)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context) (compilation : SourceCoreFunctions.Context)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

/-- The same original Tree uses the unchanged genuine finite Head sum. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodMixedExpressionRuntimeBounds.Tree
    (headers := headers) (registry := registry) (faults := faults) (solved := solved)
    (reasonAt := reasonAt) (fuel := fuel) principal context compilation

/-- Runtime literals keep the same original actual requirement ledger. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodMixedExpressionRuntimeBounds.RuntimeTree
    (headers := headers) (registry := registry) (faults := faults) (solved := solved)
    (reasonAt := reasonAt) (fuel := fuel) principal context compilation

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (prefixOne : compilation.administrativePrefix = 1)
  (prefixZero : owner.key.capturePrefix = 0)
  (globalCounts : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees owners idsUnique in
theorem preserves_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions
    (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget child childWithin children
    exact CallableIndexedOwnedGeneralMethodMixedExpressionHeads.preserves_at
      (principal := principal) (context := context) (compilation := compilation) (owner := owner)
      (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
      (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
      (owners := owners) (idsUnique := idsUnique) (sameLayouts := sameLayouts) (escaped := escaped)
      (profiles := profiles) (syntaxTrees := syntaxTrees) budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem reflects_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions
    (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget child childWithin children
    exact CallableIndexedOwnedGeneralMethodMixedExpressionHeads.reflects_at
      (principal := principal) (context := context) (compilation := compilation) (owner := owner)
      (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
      (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
      (sameLayouts := sameLayouts) (escaped := escaped)
      (profiles := profiles) (syntaxTrees := syntaxTrees) budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees owners idsUnique in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (headers := headers) (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context compilation) faults size := by
  exact preserves_at_with_literals
    (principal := principal) (context := context) (compilation := compilation) (owner := owner)
    (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
    (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
    (extension := extension) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
    (owners := owners) (idsUnique := idsUnique) (uninitialized := uninitialized) (missing := missing)
    (sameLayouts := sameLayouts) (escaped := escaped) (profiles := profiles) (syntaxTrees := syntaxTrees)
    (CompatibleExpressionLiteralRuntime.preserves
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger unique faults)
    budget size within below

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (headers := headers) (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context compilation) faults size := by
  exact reflects_at_with_literals
    (principal := principal) (context := context) (compilation := compilation) (owner := owner)
    (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
    (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
    (extension := extension) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
    (uninitialized := uninitialized) (missing := missing)
    (sameLayouts := sameLayouts) (escaped := escaped) (profiles := profiles) (syntaxTrees := syntaxTrees)
    (CompatibleExpressionLiteralRuntime.reflects
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger (CallableIndexedNamedGeneration.source principal.named) faults)
    budget size within below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionRuntimeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaBodyContinuations
/-! A genuine singleton return consumes the admitted Word literal at the same
chosen Support. The actual Source and native children retain their independent
grades and the reached state supplies readiness at the original tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaBodyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedChosenWordLiteralExpressionBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open TypedScopedStatements (head_fault terminal_intro)

section StaticReturn
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {statements : List StatementId} {statement : StatementId} {node : StatementNode} {expression : ExpressionId}
  {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}

/-- Actual singleton Source metadata exposes the original tree child and flow.
No equality of emitted finish expressions is inverted. -/
private theorem return_child
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative context scope (.statements true statements) expected type flow)
    (singleton : statements = [statement])
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) :
    ∃ expressionNode lowered, source.lookupExpression? expression = some expressionNode ∧
      expressionNode.type = expected ∧ certificates context scope expression lowered ∧
      type = lowered.type ∧ flow = LocalLoop.returnValue lowered.type lowered.expression := by
  subst statements
  cases tree <;> simp_all
  rename_i syntaxTree body
  cases body <;> simp_all
  exact ⟨_, by assumption, rfl, rfl⟩

private theorem return_typed
    (syntaxTree : GenericImperativeMatch.Syntax source expressionSyntax context
      (.statements true statements) expected)
    (singleton : statements = [statement])
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) :
    ExpressionHasType source context expression expected := by
  subst statements
  cases syntaxTree <;> try simp_all
  rename_i body
  cases body <;> simp_all

private theorem return_transfers
    {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {control : Dynamic.ControlOutcome} {size : Nat}
    {faults : FunctionCalls.FaultRep} {escaped : Word}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : RecursiveNamedLoopContracts.ExecutesAt size true program context evidence source
      environment before [statement] finalContext control after) :
    ImperativeFunctionFinish.TransferFaults faults escaped control := by
  obtain ⟨_, _, outcome, _, same, _⟩ :=
    RecursiveNamedLexicalTreeSourceBounds.returning unique found form trace
  rw [same]
  cases outcome <;> simp [ImperativeFunctionFinish.TransferFaults]

end StaticReturn

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (literalRoot : LiteralRootReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (literalId : ExpressionId) (node : ExpressionNode)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory literalRoot.root (approved literalId) receipt)
  (capturedEnvironment : Dynamic.Environment)
  (facts : WordNodeFacts (caller := caller) literalId node)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (currentContext : SourceSemantics.Context) (currentEvidence : Dynamic.EvidenceEnvironment)
  (ledger : currentContext.solvedRequirements = (context compiled.indexed caller.named).solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid currentContext)
  {statement : StatementId} {statementNode : StatementNode}
  (found : (receipt.formation.function capturedEnvironment).source.lookupStatement? statement = some statementNode)
  (form : statementNode.form = .returnStmt (some literalId))
  {childScope : SourceCoreLocalCell.Scope} {child : SourceCoreBasic.LoweredExpr}
  (actual : (receipt.formation.support capturedEnvironment).certificates
    (receipt.formation.support capturedEnvironment).body.readFuel
    (receipt.formation.function capturedEnvironment).source currentContext childScope literalId child)
  (typed : ExpressionHasType (receipt.formation.function capturedEnvironment).source currentContext literalId node.type)
  {expected : TypeSystem.Ty} (valueType : node.type = expected)
  {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)

include chosen facts ledger runtime found form actual typed valueType in
/-- The finite return joins one genuine admitted expression child. -/
theorem return_flow_preserves
    (unique : NodeOccurrencesUnique (receipt.formation.function capturedEnvironment).source) (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      callerProtocol (readiness bridge) condition (fun _ _ _ _ => True) functions
      (Program.ofChecked compiled.sourceProgram) currentEvidence (fun _ => True)
      (source := (receipt.formation.function capturedEnvironment).source) (context := currentContext)
      (registry := registry) (faults := faults) (administrative := administrative)
      (frameLayout := frameLayout) (globals := globals) size (scope := childScope) true [statement]
      expected child.type (LocalLoop.returnValue child.type child.expression) := by
  intro _valid _facts mapping world actualContext environment canonical native before after store ξ
    contextLocation nativeFrame outcome finalContext environments heaps locals agrees nativeTyped reference read unmapped
    initial _condition admitted trace
  obtain ⟨sameContext, childSize, childOutcome, childTrace, sameOutcome, _smaller⟩ :=
    RecursiveNamedLexicalTreeSourceBounds.returning unique found form trace
  subst finalContext
  subst outcome
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (preserves_at_support (registry := registry) (faults := faults) literalRoot literalId node receipt chosen capturedEnvironment facts
        bridge functions currentContext currentEvidence ledger runtime unique childSize)
      actual facts.found typed environments heaps locals agrees nativeTyped initial admitted childTrace
  cases represented with
  | value payload =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩,
      ⟨transition.choose, transition.choose_spec.1, transition.choose_spec.2.1⟩⟩
  | fault matched =>
    cases childTrace with | fault _failed =>
      exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩

include chosen facts ledger runtime found form actual typed valueType in
/-- Native inversion uses the original strict child and constructs Source size
independently at the same reached state. -/
theorem return_flow_reflects (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      callerProtocol (readiness bridge) condition (fun _ _ _ _ => True) functions
      (Program.ofChecked compiled.sourceProgram) currentEvidence (fun _ => True)
      (source := (receipt.formation.function capturedEnvironment).source) (context := currentContext)
      (registry := registry) (faults := faults) (administrative := administrative)
      (frameLayout := frameLayout) (globals := globals) size (scope := childScope) true [statement]
      expected child.type (LocalLoop.returnValue child.type child.expression) := by
  intro _valid _facts mapping world actualContext environment canonical native before store finalStore ξ
    contextLocation nativeFrame value environments heaps locals agrees nativeTyped reference read unmapped
    initial _condition admitted evaluated
  rw [LoopRenaming.returnValue] at evaluated
  obtain ⟨childSize, middleStore, input, _smaller, childEvaluation⟩ := evaluated.bind_computation
  obtain ⟨sourceSize, childOutcome, after, finalMap, finalWorld, childTrace, represented,
      finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (reflects_at_support (registry := registry) (faults := faults) literalRoot literalId node receipt chosen capturedEnvironment facts
        bridge functions currentContext currentEvidence ledger runtime childSize)
      actual facts.found typed environments heaps locals agrees nativeTyped initial admitted childEvaluation
  cases represented with
  | fault matched =>
    cases childTrace with | fault failed =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_failure _ childEvaluation.sound)
      have sourceTrace := head_fault true [] (.returnValue (lookupStatement?_sound found) form failed.sound)
      obtain ⟨flowSize, sized⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size sourceTrace
      exact ⟨flowSize, currentContext, _, after, finalMap, finalWorld, sized, .fault matched,
        finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
  | value payload =>
    cases childTrace with | value childTrace =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_success _ childEvaluation.sound)
      have sourceTrace := terminal_intro true [] (lookupStatement?_sound found)
        (by intro expression; simp [form]) (.returnValue (lookupStatement?_sound found) form childTrace.sound) (.returned _)
      obtain ⟨flowSize, sized⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size sourceTrace
      exact ⟨flowSize, currentContext, _, after, finalMap, finalWorld, sized, .returned (valueType ▸ payload),
        finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩,
        ⟨transition.choose, transition.choose_spec.1, transition.choose_spec.2.1⟩⟩


section SupportReturn
variable
  (singleton : (receipt.formation.function capturedEnvironment).body = [statement])
  (bodyLedger : (receipt.formation.support capturedEnvironment).body.context.solvedRequirements =
    (context compiled.indexed caller.named).solvedRequirements)
  (bodyRuntime : RuntimeRequirementLedgerValid (receipt.formation.support capturedEnvironment).body.context)

include chosen facts found form singleton bodyLedger bodyRuntime in
/-- The genuine selected tree supplies its original child and Source typing. -/
theorem support_flow_preserves (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      callerProtocol (readiness bridge) condition (fun _ _ _ _ => True) functions
      (Program.ofChecked compiled.sourceProgram) (receipt.formation.function capturedEnvironment).evidence (fun _ => True)
      (source := (receipt.formation.function capturedEnvironment).source)
      (context := (receipt.formation.support capturedEnvironment).body.context)
      (registry := registry) (faults := faults) (administrative := administrative)
      (frameLayout := frameLayout) (globals := globals) size
      (scope := (receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      true (receipt.formation.function capturedEnvironment).body (receipt.formation.function capturedEnvironment).resultType
      (receipt.formation.code capturedEnvironment).receipt.resultCore (receipt.formation.support capturedEnvironment).body.flow := by
  have tree := (receipt.formation.support capturedEnvironment).body.tree
  have syntaxTree := (receipt.formation.support capturedEnvironment).body.syntaxTree
  obtain ⟨other, output, outputFound, sourceType, certified, coreType, flowEq⟩ := return_child tree singleton found form
  have sameNode := Option.some.inj (outputFound.symm.trans facts.found)
  subst other
  have sourceTyped := return_typed syntaxTree singleton found form
  have expressionTyped : ExpressionHasType (receipt.formation.function capturedEnvironment).source
      (receipt.formation.support capturedEnvironment).body.context literalId node.type := by
    rw [sourceType]
    exact sourceTyped
  simpa only [singleton, coreType, flowEq] using return_flow_preserves literalRoot literalId node receipt chosen capturedEnvironment
    facts bridge functions (receipt.formation.support capturedEnvironment).body.context
    (receipt.formation.function capturedEnvironment).evidence bodyLedger bodyRuntime found form certified
    expressionTyped sourceType condition (receipt.formation.support capturedEnvironment).body.unique size

include chosen facts found form singleton bodyLedger bodyRuntime in
/-- The same static tree supplies native reflection at its original flow. -/
theorem support_flow_reflects (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      callerProtocol (readiness bridge) condition (fun _ _ _ _ => True) functions
      (Program.ofChecked compiled.sourceProgram) (receipt.formation.function capturedEnvironment).evidence (fun _ => True)
      (source := (receipt.formation.function capturedEnvironment).source)
      (context := (receipt.formation.support capturedEnvironment).body.context)
      (registry := registry) (faults := faults) (administrative := administrative)
      (frameLayout := frameLayout) (globals := globals) size
      (scope := (receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      true (receipt.formation.function capturedEnvironment).body (receipt.formation.function capturedEnvironment).resultType
      (receipt.formation.code capturedEnvironment).receipt.resultCore (receipt.formation.support capturedEnvironment).body.flow := by
  have tree := (receipt.formation.support capturedEnvironment).body.tree
  have syntaxTree := (receipt.formation.support capturedEnvironment).body.syntaxTree
  obtain ⟨other, output, outputFound, sourceType, certified, coreType, flowEq⟩ := return_child tree singleton found form
  have sameNode := Option.some.inj (outputFound.symm.trans facts.found)
  subst other
  have sourceTyped := return_typed syntaxTree singleton found form
  have expressionTyped : ExpressionHasType (receipt.formation.function capturedEnvironment).source
      (receipt.formation.support capturedEnvironment).body.context literalId node.type := by
    rw [sourceType]
    exact sourceTyped
  simpa only [singleton, coreType, flowEq] using return_flow_reflects literalRoot literalId node receipt chosen capturedEnvironment
    facts bridge functions (receipt.formation.support capturedEnvironment).body.context
    (receipt.formation.function capturedEnvironment).evidence bodyLedger bodyRuntime found form certified
    expressionTyped sourceType condition size

section Entry
variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {mapping : LocationMap} {world : StoreTyping} {actualEnvironment : Environment}
  (captured : Captures compiled.indexed mapping world scope
    (receipt.formation.function capturedEnvironment).captured actualEnvironment)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (history : History (receipt.formation.code capturedEnvironment))
  (origin : SourceOrigin (receipt.formation.support capturedEnvironment) history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (first : State headers keys ⟨callerScope, mapping, world, before, store, canonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped (receipt.formation.function capturedEnvironment).context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes (receipt.formation.function capturedEnvironment).context
    before arguments (receipt.formation.support capturedEnvironment).body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)

include chosen facts found form singleton bodyLedger bodyRuntime origin observed beforeTyped argumentsTyped stable in
/-- Genuine parameter admission and the finite literal flow feed the original
finish once, retaining the same nested packet and whole pool. -/
theorem source_at_entry (size : Nat)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext) (receipt.formation.code capturedEnvironment) history (receipt.formation.support capturedEnvironment).body.toBody.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current (first.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = (receipt.formation.code capturedEnvironment).receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys ⟨((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope), entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size (receipt.formation.function capturedEnvironment) (receipt.formation.support capturedEnvironment).body.context
      entry.entry.environment entry.entry.heap outcome after) :
    ∃ packet value finalStore finalMap finalWorld,
      Evaluates entry.entry.actualBody entry.entry.store ((receipt.formation.code capturedEnvironment).receipt.body.rename entry.entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld (receipt.formation.function capturedEnvironment).resultType (receipt.formation.code capturedEnvironment).receipt.resultCore faults outcome value ∧ CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.entry.mapping finalMap ∧ WorldExtends entry.entry.world finalWorld ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions finalMap finalWorld
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function capturedEnvironment) (receipt.formation.support capturedEnvironment).body.context ((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.entry.environment entry.entry.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (receipt.formation.support capturedEnvironment).body.context outcome
        ⟨reached, packet⟩ ⟨((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope), finalMap, finalWorld, after, finalStore, entry.entry.canonical⟩ := by
  obtain ⟨packet, source, rows⟩ := CallableIndexedOwnedChosenNestedLambdaBodyContinuations.source_parameter_admission
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
    (receipt.formation.code capturedEnvironment) history (receipt.formation.support capturedEnvironment) origin
    functions owner observed rfl first beforeTyped argumentsTyped stable entry added length copied spine kept reached
  let nested : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State _ := ⟨reached, packet⟩
  have admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (receipt.formation.support capturedEnvironment).body.context nested := ⟨source.heapTyped, rows⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  have transfers : ∀ {sourceSize finalContext control after},
      RecursiveNamedLoopContracts.ExecutesAt sourceSize true (Program.ofChecked compiled.sourceProgram)
        (receipt.formation.support capturedEnvironment).body.context
        (receipt.formation.function capturedEnvironment).evidence
        (receipt.formation.function capturedEnvironment).source
        entry.entry.environment entry.entry.heap (receipt.formation.function capturedEnvironment).body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults (receipt.formation.code capturedEnvironment).compilation.internalReason control := by
    intro sourceSize finalContext control after executed
    have executed' : RecursiveNamedLoopContracts.ExecutesAt sourceSize true (Program.ofChecked compiled.sourceProgram)
        (receipt.formation.support capturedEnvironment).body.context
        (receipt.formation.function capturedEnvironment).evidence
        (receipt.formation.function capturedEnvironment).source entry.entry.environment entry.entry.heap [statement] finalContext control after := by
      simpa only [singleton] using executed
    exact return_transfers (receipt.formation.support capturedEnvironment).body.unique found form executed'
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when_with_transfers
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := Program.ofChecked compiled.sourceProgram)
      (tree := (receipt.formation.support capturedEnvironment).body.tree)
      (projection := (receipt.formation.support capturedEnvironment).body.projection)
      (unique := (receipt.formation.support capturedEnvironment).body.unique)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (fun _ _ _ _ => True)
      (receipt.formation.support capturedEnvironment).body.emitted (fun _ => True) size
      (support_flow_preserves literalRoot literalId node receipt chosen capturedEnvironment facts
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions found form
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) singleton bodyLedger bodyRuntime size)
      trivial trivial entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups
      entry.entry.actualTyped entry.entry.reference entry.entry.read entry.entry.unmapped nested gate admitted transfers trace
  exact ⟨packet, value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, post⟩

include chosen facts found form singleton bodyLedger bodyRuntime origin observed beforeTyped argumentsTyped stable in
/-- Native finish exposes a strict real flow child, which reflects into an
independently sized Source body at the same reached packet. -/
theorem native_at_entry (size : Nat)
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext) (receipt.formation.code capturedEnvironment) history (receipt.formation.support capturedEnvironment).body.toBody.toContext functions registry arguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current)
    (reached : State headers keys ⟨((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actual entry.store ((receipt.formation.code capturedEnvironment).receipt.body.rename entry.embedding) value finalStore) :
    ∃ packet sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize (receipt.formation.function capturedEnvironment) (receipt.formation.support capturedEnvironment).body.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld (receipt.formation.function capturedEnvironment).resultType (receipt.formation.code capturedEnvironment).receipt.resultCore faults outcome value ∧ CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions finalMap finalWorld
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function capturedEnvironment) (receipt.formation.support capturedEnvironment).body.context ((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (receipt.formation.support capturedEnvironment).body.context outcome
        ⟨reached, packet⟩ ⟨((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope), finalMap, finalWorld, after, finalStore, entry.canonical⟩ := by
  obtain ⟨packet, source, rows⟩ := CallableIndexedOwnedChosenNestedLambdaBodyContinuations.native_parameter_admission
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
    (receipt.formation.code capturedEnvironment) history (receipt.formation.support capturedEnvironment) origin
    functions owner observed rfl first beforeTyped argumentsTyped stable entry reached
  let nested : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State _ := ⟨reached, packet⟩
  have admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (receipt.formation.support capturedEnvironment).body.context nested := ⟨source.heapTyped, rows⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  have transfers : ∀ {sourceSize finalContext control after},
      RecursiveNamedLoopContracts.ExecutesAt sourceSize true (Program.ofChecked compiled.sourceProgram)
        (receipt.formation.support capturedEnvironment).body.context
        (receipt.formation.function capturedEnvironment).evidence
        (receipt.formation.function capturedEnvironment).source
        entry.environment entry.heap (receipt.formation.function capturedEnvironment).body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults (receipt.formation.code capturedEnvironment).compilation.internalReason control := by
    intro sourceSize finalContext control after executed
    have executed' : RecursiveNamedLoopContracts.ExecutesAt sourceSize true (Program.ofChecked compiled.sourceProgram)
        (receipt.formation.support capturedEnvironment).body.context
        (receipt.formation.function capturedEnvironment).evidence
        (receipt.formation.function capturedEnvironment).source entry.environment entry.heap [statement] finalContext control after := by
      simpa only [singleton] using executed
    exact return_transfers (receipt.formation.support capturedEnvironment).body.unique found form executed'
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when_with_transfers
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := Program.ofChecked compiled.sourceProgram)
      (tree := (receipt.formation.support capturedEnvironment).body.tree)
      (projection := (receipt.formation.support capturedEnvironment).body.projection)
      (unique := (receipt.formation.support capturedEnvironment).body.unique)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (fun _ _ _ _ => True)
      (receipt.formation.support capturedEnvironment).body.emitted (fun _ => True) (size+1) size (Nat.le_succ size)
      (fun child _ => support_flow_reflects literalRoot literalId node receipt chosen capturedEnvironment facts
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions found form
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) singleton bodyLedger bodyRuntime child)
      trivial trivial entry.environments entry.heaps entry.locals entry.lookups
      entry.actualTyped entry.reference entry.read entry.unmapped nested gate admitted transfers completed
  exact ⟨packet, sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, frame, metadata, exit, post⟩

include chosen facts found form singleton bodyLedger bodyRuntime origin observed beforeTyped argumentsTyped stable in
/-- A finite projection retains the actual returned nested state and relates
its full pool to the original base continuation. -/
theorem source_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
      (receipt.formation.code capturedEnvironment) history
      (receipt.formation.support capturedEnvironment).body.toBody.toContext functions owner first budget := by
  intro entry added length copied spine kept reached size _strict outcome after trace
  obtain ⟨packet, value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, exit, post⟩ :=
    source_at_entry (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton) (bodyLedger := bodyLedger) (bodyRuntime := bodyRuntime)
      (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
      (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) size entry added length copied spine kept reached trace
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, returned.val,
    (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller).related related⟩

include chosen facts found form singleton bodyLedger bodyRuntime origin observed beforeTyped argumentsTyped stable in
/-- The native continuation keeps its independently sized Source result and
projects the same returned nested state without changing protocol. -/
theorem native_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
      (receipt.formation.code capturedEnvironment) history
      (receipt.formation.support capturedEnvironment).body.toBody.toContext functions owner first budget := by
  intro entry reached size _strict value finalStore completed
  obtain ⟨packet, sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, exit, post⟩ :=
    native_at_entry (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton) (bodyLedger := bodyLedger) (bodyRuntime := bodyRuntime)
      (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
      (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) size entry reached completed
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, frame, metadata, exit, returned.val,
    (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller).related related⟩

end Entry
end SupportReturn
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaBodyContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaInvocationBounds
/-! A genuine chosen singleton-return Support supplies its literal continuation
internally. The original invocation installs parameters and restores the caller
once, preserving the independent Source and native grades and the full pool. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedLambdaEntryPrefix SourceCoreCallableIndexedFrames
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedChosenWordLiteralExpressionBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (literalRoot : LiteralRootReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (literalId : ExpressionId) (node : ExpressionNode)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory literalRoot.root (approved literalId) receipt)
  (capturedEnvironment : Dynamic.Environment)
  (facts : WordNodeFacts (caller := caller) literalId node)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {statement : StatementId} {statementNode : StatementNode}
  (found : (receipt.formation.function capturedEnvironment).source.lookupStatement? statement = some statementNode)
  (form : statementNode.form = .returnStmt (some literalId))
  (singleton : (receipt.formation.function capturedEnvironment).body = [statement])
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {mapping : LocationMap} {world : StoreTyping} {actualEnvironment : Environment}
  (captured : Captures compiled.indexed mapping world scope
    (receipt.formation.function capturedEnvironment).captured actualEnvironment)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (history : History (receipt.formation.code capturedEnvironment))
  (origin : SourceOrigin (receipt.formation.support capturedEnvironment) history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (first : State headers keys ⟨callerScope, mapping, world, before, store, canonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped (receipt.formation.function capturedEnvironment).context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes (receipt.formation.function capturedEnvironment).context
    before arguments (receipt.formation.support capturedEnvironment).body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world (receipt.formation.code capturedEnvironment).receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before (receipt.formation.function capturedEnvironment).context.locals
    (receipt.formation.function capturedEnvironment).captured)
  (reference : captured.canonical[(receipt.formation.code capturedEnvironment).referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))

include chosen facts found form singleton origin observed beforeTyped argumentsTyped stable represented heaps locals reference in
/-- The actual literal continuation feeds one original invocation and restoration. -/
theorem invocation_preserves (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence (receipt.formation.function capturedEnvironment).evidence before
      (.closure (receipt.formation.function capturedEnvironment)) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: actualEnvironment)
        store ((receipt.formation.code capturedEnvironment).body.rename captured.embedding.lift.lift) value finalStore ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
        (receipt.formation.code capturedEnvironment) functions first outcome after value finalStore finalMap finalWorld := by
  have bodyLedger : (receipt.formation.support capturedEnvironment).body.context.solvedRequirements =
      (context compiled.indexed caller.named).solvedRequirements := by
    exact (receipt.formation.support capturedEnvironment).body.valid.ledger.trans
      (congrArg (fun c : SourceCoreFunctions.Context => c.solvedRequirements)
        (receipt.formation.support capturedEnvironment).compilation)
  have continuation := CallableIndexedOwnedLiteralLambdaBodyContinuations.source_continuation
      (registry := registry) (faults := faults) (nativeArguments := nativeArguments)
      (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton)
      (bodyLedger := bodyLedger) (bodyRuntime := (receipt.formation.support capturedEnvironment).body.valid.runtime)
      (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
      (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) budget
  obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
    (receipt.formation.code capturedEnvironment) history
    (receipt.formation.support capturedEnvironment).body.toBody.toContext functions represented owner first heaps locals
    reference currentCarried
    (CallableIndexedLambdaTemplatePermission.lambda_allowed (receipt.formation.code capturedEnvironment) history)
    budget continuation trace within

include chosen facts found form singleton origin observed beforeTyped argumentsTyped stable represented heaps locals reference in
/-- The native child retains its own grade and uses the genuine closure frame. -/
theorem invocation_reflects (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: actualEnvironment)
        store ((receipt.formation.code capturedEnvironment).body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence (receipt.formation.function capturedEnvironment).evidence before
        (.closure (receipt.formation.function capturedEnvironment)) arguments outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
        (receipt.formation.code capturedEnvironment) functions first outcome after value finalStore finalMap finalWorld := by
  have bodyLedger : (receipt.formation.support capturedEnvironment).body.context.solvedRequirements =
      (context compiled.indexed caller.named).solvedRequirements := by
    exact (receipt.formation.support capturedEnvironment).body.valid.ledger.trans
      (congrArg (fun c : SourceCoreFunctions.Context => c.solvedRequirements)
        (receipt.formation.support capturedEnvironment).compilation)
  have continuation := CallableIndexedOwnedLiteralLambdaBodyContinuations.native_continuation
      (registry := registry) (faults := faults)
      (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton)
      (bodyLedger := bodyLedger) (bodyRuntime := (receipt.formation.support capturedEnvironment).body.valid.runtime)
      (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
      (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) budget
  obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
    (receipt.formation.code capturedEnvironment) history
    (receipt.formation.support capturedEnvironment).body.toBody.toContext functions represented owner first heaps locals
    reference currentCarried
    (CallableIndexedLambdaTemplatePermission.lambda_allowed (receipt.formation.code capturedEnvironment) history)
    (receipt.formation.support capturedEnvironment).body.frame budget continuation completed within

include chosen facts found form singleton origin observed beforeTyped argumentsTyped stable represented heaps locals reference in
/-- The original application edge carries that same restored invocation tuple. -/
theorem application_preserves (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence (receipt.formation.function capturedEnvironment).evidence before
      (.closure (receipt.formation.function capturedEnvironment)) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value (receipt.formation.code capturedEnvironment) captured.embedding history.native actualEnvironment,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
        (receipt.formation.code capturedEnvironment) functions first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result⟩ :=
    invocation_preserves (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton) (owner := owner) (captured := captured)
      (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed)
      (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
      (represented := represented) (heaps := heaps) (locals := locals) (reference := reference) budget trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

include chosen facts found form singleton origin observed beforeTyped argumentsTyped stable represented heaps locals reference in
/-- The actual strict application child reconstructs an independently sized Source call. -/
theorem application_reflects (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value (receipt.formation.code capturedEnvironment) captured.embedding history.native actualEnvironment,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence (receipt.formation.function capturedEnvironment).evidence before
        (.closure (receipt.formation.function capturedEnvironment)) arguments outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
        (receipt.formation.code capturedEnvironment) functions first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton) (owner := owner) (captured := captured)
      (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed)
      (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
      (represented := represented) (heaps := heaps) (locals := locals) (reference := reference) budget applied
    (Nat.le_trans (Nat.le_of_lt smaller) within)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaBuiltinReceipts
/-! Accepted ordinary sites with genuine same-Code builtin body receipts yield
rank-one formation certificates. The supported bodies retain the original
imperative/control/assignment/match grammar with builtin expression children;
no named, indirect or method body child is added by this conversion.
Only the existing static Tree transport changes certificate and syntax facets. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaBuiltinReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedLambdaNestedRuntimeCertificates
open CallableIndexedLambdaNestedRuntimeBodyMeaning RecursiveNamedLambdaFormationHeads
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- Finite syntax projection follows only the fixed fragment wrappers. It
keeps the actual parent lookup and does not traverse expression children. -/
private theorem builtin_nodes {source : TypedSource} {id : ExpressionId}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) : Nodes source id := by
  cases syntaxTree with
  | fragment general =>
    cases general with
    | fragment recursive =>
      cases recursive with
      | fragment members =>
        cases members with
        | fragment constructors =>
          cases constructors with
          | fragment conditionals =>
            cases conditionals with
            | primitive primitives =>
              cases primitives with
              | product products => cases products <;> exact ⟨_, by assumption⟩
              | _ => exact ⟨_, by assumption⟩
            | _ => exact ⟨_, by assumption⟩
          | _ => exact ⟨_, by assumption⟩
        | _ => exact ⟨_, by assumption⟩
      | _ => exact ⟨_, by assumption⟩
    | _ => exact ⟨_, by assumption⟩
  | _ => exact ⟨_, by assumption⟩

private theorem lift_builtin {rank fuel : Nat} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCoreFunctions.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked)
      source context compilation.solvedRequirements reasonAt scope id lowered) :
    Certificates (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram)
      (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults rank)
      rank caller headers compilation fuel
      source context evidence compilation.solvedRequirements reasonAt scope id lowered := by
  obtain ⟨tree, sites⟩ := receipt
  exact ⟨.fragment tree, .fragment tree sites⟩

private theorem lift_sites {source : TypedSource} {compilation : SourceCoreFunctions.Context}
    {active : TypeSystem.Substitution} {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {fuel rank : Nat} {evidence : Dynamic.EvidenceEnvironment} {reasonAt : ExpressionId → Word}
    (unique : NodeOccurrencesUnique source)
    {tree : GenericImperativeMatch.Tree compiled.indexed.layouts compilation.owner active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length onError
      (.initial compiled.compatible.checked) source (CompatibleExpressionBuiltins.Syntax source)
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked)
        source context compilation.solvedRequirements reasonAt)
      compiled.indexed.layouts.definitions administrative context scope (.statements true statements) expected type flow}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ next : GenericImperativeMatch.Tree compiled.indexed.layouts compilation.owner active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length onError
      (.initial compiled.compatible.checked) source (Nodes source)
      (fun context => Certificates (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram)
      (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults rank)
      rank caller headers compilation fuel
        source context evidence compilation.solvedRequirements reasonAt)
      compiled.indexed.layouts.definitions administrative context scope (.statements true statements) expected type flow,
      next.CatalogSites .reachable registry faults := by
  have avoids : Avoids source (statements.map NodeId.statement) [] := by intro id member; cases member
  exact CallableLambdaViewMatchRuntimeCertificates.transport_sites_with
    (LocalView.refl source) avoids unique
    (fun _ _ syntaxTree => builtin_nodes syntaxTree)
    (fun _ _ _ _ _ receipt => lift_builtin caller receipt) sites
    (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {scope : SourceCoreLocalCell.Scope}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed caller.named parameters result statements
    context evidence [] scope (nativePrefix (values := .initial compiled.compatible.checked) caller))
  (body : CallableIndexedLambdaRuntimeBody.Body (values := .initial compiled.compatible.checked) site.code
    (Program.ofChecked compiled.sourceProgram) registry faults)

include body in
/-- Both real Trees and their diagnostic ledgers are lifted at the same flow.
The accepted callback, original ClosureFrame and full body context are copied
from the authentic same-Code receipt, without a ranked-support premise. -/
theorem body_at_zero : Nonempty
    (BodyAt (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 0 site.code) := by
  have viewUnique := site.code.viewOfSource.unique body.unique
  obtain ⟨actualTree, actualSites⟩ := lift_sites (rank := 0) (evidence := evidence)
    caller viewUnique body.actualSites
  obtain ⟨tree, sites⟩ := lift_sites (rank := 0) (evidence := evidence)
    caller body.unique body.sites
  have original : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) Nodes
      (fun fuel source context => Certificates (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram)
      (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 0)
        0 caller headers
        site.code.compilation fuel source context evidence site.code.compilation.solvedRequirements site.code.reasonAt)
      site.code (Program.ofChecked compiled.sourceProgram) registry faults := {
    toContext := body.toContext, frame := body.frame, readFuel := body.readFuel, policy := body.policy,
    callback := body.callback, flow := body.flow, generated := body.generated, projection := body.projection,
    emitted := body.emitted, actualTree := actualTree, actualSites := actualSites,
    tree := tree, sites := sites, valid := body.valid, unique := body.unique }
  have receipt : CallableIndexedLambdaNestedRuntimeCertificates.BodyReceipt

      (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
        (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 0)
      0 caller headers site.code registry faults :=
    ⟨rfl, site.compilation, site.active, rfl, original⟩
  have equation := CallableIndexedLambdaNestedRuntimeCertificates.BodyAt.eq_1
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 0 site.code
  exact ⟨equation.symm ▸ receipt⟩

include body in
/-- Actual accepted Site emission and original raw Source metadata supply the
rank-one ordinary formation certificate consumed by the generic admitted leaf. -/
theorem certificate_of_site
    (sourceType : site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (requirements : site.code.sourceNode.requirements = []) (coercions : site.code.sourceNode.coercions = []) :
    CallableIndexedOwnedOrdinaryLambdaFormationHeads.Certificate (headers := headers)
      (registry := registry) (faults := faults) (source := CallableIndexedNamedGeneration.source caller.named)

    (context := context) (evidence := evidence) caller scope site.code.id site.code.lowered := by
  obtain ⟨ranked⟩ := body_at_zero caller site body
  have supported : LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 1 0 site.code := by
    simpa only [LowerSupport, dif_pos (show 0 < 1 by decide)] using ranked
  exact ⟨1, CallableIndexedLambdaNestedRuntimeCertificates.Lambda.of_site
     (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram)
    (support := LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) headers caller registry faults 1)
    (source := CallableIndexedNamedGeneration.source caller.named)
    (context := context) (evidence := evidence) (caller := caller) site (show 0 < 1 by decide) supported
    (by simpa only [CallableIndexedLambdaGeneration.closure] using site.code.sourceFound)
    sourceType requirements coercions⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaBuiltinReceipts
end
