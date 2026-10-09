import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureAssociationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadFaultPolicies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredFunctionModelReceipts

/-! Positive contextual ordinary members follow one actual initialized allocation
and one initialized local read. The original accepted Selection supplies the
same code's escaped-control row. Source typing comes from the real judgment
and deep input heap; the actual current state and full member stay associated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedAllocationCompletion TypedLexicalControl
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Real Source typing fixes the reported type of the exact stored occurrence. -/
theorem reported_type_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : node.type = type := by
  obtain ⟨original, contains, sameType⟩ := typed.stored_type
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases same
  exact sameType

/-- This static list induction only identifies the actual reported type row.
It carries no child evaluation, body law or mutual semantic induction. -/
theorem source_types_at_tree {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {ids : List ExpressionId} {types reported : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (tree : DataExpressionSequence.Tree source certificate scope ids reported codes)
    (typed : ExpressionsHaveTypes source context ids types) : types = reported := by
  induction tree generalizing types with
  | nil => cases typed; rfl
  | single found _ =>
    cases typed with
    | cons head tail =>
      cases tail
      exact congrArg (fun type => [type]) (reported_type_at unique found head).symm
  | cons found _ _ ih =>
    cases typed with
    | cons head tail =>
      exact congr (congrArg List.cons (reported_type_at unique found head).symm) (ih tail)

section Selection
variable {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (formation : CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
    (registry := registry) (faults := faults) caller context evidence scope id lowered)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {parentScope : SourceCoreLocalCell.Scope}
  {parentId callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {parentLowered : SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source parentScope
    parentId callee ids metadata reasonAt parentLowered)
  {nativeContext : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler nativeContext)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared formation.site.code)

include selected in
/-- Recapture changes the Source capture environment only. The authentic
accepted call's fault row belongs to exactly this retained compiler context. -/
theorem escaped_at_formation (environment : Dynamic.Environment) :
    faults .controlEscapedFunction (formation.toFormation.code environment).compilation.internalReason :=
  selected.escaped

include selected in
/-- Ordered argument counts and native packing are consequences of this
original Selection and compiler vector, before any argument execution. -/
theorem selected_argument_shape :
    ids.length = formation.site.code.receipt.loweredParameters.length ∧
    SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (formation.site.code.receipt.loweredParameters.map Prod.snd) := by
  have counts := congrArg List.length selected.nativeTypes
  simp only [List.length_map] at counts
  exact ⟨compiler.ordered_children.1.trans counts,
    congrArg SourceCoreCompatibleCatalog.packTypes selected.nativeTypes⟩

include selected in
/-- Every accepted static call facet is retained at the same recaptured code.
Only the Source capture environment changes; no codebook or policy is selected. -/
theorem selection_at_formation (environment : Dynamic.Environment) :
    CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
      (certificate := certificate) compiler prepared (formation.toFormation.code environment) :=
  ⟨selected.children, selected.nativeTypes, selected.escaped, selected.rawResult,
    selected.nativeResult, selected.stageAccepted, selected.arityAccepted⟩

include selected in
/-- The raw argument bundle uses the original Source typing row, independently
of native projection. Lookup uniqueness aligns it with the accepted child Tree. -/
theorem selected_source_bundle {argumentContext : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source argumentContext ids types) :
    TypeSystem.Ty.productMany types = TypeSystem.Ty.productMany
      (formation.site.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) :=
  congrArg TypeSystem.Ty.productMany (source_types_at_tree unique selected.children typed)
end Selection

variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Core.Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- The initialized cell carries a positive member as an additional receipt.
The Source location and native target are the original allocation/read witnesses. -/
def StoredAt
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (location : Dynamic.Location) (function : Dynamic.Closure) (native : Core.Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameterCore resultCore : Ty) : Prop :=
  Member headers keys registry faults mapping world function native bindings parameterCore resultCore ∧
  ∃ target, ReferenceRepresents mapping world location target (CallableContract.functionType parameterCore resultCore) ∧
    Dynamic.Heap.Reads heap location ⟨FunctionValues.sourceType function, some (.closure function), none⟩ ∧
    store.read? target = some (.inRight .unit native)

theorem payload_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) :=
  .function member.represents

/-- Mutation or extension never manufactures a live stored value. Both actual
future reads are required alongside genuine map/world growth. -/
theorem StoredAt.extend_with_reads
    {heap futureHeap : Dynamic.Heap} {store futureStore : Store} {location : Dynamic.Location}
    (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (read : Dynamic.Heap.Reads futureHeap location ⟨FunctionValues.sourceType function, some (.closure function), none⟩)
    (nativeReads : ∀ target, ReferenceRepresents mapping world location target (CallableContract.functionType parameterCore resultCore) →
      futureStore.read? target = some (.inRight .unit native)) :
    StoredAt headers keys registry faults futureMapping futureWorld futureHeap futureStore location function native bindings parameterCore resultCore := by
  obtain ⟨member, target, reference, _, _⟩ := stored
  exact ⟨member.extend maps worlds, target, reference.extend maps worlds, read, nativeReads target reference⟩

section FormationMember
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {parentScope : SourceCoreLocalCell.Scope}
  {parentId callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation source parentScope
    parentId callee ids metadata reasonAt lowered)
  {nativeContext : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler nativeContext)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared code)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

include profile prefixContext observed provenance inclusion selected in
/-- One original contextual formation retains its complete traces and
represented value, plus the same positive member for later initialized reads.
The escaped row is supplied by the actual accepted compiler selection. -/
theorem formation_member_from_selection
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual)) store ∧
    functions.Represents registry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) ∧
    Member headers keys registry faults mapping world function
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  exact CallableIndexedOwnedContextualStoredClosureAssociationReceipts.formation_member
    (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (prefixContext := prefixContext)
    (observed := observed) (provenance := provenance) (functions := functions)
    (inclusion := inclusion) (escaped := selected.escaped) stored ordinary coercions

end FormationMember

section Allocation
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}

local notation "receiving" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile

/-- The positive constructor supplies the payload relation, and the original
stateful producer runs once. Every output belongs to its same allocation tuple. -/
theorem allocate_initialized
    (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry receiving))
    {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (binderType : binder.scheme.body = FunctionValues.sourceType function)
    (payloadType : payload = CallableContract.functionType parameterCore resultCore)
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {nativeFrame : NativeFrame} {location : Dynamic.Location}
    (valueTyped : Dynamic.ValueHasType context before (.closure function) binder.scheme.body)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry receiving mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame nativeFrame))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some (.closure function)) location after)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation nativeFrame)
    (admitted : Admission bridge context initial) :
    ∃ captured,
      Captures (native :: canonical)
        (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      let closureValue := native
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame nativeFrame,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit closureValue]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (closureValue :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry receiving nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: closureValue :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: closureValue :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame nativeFrame) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ∃ (_maps : LocationMap.Extends mapping nextMap) (_worlds : WorldExtends world nextWorld),
        Dynamic.HeapMetadataExtend before after ∧
        ReferenceRepresents nextMap nextWorld location (store.length + 2) payload ∧
        StoredAt headers keys registry faults nextMap nextWorld after nextStore location function native bindings parameterCore resultCore ∧
        ∃ reached : callerProtocol.State
            ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
          callerProtocol.Relates initial reached ∧
          Relates (bridge.pool initial) (bridge.pool reached) ∧
          Admission bridge nextContext reached := by
  have represented : ValueRep compiled.compatible.checked registry receiving mapping world
      binder.scheme.body (.closure function)
      native payload := by
    rw [binderType, payloadType]
    exact payload_member profile member
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related, nextAdmission⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge receiving definitions registered
      producer.toOrdinary mono extended ordinary allocation annotation same valueTyped represented
      environments heaps locals agrees actualTyped reference read allocated initial ready admitted
  have maps : LocationMap.Extends mapping (mapping ++ [store.length + 2]) := ⟨_, rfl⟩
  have worlds : WorldExtends world
      (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) := ⟨_, rfl⟩
  have freshReference : ReferenceRepresents (mapping ++ [store.length + 2])
      (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload])
      location (store.length + 2) payload := by
    refine ⟨?_, ?_⟩
    · rw [allocated.location_fresh, ← heaps.length_eq]
      simp
    · cases nextTyped with
      | cons typed _ =>
        cases typed with
        | cellRef found => exact found
  have stored : StoredAt headers keys registry faults (mapping ++ [store.length + 2])
      (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode frame nativeFrame,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit native]) location function native bindings parameterCore resultCore := by
    refine ⟨member.extend maps worlds, store.length + 2,
      payloadType ▸ freshReference, ?_, ?_⟩
    · change after.Reads location ⟨FunctionValues.sourceType function, some (.closure function), none⟩
      simpa only [binderType] using allocated.reads_new
    · simp [Store.read?] <;> rfl
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps,
    nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation,
    maps, worlds, .of_allocation allocated, freshReference, stored,
    reached, related, bridge.related related, nextAdmission⟩

end Allocation

section Read
open CompatibleExpressionReads
variable {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : Certificate fuel (.initial compiled.compatible.checked) source scope id reason code)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}

/-- The real binder and initialized cell exclude the reached empty witness. -/
theorem initialized_policy
    (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    UninitializedPolicy certificate context environment heap faults := by
  intro other cell witness
  have same := witness.lookup.functional lookup
  subst other
  obtain ⟨_, target, reference, read, nativeRead⟩ := stored
  have same := witness.read.functional read
  subst cell
  cases witness.empty

/-- Genuine lexical and stored receipts construct the exact initialized
Source/native read; no heap-relation inverse supplies the qualified member. -/
theorem initialized_traces
    (binding : StaticBinding certificate context)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    (CallableContract.functionType parameterCore resultCore) = certificate.type ∧
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence source environment heap
      id (.closure function) heap ∧
    Evaluates actual store (code.rename ξ) (.inRight .word native) store := by
  rcases certificate with ⟨node, readType, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  dsimp only at *
  obtain ⟨_member, target, reference, read, nativeRead⟩ := stored
  obtain ⟨other, cell, otherLookup, otherRead, cellType, _⟩ := locals.lookup binding.declared
  have same := otherLookup.functional lookup
  subst other
  have same := otherRead.functional read
  subst cell
  have nominal : FunctionValues.sourceType function = declared.scheme.body := cellType
  have notMapping : ¬ ∃ key value, declared.scheme.body = .mapping key value := by
    intro ⟨key, value, mapped⟩
    have mapped : FunctionValues.sourceType function = .mapping key value := nominal.trans mapped
    cases mapped
  obtain ⟨selectedTarget, nativeLookup, selectedReference⟩ := environments.lookup_visible lookup slot
  have same : selectedTarget = target := Option.some.inj (selectedReference.mapped.symm.trans reference.mapped)
  subst selectedTarget
  have sameType : CallableContract.functionType parameterCore resultCore = readType := by
    exact (Ty.sum.inj (Option.some.inj (reference.typed.symm.trans selectedReference.typed))).2
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id (.closure function) heap := by
    have formTrace : Dynamic.ExpressionFormEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
        source environment heap node.form [] [] (.closure function) heap :=
      form ▸ Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup read rfl rfl
    exact .intro (lookupExpression?_sound metadata.found)
      (by rw [metadata.requirements, metadata.coercions]; exact formTrace)
      (by rw [metadata.coercions]; exact .nil)
  refine ⟨sameType, sourceTrace, ?_⟩
  cases emitted with
  | ordinary _ =>
    change Evaluates actual store (OptionalCell.read readType (.var (ξ index)) reason)
      (.inRight .word native) store
    exact OptionalCell.read_success reason (.var (agrees nativeLookup)) nativeRead
  | mapping declared _ => exact False.elim (notMapping ⟨_, _, declared⟩)

/-- One original read producer retains its broad result, heap/frame/metadata
and the same initialized qualifier. Its empty-cell policy is derived above. -/
theorem read_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id (.value (.closure function)) heap ∧
    Evaluates actual store (code.rename ξ) (.inRight .word native) store ∧
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile))
      mapping world certificate.node.type certificate.type faults (.value (.closure function)) (.inRight .word native) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world heap store ∧
    AdministrativePreserved mapping store mapping store ∧ Dynamic.HeapMetadataExtend heap heap ∧
    StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore := by
  obtain ⟨_, sourceTrace, nativeTrace⟩ := initialized_traces certificate binding environments locals agrees stored lookup
  obtain ⟨outcome, after, result, finalStore, actualSource, actualNative, related, finalHeaps, frame, metadata⟩ :=
    certificate.evaluates_with_diagnostics
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      extension (Program.ofChecked compiled.sourceProgram) context evidence binding environments heaps locals agrees
      (initialized_policy certificate stored lookup)
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic actualNative nativeTrace
  subst result
  subst finalStore
  obtain ⟨sameOutcome, sameHeap⟩ := source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup stored.2.choose_spec.2.1 rfl actualSource (.value sourceTrace)
  subst outcome
  subst after
  exact ⟨actualSource, actualNative, related, finalHeaps, frame, metadata, stored⟩

section Parent
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {childFuel : Nat}
  {parentCompilation : SourceCoreFunctions.Context} {parentId : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body childFuel parentCompilation source scope parentId id ids metadata reasonAt lowered)
  {calleeNode : ExpressionNode}
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
  (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)

include evidence unique locals stored lookup in
/-- Raw success typing comes from the actual Source judgment and typed input
heap. Neither a native type nor erased function representation supplies it. -/
theorem source_value_typed
    (typed : ExpressionHasType source context id certificate.node.type)
    (heapTyped : Dynamic.HeapWellTyped context heap) :
    Dynamic.ValueHasType context heap (.closure function) certificate.node.type := by
  generalize reportedEq : certificate.node.type = reported at typed
  cases typed with
  | @intro _ _ node raw plan contains formTyped rawEq _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans certificate.metadata.found)
    subst node
    have path := requirements.outputPath
    rw [certificate.metadata.coercions] at path
    cases path
    rw [certificate.form] at formTyped
    have formTrace : Dynamic.ExpressionFormEvaluates (Program.ofChecked compiled.sourceProgram)
        context evidence source environment heap
        (.reference certificate.name (.local certificate.binder)) [] [] (.closure function) heap :=
      Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup stored.2.choose_spec.2.1 rfl rfl
    exact (Dynamic.ExpressionFormEvaluates.referencePreserves locals heapTyped formTyped formTrace).1

include evidence unique locals stored lookup in
/-- The initialized read's admission belongs to the identical input state,
heap and row pool, independently of the eventual argument/application suffix. -/
theorem post_admission
    (typed : ExpressionHasType source context id certificate.node.type)
    (admitted : Admission bridge context initial) :
    PostAdmission bridge context certificate.node.type (.value (.closure function)) initial := by
  refine ⟨admitted.rows, ?_⟩
  intro result same
  cases same
  exact ⟨source_value_typed (evidence := evidence) (certificate := certificate) (unique := unique)
      (locals := locals) (stored := stored) (lookup := lookup) typed admitted.heap,
    admitted.heap⟩

include extension binding unique environments heaps locals agrees stored lookup in
/-- One original accepted read produces the same callee Source trace, genuine
ValuePost and positive invocation Association. Source/native grades stay distinct. -/
theorem callee_post
    (sameCode : compiler.calleeCode.expression = code)
    (sameNode : calleeNode = certificate.node) (sameType : compiler.calleeCode.type = certificate.type)
    (sourceTyped : ExpressionHasType source context id certificate.node.type)
    (admitted : Admission bridge context initial) :
    ∃ sourceSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment heap id (.closure function) heap ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
        compiler initial (.closure function) heap native store mapping world ∧
      CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
        function native bindings parameterCore resultCore ∧
      CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native
        (CallableContract.functionType parameterCore resultCore) ∧
      StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore := by
  obtain ⟨sourceTrace, nativeTrace, represented, finalHeaps, frame, metadata, retained⟩ :=
    read_member certificate profile extension binding unique environments heaps locals agrees stored lookup
  have payload : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world certificate.node.type (.closure function) native certificate.type := by
    cases represented with
    | value related => exact related
  have admittedPost := post_admission (evidence := evidence) (certificate := certificate)
    (bridge := bridge) (initial := initial) (unique := unique) (locals := locals)
    (stored := stored) (lookup := lookup) sourceTyped admitted
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size sourceTrace
  cases sized with
  | value sized =>
    refine ⟨sourceSize, sized, ?_, stored.1.association, stored.1.selection, retained⟩
    unfold CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost
    rw [sameCode, sameNode, sameType]
    exact ⟨nativeTrace, payload, finalHeaps, ⟨[], by simp⟩, ⟨[], by simp⟩,
      frame, metadata, initial, callerProtocol.refl initial, admittedPost⟩
end Parent
end Read
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts
