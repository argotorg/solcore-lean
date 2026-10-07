import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlTree
import Solcore.SourceSemantics.CoreLowering.LoopStatementLayout
import Solcore.SourceSemantics.CoreLowering.ProtectedStateOrdinaryAllocation

/-! Mode-aware source let inversion and actual marked allocation. The helpers
retain the snapshot, marker, and source payload cells and live frame lookup. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedLexicalControl
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof
open TypedScopedStatements (Executes)

private theorem extended_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

private theorem locals_allocate {owner : Resolved.DeclarationId} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {location : Dynamic.Location}
    (extended : BinderExtends owner context binder nextContext) (mono : binder.scheme.quantified = [])
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after) :
    Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
  cases extended
  exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))

theorem source_view_absent {mode : Bool} {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none) (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    ∃ location middle, Dynamic.Heap.Allocates before binder.scheme.body none location middle ∧
      Executes mode program nextContext evidence source ((binder.id, location) :: environment)
        middle rest finalContext outcome after := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨extension, location, same, allocated⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases extended_eq extended extension
      cases same
      exact ⟨location, _, allocated, by cases mode <;> exact .control tail⟩
    · obtain ⟨_, _, same, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases same; cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, tail⟩
    · exact False.elim (ScalarStatementViews.letUninitialized_cannot_fault unique contains form mono head)
    · obtain ⟨extension, location, same, allocated⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases extended_eq extended extension
      cases same
      exact ⟨location, _, allocated, by cases mode <;> exact .fault tail⟩

theorem source_view_initialized {mode : Bool} {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {initializer : ExpressionId} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧
      Dynamic.ExpressionFaults program context evidence source environment before initializer reason after) ∨
    (∃ value location middle allocatedHeap,
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location allocatedHeap ∧
      Executes mode program nextContext evidence source ((binder.id, location) :: environment)
        allocatedHeap rest finalContext outcome after) := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨extension, location, value, middle, same, initial, allocated⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases extended_eq extended extension
      cases same
      exact .inr ⟨value, location, middle, _, initial, allocated, by cases mode <;> exact .control tail⟩
    · obtain ⟨_, _, _, _, same, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases same; cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨same, head⟩ | ⟨_, _, _, head, tail⟩
    · exact .inl ⟨_, same, rfl, ScalarStatementViews.letInitialized_fault unique contains form mono head⟩
    · obtain ⟨extension, location, value, middle, same, initial, allocated⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases extended_eq extended extension
      cases same
      exact .inr ⟨value, location, middle, _, initial, allocated, by cases mode <;> exact .fault tail⟩

theorem sequence_rename (type : Ty) (initializer allocation body : Expr) (ξ : Renaming) :
    (CompatibleStatementInitialized.sequence type initializer allocation body).rename ξ =
      LanguageResult.bind (LocalLoop.controlType type) (initializer.rename ξ)
        (.letE (allocation.rename ξ.lift) (body.rename (Renaming.comp (Renaming.insertion 0) ξ).lift)) := by
  rw [LoopStatements.rename_insert_lift]
  simp [CompatibleStatementInitialized.sequence, LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne]

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

namespace Stateful
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))

include definitions registered in
/-- The ordinary absent allocation carries its exact selected capture and
the producer's concrete bound post-state into the lexical continuation. -/
theorem allocate_absent {context nextContext : SourceSemantics.Context} {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native) :
    ∃ captured,
      Captures canonical (absentRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) ambient.definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename ξ) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree ξ.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual) (OptionalCell.referenceType payload :: actualContext) ambient.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  have referenceAt : canonical[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (absentRequest source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (absentRequest source scope binder payload) = false := ordinary
    change canonical[scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
      (absentRequest source scope binder payload) then 0 else 1) + globals]? = _
    rw [named]
    exact reference
  obtain ⟨captured, captures, capturedTyped, evaluated, nextHeaps, nextReference, preservation, transition⟩ :=
    producer.complete allocation annotation same definitions registered environments
      (show EnvironmentsAgree Renaming.id canonical canonical from fun found => found) heaps referenceAt read
      (.absent rfl) (.uninitialized projection) allocated initial ready
  refine ⟨captured, captures, capturedTyped, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inl rfl) evaluated agrees,
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference,
    nextHeaps, locals_allocate extended mono locals allocated, agrees.lift _,
    .cons (.cellRef nextReference.typed) (actualTyped.weaken ⟨_, rfl⟩), ?_, ?_, preservation, transition⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read


variable {context nextContext : SourceSemantics.Context}

include definitions registered in
/-- The successful initializer's reached state is the input to allocation;
its hidden value slot is retained only in the actual Core environment. -/
theorem allocate_initialized {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep values.checked registry functions mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native) :
    ∃ captured,
      Captures (value :: canonical) (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) ambient.definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) ambient.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  have canonicalLayout : EnvironmentsAgree (initializedRequest source scope binder payload).references canonical (value :: canonical) := fun found => found
  have referenceAt : (value :: canonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (initializedRequest source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest source scope binder payload) = false := ordinary
    change (value :: canonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest source scope binder payload) then 0 else 1) + globals)]? = _
    rw [named]
    exact reference
  obtain ⟨captured, captures, capturedTyped, evaluated, nextHeaps, nextReference, preservation, transition⟩ :=
    producer.complete allocation annotation same definitions registered environments
      canonicalLayout heaps referenceAt read (.initialized rfl rfl) (.initialized represented) allocated initial ready
  have nextLocals : Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
    cases extended
    exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))
  have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := fun found => agrees found
  refine ⟨captured, captures, capturedTyped, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl) evaluated (agrees.lift value),
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference, nextHeaps, nextLocals, inserted.lift _,
    .cons (.cellRef nextReference.typed) (.cons (represented.runtime_hasType.weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)), ?_, ?_, preservation, transition⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

end Stateful

include definitions registered in
/-- Compatibility wrapper for the existing ordinary allocation API. -/
theorem allocate_absent {context nextContext : SourceSemantics.Context} {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename ξ) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree ξ.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual) (OptionalCell.referenceType payload :: actualContext) ambient.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore := by
  obtain ⟨captured, _, _, evaluated, environments, heaps, locals, agrees, typed, reference, read, frame, _⟩ :=
    Stateful.allocate_absent functions definitions registered
      ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.OrdinaryAllocation.unitProducer layouts frame
        (CompatibleAmbientHeap.payloadModel values.checked registry functions))
      mono extended ordinary projection allocation annotation same
      environments heaps locals agrees actualTyped reference read allocated () True.intro
  exact ⟨captured, evaluated, environments, heaps, locals, agrees, typed, reference, read, frame⟩

variable {context nextContext : SourceSemantics.Context}

include definitions registered in
theorem allocate_initialized {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep values.checked registry functions mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) ambient.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore := by
  obtain ⟨captured, _, _, evaluated, environments, heaps, locals, agrees, typed, reference, read, frame, _⟩ :=
    Stateful.allocate_initialized functions definitions registered
      ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.OrdinaryAllocation.unitProducer layouts frame
        (CompatibleAmbientHeap.payloadModel values.checked registry functions))
      mono extended ordinary allocation annotation same represented
      environments heaps locals agrees actualTyped reference read allocated () True.intro
  exact ⟨captured, evaluated, environments, heaps, locals, agrees, typed, reference, read, frame⟩

/-- The same reached-prefix relation as the ordinary mixed profile. -/
abbrev LexicalResult := CompatibleStatementMixed.LexicalResult

theorem LexicalResult.bind {checked : SourceCoreCompatibleCatalog.Checked} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {owner : Resolved.DeclarationId} {context nextContext resultContext : SourceSemantics.Context}
    {scope : Scope} {environment : Dynamic.Environment} {after : Dynamic.Heap} {binder : TypedBinder} {payload : Ty}
    {location : Dynamic.Location}
    (extended : BinderExtends owner context binder nextContext)
    (result : LexicalResult checked definitions mapping world administrative owner nextContext
      ((binder.id, payload) :: scope) ((binder.id, location) :: environment) resultContext after) :
    LexicalResult checked definitions mapping world administrative owner context scope environment resultContext after := by
  obtain ⟨resultScope, resultEnvironment, canonical, reached, environments, locals⟩ := result
  exact ⟨resultScope, resultEnvironment, canonical, .bind extended reached, environments, locals⟩

theorem valid_extend {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
    {owner : Resolved.DeclarationId} {context nextContext : SourceSemantics.Context} {binder : TypedBinder}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extended : BinderExtends owner context binder nextContext) :
    CompatibleExpressionLiterals.ContextValid solved nextContext evidence := by
  cases extended
  exact ⟨valid.ledger, valid.valid.transport rfl rfl rfl, valid.covers⟩


end Solcore.SourceSemantics.CoreLowering.TypedLexicalControl
