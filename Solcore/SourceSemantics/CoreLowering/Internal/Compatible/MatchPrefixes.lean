import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PatternsAndArms
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Matches
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalWhile
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Payloads
import Solcore.Core.Internal.Renaming

/-!
# Compatible matches: prefixes

Arm scopes, hidden allocation, selection prefixes, match meaning and native arms and children.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes
/-! Static source scope correspondence for a real match arm. Compiler
bindings are authenticated by the independently typed source pattern and its
retained declaration. The hidden scrutinee remains a separate internal slot. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatiblePatternCertificates CompatibleMatchCertificates

theorem rootBinder_filter
    {source : TypedSource} {id : Resolved.LocalId} {declared : TypedBinder}
    (accepted : SourceCoreDataPlaces.rootBinder source id = .ok declared) :
    (SourceCoreDataPlaces.declaredBinders source).filter (fun candidate => decide (candidate.id = id)) = [declared] := by
  unfold SourceCoreDataPlaces.rootBinder at accepted
  by_cases owned : id.owner ≠ source.owner
  · simp [owned, throw, bind, Except.bind] at accepted
  · simp only [owned, ↓reduceIte, bind, Except.bind] at accepted
    generalize selectedEq : (SourceCoreDataPlaces.declaredBinders source).filter
      (fun candidate => decide (candidate.id = id)) = selected at accepted
    cases selected with
    | nil => contradiction
    | cons first tail =>
      cases tail with
      | cons => contradiction
      | nil =>
        by_cases mono : first.scheme.quantified.isEmpty = true
        · by_cases empty : first.schemeRequirements.isEmpty = true
          · simp [mono, empty, pure, Except.pure] at accepted
            subst declared
            rfl
          · simp [mono, empty, throw] at accepted
        · simp [mono, throw] at accepted

theorem rootBinder_identifies
    {source : TypedSource} {binder declared : TypedBinder}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (accepted : SourceCoreDataPlaces.rootBinder source binder.id = .ok declared) : declared = binder := by
  have filtered : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun candidate => decide (candidate.id = binder.id)) := List.mem_filter.mpr ⟨member, by simp⟩
  rw [rootBinder_filter accepted] at filtered
  exact (List.mem_singleton.mp filtered).symm

theorem scope_internal
    {source : TypedSource} {scope : Scope} {context : SourceSemantics.Context}
    {internal : Resolved.LocalId} (payload : Ty)
    (absent : internal ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id))
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations source ((internal, payload) :: scope) context := by
  intro id declared index type selected authentic
  by_cases same : internal = id
  · subst id
    have present : declared ∈ (SourceCoreDataPlaces.declaredBinders source).filter
        (fun candidate => decide (candidate.id = internal)) := by
      rw [rootBinder_filter authentic]
      exact List.mem_singleton_self declared
    obtain ⟨member, sameId⟩ := List.mem_filter.mp present
    have sameId : declared.id = internal := of_decide_eq_true sameId
    exact False.elim (absent (List.mem_map.mpr ⟨declared, member, sameId⟩))
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact declarations _ _ _ _ previous authentic

theorem pattern_declarations
    {source : TypedSource} {site : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {arm : TypedMatchCase}
    (found : source.lookupStatement? site = some node)
    (form : node.form = .matchWith resolution) (member : arm ∈ resolution.cases)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {binders : List TypedBinder} {arity : Nat}
    (typed : TypedMatchPatternHasType context arm.pattern type binders arity) :
    ∀ binder ∈ binders, binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  intro binder bound
  have patternMember : binder ∈ SourceCoreDataPlaces.patternBinders arm.pattern :=
    CompatiblePatternSourceBinders.pattern_binders typed ▸ bound
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨.statement node, (lookupStatement?_sound found).1, ?_⟩
  simp only [form]
  exact List.mem_flatMap.mpr ⟨arm, member, patternMember⟩

theorem scope_bind
    {source : TypedSource} {scope : Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} (payload : Ty)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (extended : BinderExtends source.owner context binder nextContext) :
    CompatibleExpressionReads.ScopeDeclarations source ((binder.id, payload) :: scope) nextContext := by
  cases extended
  intro id declared index type selected authentic
  by_cases same : binder.id = id
  · subst id
    have identical := rootBinder_identifies member authentic
    subst declared
    exact .head
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact .tail same (declarations _ _ _ _ previous authentic)

theorem scope_binders
    {source : TypedSource} {scope : Scope} {context finalContext : SourceSemantics.Context}
    {bindings : List (TypedBinder × Ty)}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (members : ∀ binder ∈ bindings.map Prod.fst, binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (extended : BindersExtend source.owner context (bindings.map Prod.fst) finalContext) :
    CompatibleExpressionReads.ScopeDeclarations source
      (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalContext := by
  induction bindings generalizing scope context with
  | nil => cases extended; exact declarations
  | cons binding rest ih =>
    obtain ⟨binder, payload⟩ := binding
    cases extended with
    | cons head tail =>
      exact ih (scope_bind payload declarations (members binder List.mem_cons_self) head)
        (fun other member => members other (List.mem_cons_of_mem _ member)) tail

private theorem lookup_same_ids {first second : Scope} {binder : Resolved.LocalId} {index : Nat} {type : Ty}
    (same : first.map Prod.fst = second.map Prod.fst)
    (selected : SourceCoreLocalCell.lookup? second binder = some (index, type)) :
    ∃ payload, SourceCoreLocalCell.lookup? first binder = some (index, payload) := by
  induction first generalizing second index type with
  | nil =>
    cases second with
    | nil => cases selected
    | cons => cases same
  | cons entry rest ih =>
    obtain ⟨candidate, payload⟩ := entry
    cases second with
    | nil => cases same
    | cons entry tail =>
      obtain ⟨other, otherPayload⟩ := entry
      obtain ⟨rfl, sameTail⟩ := List.cons.inj same
      by_cases identical : candidate = binder
      · simp only [SourceCoreLocalCell.lookup?, identical, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at selected
        exact ⟨payload, selected.1.symm ▸ (by simp [SourceCoreLocalCell.lookup?, identical])⟩
      · simp only [SourceCoreLocalCell.lookup?, identical, ↓reduceIte] at selected ⊢
        cases previous : SourceCoreLocalCell.lookup? tail binder with
        | none => simp [previous] at selected
        | some entry =>
          obtain ⟨previousIndex, previousPayload⟩ := entry
          simp only [previous, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
          obtain ⟨firstPayload, found⟩ := ih sameTail previous
          exact ⟨firstPayload, by simp only [found, Option.map_some]; exact congrArg some (congrArg (fun n => (n, firstPayload)) selected.1)⟩

/-- Source declaration agreement depends on source identities in the scope.
This transports no native type or runtime environment typing. -/
theorem scope_ids {source : TypedSource} {first second : Scope} {context : SourceSemantics.Context}
    (same : first.map Prod.fst = second.map Prod.fst)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source first context) :
    CompatibleExpressionReads.ScopeDeclarations source second context := by
  intro binder declared index type selected authentic
  obtain ⟨payload, found⟩ := lookup_same_ids same selected
  exact declarations binder declared index payload found authentic

theorem Certificate.arm_scope
    {compilation : Compilation} {source : TypedSource} {scope : Scope} {site : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {arm : TypedMatchCase}
    {expected : TypeSystem.Ty} {compiled : Pattern}
    (found : source.lookupStatement? site = some node)
    (form : node.form = .matchWith resolution) (member : arm ∈ resolution.cases)
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span expected arm.pattern compiled)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder} {arity : Nat}
    (signatures : context.signatures = compilation.signatures)
    (typed : TypedMatchPatternHasType context arm.pattern expected binders arity)
    (extended : BindersExtend source.owner context binders armContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations source (armScope scope compiled) armContext := by
  have sameBinders := CompatiblePatternSourceBinders.Certificate.source_binders certificate signatures typed
  apply scope_binders declarations
  · rw [sameBinders]
    exact pattern_declarations found form member typed
  · exact sameBinders.symm ▸ extended

theorem Certificate.hidden_arm_scope
    {compilation : Compilation} {source : TypedSource} {scope : Scope} {site : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {arm : TypedMatchCase}
    {expected : TypeSystem.Ty} {payload : Ty} {compiled : Pattern}
    (found : source.lookupStatement? site = some node)
    (form : node.form = .matchWith resolution) (member : arm ∈ resolution.cases)
    (certificate : CompatiblePatternCertificates.Certificate compilation source
      ((resolution.hiddenScrutinee, payload) :: scope) site arm.span expected arm.pattern compiled)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder} {arity : Nat}
    (signatures : context.signatures = compilation.signatures)
    (typed : TypedMatchPatternHasType context arm.pattern expected binders arity)
    (extended : BindersExtend source.owner context binders armContext)
    (hidden : resolution.hiddenScrutinee ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id))
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations source
      (armScope ((resolution.hiddenScrutinee, payload) :: scope) compiled) armContext :=
  Certificate.arm_scope found form member certificate signatures typed extended
    (scope_internal payload hidden declarations)

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenAllocation
/-! The hidden scrutinee is an internal scope reference, never a source lexical
binder. Its independent source cell retains the complete scrutinee type even
when the real marker key uses the compiler's erased runtime binder type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion
universe u v

def request (source : TypedSource) (scope : SourceCoreSourceCells.Scope)
    (binder : TypedBinder) (payload : Ty) : SourceCoreSourceCells.Request :=
  CompatibleStatementInitialized.request source scope binder payload

/-- The erased marker metadata does not retype the independent hidden heap
cell. Actual captures and payloads still come from their real typed slots. -/
theorem preserves_cells_with_state {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {allocationSource : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder} {payload : Ty}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request allocationSource scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (request allocationSource scope binder payload))
    (same : annotation.original = allocation.expression)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {cells : GenericHeap.CellModel definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells model cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts frame cells)
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {before after : Dynamic.Heap} {store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {location : Dynamic.Location}
    {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native)
    (allocated : Dynamic.Heap.Allocates before sourceType (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      nextStore.read? (store.length + 2) = some (.inRight .unit value) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  have canonicalLayout : EnvironmentsAgree (request allocationSource scope binder payload).references canonical (value :: canonical) :=
    fun found => found
  have referenceAt : (value :: canonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (request allocationSource scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have kind : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request allocationSource scope binder payload) = false := ordinary
    simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, kind]
    exact canonicalLayout reference
  obtain ⟨captured, _captures, _captureTyped, evaluated, nextHeaps, nextReference, preserved, transition⟩ :=
    producer.complete allocation annotation same definitionsEq registered
      environments canonicalLayout heaps referenceAt read (PayloadAt.initialized rfl rfl)
      (ordinaryCells.inject (GenericHeap.CellRepresents.initialized represented)) (.ordinary allocated) initial ready
  refine ⟨captured, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
    evaluated (agrees.lift value),
    .internal nextReference.typed (environments.fresh_absent fresh) (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩),
    nextHeaps, preserved, ?_, transition⟩
  simp [Store.read?]

/-- Compatibility with the original ordinary heap uses the same cell proof. -/
theorem preserves_with_state {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder} {payload : Ty}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (request source scope binder payload))
    (same : annotation.original = allocation.expression)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame model)
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {before after : Dynamic.Heap} {store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {location : Dynamic.Location}
    {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native)
    (allocated : Dynamic.Heap.Allocates before sourceType (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld after nextStore ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      nextStore.read? (store.length + 2) = some (.inRight .unit value) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  obtain ⟨captured, evaluated, nextEnvironments, nextHeaps, preservation, payloadRead, transition⟩ :=
    preserves_cells_with_state (allocationSource := source) allocation annotation same ordinary fresh
      (GenericHeap.OrdinaryCells.ordinary model) protocol producer.toCells definitionsEq registered
      represented environments (GenericHeap.ordinaryHeap_iff.mpr heaps) agrees reference read initial ready allocated
  exact ⟨captured, evaluated, nextEnvironments, GenericHeap.ordinaryHeap_iff.mp nextHeaps,
    preservation, payloadRead, transition⟩

/-- The original API forgets only the reached state. -/
theorem preserves {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder} {payload : Ty}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (request source scope binder payload))
    (same : annotation.original = allocation.expression)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {before after : Dynamic.Heap} {store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {location : Dynamic.Location}
    {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before sourceType (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld after nextStore ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      nextStore.read? (store.length + 2) = some (.inRight .unit value) := by
  obtain ⟨captured, evaluated, nextEnvironment, nextHeaps, preserved, readPayload, _transition⟩ :=
    preserves_with_state allocation annotation same ordinary fresh
      ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts frame model)
      definitionsEq registered represented environments heaps agrees reference read () True.intro allocated
  exact ⟨captured, evaluated, nextEnvironment, nextHeaps, preserved, readPayload⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenPrefix
/-! Successful scrutinee evaluation reaches the actual compatible branch
fold after exactly one hidden source allocation and two administrative cells.
The raw source heap type and source lexical environment are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion CompatibleMatchHiddenAllocation
open CompatibleEncoding (bind_ok)

private theorem case_right {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  constructor
  · intro result finalStore body; exact .caseRight evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_right evaluated
    exact body.sound

/-- Scrutinee failure retains its effects and executes no allocator or arm. -/
theorem failure_prefix {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {allocator : SourceCoreSourceCells.Allocator} {payload outputType : Ty}
    {computation branches code : Expr} {internalReason reason : Word}
    (accepted : SourceCoreSourceCells.letInitialized (some allocator) source scope Renaming.id binder
      outputType payload computation (.caseE (.loadCell (.var 0))
        (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {inputType : Ty}
    (failed : Evaluates environment before (computation.rename ξ) (.inLeft inputType (.word reason)) after) :
    Evaluates environment before (code.rename ξ) (.inLeft outputType (.word reason)) after := by
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocation, compiled, same⟩ := bind_ok accepted
  cases same
  exact .caseLeft failed (.inLeft (.var rfl))

/-- The initializer evaluation is a compositional boundary. Everything after
it, including the marked hidden allocation and load, follows from actual
compiler receipts and live slots. Both finite continuation directions hold. -/
theorem success_prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {payload outputType : Ty} {computation branches code : Expr} {internalReason : Word}
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    (accepted : SourceCoreSourceCells.letInitialized
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      source scope Renaming.id binder outputType payload computation
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location nextStore nextWorld nextMap nextRef,
      Dynamic.Heap.Allocates heap sourceType (some sourceValue) location hiddenHeap ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld hiddenHeap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
        (value :: nextRef :: canonical) (value :: nextRef :: value :: actual) ∧
      ContinuationAgreement actual before (code.rename ξ)
        (value :: nextRef :: value :: actual) nextStore
        (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) := by
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocationCode, compiled, sameCode⟩ := bind_ok accepted
  obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError compiled
  cases sameCode
  rw [emitted]
  obtain ⟨captured, allocated, nextEnvironments, nextHeaps, framePreserved, payloadRead⟩ :=
    CompatibleMatchHiddenAllocation.preserves allocation annotation same ordinary fresh definitionsEq registered
      represented environments heaps agrees reference read (Dynamic.Heap.Allocates.append (type := sourceType) (value := some sourceValue))
  let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
  let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
    SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
  refine ⟨_, _, nextStore, _, _, nextRef, .append, nextEnvironments, nextHeaps, ⟨_, rfl⟩, ⟨_, rfl⟩,
    framePreserved, ?_, ?_⟩
  · intro index foundValue found
    cases index with
    | zero => exact found
    | succ index => cases index with
      | zero => exact found
      | succ index => exact agrees found
  · simp only [LanguageResult.bind, Expr.rename, LoopRenaming.weakenOne]
    apply (ContinuationAgreement.bind evaluated).trans
    apply (ContinuationAgreement.letE allocated).trans
    have loaded : Evaluates (nextRef :: value :: actual) nextStore (.loadCell (.var 0))
        (.inRight .unit value) nextStore := .loadCell (.var rfl) payloadRead
    simpa [← Expr.rename_insertion, Expr.rename_comp, Expr.rename, Renaming.lift_comp,
      Renaming.lift, Renaming.insertion] using
      (case_right (left := (LanguageResult.failure outputType (.word internalReason)).rename
        (Renaming.comp (Renaming.insertion 1) ξ.lift).lift)
        (right := branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) loaded)

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectionPrefix
/-! The actual compatible match compiler reaches exactly its independently
selected source body. Hidden and successful arm allocations, raw scrutinee
heap type, source binder order and both continuation directions are composed.
The enclosing statement tree owns scrutinee and selected body semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectionPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchDecision
open DataMatchBranchPrefix CallableIndexedHistory

/-- Static binder IDs follow the same ordered flat instruction stream. -/
theorem tree_binding_ids {compilation : CompatiblePatternCertificates.Compilation}
    {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope}
    {expected : TypeSystem.Ty} {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (tree : CompatiblePatternCertificates.Tree compilation source site span scope expected instructions pattern rest) :
    pattern.bindings.map (fun binding => binding.1.id) ++ MatchPatternInstruction.binderIds rest =
      MatchPatternInstruction.binderIds instructions := by
  induction tree using CompatiblePatternCertificates.Tree.rec
    (motive_2 := fun _ instructions patterns rest _ =>
      (patterns.flatMap (·.bindings)).map (fun binding => binding.1.id) ++ MatchPatternInstruction.binderIds rest =
        MatchPatternInstruction.binderIds instructions) with
  | wildcard => rfl
  | binder => rfl
  | literal => rfl
  | tuple projection unpacked children projectedChildren ih => exact ih
  | constructor projection result count resolved coreType raw children projectedChildren registered ih => exact ih
  | nil => rfl
  | cons head tail headIH tailIH =>
    simp only [List.flatMap_cons, List.map_append]
    rw [List.append_assoc, tailIH, headIH]

theorem certificate_binding_ids {compilation : CompatiblePatternCertificates.Compilation}
    {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled) :
    compiled.bindings.map (fun binding => binding.1.id) = pattern.binderIds := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, same, _⟩ := CompatiblePatternCertificates.rootInstructions_sound compilation
    (.ofSignatures compilation.signatures) rfl _ _ _ root
  have ids := tree_binding_ids tree
  rw [same] at ids
  cases resolutionEq : pattern.resolution <;>
    simpa [resolutionEq, MatchPatternInstruction.binderIds,
      matchPatternResolutionInstructions, TypedMatchPattern.binderIds] using ids

/-- A static allocation classification for this exact compiled tree. These
sites are ordinary lexical allocations, rather than named input allocations. -/
def Ordinary {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (_certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) : Prop :=
  source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false ∧
  ∀ payload expected arms, Arms compilation source id ((resolution.hiddenScrutinee, payload) :: scope)
      expected bodyCertificate resolution.cases arms →
    ∀ item ∈ arms, ∀ binding ∈ item.1.bindings,
      source.inputs.any (fun input => decide (input.id = binding.1.id)) = false

private theorem arms_ordinary {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source id scope expected bodyCertificate cases arms)
    (binders : ∀ arm ∈ cases, ∀ binder ∈ arm.pattern.binderIds,
      source.inputs.any (fun input => decide (input.id = binder)) = false) :
    ∀ item ∈ arms, ∀ binding ∈ item.1.bindings,
      source.inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
  revert binders
  induction certified with
  | nil => intro binders item member; cases member
  | @cons arm rest pattern body arms patternCertified matcherTyped bodyCertified tail ih =>
    intro binders item member binding bindingMember
    rcases List.mem_cons.mp member with rfl | remaining
    · have ids := certificate_binding_ids patternCertified
      have selected : binding.1.id ∈ arm.pattern.binderIds := by
        rw [← ids]
        exact List.mem_map.mpr ⟨binding, bindingMember, rfl⟩
      exact binders arm (by simp) binding.1.id selected
    · exact ih (fun arm member => binders arm (List.mem_cons_of_mem _ member)) item remaining binding bindingMember

/-- Only source binder IDs are inspected to classify the actual arm sites.
This condition is independent of runtime matching and body execution. -/
theorem ordinary_of_source_ids {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (hidden : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
    (binders : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
      source.inputs.any (fun input => decide (input.id = binder)) = false) : Ordinary certificate := by
  exact ⟨hidden, fun _ _ _ certified => arms_ordinary certified binders⟩

/-- Scrutinee completion constructs independent source selection and the
entire real prefix. Body execution is absent from the hypotheses. Source
heap and Core store extensions account for every actual allocation. -/
theorem Certificate.success_prefix_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  cases sites with
  | @matchWith statementNode statementType scrutineeNode type scrutinee arms fallback branches _
      readStatement allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expressionCertified sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled supported =>
    have nodeEq := Option.some.inj (found.symm.trans scrutineeFound)
    subst scrutineeNode
    have expressionEq := uniqueExpression scrutinee expressionCertified
    subst scrutinee
    have payloadEq : payload = type := Except.ok.inj
      (represented.projection.symm.trans (CompatibleExpressionReads.projectType_of_accepted projection))
    subst payload
    obtain ⟨hiddenOrdinary, ordinaryArms⟩ := ordinary
    have kinds := ordinaryArms type node.type arms armCertificates
    rw [allocator] at hiddenCompiled
    obtain ⟨hiddenHeap, location, hiddenStore, hiddenWorld, hiddenMap, hiddenRef, allocated, hiddenEnvironments,
      hiddenHeaps, hiddenMaps, hiddenWorlds, hiddenFrame, hiddenLayout, hiddenAgreement⟩ :=
      CompatibleMatchHiddenPrefix.success_prefix onError hiddenOrdinary hiddenFresh hiddenCompiled definitions registered
        (model := CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        represented environments heaps agrees reference read evaluated
    have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
    obtain ⟨stillUnmapped, stillRead⟩ := hiddenFrame contextLocation unmapped bound
    have nextRead := stillRead.trans read
    have nextReference : (hiddenRef :: canonical)[((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals]? =
        some (.cellRef frame.type contextLocation) := by
      have indexEq : ((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals =
          (scope.length + 1 + globals) + 1 := by simp only [List.length_cons]; omega
      rw [indexEq]
      exact reference
    have nextRepresented := represented.extend (.refl _) hiddenMaps hiddenWorlds
    obtain ⟨selection, decision⟩ := CompatibleMatchDecision.Arms.decides_with_literals armCertificates fallbackCertificate literals signatures numericRequirements supported
      catalogValid extended nextRepresented
    obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
      finalEmbedding, body, selected, finalEnvironments, finalHeaps, maps, worlds, preserved, finalLayout, agreement⟩ :=
      CompatibleMatchBranchesPrefix.Decision.prefix definitions registered allocator decision armCertificates
        branchesCertified kinds nextReference nextRead stillUnmapped hiddenEnvironments hiddenHeaps hiddenLayout
    exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, body, allocated, decision.source, selected, finalEnvironments, finalHeaps,
      hiddenMaps.trans maps, hiddenWorlds.trans worlds, hiddenFrame.trans preserved, finalLayout, hiddenAgreement.trans agreement⟩


theorem Certificate.success_prefix
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  exact Certificate.success_prefix_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees reference read unmapped evaluated


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectionPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchSourceSelection
/-! Independent source arm selection drives the actual compatible compiler's
ordered decision. Malformed-pattern exclusion is a static certificate law,
independent of scrutinee execution, body execution and heap representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchSourceSelection
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataMatches CompatiblePatternCertificates CompatiblePatternLeaves
open CompatiblePatternExecution CompatibleMatchCertificates CompatibleMatchDecision
variable {compilation : Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

private theorem pattern_success_with_signatures {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (signatures : context.signatures = compilation.signatures)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value payload)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) :
    ∃ values, BindingsRep compilation.checked registry functions mapping world compiled.bindings bindings values ∧
      MatcherRuns compiled value values := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  have payloadEq : payload = compiled.type := Except.ok.inj
    (represented.projection.symm.trans (CompatiblePatternSuccess.Tree.projected tree))
  cases payloadEq
  cases matched with
  | intro spelling instructionMatch =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep spelling
    subst arityEq
    subst instructions
    obtain ⟨values, _, bindingsRep, runs⟩ := CompatiblePatternSuccess.Tree.success catalogValid extended tree
      sourceValue value bindings [] represented instructionMatch
    exact ⟨values, bindingsRep, runs⟩

private theorem pattern_success {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value payload)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) :
    ∃ values, BindingsRep compilation.checked registry functions mapping world compiled.bindings bindings values ∧
      MatcherRuns compiled value values := by
  exact pattern_success_with_signatures certificate valid.signatures catalogValid extended represented matched


/-- A source-selected arm preserves its exact source binder values and first
match order. Every matcher child is closed by the compatible pattern Tree. -/
theorem Arms.selects_with_literals {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (requirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Arms.LiteralSites literals certificates)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value payload)
    {selection : Dynamic.MatchCaseSelection}
    (selected : Dynamic.MatchCasesSelect context sourceValue cases fallback selection) :
    Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  induction selected generalizing arms with
  | head matched =>
    cases certificates with
    | cons certificate typed bodyCertified tail =>
      obtain ⟨values, related, runs⟩ := pattern_success_with_signatures certificate signatures catalogValid extended represented matched
      exact .head matched related runs bodyCertified
  | tail notMatched selected ih =>
    cases certificates with
    | cons certificate typed bodyCertified tail =>
      cases sites with
      | cons headSites tailSites =>
        cases pattern_decides_with_literals certificate literals signatures requirements headSites catalogValid extended represented with
        | inl found =>
          obtain ⟨_, _, matched, _⟩ := found
          exact False.elim (notMatched.excludes matched)
        | inr failed => exact .tail notMatched failed.2 (ih tail fallbackCertificate tailSites)
  | default => cases certificates; cases fallbackCertificate with
    | some certified => exact .default certified
  | noBranch => cases certificates; cases fallbackCertificate; exact .noBranch

theorem Arms.selects {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value payload)
    {selection : Dynamic.MatchCaseSelection}
    (selected : Dynamic.MatchCasesSelect context sourceValue cases fallback selection) :
    Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  exact Arms.selects_with_literals certificates fallbackCertificate _ valid.signatures (fun _ proof => proof)
    (CompatibleMatchDecision.Arms.ordinary_sites certificates valid) catalogValid extended represented selected


/-- Accepted compatible metadata always supplies a delimited source pattern;
this uses no runtime value or native type authentication assumption. -/
theorem pattern_not_malformed_with_signatures {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (signatures : context.signatures = compilation.signatures) : ¬ Dynamic.PatternMalformed context pattern := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  intro malformed
  cases malformed with
  | source absent => exact absent arity sourceRep
  | «prefix» other absent =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep other
    subst arityEq
    subst instructions
    exact absent (CompatiblePatternCertificates.Tree.skips tree)


theorem pattern_not_malformed {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) : ¬ Dynamic.PatternMalformed context pattern := by
  exact pattern_not_malformed_with_signatures certificate valid.signatures

theorem Arms.not_pattern_fault_with_signatures {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (signatures : context.signatures = compilation.signatures) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value cases := by
  induction certificates with
  | nil => intro fault; cases fault
  | cons certificate typed body tail ih =>
    intro fault
    cases fault with
    | head malformed => exact pattern_not_malformed_with_signatures certificate signatures malformed
    | tail _ next => exact ih next


theorem Arms.not_pattern_fault {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (valid : ContextValid compilation context) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value cases := by
  exact Arms.not_pattern_fault_with_signatures certificates valid.signatures value

theorem Certificate.not_pattern_fault_with_signatures {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (signatures : context.signatures = compilation.signatures) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value resolution.cases := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression
      sameType arms fallback branches hiddenCompiled =>
    exact Arms.not_pattern_fault_with_signatures arms signatures value


theorem Certificate.not_pattern_fault {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (valid : ContextValid compilation context) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value resolution.cases := by
  exact Certificate.not_pattern_fault_with_signatures certificate valid.signatures value

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchSourceSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmPrefix
/-! The real successful marked arm prefix preserves typing of every actual
slot, including the retained bundle, scrutinee and initializer temporaries.
Typed child expressions can therefore enter without a supplied final typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmPrefix
open Core Frontend SourceInference GeneralHeap DataEquality CoreProof ReadOnly DataPatternValues
open CompatibleMatchArmPrefix DataMatchCoreAllocation
open CompatibleMatchArmCertificates (Scope)
universe u v

private theorem liftMany_twoInsertions (count cutoff : Nat) :
    liftMany count (Renaming.comp (Renaming.insertion cutoff) (Renaming.insertion cutoff)) =
      Renaming.comp (Renaming.insertion (cutoff + count)) (Renaming.insertion (cutoff + count)) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [liftMany, Renaming.lift_comp, Renaming.lift_insertion, ih]
    congr 2 <;> omega

/-- This is the successful branch emitted by compatible match lowering,
including its two hidden lexical slots. The result relates the arm's ordinary lexical scope
to its actual Core environment and transforms the body syntax with the same
embedding. Both finite evaluation directions retain the exact final store. -/
theorem Stateful.bindArm_prefix_cells_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {allocationSource : TypedSource} {context : SourceCoreCompatibleDataMatches.Context}
    {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {cells : GenericHeap.CellModel nativeDefinitions}
    (ordinaryCells : GenericHeap.OrdinaryCells model cells)
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values)
    {scrutinee : Value} {outputType : Ty} {body code : Expr}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts layout cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    (allocator : context.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context allocationSource scope bindings outputType
      (body.weakenAt bindings.length) = .ok code)
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (kinds : ∀ binding ∈ bindings, allocationSource.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (CompatibleMatchTypedArmAllocation.prefixContext bindings actualContext) nativeDefinitions ∧
      finalCanonical[(bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length +
        (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical ∧
      ContinuationSize false actual store
        (code.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State
          ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical) := by
  let κ := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
  have sourceLayout : EnvironmentsAgree κ canonical (packValues values :: scrutinee :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by
    simpa using represented.length.2
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
    finalSourceLayout, finalActualLayout, spine, finalTyped, agreement, finalState, related, restoration⟩ :=
    CompatibleMatchTypedArmAllocation.Stateful.prefix_cells_sized
      (CompatibleMatchArmCertificates.of_accepted onError allocator accepted) ordinaryCells protocol producer stateBindings definitions registered represented
      environments heaps sourceLayout actualLayout actualTyped (start := 0) rfl rfl length
      (fun {_ _} found => by simpa using found) kinds reference read unmapped initial readyAt
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have finalReference : finalCanonical[(bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length +
      (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation) := by
    rw [canonicalEq]
    have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length =
        bindings.length + scope.length := by simp
    rw [scopeLength]
    have index : bindings.length + scope.length + (if named then 0 else 1) + globals =
        added.length + (scope.length + (if named then 0 else 1) + globals) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  refine ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, Renaming.comp finalEmbedding (liftMany bindings.length κ), allocated, finalEnv,
    finalHeapRep, maps, worlds, frame, ?_, finalTyped, finalReference, stillRead.trans read, stillUnmapped, ?_, ?_, finalState, related, restoration⟩
  · intro index value found
    exact finalActualLayout (finalSourceLayout found)
  · rw [canonicalEq]
    exact CanonicalPrefix.fold scope canonical bindings (fun binding => (binding.1.id, binding.2)) prefixLength
  · have same : ((body.weakenAt bindings.length).weakenAt bindings.length).rename finalEmbedding =
        body.rename (Renaming.comp finalEmbedding (liftMany bindings.length κ)) := by
      simp only [κ, liftMany_twoInsertions, Nat.zero_add]
      rw [← Expr.rename_insertion, ← Expr.rename_insertion, Expr.rename_comp, Expr.rename_comp]
      rfl
    rw [same] at agreement
    exact agreement

/-- Compatibility with the original ordinary heap uses the same cell proof. -/
theorem Stateful.bindArm_prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {context : SourceCoreCompatibleDataMatches.Context}
    {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values)
    {scrutinee : Value} {outputType : Ty} {body code : Expr}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts layout model)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    (allocator : context.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings outputType
      (body.weakenAt bindings.length) = .ok code)
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (CompatibleMatchTypedArmAllocation.prefixContext bindings actualContext) nativeDefinitions ∧
      finalCanonical[(bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length +
        (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical ∧
      ContinuationSize false actual store
        (code.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State
          ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical) := by
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, finalAgrees,
    finalTyped, finalReference, finalRead, finalUnmapped, canonicalPrefix, continuation, finalState, related, restoration⟩ :=
    Stateful.bindArm_prefix_cells_sized (allocationSource := source) (GenericHeap.OrdinaryCells.ordinary model) represented
      protocol producer.toCells stateBindings definitions registered allocator accepted kinds reference read unmapped
      environments (GenericHeap.ordinaryHeap_iff.mpr heaps) actualLayout actualTyped initial readyAt
  exact ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnvironments, GenericHeap.ordinaryHeap_iff.mp finalHeaps, maps,
    worlds, preservation, finalAgrees, finalTyped, finalReference, finalRead, finalUnmapped,
    canonicalPrefix, continuation, finalState, related, restoration⟩



/-- Compatibility erasure of the same actual arm prefix. -/
theorem bindArm_prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {context : SourceCoreCompatibleDataMatches.Context}
    {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values)
    {scrutinee : Value} {outputType : Ty} {body code : Expr}
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    (allocator : context.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings outputType
      (body.weakenAt bindings.length) = .ok code)
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (CompatibleMatchTypedArmAllocation.prefixContext bindings actualContext) nativeDefinitions ∧
      finalCanonical[(bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length +
        (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical ∧
      ContinuationSize false actual store
        (code.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, preserved, finalLayout, finalTyped,
    finalReference, finalRead, finalUnmapped, spine, agreement, _final, _related, _return⟩ :=
    Stateful.bindArm_prefix_sized represented ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts layout model)
      ProtectedStateTransition.MatchPrefix.unitBindings definitions registered allocator accepted kinds reference read unmapped
      environments heaps actualLayout actualTyped () (fun _ _ => True.intro)
  exact ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, preserved, finalLayout, finalTyped,
    finalReference, finalRead, finalUnmapped, spine, agreement⟩

theorem bindArm_prefix_typed {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {context : SourceCoreCompatibleDataMatches.Context}
    {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values)
    {scrutinee : Value} {outputType : Ty} {body code : Expr}
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    (allocator : context.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings outputType
      (body.weakenAt bindings.length) = .ok code)
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (CompatibleMatchTypedArmAllocation.prefixContext bindings actualContext) nativeDefinitions ∧
      finalCanonical[(bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length +
        (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      ContinuationAgreement actual store
        (code.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, frame, layout, typed, finalReference,
    finalRead, finalUnmapped, _, agreement⟩ :=
    bindArm_prefix_sized represented definitions registered allocator accepted kinds reference read unmapped
      environments heaps actualLayout actualTyped
  exact ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, frame, layout, typed, finalReference,
    finalRead, finalUnmapped, agreement.agreement⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedBranchesPrefix
/-! Under an arbitrary payload model containing the finite pattern values, the
emitted ordered match branches reach exactly the selected arm/default
continuation, allocating only the successful arm's binders. This is a complete
prefix correspondence (wrap and unwrap), not a supplied child evaluation. The
selected body's own statement correspondence is a separate structural proof. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedBranchesPrefix
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreCompatibleDataMatches DataPatternValues CompatiblePatternLeaves CompatiblePatternExecution
open CompatibleMatchCertificates CompatibleMatchDecision CoreProof ReadOnly

open DataMatchBranchPrefix CompatibleMatchArmPrefix
open CallableIndexedParameters
universe u v

private theorem case_right {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  constructor
  · intro result finalStore body; exact .caseRight evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_right evaluated
    exact body.sound

private theorem case_left {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {rightType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inLeft rightType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle left := by
  constructor
  · intro result finalStore body; exact .caseLeft evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_left evaluated
    exact body.sound

/-- The entire attempted-arm fold has no other finite result than execution
of its selected, related continuation. The initial store may contain arbitrary
typed administrative functions, and the body itself is unrestricted syntax. -/
theorem Stateful.Decision.prefix_cells_sized {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel compilation.checked.catalog ambient}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel compilation.checked registry functions) cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := CompatibleEquality.storageCatalog compilation.checked.catalog) protocol layouts layout cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    {mapping : LocationMap} {world : StoreTyping}
    {allocationSource : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection)
    (certificates : Arms compilation allocationSource site scope expected bodyCertificate cases arms)
    {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {branches : Expr}
    (branchesCompiled : Branches compilation allocationSource scope (LocalLoop.controlType resultType) fallbackCode arms branches)
    (kinds : ∀ item ∈ arms, ∀ binding ∈ item.1.bindings, allocationSource.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (value :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native) :
    ∃ finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding finalContext body,
      SelectedBody bodyCertificate scope environment heap resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize false actual store
        (branches.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  induction decision generalizing actual ξ branches actualContext with
  | @head arm rest pattern body arms fallback fallbackCode bindings values matched bindingsRepresented runs certified =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have matchedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inRight .unit (packValues values)) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact runs actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      cases branchesCompiled with
      | cons allocation tailBranches =>
        obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration⟩ :=
          CompatibleMatchTypedArmPrefix.Stateful.bindArm_prefix_cells_sized ordinaryCells (bindings_arguments bindingsRepresented) protocol producer stateBindings definitions registered allocator allocation
            (named := false) (kinds (pattern, body) (by simp)) reference read unmapped
            environments heaps (actualLayout.lift (packValues values))
            (.cons (Arguments.pack_typed (bindings_arguments bindingsRepresented)) actualTyped) initial readyAt
        have bindings := bindings_identical bindingsRepresented
        rw [bindings] at allocated
        exact ⟨_, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, _, body, .arm bindings allocated certified,
          finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, ((ContinuationSize.case_right matchedCore).trans agreement).weak, finalState, related, restoration⟩
  | @tail arm rest pattern body arms fallback fallbackCode selection notMatched fails next ih =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have failedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inLeft (bundleType pattern.bindingTypes) .unit) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact fails actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ)
          (value :: canonical) (.unit :: actual) := by
        intro index foundValue found
        exact actualLayout found
      cases branchesCompiled with
      | cons allocation tailBranches =>
        obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, finalContext, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration⟩ :=
          ih tail tailBranches (fun item member => kinds item (List.mem_cons_of_mem _ member)) nextLayout (.cons .unit actualTyped)
        refine ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, finalContext, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, ?_, finalState, related, restoration⟩
        simp only [LoopStatements.rename_insert] at agreement
        simp only [Expr.rename, LoopRenaming.weakenZero]
        exact ((ContinuationSize.case_left failedCore).trans agreement).weak
  | default certified =>
    cases branchesCompiled
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), actualContext, _, .default certified, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, actualTyped, reference, read, unmapped, .refl _ _, ?_, initial, protocol.refl initial,
      ⟨ProtectedStateTransition.ReturnTo.refl protocol scope canonical⟩⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _
  | noBranch =>
    cases branchesCompiled
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), actualContext, _, .noBranch, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, actualTyped, reference, read, unmapped, .refl _ _, ?_, initial, protocol.refl initial,
      ⟨ProtectedStateTransition.ReturnTo.refl protocol scope canonical⟩⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _

/-- The original ordinary-heap API specializes the same cell proof. -/
theorem Stateful.Decision.prefix_sized {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel compilation.checked.catalog ambient}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts layout
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    {mapping : LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection)
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {branches : Expr}
    (branchesCompiled : Branches compilation source scope (LocalLoop.controlType resultType) fallbackCode arms branches)
    (kinds : ∀ item ∈ arms, ∀ binding ∈ item.1.bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (value :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding finalContext body,
      SelectedBody bodyCertificate scope environment heap resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize false actual store
        (branches.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  simpa only [GenericHeap.ordinaryHeap_iff] using
    Stateful.Decision.prefix_cells_sized (GenericHeap.OrdinaryCells.ordinary (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
      protocol producer.toCells stateBindings definitions registered allocator decision certificates branchesCompiled
      kinds reference read unmapped environments (GenericHeap.ordinaryHeap_iff.mpr heaps) actualLayout actualTyped initial readyAt


/-- Compatibility erasure of the same actual branch decision. -/
theorem Decision.prefix_sized {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel compilation.checked.catalog ambient}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    {mapping : LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection)
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {branches : Expr}
    (branchesCompiled : Branches compilation source scope (LocalLoop.controlType resultType) fallbackCode arms branches)
    (kinds : ∀ item ∈ arms, ∀ binding ∈ item.1.bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (value :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    ∃ finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding finalContext body,
      SelectedBody bodyCertificate scope environment heap resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize false actual store
        (branches.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, finalContext, body, selected, finalEnv, finalHeaps, maps, worlds, preserved, finalLayout,
    finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, _final, _related, _return⟩ :=
    Stateful.Decision.prefix_sized ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts layout
        (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
      ProtectedStateTransition.MatchPrefix.unitBindings definitions registered allocator decision certificates branchesCompiled
      kinds reference read unmapped environments heaps actualLayout actualTyped () (fun _ _ => True.intro)
  exact ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, finalContext, body, selected, finalEnv, finalHeaps, maps, worlds, preserved, finalLayout,
    finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement⟩

theorem Decision.prefix_typed {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel compilation.checked.catalog ambient}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    {mapping : LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection)
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {branches : Expr}
    (branchesCompiled : Branches compilation source scope (LocalLoop.controlType resultType) fallbackCode arms branches)
    (kinds : ∀ item ∈ arms, ∀ binding ∈ item.1.bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (value :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    ∃ finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding finalContext body,
      SelectedBody bodyCertificate scope environment heap resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      ContinuationAgreement actual store
        (branches.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, finalContext, body, selected, finalEnv, finalHeaps, maps, worlds, frame, layout, typed,
    finalReference, finalRead, finalUnmapped, _, agreement⟩ :=
    Decision.prefix_sized definitions registered allocator decision certificates branchesCompiled kinds reference read unmapped
      environments heaps actualLayout actualTyped
  exact ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, finalContext, body, selected, finalEnv, finalHeaps, maps, worlds, frame, layout, typed,
    finalReference, finalRead, finalUnmapped, agreement.agreement⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedBranchesPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedHiddenPrefix
/-! The actual hidden-cell prefix derives runtime typing for both surviving
scrutinee temporaries and its new payload reference. Raw source type and erased
marker type remain separate, with exactly the allocator's world extension. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedHiddenPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion CompatibleEncoding
universe u v

private theorem case_right {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  constructor
  · intro result finalStore body; exact .caseRight evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_right evaluated
    exact body.sound

theorem Stateful.success_prefix_cells_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {allocationSource : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {payload outputType : Ty} {computation branches code : Expr} {internalReason : Word}
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    (accepted : SourceCoreSourceCells.letInitialized
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      allocationSource scope Renaming.id binder outputType payload computation
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {cells : GenericHeap.CellModel definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells model cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native) :
    ∃ hiddenHeap location nextStore nextWorld nextMap nextRef,
      Dynamic.Heap.Allocates heap sourceType (some sourceValue) location hiddenHeap ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld hiddenHeap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
        (value :: nextRef :: canonical) (value :: nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (value :: nextRef :: value :: actual)
        (payload :: OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      ContinuationSize true actual before (code.rename ξ)
        (value :: nextRef :: value :: actual) nextStore
        (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) ∧
      ∃ final : protocol.State ⟨(binder.id, payload) :: scope, nextMap, nextWorld, hiddenHeap, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          ((binder.id, payload) :: scope) (nextRef :: canonical)) := by
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocationCode, compiled, sameCode⟩ := bind_ok accepted
  obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError compiled
  cases sameCode
  rw [emitted]
  obtain ⟨captured, allocated, nextEnvironments, nextHeaps, framePreserved, payloadRead, transition⟩ :=
    CompatibleMatchHiddenAllocation.preserves_cells_with_state allocation annotation same ordinary fresh ordinaryCells protocol producer definitionsEq registered
      represented environments heaps agrees reference read initial (readyAt initial read) (Dynamic.Heap.Allocates.append (type := sourceType) (value := some sourceValue))
  obtain ⟨nextState, related⟩ := transition
  let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
  let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
    SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
  refine ⟨_, _, nextStore, _, _, nextRef, .append, nextEnvironments, nextHeaps, ⟨_, rfl⟩, ⟨_, rfl⟩,
    framePreserved, ?_, ?_, ?_, nextState, related,
    ⟨ProtectedStateTransition.ReturnTo.binding stateBindings scope canonical binder.id payload nextRef⟩⟩
  · intro index foundValue found
    cases index with
    | zero => exact found
    | succ index => cases index with
      | zero => exact found
      | succ index => exact agrees found
  · have referenceTyped : RuntimeValueHasType
        (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload])
        nextRef (OptionalCell.referenceType payload) definitions := by
      obtain ⟨reference, same, typed⟩ := nextEnvironments.runtime_hasTypes.lookup (index := 0) (by rfl)
      have identical : nextRef = reference := Option.some.inj same
      cases identical
      exact typed
    exact .cons ((model.runtime_hasType represented).weaken ⟨_, rfl⟩)
      (.cons referenceTyped (.cons ((model.runtime_hasType represented).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)))
  · simp only [LanguageResult.bind, Expr.rename, LoopRenaming.weakenOne]
    apply (ContinuationSize.bind evaluated).trans (b := true)
    apply (ContinuationSize.letE allocated).trans (b := true)
    have loaded : Evaluates (nextRef :: value :: actual) nextStore (.loadCell (.var 0))
        (.inRight .unit value) nextStore := .loadCell (.var rfl) payloadRead
    simpa [← Expr.rename_insertion, Expr.rename_comp, Expr.rename, Renaming.lift_comp,
      Renaming.lift, Renaming.insertion] using
      (ContinuationSize.case_right (left := (LanguageResult.failure outputType (.word internalReason)).rename
        (Renaming.comp (Renaming.insertion 1) ξ.lift).lift)
        (right := branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) loaded)

/-- Compatibility with the original ordinary heap uses the same cell proof. -/
theorem Stateful.success_prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {payload outputType : Ty} {computation branches code : Expr} {internalReason : Word}
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    (accepted : SourceCoreSourceCells.letInitialized
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      source scope Renaming.id binder outputType payload computation
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame model)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ hiddenHeap location nextStore nextWorld nextMap nextRef,
      Dynamic.Heap.Allocates heap sourceType (some sourceValue) location hiddenHeap ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld hiddenHeap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
        (value :: nextRef :: canonical) (value :: nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (value :: nextRef :: value :: actual)
        (payload :: OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      ContinuationSize true actual before (code.rename ξ)
        (value :: nextRef :: value :: actual) nextStore
        (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) ∧
      ∃ final : protocol.State ⟨(binder.id, payload) :: scope, nextMap, nextWorld, hiddenHeap, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          ((binder.id, payload) :: scope) (nextRef :: canonical)) := by
  obtain ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnvironments,
    nextHeaps, maps, worlds, preservation, finalAgrees, finalTyped, continuation, finalState, related, restoration⟩ :=
    Stateful.success_prefix_cells_sized (allocationSource := source) onError ordinary fresh accepted
      (GenericHeap.OrdinaryCells.ordinary model) protocol producer.toCells stateBindings definitionsEq registered
      represented environments (GenericHeap.ordinaryHeap_iff.mpr heaps) agrees actualTyped reference read evaluated initial readyAt
  exact ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnvironments,
    GenericHeap.ordinaryHeap_iff.mp nextHeaps, maps, worlds, preservation, finalAgrees, finalTyped,
    continuation, finalState, related, restoration⟩


/-- Compatibility erasure of the same actual prefix. -/
theorem success_prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {payload outputType : Ty} {computation branches code : Expr} {internalReason : Word}
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    (accepted : SourceCoreSourceCells.letInitialized
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      source scope Renaming.id binder outputType payload computation
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location nextStore nextWorld nextMap nextRef,
      Dynamic.Heap.Allocates heap sourceType (some sourceValue) location hiddenHeap ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld hiddenHeap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
        (value :: nextRef :: canonical) (value :: nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (value :: nextRef :: value :: actual)
        (payload :: OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      ContinuationSize true actual before (code.rename ξ)
        (value :: nextRef :: value :: actual) nextStore
        (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) := by
  obtain ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnv, nextHeaps,
    maps, worlds, frame, layout, typed, agreement, _final, _related, _return⟩ :=
    Stateful.success_prefix_sized onError ordinary fresh accepted
      ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts frame model)
      ProtectedStateTransition.MatchPrefix.unitBindings definitionsEq registered represented environments heaps agrees
      actualTyped reference read evaluated () (fun _ _ => True.intro)
  exact ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnv, nextHeaps,
    maps, worlds, frame, layout, typed, agreement⟩

theorem success_prefix_typed {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {payload outputType : Ty} {computation branches code : Expr} {internalReason : Word}
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    (accepted : SourceCoreSourceCells.letInitialized
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      source scope Renaming.id binder outputType payload computation
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location nextStore nextWorld nextMap nextRef,
      Dynamic.Heap.Allocates heap sourceType (some sourceValue) location hiddenHeap ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld hiddenHeap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
        (value :: nextRef :: canonical) (value :: nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (value :: nextRef :: value :: actual)
        (payload :: OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      ContinuationAgreement actual before (code.rename ξ)
        (value :: nextRef :: value :: actual) nextStore
        (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) := by
  obtain ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnv, nextHeaps,
    maps, worlds, frame, layout, typed, agreement⟩ :=
    success_prefix_sized onError ordinary fresh accepted definitionsEq registered represented environments heaps agrees
      actualTyped reference read evaluated
  exact ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnv, nextHeaps,
    maps, worlds, frame, layout, typed, agreement.agreement⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedHiddenPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix
/-! The exact actual marked prefix preserves an independently selected source
arm/default. No global source evaluator determinism or body execution is
required. The enclosing statement Tree supplies scrutinee/body correspondence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchDecision
open CompatibleMatchSelectionPrefix DataMatchBranchPrefix CallableIndexedHistory
universe u v

theorem Stateful.Certificate.selected_prefix_cells_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {allocationSource : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation allocationSource scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel compilation.checked registry functions) cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := CompatibleEquality.storageCatalog compilation.checked.catalog) protocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : allocationSource.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  cases sites with
  | @matchWith statementNode statementType scrutineeNode type scrutinee arms fallback branches _
      readStatement allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expressionCertified sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled supported =>
    have nodeEq := Option.some.inj (found.symm.trans scrutineeFound)
    subst scrutineeNode
    have expressionEq := uniqueExpression scrutinee expressionCertified
    subst scrutinee
    have payloadEq : payload = type := Except.ok.inj
      (represented.projection.symm.trans (CompatibleExpressionReads.projectType_of_accepted projection))
    subst payload
    obtain ⟨hiddenOrdinary, ordinaryArms⟩ := ordinary
    have kinds := ordinaryArms type node.type arms armCertificates
    rw [allocator] at hiddenCompiled
    obtain ⟨hiddenHeap, location, hiddenStore, hiddenWorld, hiddenMap, hiddenRef, allocated, hiddenEnvironments,
      hiddenHeaps, hiddenMaps, hiddenWorlds, hiddenFrame, hiddenLayout, hiddenTyped, hiddenAgreement, hiddenState, hiddenRelated, ⟨hiddenReturn⟩⟩ :=
      CompatibleMatchTypedHiddenPrefix.Stateful.success_prefix_cells_sized onError hiddenOrdinary hiddenFresh hiddenCompiled ordinaryCells protocol producer stateBindings definitions registered
        (model := CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        represented environments heaps agrees actualTyped reference read evaluated initial readyAt
    have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
    obtain ⟨stillUnmapped, stillRead⟩ := hiddenFrame contextLocation unmapped bound
    have nextRead := stillRead.trans read
    have nextReference : (hiddenRef :: canonical)[((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals]? =
        some (.cellRef frame.type contextLocation) := by
      have indexEq : ((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals =
          (scope.length + 1 + globals) + 1 := by simp only [List.length_cons]; omega
      rw [indexEq]
      exact reference
    have nextRepresented := represented.extend (.refl _) hiddenMaps hiddenWorlds
    have decision := CompatibleMatchSourceSelection.Arms.selects_with_literals armCertificates fallbackCertificate literals signatures numericRequirements supported
      catalogValid extended nextRepresented selectedSource
    obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
      finalEmbedding, finalContext, body, selected, finalEnvironments, finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, selectedRelated, ⟨selectedReturn⟩⟩ :=
      CompatibleMatchTypedBranchesPrefix.Stateful.Decision.prefix_cells_sized ordinaryCells protocol producer stateBindings definitions registered allocator decision armCertificates
        branchesCertified kinds nextReference nextRead stillUnmapped hiddenEnvironments hiddenHeaps hiddenLayout hiddenTyped hiddenState readyAt
    exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, decision.source, selected, finalEnvironments, finalHeaps,
      hiddenMaps.trans maps, hiddenWorlds.trans worlds, hiddenFrame.trans preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped,
      (CanonicalPrefix.cons scope canonical (resolution.hiddenScrutinee, type) hiddenRef).trans spine, hiddenAgreement.trans agreement, finalState, protocol.trans hiddenRelated selectedRelated,
      ⟨ProtectedStateTransition.ReturnTo.then hiddenReturn selectedReturn⟩⟩

/-- The original ordinary-heap API specializes the same cell proof. -/
theorem Stateful.Certificate.selected_prefix_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  simpa only [GenericHeap.ordinaryHeap_iff] using
    Stateful.Certificate.selected_prefix_cells_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid
      (GenericHeap.OrdinaryCells.ordinary (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)) protocol producer.toCells stateBindings definitions registered extended found uniqueExpression represented environments
      (GenericHeap.ordinaryHeap_iff.mpr heaps) agrees actualTyped reference read unmapped evaluated initial readyAt selectedSource




theorem Stateful.Certificate.selected_prefix_cells_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {allocationSource : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation allocationSource scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel compilation.checked registry functions) cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := CompatibleEquality.storageCatalog compilation.checked.catalog) protocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : allocationSource.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  exact Stateful.Certificate.selected_prefix_cells_sized_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid ordinaryCells protocol producer stateBindings definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated initial readyAt selectedSource

/-- The original ordinary-heap API specializes the same cell proof. -/
theorem Stateful.Certificate.selected_prefix_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  simpa only [GenericHeap.ordinaryHeap_iff] using
    Stateful.Certificate.selected_prefix_cells_sized certificate ordinary onError allocator valid catalogValid
      (GenericHeap.OrdinaryCells.ordinary (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)) protocol producer.toCells stateBindings definitions registered extended found uniqueExpression represented environments
      (GenericHeap.ordinaryHeap_iff.mpr heaps) agrees actualTyped reference read unmapped evaluated initial readyAt selectedSource



theorem Stateful.Certificate.success_prefix_cells_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {allocationSource : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation allocationSource scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel compilation.checked registry functions) cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := CompatibleEquality.storageCatalog compilation.checked.catalog) protocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : allocationSource.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  obtain ⟨selection, selected⟩ := CompatibleMatchDecision.Certificate.source_selects_with_literals certificate literals signatures numericRequirements sites catalogValid extended found represented
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
      finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration⟩ :=
    Stateful.Certificate.selected_prefix_cells_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid ordinaryCells protocol producer stateBindings definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated initial readyAt selected
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration⟩

/-- The original ordinary-heap API specializes the same cell proof. -/
theorem Stateful.Certificate.success_prefix_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  simpa only [GenericHeap.ordinaryHeap_iff] using
    Stateful.Certificate.success_prefix_cells_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid
      (GenericHeap.OrdinaryCells.ordinary (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)) protocol producer.toCells stateBindings definitions registered extended found uniqueExpression represented environments
      (GenericHeap.ordinaryHeap_iff.mpr heaps) agrees actualTyped reference read unmapped evaluated initial readyAt


theorem Stateful.Certificate.success_prefix_cells_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {allocationSource : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation allocationSource scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel compilation.checked registry functions) cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := CompatibleEquality.storageCatalog compilation.checked.catalog) protocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : allocationSource.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  exact Stateful.Certificate.success_prefix_cells_sized_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid ordinaryCells protocol producer stateBindings definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated initial readyAt

/-- The original ordinary-heap API specializes the same cell proof. -/
theorem Stateful.Certificate.success_prefix_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) := by
  simpa only [GenericHeap.ordinaryHeap_iff] using
    Stateful.Certificate.success_prefix_cells_sized certificate ordinary onError allocator valid catalogValid
      (GenericHeap.OrdinaryCells.ordinary (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)) protocol producer.toCells stateBindings definitions registered extended found uniqueExpression represented environments
      (GenericHeap.ordinaryHeap_iff.mpr heaps) agrees actualTyped reference read unmapped evaluated initial readyAt




/-- The original API forgets only actual state and future restoration. -/
theorem Certificate.selected_prefix_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnv,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped,
    spine, agreement, _final, _related, _return⟩ :=
    Stateful.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures
      numericRequirements sites catalogValid ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts frame
        (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
      ProtectedStateTransition.MatchPrefix.unitBindings definitions registered extended found uniqueExpression
      represented environments heaps agrees actualTyped reference read unmapped evaluated () (fun _ _ => True.intro) selectedSource
  exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnv,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped,
    spine, agreement⟩

theorem Certificate.selected_prefix_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  exact Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selectedSource


/-- Whole Core success can use the independently constructed source decision.
The selected actual body's complete runtime context is derived by the prefix. -/
theorem Certificate.success_prefix_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨selection, selected⟩ := CompatibleMatchDecision.Certificate.source_selects_with_literals certificate literals signatures numericRequirements sites catalogValid extended found represented
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
      finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement⟩ :=
    Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selected
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement⟩

theorem Certificate.success_prefix_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  exact Certificate.success_prefix_sized_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated


/-- Compatibility erasure of the same measured prefix. -/
theorem Certificate.selected_prefix_typed
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      ContinuationAgreement actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, _, agreement⟩ :=
    Certificate.selected_prefix_sized certificate ordinary onError allocator valid catalogValid definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selectedSource
  exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, agreement.agreement⟩

/-- Compatibility erasure of the same measured prefix. -/
theorem Certificate.success_prefix_typed
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      ContinuationAgreement actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, _, agreement⟩ :=
    Certificate.success_prefix_sized certificate ordinary onError allocator valid catalogValid definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, agreement.agreement⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectedPrefix
/-! The exact actual marked prefix preserves an independently selected source
arm/default. No global source evaluator determinism or body execution is
required. The enclosing statement Tree supplies scrutinee/body correspondence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectedPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchDecision
open CompatibleMatchSelectionPrefix DataMatchBranchPrefix CallableIndexedHistory

theorem Certificate.selected_prefix
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  cases certificate with
  | @matchWith statementNode statementType scrutineeNode type scrutinee arms fallback branches _
      readStatement allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expressionCertified sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled =>
    have nodeEq := Option.some.inj (found.symm.trans scrutineeFound)
    subst scrutineeNode
    have expressionEq := uniqueExpression scrutinee expressionCertified
    subst scrutinee
    have payloadEq : payload = type := Except.ok.inj
      (represented.projection.symm.trans (CompatibleExpressionReads.projectType_of_accepted projection))
    subst payload
    obtain ⟨hiddenOrdinary, ordinaryArms⟩ := ordinary
    have kinds := ordinaryArms type node.type arms armCertificates
    rw [allocator] at hiddenCompiled
    obtain ⟨hiddenHeap, location, hiddenStore, hiddenWorld, hiddenMap, hiddenRef, allocated, hiddenEnvironments,
      hiddenHeaps, hiddenMaps, hiddenWorlds, hiddenFrame, hiddenLayout, hiddenAgreement⟩ :=
      CompatibleMatchHiddenPrefix.success_prefix onError hiddenOrdinary hiddenFresh hiddenCompiled definitions registered
        (model := CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        represented environments heaps agrees reference read evaluated
    have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
    obtain ⟨stillUnmapped, stillRead⟩ := hiddenFrame contextLocation unmapped bound
    have nextRead := stillRead.trans read
    have nextReference : (hiddenRef :: canonical)[((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals]? =
        some (.cellRef frame.type contextLocation) := by
      have indexEq : ((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals =
          (scope.length + 1 + globals) + 1 := by simp only [List.length_cons]; omega
      rw [indexEq]
      exact reference
    have nextRepresented := represented.extend (.refl _) hiddenMaps hiddenWorlds
    have decision := CompatibleMatchSourceSelection.Arms.selects armCertificates fallbackCertificate valid
      catalogValid extended nextRepresented selectedSource
    obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
      finalEmbedding, body, selected, finalEnvironments, finalHeaps, maps, worlds, preserved, finalLayout, agreement⟩ :=
      CompatibleMatchBranchesPrefix.Decision.prefix definitions registered allocator decision armCertificates
        branchesCertified kinds nextReference nextRead stillUnmapped hiddenEnvironments hiddenHeaps hiddenLayout
    exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, body, allocated, decision.source, selected, finalEnvironments, finalHeaps,
      hiddenMaps.trans maps, hiddenWorlds.trans worlds, hiddenFrame.trans preserved, finalLayout, hiddenAgreement.trans agreement⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectedPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchScrutineeReflection
/-! Finite evaluation inversion for the actual compatible hidden-cell wrapper.
Any completed whole match exposes the actual scrutinee completion. Failure
retains its effects and reaches neither allocation nor any candidate arm. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchScrutineeReflection
open Core Frontend SourceInference CoreProof ReadOnly
open CompatibleMatchCertificates
open CompatibleEncoding (bind_ok)

theorem initial_evaluation {allocator : Option SourceCoreSourceCells.Allocator}
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {references : Renaming} {binder : TypedBinder}
    {outputType payloadType : Ty} {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitialized allocator source scope references binder
      outputType payloadType initializer body = .ok code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {result : Value}
    (completed : Evaluates environment before (code.rename ξ) result after) :
    ∃ value middle, Evaluates environment before (initializer.rename ξ) value middle := by
  cases allocator with
  | none =>
    cases accepted
    rw [LoopRenaming.letInitialized] at completed
    cases completed with
    | caseLeft evaluated _ => exact ⟨_, _, evaluated⟩
    | caseRight evaluated _ => exact ⟨_, _, evaluated⟩
  | some allocate =>
    unfold SourceCoreSourceCells.letInitialized at accepted
    obtain ⟨allocation, generated, same⟩ := bind_ok accepted
    cases same
    cases completed with
    | caseLeft evaluated _ => exact ⟨_, _, evaluated⟩
    | caseRight evaluated _ => exact ⟨_, _, evaluated⟩

theorem failure_evaluation {allocator : Option SourceCoreSourceCells.Allocator}
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {references : Renaming} {binder : TypedBinder}
    {outputType payloadType : Ty} {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitialized allocator source scope references binder
      outputType payloadType initializer body = .ok code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {inputType : Ty} {reason : Word}
    (failed : Evaluates environment before (initializer.rename ξ) (.inLeft inputType (.word reason)) after) :
    Evaluates environment before (code.rename ξ) (.inLeft outputType (.word reason)) after := by
  cases allocator with
  | none =>
    cases accepted
    rw [LoopRenaming.letInitialized]
    exact .caseLeft failed (.inLeft (.var rfl))
  | some allocate =>
    unfold SourceCoreSourceCells.letInitialized at accepted
    obtain ⟨allocation, generated, same⟩ := bind_ok accepted
    cases same
    exact .caseLeft failed (.inLeft (.var rfl))

/-- Reflection starts from whole Core completion and extracts the exact static
child certificate together with the child's finite completion; source child
execution remains the enclosing concrete expression Tree's conclusion. -/
theorem Certificate.initial_evaluation
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : SourceCoreSourceCells.Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {result : Value}
    (completed : Evaluates environment before (code.rename ξ) result after) :
    ∃ node lowered value middle, source.lookupExpression? resolution.scrutinee = some node ∧
      expressionCertificate scope resolution.scrutinee lowered ∧
      Evaluates environment before (lowered.expression.rename ξ) value middle := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    obtain ⟨value, middle, evaluated⟩ := CompatibleMatchScrutineeReflection.initial_evaluation hiddenCompiled completed
    exact ⟨_, _, value, middle, found, expression, evaluated⟩

/-- An independently established child failure has the actual whole match
failure envelope, with exactly the child's completed store. -/
theorem Certificate.failure_preserves
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : SourceCoreSourceCells.Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {environment : Environment} {before after : Store} {ξ : Renaming} {inputType : Ty} {reason : Word}
    (failed : Evaluates environment before (lowered.expression.rename ξ) (.inLeft inputType (.word reason)) after) :
    Evaluates environment before (code.rename ξ) (.inLeft (LocalLoop.controlType resultType) (.word reason)) after := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    have same := uniqueExpression _ expression
    subst lowered
    exact failure_evaluation hiddenCompiled failed

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchScrutineeReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchMeaning
/-! Selected compatible match bodies receive the actual native frame and typed
captures. These are structural induction interfaces, separate from the static
compiler receipts. The source selection and binder context remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates DataMatchBranchPrefix
open TypedLexicalWhile (FlowRep Restored)

variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {source : TypedSource}
  (program : Program) (parent : SourceSemantics.Context) (control : ControlContext)
  (evidence : Dynamic.EvidenceEnvironment) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty)
  {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : FunctionCalls.FaultRep}

def ArmPreserves : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    TypedLexicalWhile.Preserves functions program evidence (values := compilation.values)
      (source := source) (context := armContext) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def ArmReflects : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    TypedLexicalWhile.Reflects functions program evidence (values := compilation.values)
      (source := source) (context := armContext) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def DefaultPreserves : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    TypedLexicalWhile.Preserves functions program evidence (values := compilation.values)
      (source := source) (context := parent) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def DefaultReflects : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    TypedLexicalWhile.Reflects functions program evidence (values := compilation.values)
      (source := source) (context := parent) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def ArmPreservesScoped (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    TypedLexicalWhile.Preserves functions program evidence (values := compilation.values)
      (source := source) (context := armContext) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def ArmReflectsScoped (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    TypedLexicalWhile.Reflects functions program evidence (values := compilation.values)
      (source := source) (context := armContext) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def DefaultPreservesScoped (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    TypedLexicalWhile.Preserves functions program evidence (values := compilation.values)
      (source := source) (context := parent) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

def DefaultReflectsScoped (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    TypedLexicalWhile.Reflects functions program evidence (values := compilation.values)
      (source := source) (context := parent) (registry := registry) (solved := solved)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) false statements expected type body

section Adaptation
variable {functions program parent control evidence resolution bodyCertificate expected type}
theorem ArmPreserves.scoped (meaning : ArmPreserves functions program parent control evidence resolution bodyCertificate expected type (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) (outerScope : Scope) :
    ArmPreservesScoped functions program parent control evidence resolution bodyCertificate expected type outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope
  exact meaning

theorem ArmReflects.scoped (meaning : ArmReflects functions program parent control evidence resolution bodyCertificate expected type (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) (outerScope : Scope) :
    ArmReflectsScoped functions program parent control evidence resolution bodyCertificate expected type outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope
  exact meaning

theorem DefaultPreserves.scoped (meaning : DefaultPreserves functions program parent control evidence resolution bodyCertificate expected type (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) (outerScope : Scope) :
    DefaultPreservesScoped functions program parent control evidence resolution bodyCertificate expected type outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body sameScope
  exact meaning

theorem DefaultReflects.scoped (meaning : DefaultReflects functions program parent control evidence resolution bodyCertificate expected type (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) (outerScope : Scope) :
    DefaultReflectsScoped functions program parent control evidence resolution bodyCertificate expected type outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body sameScope
  exact meaning

end Adaptation

theorem valid_binders {owner : Resolved.DeclarationId} {context finalContext : SourceSemantics.Context}
    {binders : List TypedBinder} (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extended : BindersExtend owner context binders finalContext) :
    CompatibleExpressionLiterals.ContextValid solved finalContext evidence := by
  induction extended with
  | nil => exact valid
  | cons head tail ih => exact ih (TypedLexicalControl.valid_extend valid head)

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeArms
/-! Native child typing follows the actual marked compatible arm prefix.
Only syntactic unused slots are removed. No source type, closure identity or
runtime authority is inferred from these native typing statements. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeArms
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchArmCertificates hiding Scope
open TypedLexicalWhile.Native

def referenceContext (bindings : List Binding) (context : Core.Context) : Core.Context :=
  bindings.foldl (fun context binding => OptionalCell.referenceType binding.2 :: context) context

def referencePrefix (bindings : List Binding) : Core.Context :=
  bindings.reverse.map (fun binding => OptionalCell.referenceType binding.2)

private theorem referenceContext_prefix (bindings : List Binding) (context : Core.Context) :
    referenceContext bindings context = referencePrefix bindings ++ context := by
  induction bindings generalizing context with
  | nil => rfl
  | cons head tail ih => simp [referenceContext, referencePrefix, List.reverse_cons, List.append_assoc]

private theorem referenceContext_scope (bindings : List Binding) (scope : Scope) (administrative : Core.Context) :
    referenceContext bindings (SourceCoreLocalCell.coreContext scope ++ administrative) =
      SourceCoreLocalCell.coreContext (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) ++ administrative := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons head tail ih =>
    simpa only [referenceContext, List.foldl_cons, SourceCoreLocalCell.coreContext, List.map_cons, List.cons_append, OptionalCell.referenceType] using
      ih ((head.1.id, head.2) :: scope)

private theorem remove_at {definitions : DataEnvironment} (leading suffix : Core.Context) (inserted : Ty)
    {expression : Expr} {type : Ty}
    (typed : HasType (leading ++ inserted :: suffix) (expression.weakenAt leading.length) type definitions) :
    HasType (leading ++ suffix) expression type definitions := by
  rw [← Expr.rename_insertion] at typed
  apply typing expression ?_ typed
  clear typed
  induction leading with
  | nil => intro index type found; simpa [Renaming.insertion] using found
  | cons head leading ih =>
    simpa only [List.length_cons, List.cons_append, ← Renaming.lift_insertion] using ih.lift head

theorem Tree.body_typing {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {types : List Ty} {output : Ty} {body : Expr}
    {scope : Scope} {index : Nat} {bindings : List Binding} {code : Expr}
    (tree : CompatibleMatchArmCertificates.Tree layouts owner active frame globals onError source types output body scope index bindings code)
    {context : Core.Context} {definitions : DataEnvironment} {type : Ty}
    (typed : HasType context code type definitions) :
    HasType (referenceContext bindings context) body type definitions := by
  induction tree generalizing context with
  | nil => exact typed
  | cons allocation annotation same tail ih =>
    cases typed with
    | caseE initial failure next =>
      exact ih (remove_second (absent_child allocation annotation same next))

/-- The two actual lexical temporaries are removed from the weakened body.
The resulting context is exactly the compiler arm scope plus its ambient tail. -/
theorem bindArm_body_typing {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {source : TypedSource} {scope : Scope} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : bindArmWithAllocator compilation source scope bindings output (body.weakenAt bindings.length) = .ok code)
    {bundle scrutinee type : Ty} {administrative : Core.Context} {definitions : DataEnvironment}
    (typed : HasType (bundle :: scrutinee :: (SourceCoreLocalCell.coreContext scope ++ administrative)) code type definitions) :
    HasType (SourceCoreLocalCell.coreContext (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) ++ administrative)
      body type definitions := by
  have initial := Tree.body_typing (CompatibleMatchArmCertificates.of_accepted onError allocator accepted) typed
  rw [referenceContext_prefix] at initial
  have length : (referencePrefix bindings).length = bindings.length := by simp [referencePrefix]
  rw [← length] at initial
  have once := remove_at (referencePrefix bindings) (scrutinee :: (SourceCoreLocalCell.coreContext scope ++ administrative)) bundle initial
  have twice := remove_at (referencePrefix bindings) (SourceCoreLocalCell.coreContext scope ++ administrative) scrutinee once
  rw [← referenceContext_prefix, referenceContext_scope] at twice
  exact twice

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeArms
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildren
/-! One native typing receipt for the emitted compatible match supplies native
typing of every real child body. Static receipts retain the original source
metadata and compiler scopes. No child evaluation premise is introduced. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildren
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates TypedLexicalWhile.Native
open CompatibleEncoding (bind_ok)

def TypedBody (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (certificate : BodyCertificate) : BodyCertificate :=
  fun scope statements code => certificate scope statements code ∧
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions

private theorem Fallback.add_typing {certificate : BodyCertificate} {scope : Scope} {result : Ty}
    {fallback : Option (List StatementId)} {code : Expr}
    (certified : Fallback certificate scope result fallback code)
    {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    Fallback (TypedBody definitions administrative type certificate) scope result fallback code := by
  cases certified with
  | none => exact .none
  | some body => exact .some ⟨body, typed⟩

private theorem matcher_typed {context : Core.Context} {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) : HasType context expression type definitions := by
  have extended := typed.rename (target := context) (mapping := Renaming.id)
    (by intro index type found; cases found)
  simpa using extended

theorem Arms.add_typing
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (sameDefinitions : compilation.definitions = definitions)
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {certificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source site scope expected certificate cases arms)
    {result : Ty} {fallback : Option (List StatementId)} {fallbackCode branches : Expr}
    (fallbackCertified : Fallback certificate scope result fallback fallbackCode)
    (generated : Branches compilation source scope (LocalLoop.controlType result) fallbackCode arms branches)
    {scrutinee type : Ty} {administrative : Core.Context}
    (typed : HasType (scrutinee :: (SourceCoreLocalCell.coreContext scope ++ administrative)) branches type definitions) :
    Arms compilation source site scope expected (TypedBody definitions administrative type certificate) cases arms ∧
      Fallback (TypedBody definitions administrative type certificate) scope result fallback fallbackCode := by
  induction certified generalizing branches with
  | nil =>
    cases generated
    exact ⟨.nil, Fallback.add_typing fallbackCertified (remove_front typed)⟩
  | @cons arm rest pattern body arms patternCertificate patternTyped bodyCertified tail ih =>
    cases generated with
    | cons allocation next =>
      cases typed with
      | caseE applied failed chosen =>
        cases applied with
        | apply function argument =>
          rw [sameDefinitions] at patternTyped
          have same := typing_deterministic function (matcher_typed patternTyped)
          have resultEq := (Ty.function.inj same).2
          simp only [Pattern.resultType, Ty.sum.injEq] at resultEq
          rcases resultEq with ⟨rfl, rfl⟩
          obtain ⟨nextCertified, finalFallback⟩ := ih next (remove_front failed)
          exact ⟨.cons patternCertificate (sameDefinitions.symm ▸ patternTyped)
            ⟨bodyCertified, CompatibleMatchNativeArms.bindArm_body_typing onError allocator allocation chosen⟩ nextCertified,
            finalFallback⟩

/-- The actual hidden marked allocation removes only its initializer slot.
Its subsequent load supplies the real scrutinee type to the branch fold. -/
private theorem hidden_branches
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {source : TypedSource} {scope : Scope} {binder : TypedBinder} {payload output : Ty}
    {initializer branches code : Expr} {reason : Word}
    (accepted : SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Renaming.id binder output payload initializer
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure output (.word reason)) branches) = .ok code)
    {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    HasType (payload :: OptionalCell.referenceType payload :: (SourceCoreLocalCell.coreContext scope ++ administrative))
      branches type definitions := by
  rw [allocator] at accepted
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocation, allocated, exactCode⟩ := bind_ok accepted
  obtain ⟨receipt, annotation, same, sameCode⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError allocated
  cases exactCode
  cases sameCode
  cases typed with
  | caseE initial failure next =>
    have bodyTyped := remove_second (absent_child receipt annotation same next)
    cases bodyTyped with
    | caseE loaded failure branch =>
      cases loaded with
      | loadCell reference =>
        cases reference with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Ty.cell.injEq, OptionalCell.referenceType,
            OptionalCell.cellType, Ty.sum.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          exact branch

theorem Certificate.typed_bodies
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (sameDefinitions : compilation.definitions = definitions)
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason expressionCertificate bodyCertificate code)
    {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason expressionCertificate
      (TypedBody definitions administrative type bodyCertificate) code := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    have branchesTyped := hidden_branches onError allocator hiddenCompiled typed
    obtain ⟨nextArms, nextFallback⟩ := Arms.add_typing onError allocator sameDefinitions arms fallback branches branchesTyped
    exact .matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      nextArms nextFallback branches hiddenCompiled

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildren
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildrenExtension
/-! The emitted compatible match may be typed in an environment that extends
the match compilation's own data definitions, as the indexed layouts extend the
catalog. Every child body then keeps its native typing in that environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildren
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates TypedLexicalWhile.Native
open CompatibleEncoding (bind_ok)

private theorem Fallback.add_typing' {certificate : BodyCertificate} {scope : Scope} {result : Ty}
    {fallback : Option (List StatementId)} {code : Expr}
    (certified : Fallback certificate scope result fallback code)
    {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    Fallback (TypedBody definitions administrative type certificate) scope result fallback code := by
  cases certified with
  | none => exact .none
  | some body => exact .some ⟨body, typed⟩

private theorem matcher_typed' {context : Core.Context} {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) : HasType context expression type definitions := by
  have extended := typed.rename (target := context) (mapping := Renaming.id)
    (by intro index type found; cases found)
  simpa using extended

theorem Arms.add_typing_extended
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (extension : compilation.definitions.Extends definitions)
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {certificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source site scope expected certificate cases arms)
    {result : Ty} {fallback : Option (List StatementId)} {fallbackCode branches : Expr}
    (fallbackCertified : Fallback certificate scope result fallback fallbackCode)
    (generated : Branches compilation source scope (LocalLoop.controlType result) fallbackCode arms branches)
    {scrutinee type : Ty} {administrative : Core.Context}
    (typed : HasType (scrutinee :: (SourceCoreLocalCell.coreContext scope ++ administrative)) branches type definitions) :
    Arms compilation source site scope expected (TypedBody definitions administrative type certificate) cases arms ∧
      Fallback (TypedBody definitions administrative type certificate) scope result fallback fallbackCode := by
  induction certified generalizing branches with
  | nil =>
    cases generated
    exact ⟨.nil, Fallback.add_typing' fallbackCertified (remove_front typed)⟩
  | @cons arm rest pattern body arms patternCertificate patternTyped bodyCertified tail ih =>
    cases generated with
    | cons allocation next =>
      cases typed with
      | caseE applied failed chosen =>
        cases applied with
        | apply function argument =>
          have same := typing_deterministic function (matcher_typed' (patternTyped.extend_definitions extension))
          have resultEq := (Ty.function.inj same).2
          simp only [Pattern.resultType, Ty.sum.injEq] at resultEq
          rcases resultEq with ⟨rfl, rfl⟩
          obtain ⟨nextCertified, finalFallback⟩ := ih next (remove_front failed)
          exact ⟨.cons patternCertificate patternTyped
            ⟨bodyCertified, CompatibleMatchNativeArms.bindArm_body_typing onError allocator allocation chosen⟩ nextCertified,
            finalFallback⟩

private theorem hidden_branches'
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {source : TypedSource} {scope : Scope} {binder : TypedBinder} {payload output : Ty}
    {initializer branches code : Expr} {reason : Word}
    (accepted : SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Renaming.id binder output payload initializer
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure output (.word reason)) branches) = .ok code)
    {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    HasType (payload :: OptionalCell.referenceType payload :: (SourceCoreLocalCell.coreContext scope ++ administrative))
      branches type definitions := by
  rw [allocator] at accepted
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocation, allocated, exactCode⟩ := bind_ok accepted
  obtain ⟨receipt, annotation, same, sameCode⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError allocated
  cases exactCode
  cases sameCode
  cases typed with
  | caseE initial failure next =>
    have bodyTyped := remove_second (absent_child receipt annotation same next)
    cases bodyTyped with
    | caseE loaded failure branch =>
      cases loaded with
      | loadCell reference =>
        cases reference with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Ty.cell.injEq, OptionalCell.referenceType,
            OptionalCell.cellType, Ty.sum.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          exact branch

theorem Certificate.typed_bodies_extended
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (extension : compilation.definitions.Extends definitions)
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason expressionCertificate bodyCertificate code)
    {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason expressionCertificate
      (TypedBody definitions administrative type bodyCertificate) code := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    have branchesTyped := hidden_branches' onError allocator hiddenCompiled typed
    obtain ⟨nextArms, nextFallback⟩ := Arms.add_typing_extended onError allocator extension arms fallback branches branchesTyped
    exact .matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      nextArms nextFallback branches hiddenCompiled

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildren
end
