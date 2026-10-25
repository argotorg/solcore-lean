import Solcore.Frontend.RustHull.GlobalFunctionCorrespondence

/-! State relations for independent Hull effects. Runtime resources occupy a
fixed prefix of the Core store; source locals are allocated beyond that prefix.
The generic model requires only structural store laws, never an execution or
compiler-correctness premise. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

/-- All cells already present keep their values; later allocations may add cells. -/
structure StoreRetains (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location, location < initial.length → final.read? location = initial.read? location

theorem StoreRetains.refl (store : Core.Store) : StoreRetains store store :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem StoreRetains.trans {initial middle final : Core.Store}
    (first : StoreRetains initial middle) (second : StoreRetains middle final) :
    StoreRetains initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun location bound => by
    rw [second.read location (Nat.lt_of_lt_of_le bound first.length_le), first.read location bound]⟩

theorem StoreRetains.append (store suffix : Core.Store) : StoreRetains store (store ++ suffix) := by
  refine ⟨by simp, ?_⟩
  intro location bound
  exact List.getElem?_append_left bound

/-- An external-state representation and the three structural frame rules used
by ordinary Hull code. Writes are restricted to represented source locations. -/
structure StateModel (σ : Type) where
  rel : σ → World → Core.Store → Prop
  retained : ∀ {source world initial final}, rel source world initial →
    StoreRetains initial final → rel source world final
  allocate : ∀ {source world store} (type : Core.Ty) (value : Core.Value),
    rel source world store →
    rel source (world ++ [(type, store.length)]) (store ++ [.inRight .unit value])
  write : ∀ {source world store updated} {index : Nat} {type : Core.Ty} {location : Nat} {value : Core.Value},
    rel source world store → world[index]? = some (type, location) →
    store.write? location value = some updated → rel source world updated

/-- Pure scalar execution carries no external resources. -/
def StateModel.trivial (σ : Type) : StateModel σ where
  rel := fun _ _ _ => True
  retained := fun _ _ => True.intro
  allocate := fun _ _ _ => True.intro
  write := fun _ _ _ => True.intro

/-- Read exactly the resource prefix. No observation can inspect later locals. -/
def prefixRead (boundary : Nat) (store : Core.Store) (location : Nat) : Option Core.Value :=
  if location < boundary then store.read? location else none

def WorldAbove (boundary : Nat) (world : World) : Prop :=
  ∀ (index : Nat) (type : Core.Ty) (location : Nat), world[index]? = some (type, location) → boundary ≤ location

theorem WorldAbove.allocate {boundary : Nat} {world : World} {store : Core.Store}
    (separated : WorldAbove boundary world) (bounded : boundary ≤ store.length) (type : Core.Ty) :
    WorldAbove boundary (world ++ [(type, store.length)]) := by
  intro index foundType location found
  by_cases old : index < world.length
  · rw [List.getElem?_append_left old] at found
    exact separated index foundType location found
  · have bound := (List.getElem?_eq_some_iff.mp found).1
    have fresh : index = world.length := by simp only [List.length_append, List.length_singleton] at bound; omega
    subst index
    simp only [List.getElem?_concat_length, Option.some.injEq, Prod.mk.injEq] at found
    have same : store.length = location := found.2
    omega

theorem prefixRead_retained {boundary : Nat} {initial final : Core.Store}
    (bounded : boundary ≤ initial.length) (retained : StoreRetains initial final) :
    prefixRead boundary final = prefixRead boundary initial := by
  funext location
  by_cases before : location < boundary
  · simp only [prefixRead, before, ↓reduceIte]
    exact retained.read location (Nat.lt_of_lt_of_le before bounded)
  · simp only [prefixRead, before, ↓reduceIte]

theorem prefixRead_write {boundary location : Nat} {initial final : Core.Store} {value : Core.Value}
    (separated : boundary ≤ location) (written : initial.write? location value = some final) :
    prefixRead boundary final = prefixRead boundary initial := by
  funext other
  by_cases before : other < boundary
  · simp only [prefixRead, before, ↓reduceIte]
    exact Core.Store.write?_preserves_other (location := location) (otherLocation := other) written
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le before separated))
  · simp only [prefixRead, before, ↓reduceIte]

/-- Any concrete representation using only the fixed resource cells satisfies
all local-code frame laws. The boundary and local separation are established by
actual runtime initialization, not inferred from the shapes of cell values. -/
def StateModel.cutoff {σ : Type} (boundary : Nat)
    (resources : σ → (Nat → Option Core.Value) → Prop) : StateModel σ where
  rel source world store := boundary ≤ store.length ∧ WorldAbove boundary world ∧
    resources source (prefixRead boundary store)
  retained := by
    intro source world initial final related retained
    exact ⟨Nat.le_trans related.1 retained.length_le, related.2.1,
      by rw [prefixRead_retained related.1 retained]; exact related.2.2⟩
  allocate := by
    intro source world store type value related
    refine ⟨by simp; omega, related.2.1.allocate related.1 type, ?_⟩
    rw [prefixRead_retained related.1 (StoreRetains.append store [.inRight .unit value])]
    exact related.2.2
  write := by
    intro source world store updated index type location value related entry written
    refine ⟨by rw [Core.Store.write?_preserves_length written]; exact related.1, related.2.1, ?_⟩
    rw [prefixRead_write (related.2.1 index type location entry) written]
    exact related.2.2

/-- Local-heap correspondence and external-state correspondence at one actual
Core store. Extending HeapRel keeps its cell and distinctness projections. -/
structure StateRel {σ : Type} (model : StateModel σ) (world : World)
    (source : Semantics.State σ) (store : Core.Store) : Prop extends HeapRel world source.heap store where
  external : model.rel source.external world store

theorem StateRel.trivial {σ : Type} {world : World} {source : Semantics.State σ} {store : Core.Store}
    (heap : HeapRel world source.heap store) : StateRel (StateModel.trivial σ) world source store :=
  ⟨heap, True.intro⟩

theorem StateRel.appendCore {σ : Type} {model : StateModel σ} {world : World}
    {source : Semantics.State σ} {store : Core.Store}
    (related : StateRel model world source store) (suffix : Core.Store) :
    StateRel model world source (store ++ suffix) :=
  ⟨related.toHeapRel.appendCore suffix, model.retained related.external (StoreRetains.append store suffix)⟩

theorem StateRel.allocate {σ : Type} {model : StateModel σ} {world : World}
    {source : Semantics.State σ} {store : Core.Store} (related : StateRel model world source store)
    {type : Core.Ty} {sourceValue : Semantics.Value} {targetValue : Core.Value}
    (valueRelated : ValueRel type sourceValue targetValue) :
    StateRel model (world ++ [(type, store.length)]) (Semantics.allocate source sourceValue).2
      (store ++ [.inRight .unit targetValue]) :=
  ⟨related.toHeapRel.allocate valueRelated, model.allocate type targetValue related.external⟩

theorem StateRel.write {σ : Type} {model : StateModel σ} {world : World}
    {source : Semantics.State σ} {store updated : Core.Store} (related : StateRel model world source store)
    {index : Nat} {type : Core.Ty} {location : Nat}
    (entry : world[index]? = some (type, location))
    {sourceValue : Semantics.Value} {targetValue : Core.Value}
    (valueRelated : ValueRel type sourceValue targetValue)
    (written : store.write? location (.inRight .unit targetValue) = some updated) :
    StateRel model world {source with heap := source.heap.set index sourceValue} updated :=
  ⟨related.toHeapRel.write entry valueRelated written, model.write related.external entry written⟩

theorem initializedGlobals_retains (signatures : List Signature) (codes : List GlobalCode)
    (environment : Core.Environment) (store : Core.Store) :
    StoreRetains store (initializedGlobals signatures codes environment store) := by
  refine ⟨?_, ?_⟩
  · simp [initializedGlobals, installationStore_length, globalStore]
  · intro location bound
    rw [initializedGlobals, installationStore_preserves]
    · exact List.getElem?_append_left bound
    · intro offset _
      simp only [globalLocations]
      omega

theorem StateRel.initializeGlobals {σ : Type} {model : StateModel σ} {world : World}
    {source : Semantics.State σ} {store : Core.Store}
    (related : StateRel model world source store) (signatures : List Signature) (codes : List GlobalCode)
    (environment : Core.Environment) :
    StateRel model world source (initializedGlobals signatures codes environment store) :=
  ⟨related.toHeapRel.initializeGlobals signatures codes environment,
    model.retained related.external (initializedGlobals_retains signatures codes environment store)⟩

/-- Resource updates preserve all cells beyond their fixed prefix, including
source locals and function/loop cells. Appended helper cells remain available. -/
structure StoreRetainsFrom (boundary : Nat) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location, boundary ≤ location → location < initial.length →
    final.read? location = initial.read? location

theorem StoreRetainsFrom.ofRetains {boundary : Nat} {initial final : Core.Store}
    (retained : StoreRetains initial final) : StoreRetainsFrom boundary initial final :=
  ⟨retained.length_le, fun location _ bound => retained.read location bound⟩

theorem StoreRetainsFrom.trans {boundary : Nat} {initial middle final : Core.Store}
    (first : StoreRetainsFrom boundary initial middle)
    (second : StoreRetainsFrom boundary middle final) : StoreRetainsFrom boundary initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun location separated bound => by
    rw [second.read location separated (Nat.lt_of_lt_of_le bound first.length_le),
      first.read location separated bound]⟩

theorem StoreRetainsFrom.writeBelow {boundary location : Nat}
    {initial final : Core.Store} {value : Core.Value} (below : location < boundary)
    (written : initial.write? location value = some final) : StoreRetainsFrom boundary initial final := by
  refine ⟨by simp only [Core.Store.write?_preserves_length written, Nat.le_refl], ?_⟩
  intro other separated _
  exact Core.Store.write?_preserves_other (location := location) (otherLocation := other) written
    (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le below separated)))

theorem HeapRel.frameAbove {boundary : Nat} {world : World} {source : Semantics.Heap}
    {initial final : Core.Store} (heap : HeapRel world source initial)
    (separated : WorldAbove boundary world) (retained : StoreRetainsFrom boundary initial final) :
    HeapRel world source final where
  length_eq := heap.length_eq
  distinct := heap.distinct
  cell := by
    intro index type location entry
    obtain ⟨sourceValue, targetValue, sourceFound, targetFound, related⟩ := heap.cell index type location entry
    exact ⟨sourceValue, targetValue, sourceFound, by
      rw [retained.read location (separated index type location entry) (heap.location_bound entry)]
      exact targetFound, related⟩

/-- Concrete effect primitives supply their updated resource observations and
frame all preexisting non-resource cells. No source allocation is hidden here. -/
theorem StateRel.cutoff_effect {σ : Type} {boundary : Nat}
    {resources : σ → (Nat → Option Core.Value) → Prop} {world : World}
    {source : Semantics.State σ} {initial final : Core.Store}
    (related : StateRel (StateModel.cutoff boundary resources) world source initial)
    {external : σ} (retained : StoreRetainsFrom boundary initial final)
    (updated : resources external (prefixRead boundary final)) :
    StateRel (StateModel.cutoff boundary resources) world {source with external := external} final :=
  ⟨related.toHeapRel.frameAbove related.external.2.1 retained,
    Nat.le_trans related.external.1 retained.length_le, related.external.2.1, updated⟩

/-- Actual runtime initialization fixes the resource prefix before allocating
any Hull local. Concrete contents are checked at that exact initialized store. -/
theorem StateRel.cutoff_initial {σ : Type} {resources : σ → (Nat → Option Core.Value) → Prop}
    (external : σ) (store : Core.Store)
    (initialized : resources external (prefixRead store.length store)) :
    StateRel (StateModel.cutoff store.length resources) [] ⟨[], external⟩ store :=
  ⟨HeapRel.empty store, Nat.le_refl _, (by intro index type location found; cases found), initialized⟩

/-- The real parameter allocator extends the state model along with the local
heap. The final relation refers to the state returned by source bindArguments. -/
theorem initialize_parameters_state_renamed {σ : Type} {model : StateModel σ}
    {arguments : List Arg} {types : List Core.Ty}
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel types sources targets) (arity : arguments.length = types.length)
    {sourceEnvironment : Semantics.Environment} {scope : Scope} {sourceState : Semantics.State σ}
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (stateRelated : StateRel model world sourceState store)
    {external : σ → Core.Store → Prop} (externalRelated : external sourceState.external store)
    (frame : ∀ state store type value, external state store →
      external state (store ++ [Core.Value.inRight type value])) :
    ∃ extension sourceEnvironment' sourceState' environment' store',
      Semantics.bindArguments arguments sources sourceEnvironment sourceState = some (sourceEnvironment', sourceState') ∧
      ParameterCells types targets environment store environment' store' ∧
      EnvironmentRel (world ++ extension) sourceEnvironment' (parameterScope arguments types scope)
        (parameterRenaming types.length mapping) environment' ∧
      StateRel model (world ++ extension) sourceState' store' ∧
      external sourceState'.external store' := by
  induction values generalizing arguments sourceEnvironment scope sourceState world mapping environment store with
  | nil =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      exact ⟨[], sourceEnvironment, sourceState, environment, store, rfl, .nil,
        by simpa [parameterScope, parameterRenaming] using environmentRelated,
        by simpa using stateRelated, externalRelated⟩
  | @cons type types source sources target targets head tail ih =>
      cases arguments with
      | nil => simp at arity
      | cons argument arguments =>
          have arity' : arguments.length = types.length := Nat.succ.inj arity
          have entry : (world ++ [(type, store.length)])[sourceState.heap.length]? = some (type, store.length) := by
            rw [← stateRelated.length_eq, List.getElem?_concat_length]
          have environment' := ((environmentRelated.extendWorld [(type, store.length)]).addLocal
            argument.name type sourceState.heap.length store.length entry)
          have state' := stateRelated.allocate head
          have external' := frame sourceState.external store .unit target externalRelated
          obtain ⟨extension, sourceEnvironment', sourceState', environment'', store', bound,
            allocated, locals, state, external⟩ := ih arity'
              (sourceState := (Semantics.allocate sourceState source).2)
              (sourceEnvironment := (argument.name, sourceState.heap.length) :: sourceEnvironment)
              (scope := scope.addLocal argument.name type)
              (world := world ++ [(type, store.length)])
              (mapping := mapping.lift)
              (environment := .cellRef (Core.OptionalCell.cellType type) store.length :: environment)
              (store := store ++ [.inRight .unit target]) environment' state'
              (by simpa only [Semantics.allocate] using external')
          refine ⟨[(type, store.length)] ++ extension, sourceEnvironment', sourceState', environment'', store',
            ?_, .cons allocated, ?_, ?_, external⟩
          · exact bound
          · simpa only [List.append_assoc, parameterScope, List.zip_cons_cons, List.foldl_cons,
              List.length_cons, parameterRenaming] using locals
          · simpa only [List.append_assoc] using state

end Solcore.Frontend.RustHull.Correspondence
