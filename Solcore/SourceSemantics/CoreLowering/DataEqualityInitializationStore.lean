import Solcore.SourceSemantics.CoreLowering.DataEqualityInitialization

/-! Store confinement for actual comparison initialization. Closure bodies and
captured values remain suspended, so only directly accessible reference values
can authorize a write. This requires no acyclic traversal of closure heaps. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityInitializationStore
open Core Frontend SourceCoreDataEquality DataEqualityInitialization

/-- Direct references visible to the initializer point at administrative
cells. Closures need no condition on their suspended captured environments. -/
def ReferenceAbove (boundary : Nat) (value : Value) : Prop :=
  ∀ type location, value = .cellRef type location → boundary ≤ location

/-- Typing restricts accessible variable indices; inaccessible ambient values
need no condition, in particular when the initializer has closed Core type. -/
def AccessibleReferencesAbove (boundary : Nat) (context : Core.Context) (environment : Environment) : Prop :=
  ∀ (index : Nat) (type : Ty) (value : Value), context[index]? = some type → environment[index]? = some value → ReferenceAbove boundary value

/-- Administrative writes and allocations preserve every preexisting slot. -/
def PrefixPreserved (boundary : Nat) (initial final : Store) : Prop :=
  ∀ location, location < boundary → final.read? location = initial.read? location

private theorem PrefixPreserved.refl (boundary : Nat) (store : Store) : PrefixPreserved boundary store store :=
  fun _ _ => rfl
private theorem PrefixPreserved.trans {boundary : Nat} {first middle last : Store}
    (left : PrefixPreserved boundary first middle) (right : PrefixPreserved boundary middle last) :
    PrefixPreserved boundary first last := fun location bound => (right location bound).trans (left location bound)

private theorem references_cons {boundary : Nat} {context : Core.Context} {environment : Environment}
    {value : Value} {type : Ty} (head : ReferenceAbove boundary value)
    (tail : AccessibleReferencesAbove boundary context environment) :
    AccessibleReferencesAbove boundary (type :: context) (value :: environment) := by
  intro index selected actual typed found
  cases index with
  | zero => cases typed; cases found; exact head
  | succ index => exact tail index selected actual typed found

/-- This finite fragment cannot reach a preexisting cell through a suspended
closure. Every actual write target comes from a checked accessible variable or
a fresh allocation, and the proof follows its real evaluation. -/
theorem Initializer.preserves_prefix {expression : Expr} (initializing : Initializer expression)
    {definitions : DataEnvironment} {context : Core.Context} {type : Ty} {environment : Environment}
    {boundary : Nat} {initialStore finalStore : Store} {value : Value}
    (typed : HasType context expression type definitions)
    (accessible : AccessibleReferencesAbove boundary context environment)
    (inBounds : boundary ≤ initialStore.length)
    (evaluated : Evaluates environment initialStore expression value finalStore) :
    ReferenceAbove boundary value ∧ PrefixPreserved boundary initialStore finalStore := by
  induction initializing generalizing context type environment initialStore finalStore value with
  | unit => cases evaluated; exact ⟨(by intro _ _ impossible; cases impossible), PrefixPreserved.refl _ _⟩
  | var index =>
    cases typed with
    | var found => cases evaluated with
      | var read => exact ⟨accessible index _ _ found read, PrefixPreserved.refl _ _⟩
  | lambda => cases evaluated; exact ⟨(by intro _ _ impossible; cases impossible), PrefixPreserved.refl _ _⟩
  | inLeft child ih =>
    cases typed with
    | inLeft _ childTyped => cases evaluated with
      | inLeft childEvaluated =>
        exact ⟨(by intro _ _ impossible; cases impossible), (ih childTyped accessible inBounds childEvaluated).2⟩
  | inRight child ih =>
    cases typed with
    | inRight _ childTyped => cases evaluated with
      | inRight childEvaluated =>
        exact ⟨(by intro _ _ impossible; cases impossible), (ih childTyped accessible inBounds childEvaluated).2⟩
  | newCell child ih =>
    cases typed with
    | newCell childTyped => cases evaluated with
      | newCell childEvaluated =>
        have childBounds := Nat.le_trans inBounds (evaluation_store_length_monotone childEvaluated)
        refine ⟨?_, ?_⟩
        · intro type location same
          cases same
          exact childBounds
        · intro location bound
          have current := (ih childTyped accessible inBounds childEvaluated).2 location bound
          apply Eq.trans ?_ current
          apply Store.allocate_old_lookup
          exact Nat.lt_of_lt_of_le bound childBounds
  | storeCell first second firstIH secondIH =>
    cases typed with
    | storeCell firstTyped secondTyped => cases evaluated with
      | storeCell referenceRead oldRead valueRead written =>
        obtain ⟨referenceAbove, referencePrefix⟩ := firstIH firstTyped accessible inBounds referenceRead
        have targetAbove := referenceAbove _ _ rfl
        obtain ⟨_, valuePrefix⟩ := secondIH secondTyped accessible
          (Nat.le_trans inBounds (evaluation_store_length_monotone referenceRead)) valueRead
        refine ⟨(by intro _ _ impossible; cases impossible), ?_⟩
        intro location bound
        apply Eq.trans ?_ ((valuePrefix location bound).trans (referencePrefix location bound))
        exact Store.write?_preserves_other written (Nat.ne_of_lt (Nat.lt_of_lt_of_le bound targetAbove))
  | letE first second firstIH secondIH =>
    cases typed with
    | letE firstTyped secondTyped => cases evaluated with
      | letE firstEvaluated bodyEvaluated =>
        obtain ⟨valueAbove, firstPrefix⟩ := firstIH firstTyped accessible inBounds firstEvaluated
        obtain ⟨resultAbove, bodyPrefix⟩ := secondIH secondTyped (references_cons valueAbove accessible)
          (Nat.le_trans inBounds (evaluation_store_length_monotone firstEvaluated)) bodyEvaluated
        exact ⟨resultAbove, firstPrefix.trans bodyPrefix⟩

/-- Closed prepared code cannot write through an ambient reference, even when
the caller's environment contains references into the preexisting store. -/
theorem prepared_preserves_prefix {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {initialStore finalStore : Store} {value : Value}
    (evaluated : Evaluates environment initialStore prepared.expression value finalStore) :
    PrefixPreserved initialStore.length initialStore finalStore := by
  have accessible : AccessibleReferencesAbove initialStore.length [] environment := by
    intro index type value found
    simp at found
  exact (Initializer.preserves_prefix (prepared_initializes prepared) prepared.typed accessible (Nat.le_refl _) evaluated).2

/-- The actual initializer extends the store with exactly the catalog's helper
cells and leaves the complete source-visible prefix unchanged. -/
theorem prepared_store_extension {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {initialStore finalStore : Store} {value : Value}
    (evaluated : Evaluates environment initialStore prepared.expression value finalStore) :
    ∃ administrative, finalStore = initialStore ++ administrative ∧ administrative.length = checked.catalog.entries.length := by
  have preserved :=  prepared_preserves_prefix prepared evaluated
  have length := prepared_evaluation_length prepared evaluated
  refine ⟨finalStore.drop initialStore.length, ?_, ?_⟩
  · have take : finalStore.take initialStore.length = initialStore := by
      apply List.ext_getElem?
      intro index
      by_cases bound : index < initialStore.length
      · simp only [List.getElem?_take, bound, ↓reduceIte]
        exact preserved index bound
      · simp [List.getElem?_take, bound]
    exact (List.take_append_drop initialStore.length finalStore).symm.trans
      (congrArg (fun head => head ++ finalStore.drop initialStore.length) take)
  · simp only [List.length_drop]
    omega

/-- Preparation returns its real closure and appends a precisely sized
administrative suffix. Resumption/completion can retain the original source
heap representation because every existing slot remains byte-for-byte equal. -/
theorem prepared_run_extends {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {context : Core.Context} {store : Store} {world : StoreTyping}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (storeTyped : RuntimeStoreHasTypes world store checked.catalog.definitions) :
    ∃ body captured administrative finalWorld,
      administrative.length = checked.catalog.entries.length ∧ WorldExtends world finalWorld ∧
      RuntimeStoreHasTypes finalWorld (store ++ administrative) checked.catalog.definitions ∧
      RuntimeValueHasType finalWorld (.closure (.product prepared.type prepared.type) .bool body captured)
        (comparatorType prepared.type) checked.catalog.definitions ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial prepared.expression environment store) =
          .done (.closure (.product prepared.type prepared.type) .bool body captured) (store ++ administrative)) ∧
      (∀ fuel actual actualStore,
        runStateful fuel (.initial prepared.expression environment store) = .done actual actualStore →
        actual = .closure (.product prepared.type prepared.type) .bool body captured ∧ actualStore = store ++ administrative) := by
  obtain ⟨body, captured, finalStore, finalWorld, evaluated, extension, storeTyped, valueTyped⟩ :=
    prepared_evaluates prepared environmentTyped storeTyped
  obtain ⟨administrative, rfl, length⟩ := prepared_store_extension prepared evaluated
  exact ⟨body, captured, administrative, finalWorld, length, extension, storeTyped, valueTyped,
    evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

end Solcore.SourceSemantics.CoreLowering.DataEqualityInitializationStore
