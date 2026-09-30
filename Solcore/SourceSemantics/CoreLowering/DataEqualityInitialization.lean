import Solcore.SourceSemantics.CoreLowering.DataEquality
import Solcore.Core.Renaming

/-! Equality preparation only allocates cells and installs suspended closures.
This finite fragment theorem establishes termination of that actual generated
initializer, even when the closures are mutually recursive. It does not yet
identify each installed helper with its source comparison certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityInitialization
open Core Frontend SourceCoreDataEquality

/-- Suspended lambda bodies need not terminate. No function application is
executed while preparing the comparison closures. -/
inductive Initializer : Expr → Prop where
  | unit : Initializer .unit
  | var (index : Nat) : Initializer (.var index)
  | lambda (parameter result : Ty) (body : Expr) : Initializer (.lambda parameter result body)
  | inLeft {right : Ty} {payload : Expr} (child : Initializer payload) : Initializer (.inLeft right payload)
  | inRight {left : Ty} {payload : Expr} (child : Initializer payload) : Initializer (.inRight left payload)
  | newCell {type : Ty} {payload : Expr} (child : Initializer payload) : Initializer (.newCell type payload)
  | storeCell {reference value : Expr} (first : Initializer reference) (second : Initializer value) :
      Initializer (.storeCell reference value)
  | letE {value body : Expr} (first : Initializer value) (second : Initializer body) : Initializer (.letE value body)

theorem Initializer.rename {expression : Expr} (initializing : Initializer expression) (mapping : Renaming) :
    Initializer (expression.rename mapping) := by
  induction initializing generalizing mapping with
  | unit => exact .unit
  | var => exact .var _
  | lambda => exact .lambda _ _ _
  | inLeft _ ih => exact .inLeft (ih mapping)
  | inRight _ ih => exact .inRight (ih mapping)
  | newCell _ ih => exact .newCell (ih mapping)
  | storeCell _ _ left right => exact .storeCell (left mapping) (right mapping)
  | letE _ _ first second => exact .letE (first mapping) (second mapping.lift)

theorem Initializer.weakenAt {expression : Expr} (initializing : Initializer expression) (cutoff : Nat) :
    Initializer (expression.weakenAt cutoff) := by
  rw [← Expr.rename_insertion]
  exact initializing.rename _

/-- Structural termination uses runtime store typing between effects, so it
also admits cells containing closures, cells and recursive references. -/
theorem Initializer.evaluates {expression : Expr} (initializing : Initializer expression)
    {definitions : DataEnvironment} {context : Core.Context} {type : Ty} {environment : Environment}
    {world : StoreTyping} {store : Store} (typed : HasType context expression type definitions)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyped : RuntimeStoreHasTypes world store definitions) :
    ∃ value finalStore, Evaluates environment store expression value finalStore := by
  induction initializing generalizing context type environment world store with
  | unit => exact ⟨_, _, .unit⟩
  | var index =>
    cases typed with
    | var found => obtain ⟨value, lookup, _⟩ := environmentTyped.lookup found; exact ⟨value, store, .var lookup⟩
  | lambda => exact ⟨_, _, .lambda⟩
  | inLeft child ih =>
    cases typed with
    | inLeft _ childTyped => obtain ⟨value, finalStore, evaluated⟩ := ih childTyped environmentTyped storeTyped; exact ⟨_, _, .inLeft evaluated⟩
  | inRight child ih =>
    cases typed with
    | inRight _ childTyped => obtain ⟨value, finalStore, evaluated⟩ := ih childTyped environmentTyped storeTyped; exact ⟨_, _, .inRight evaluated⟩
  | newCell child ih =>
    cases typed with
    | newCell childTyped => obtain ⟨value, finalStore, evaluated⟩ := ih childTyped environmentTyped storeTyped; exact ⟨_, _, .newCell evaluated⟩
  | storeCell first second firstIH secondIH =>
    cases typed with
    | storeCell referenceTyped valueTyped =>
      obtain ⟨reference, referenceStore, referenceEvaluated⟩ := firstIH referenceTyped environmentTyped storeTyped
      obtain ⟨referenceWorld, extension, referenceStoreTyped, referenceValueTyped⟩ :=
        evaluation_preserves_type referenceEvaluated referenceTyped environmentTyped storeTyped
      cases referenceValueTyped with
      | cellRef worldLookup =>
        obtain ⟨old, oldRead, _⟩ := referenceStoreTyped.read worldLookup
        obtain ⟨value, valueStore, valueEvaluated⟩ := secondIH valueTyped (environmentTyped.weaken extension) referenceStoreTyped
        obtain ⟨valueWorld, valueExtends, valueStoreTyped, _⟩ :=
          evaluation_preserves_type valueEvaluated valueTyped (environmentTyped.weaken extension) referenceStoreTyped
        obtain ⟨finalStore, written⟩ := (Store.write?_success_iff _ _ value).mpr
          (valueStoreTyped.location_lt (valueExtends.lookup worldLookup))
        exact ⟨_, _, .storeCell referenceEvaluated oldRead valueEvaluated written⟩
  | letE first second firstIH secondIH =>
    cases typed with
    | letE firstTyped secondTyped =>
      obtain ⟨value, middleStore, firstEvaluated⟩ := firstIH firstTyped environmentTyped storeTyped
      obtain ⟨middleWorld, extension, middleStoreTyped, valueTyped⟩ :=
        evaluation_preserves_type firstEvaluated firstTyped environmentTyped storeTyped
      obtain ⟨result, finalStore, bodyEvaluated⟩ := secondIH secondTyped
        (.cons valueTyped (environmentTyped.weaken extension)) middleStoreTyped
      exact ⟨result, finalStore, .letE firstEvaluated bodyEvaluated⟩

private theorem install_initializes (catalog : Catalog) (bodies : List Expr) {next : Expr}
    (initialized : Initializer next) : Initializer (install catalog bodies next) := by
  unfold install
  generalize bodies.zipIdx = rows
  induction rows with
  | nil => exact initialized
  | cons row rows ih =>
    exact .letE (.storeCell (.var _) (.inRight (.lambda _ _ _))) (ih.weakenAt 0)

private theorem allocate_initializes (catalog : Catalog) {next : Expr} (initialized : Initializer next) :
    Initializer (allocate catalog next) := by
  unfold allocate
  generalize catalog.entries.zipIdx = rows
  induction rows with
  | nil => exact initialized
  | cons row rows ih => exact .letE (.newCell (.inLeft .unit)) ih

theorem prepared_initializes {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked) :
    Initializer prepared.expression := by
  rw [prepared.expression_eq]
  exact allocate_initializes _ (install_initializes _ _ (.lambda _ _ _))

/-- Actual prepared code executes finitely in any aligned ambient environment
and store. Returned closure syntax and captured values are the machine's real
result, including administrative binders introduced during installation. -/
theorem prepared_evaluates {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {context : Core.Context} {store : Store} {world : StoreTyping}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (storeTyped : RuntimeStoreHasTypes world store checked.catalog.definitions) :
    ∃ body captured finalStore finalWorld,
      Evaluates environment store prepared.expression
        (.closure (.product prepared.type prepared.type) .bool body captured) finalStore ∧
      WorldExtends world finalWorld ∧ RuntimeStoreHasTypes finalWorld finalStore checked.catalog.definitions ∧
      RuntimeValueHasType finalWorld (.closure (.product prepared.type prepared.type) .bool body captured)
        (comparatorType prepared.type) checked.catalog.definitions := by
  have typed : HasType context prepared.expression (comparatorType prepared.type) checked.catalog.definitions := by
    have respect : Renaming.Respects Renaming.id [] context := by intro index type found; simp at found
    simpa using prepared.typed.rename respect
  obtain ⟨value, finalStore, evaluated⟩ := (prepared_initializes prepared).evaluates typed environmentTyped storeTyped
  obtain ⟨finalWorld, extension, finalStoreTyped, resultTyped⟩ :=
    evaluation_preserves_type evaluated typed environmentTyped storeTyped
  cases resultTyped with
  | closure capturedTyped bodyTyped =>
    exact ⟨_, _, finalStore, finalWorld, evaluated, extension, finalStoreTyped, .closure capturedTyped bodyTyped⟩

theorem prepared_run {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {context : Core.Context} {store : Store} {world : StoreTyping}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (storeTyped : RuntimeStoreHasTypes world store checked.catalog.definitions) :
    ∃ body captured finalStore finalWorld,
      WorldExtends world finalWorld ∧ RuntimeStoreHasTypes finalWorld finalStore checked.catalog.definitions ∧
      RuntimeValueHasType finalWorld (.closure (.product prepared.type prepared.type) .bool body captured)
        (comparatorType prepared.type) checked.catalog.definitions ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial prepared.expression environment store) =
          .done (.closure (.product prepared.type prepared.type) .bool body captured) finalStore) ∧
      (∀ fuel actual actualStore,
        runStateful fuel (.initial prepared.expression environment store) = .done actual actualStore →
        actual = .closure (.product prepared.type prepared.type) .bool body captured ∧ actualStore = finalStore) := by
  obtain ⟨body, captured, finalStore, finalWorld, evaluated, extension, storeTyped, resultTyped⟩ :=
    prepared_evaluates prepared environmentTyped storeTyped
  exact ⟨body, captured, finalStore, finalWorld, extension, storeTyped, resultTyped,
    evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

/-- Count allocation effects in the initialization fragment. Suspended lambda
bodies do not contribute effects. -/
def allocations : Expr → Nat
  | .newCell _ initializer => allocations initializer + 1
  | .letE value body | .storeCell value body => allocations value + allocations body
  | .inLeft _ value | .inRight _ value => allocations value
  | _ => 0

private theorem Initializer.allocations_rename {expression : Expr} (initializing : Initializer expression)
    (mapping : Renaming) : allocations (expression.rename mapping) = allocations expression := by
  induction initializing generalizing mapping with
  | unit | var | lambda => rfl
  | inLeft _ ih | inRight _ ih | newCell _ ih => simpa [Expr.rename, allocations] using ih mapping
  | storeCell _ _ left right => simp [Expr.rename, allocations, left mapping, right mapping]
  | letE _ _ first second => simp [Expr.rename, allocations, first mapping, second mapping.lift]

private theorem Initializer.allocations_weaken {expression : Expr} (initializing : Initializer expression)
    (cutoff : Nat) : allocations (expression.weakenAt cutoff) = allocations expression := by
  rw [← Expr.rename_insertion]
  exact initializing.allocations_rename _

/-- Every successful initializer execution has precisely its syntactic
allocation count; stores are allowed to grow and contain recursive closures. -/
theorem Initializer.evaluation_length {expression : Expr} (initializing : Initializer expression)
    {environment : Environment} {initialStore finalStore : Store} {value : Value}
    (evaluated : Evaluates environment initialStore expression value finalStore) :
    finalStore.length = initialStore.length + allocations expression := by
  induction initializing generalizing environment initialStore finalStore value with
  | unit | var | lambda => cases evaluated; simp [allocations]
  | inLeft child ih => cases evaluated with
    | inLeft payload => exact ih payload
  | inRight child ih => cases evaluated with
    | inRight payload => exact ih payload
  | newCell child ih => cases evaluated with
    | newCell payload => simp [allocations, List.length_append, ih payload, Nat.add_assoc]
  | storeCell first second firstIH secondIH => cases evaluated with
    | storeCell reference _ value written =>
      have left := firstIH reference
      have right := secondIH value
      have same := Store.write?_preserves_length written
      simp only [allocations]
      omega
  | letE first second firstIH secondIH => cases evaluated with
    | letE initial body =>
      have left := firstIH initial
      have right := secondIH body
      simp only [allocations]
      omega

private theorem install_count (catalog : Catalog) (bodies : List Expr) {next : Expr}
    (initialized : Initializer next) : allocations (install catalog bodies next) = allocations next := by
  unfold install
  generalize bodies.zipIdx = rows
  suffices ∀ rows : List (Expr × Nat),
      Initializer (rows.foldr (fun (body, index) next =>
        .letE (.storeCell (.var (referenceIndex catalog 0 ⟨index⟩))
          (.inRight .unit (.lambda (.product (.namedData ⟨index⟩) (.namedData ⟨index⟩)) .bool body)))
          (next.weakenAt 0)) next) ∧
      allocations (rows.foldr (fun (body, index) next =>
        .letE (.storeCell (.var (referenceIndex catalog 0 ⟨index⟩))
          (.inRight .unit (.lambda (.product (.namedData ⟨index⟩) (.namedData ⟨index⟩)) .bool body)))
          (next.weakenAt 0)) next) = allocations next by exact (this rows).2
  intro rows
  induction rows with
  | nil => exact ⟨initialized, rfl⟩
  | cons row rows ih =>
    refine ⟨.letE (.storeCell (.var _) (.inRight (.lambda _ _ _))) (ih.1.weakenAt 0), ?_⟩
    simp only [List.foldr_cons, allocations, Nat.zero_add, ih.1.allocations_weaken, ih.2]

private theorem allocate_count (catalog : Catalog) (next : Expr) :
    allocations (allocate catalog next) = catalog.entries.length + allocations next := by
  unfold allocate
  have count : catalog.entries.zipIdx.length = catalog.entries.length := by simp
  generalize catalog.entries.zipIdx = rows at *
  rw [← count]
  clear count
  induction rows with
  | nil => simp
  | cons row rows ih =>
    simp only [List.foldr_cons, List.length_cons, OptionalCell.allocate, allocations] at ih ⊢
    omega

/-- Preparation allocates exactly one administrative cell for each catalog
entry. Installation changes those cells without allocating more cells. -/
theorem prepared_allocation_count {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked) :
    allocations prepared.expression = checked.catalog.entries.length := by
  rw [prepared.expression_eq, allocate_count, install_count _ _ (.lambda _ _ _)]
  simp [allocations]

theorem prepared_evaluation_length {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {initialStore finalStore : Store} {value : Value}
    (evaluated : Evaluates environment initialStore prepared.expression value finalStore) :
    finalStore.length = initialStore.length + checked.catalog.entries.length := by
  simpa only [prepared_allocation_count] using (prepared_initializes prepared).evaluation_length evaluated

end Solcore.SourceSemantics.CoreLowering.DataEqualityInitialization
