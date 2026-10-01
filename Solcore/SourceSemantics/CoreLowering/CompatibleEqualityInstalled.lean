import Solcore.Frontend.SourceCoreCompatibleDataEquality
import Solcore.SourceSemantics.CoreLowering.DataEqualityGeneration

/-! Exact initialization of the actual compatible comparator helpers. The
adapter below is used only by generic allocation/closure-storage lemmas. It
never reuses a strict projection or a strict semantic preparation receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceCoreCompatibleDataEquality

/-- Same administrative layout, with no claim about strict data semantics. -/
def storageCatalog (catalog : Catalog) : SourceCoreDataCatalog.Catalog :=
  ⟨catalog.entries, catalog.callableContracts⟩

theorem allocate_storage (catalog : Catalog) (next : Expr) :
    allocate catalog next = SourceCoreDataEquality.allocate (storageCatalog catalog) next := rfl

theorem install_storage (catalog : Catalog) (bodies : List Expr) (next : Expr) :
    install catalog bodies next = SourceCoreDataEquality.install (storageCatalog catalog) bodies next := rfl

private theorem mapM_length {α β ε : Type} (function : α → Except ε β) {inputs : List α} {outputs : List β}
    (generated : inputs.mapM function = .ok outputs) : outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => cases generated; rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at generated
    obtain ⟨first, _, generated⟩ := DataEqualityGeneration.bind_ok generated
    obtain ⟨rest, remaining, generated⟩ := DataEqualityGeneration.bind_ok generated
    cases generated
    exact congrArg Nat.succ (ih remaining)

theorem bodies_length {fuel : Nat} {catalog : Catalog} {bodies : List Expr}
    (generated : helperBodies fuel catalog = .ok bodies) : bodies.length = catalog.entries.length := by
  simpa using mapM_length (fun (row : SourceCoreDataCatalog.Entry × Nat) => helperBody fuel catalog ⟨row.2⟩) generated

abbrev Installed (catalog : Catalog) := DataEqualityInstalled.Installed (storageCatalog catalog)

def preparedClosure {checked : Checked} (prepared : Prepared checked) (environment : Environment) (base : Nat) : Value :=
  .closure (.product prepared.type prepared.type) .bool
    (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
    (DataEqualityInstalled.captured prepared.bodies.length
      (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) base environment))

def preparedStore {checked : Checked} (prepared : Prepared checked) (environment : Environment) (store : Store) : Store :=
  store ++ DataEqualityInstalled.cells
    (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment) prepared.bodies

theorem prepared_evaluates_exact {checked : Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) :
    Evaluates environment store prepared.expression (preparedClosure prepared environment store.length)
      (preparedStore prepared environment store) := by
  rw [prepared.expression_eq, allocate_storage, install_storage, DataEqualityInstalled.allocate_eq_types]
  apply DataEqualityInstalled.allocate_types_evaluates
  apply DataEqualityInstalled.install_evaluates (storageCatalog checked.catalog) _ store _ prepared.bodies
  · exact DataEqualityInstalled.allocated_references _ _ _
  · simp [DataEqualityInstalled.emptyCells, DataEqualityInstalled.catalogTypes_length, storageCatalog, bodies_length prepared.bodiesGenerated]
  · exact Nat.le_of_eq (bodies_length prepared.bodiesGenerated)

theorem prepared_installed {checked : Checked} (prepared : Prepared checked) (environment : Environment) (store : Store) :
    Installed checked.catalog prepared.bodies store.length environment (preparedStore prepared environment store) := by
  intro index body found
  simpa [preparedStore, Store.read?, List.getElem?_append_right] using
    (DataEqualityInstalled.cells_lookup
      (environment := DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment) found)

theorem prepared_run {checked : Checked} (prepared : Prepared checked) (environment : Environment) (store : Store) :
    (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel (.initial prepared.expression environment store) =
      .done (preparedClosure prepared environment store.length) (preparedStore prepared environment store)) ∧
    (∀ fuel value finalStore, runStateful fuel (.initial prepared.expression environment store) = .done value finalStore →
      value = preparedClosure prepared environment store.length ∧ finalStore = preparedStore prepared environment store) :=
  ⟨evaluation_runStateful_complete_with_sufficient_fuel (prepared_evaluates_exact prepared environment store),
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) (prepared_evaluates_exact prepared environment store)⟩

/-- Lookup in the actual compatible helper generator, retaining each body. -/
theorem helperBodies_lookup {fuel : Nat} {catalog : Catalog} {bodies : List Expr}
    (generated : helperBodies fuel catalog = .ok bodies) {index : Nat} (bound : index < catalog.entries.length) :
    ∃ body, bodies[index]? = some body ∧ helperBody fuel catalog ⟨index⟩ = .ok body :=
  DataEqualityGeneration.mapM_lookup
    (fun (row : SourceCoreDataCatalog.Entry × Nat) => helperBody fuel catalog ⟨row.2⟩) generated
    (input := (catalog.entries[index], index)) (by simp [List.getElem?_zipIdx, List.getElem?_eq_getElem bound])

theorem nominalBody_branches {fuel : Nat} {catalog : Catalog} {id : DataTypeId}
    {payloads : List Ty} {body : Expr} (generated : nominalBody fuel catalog id payloads = .ok body)
    {leftIndex rightIndex : Nat} {leftType rightType : Ty}
    (leftSelected : payloads[leftIndex]? = some leftType) (rightSelected : payloads[rightIndex]? = some rightType) :
    ∃ branches rightBranches branch,
      body = .matchData id .bool (.first (.var 0)) branches ∧
      branches[leftIndex]? = some (.matchData id .bool (.second (.var 1)) rightBranches) ∧
      rightBranches[rightIndex]? = some branch ∧
      (if leftIndex = rightIndex then compareType fuel catalog 3 leftType (.var 1) (.var 0)
       else .ok (.bool false)) = .ok branch := by
  unfold nominalBody at generated
  obtain ⟨branches, generatedBranches, generated⟩ := DataEqualityGeneration.bind_ok generated
  cases generated
  obtain ⟨leftBranch, selectedBranch, generatedLeft⟩ := DataEqualityGeneration.mapM_lookup _ generatedBranches
    (index := leftIndex) (input := (leftType, leftIndex)) (by simp [List.getElem?_zipIdx, leftSelected])
  obtain ⟨rightBranches, generatedRight, generatedLeft⟩ := DataEqualityGeneration.bind_ok generatedLeft
  cases generatedLeft
  obtain ⟨branch, selectedRight, generatedBranch⟩ := DataEqualityGeneration.mapM_lookup _ generatedRight
    (index := rightIndex) (input := (rightType, rightIndex)) (by simp [List.getElem?_zipIdx, rightSelected])
  exact ⟨branches, rightBranches, branch, rfl, selectedBranch, selectedRight, generatedBranch⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
