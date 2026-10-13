import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission

/-! Static program certification can leave selected actual cached roots to
compiler receipt producers. Every closure, method and other root is checked.
Completing every selected position yields the existing full program certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProgramRootCompletion
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedProgramAdmission

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← allProof? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

inductive Root (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) where
  | checked (root : RootCertificate compiled named directRows)
  | chosen (member : position ∈ chosen)

structure Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) where
  root : Root compiled chosen position named directRows
  closures : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
    compiled named directRows allowCoerced

/-- Each requested position exists in the actual complete cache. Only its root
is pending; its closures receive the same checks as every other row. -/
structure Pending (compiled : SourceCoreUnifiedCompilation.Compiled)
    (positions : List Nat) where
  selected : ∀ position ∈ positions, ∃ named, compiled.indexed.base.functions[position]? = some named
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ pair ∈ compiled.indexed.base.functions.zipIdx,
    Nonempty (Row compiled positions pair.2 pair.1 table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) :
    Option (Row compiled chosen position named directRows allowCoerced) := do
  let root ← if member : position ∈ chosen then pure (.chosen member) else do
    let checked ← CallableIndexedOwnedPreparedProgramAdmission.certifyRoot compiled named directRows fuel
    pure (.checked checked)
  let ⟨closures⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource
    compiled named directRows allowCoerced fuel
  pure ⟨root, closures⟩

/-- All requested indices are validated before root scanning. Every selected
root is deferred while its actual closures and the rest of the cache are checked. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (positions : List Nat) (fuel : Nat) :
    Option (Pending compiled positions) := do
  let ⟨selected⟩ ← allProof?
    (fun position => ∃ named, compiled.indexed.base.functions[position]? = some named)
    (fun position => match compiled.indexed.base.functions[position]? with
      | none => none
      | some named => some ⟨⟨named, rfl⟩⟩) positions
  if profile : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
      let selection ← certifySelection compiled table.rows fuel
      let ⟨rows⟩ ← allProof?
        (fun pair : SourceCoreGeneralFunctions.Function × Nat =>
          Nonempty (Row compiled positions pair.2 pair.1 table.rows selection.allowCoerced))
        (fun pair => do
          let row ← certifyRow compiled positions pair.2 pair.1 table.rows selection.allowCoerced fuel
          pure ⟨⟨row⟩⟩) compiled.indexed.base.functions.zipIdx
      pure ⟨selected, table, selection, rows, profile, diagnostics, present⟩
  else none

/-- Completion is indexed by actual cache lookup. Every selected row receives
its own root certificate, even when rows have the same name or result type. -/
def Pending.complete {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        RootCertificate compiled named pending.table.rows) : Certificate compiled := {
  table := pending.table
  selection := pending.selection
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    cases row.root with
    | checked checked => exact ⟨⟨checked, row.closures⟩⟩
    | chosen selected => exact ⟨⟨roots index selected named found, row.closures⟩⟩
  profile := pending.profile
  diagnostics := pending.diagnostics }

theorem Pending.complete_table {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        RootCertificate compiled named pending.table.rows) :
    (pending.complete roots).table = pending.table := rfl

theorem Pending.complete_selection {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        RootCertificate compiled named pending.table.rows) :
    (pending.complete roots).selection = pending.selection := rfl


/-- Compiler producers may retain data certificates in a proposition. Each
receipt is opened only inside the existing cached-row proof. -/
def Pending.complete_receipts {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows)) : Certificate compiled := {
  table := pending.table
  selection := pending.selection
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    cases row.root with
    | checked checked => exact ⟨⟨checked, row.closures⟩⟩
    | chosen selected =>
        obtain ⟨root⟩ := roots index selected named found
        exact ⟨⟨root, row.closures⟩⟩
  profile := pending.profile
  diagnostics := pending.diagnostics }

theorem Pending.complete_receipts_table {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows)) :
    (pending.complete_receipts roots).table = pending.table := rfl

theorem Pending.complete_receipts_selection {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows)) :
    (pending.complete_receipts roots).selection = pending.selection := rfl

end Solcore.SourceSemantics.CoreLowering.AcceptedProgramRootCompletion
