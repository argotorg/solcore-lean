import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission

/-! Static program certification can leave one actual cached root to the
compiler receipt producer. Every closure, method and other root is still checked.
Completing the exact root yields the existing full program certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProgramBodyCompletion
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
    (chosen position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) where
  | checked (root : RootCertificate compiled named directRows)
  | chosen (same : position = chosen)

structure Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) where
  root : Root compiled chosen position named directRows
  closures : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
    compiled named directRows allowCoerced

/-- The pending row is a member of the actual complete cache. Its exact root
is the only missing field; its closures receive the same checks as every row. -/
structure Pending (compiled : SourceCoreUnifiedCompilation.Compiled)
    (position : Nat) where
  chosen : SourceCoreGeneralFunctions.Function
  selected : compiled.indexed.base.functions[position]? = some chosen
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ pair ∈ compiled.indexed.base.functions.zipIdx,
    Nonempty (Row compiled position pair.2 pair.1 table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) :
    Option (Row compiled chosen position named directRows allowCoerced) := do
  let root ← if same : position = chosen then pure (.chosen same) else do
    let checked ← CallableIndexedOwnedPreparedProgramAdmission.certifyRoot compiled named directRows fuel
    pure (.checked checked)
  let ⟨closures⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource
    compiled named directRows allowCoerced fuel
  pure ⟨root, closures⟩

/-- This checker never invokes the root scanner for the exact chosen row.
The completed certificate still requires its authentic root proof. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (position : Nat) (fuel : Nat) :
    Option (Pending compiled position) := do
  match selected : compiled.indexed.base.functions[position]? with
  | none => none
  | some chosen =>
    if profile : compiled.compatible.checked.catalog.callableContracts = true then
      match present : compiled.indexed.base.diagnostics with
      | none => none
      | some diagnostics =>
        let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
        let selection ← certifySelection compiled table.rows fuel
        let ⟨rows⟩ ← allProof?
          (fun pair : SourceCoreGeneralFunctions.Function × Nat =>
            Nonempty (Row compiled position pair.2 pair.1 table.rows selection.allowCoerced))
          (fun pair => do
            let row ← certifyRow compiled position pair.2 pair.1 table.rows selection.allowCoerced fuel
            pure ⟨⟨row⟩⟩) compiled.indexed.base.functions.zipIdx
        pure ⟨chosen, selected, table, selection, rows, profile, diagnostics, present⟩
    else none

/-- Every completed root is either checked at its own cached source or supplied
by the exact chosen-row proof. No cached entry is omitted from coverage. -/
def Pending.complete {compiled : SourceCoreUnifiedCompilation.Compiled}
    {position : Nat} (pending : Pending compiled position)
    (root : RootCertificate compiled pending.chosen pending.table.rows) : Certificate compiled := {
  table := pending.table
  selection := pending.selection
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    cases row.root with
    | checked checked => exact ⟨⟨checked, row.closures⟩⟩
    | chosen same =>
      change index = position at same
      rw [same] at found
      have exactRow : named = pending.chosen :=
        Option.some.inj (found.symm.trans pending.selected)
      cases exactRow
      exact ⟨⟨root, row.closures⟩⟩
  profile := pending.profile
  diagnostics := pending.diagnostics }

theorem Pending.complete_table {compiled : SourceCoreUnifiedCompilation.Compiled}
    {position : Nat} (pending : Pending compiled position)
    (root : RootCertificate compiled pending.chosen pending.table.rows) :
    (pending.complete root).table = pending.table := rfl

theorem Pending.complete_selection {compiled : SourceCoreUnifiedCompilation.Compiled}
    {position : Nat} (pending : Pending compiled position)
    (root : RootCertificate compiled pending.chosen pending.table.rows) :
    (pending.complete root).selection = pending.selection := rfl

end Solcore.SourceSemantics.CoreLowering.AcceptedProgramBodyCompletion
