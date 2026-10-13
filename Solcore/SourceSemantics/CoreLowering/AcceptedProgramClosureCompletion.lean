import Solcore.SourceSemantics.CoreLowering.AcceptedProgramRootCompletion

/-! Selected actual cached roots and closure sources can be completed by
compiler receipt producers. Other rows and every method keep their finite checks.
The completed value is the existing full program certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProgramClosureCompletion
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedProgramAdmission
open AcceptedProgramRootCompletion (Root)

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

inductive Closures (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) where
  | checked (certificate : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
      compiled named directRows allowCoerced)
  | chosen (member : position ∈ chosen)

structure Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (roots closures : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) where
  root : Root compiled roots position named directRows
  closures : Closures compiled closures position named directRows allowCoerced

/-- Both sets of positions refer to the complete actual cache. A deferred
closure source must later account for every original node in that same row. -/
structure Pending (compiled : SourceCoreUnifiedCompilation.Compiled)
    (rootPositions closurePositions : List Nat) where
  rootsSelected : ∀ position ∈ rootPositions,
    ∃ named, compiled.indexed.base.functions[position]? = some named
  closuresSelected : ∀ position ∈ closurePositions,
    ∃ named, compiled.indexed.base.functions[position]? = some named
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ pair ∈ compiled.indexed.base.functions.zipIdx,
    Nonempty (Row compiled rootPositions closurePositions pair.2 pair.1 table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (rootPositions closurePositions : List Nat) (position : Nat)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) :
    Option (Row compiled rootPositions closurePositions position named directRows allowCoerced) := do
  let root ← if member : position ∈ rootPositions then pure (.chosen member) else do
    let checked ← CallableIndexedOwnedPreparedProgramAdmission.certifyRoot compiled named directRows fuel
    pure (.checked checked)
  let closures ← if member : position ∈ closurePositions then pure (.chosen member) else do
    let ⟨checked⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource
      compiled named directRows allowCoerced fuel
    pure (.checked checked)
  pure ⟨root, closures⟩

/-- Deferral is authenticated by actual cache index before row checks. Direct
inventory, methods, profile and diagnostics retain their original checks. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (rootPositions closurePositions : List Nat) (fuel : Nat) :
    Option (Pending compiled rootPositions closurePositions) := do
  let ⟨rootsSelected⟩ ← allProof?
    (fun position => ∃ named, compiled.indexed.base.functions[position]? = some named)
    (fun position => match compiled.indexed.base.functions[position]? with
      | none => none
      | some named => some ⟨⟨named, rfl⟩⟩) rootPositions
  let ⟨closuresSelected⟩ ← allProof?
    (fun position => ∃ named, compiled.indexed.base.functions[position]? = some named)
    (fun position => match compiled.indexed.base.functions[position]? with
      | none => none
      | some named => some ⟨⟨named, rfl⟩⟩) closurePositions
  if profile : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
      let selection ← certifySelection compiled table.rows fuel
      let ⟨rows⟩ ← allProof?
        (fun pair : SourceCoreGeneralFunctions.Function × Nat =>
          Nonempty (Row compiled rootPositions closurePositions pair.2 pair.1 table.rows selection.allowCoerced))
        (fun pair => do
          let row ← certifyRow compiled rootPositions closurePositions pair.2 pair.1 table.rows selection.allowCoerced fuel
          pure ⟨⟨row⟩⟩) compiled.indexed.base.functions.zipIdx
      pure ⟨rootsSelected, closuresSelected, table, selection, rows, profile, diagnostics, present⟩
  else none

/-- Each supplied receipt belongs to its actual indexed row. Closure receipts
cover every original node and use the same direct inventory and coercion lane. -/
def Pending.complete_receipts {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows pending.selection.allowCoerced) : Certificate compiled := {
  table := pending.table
  selection := pending.selection
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    have closed : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
        compiled named pending.table.rows pending.selection.allowCoerced := by
      cases row.closures with
      | checked certificate => exact certificate
      | chosen selected => exact closures index selected named found
    cases row.root with
    | checked checked => exact ⟨⟨checked, closed⟩⟩
    | chosen selected =>
        obtain ⟨root⟩ := roots index selected named found
        exact ⟨⟨root, closed⟩⟩
  profile := pending.profile
  diagnostics := pending.diagnostics }

theorem Pending.complete_receipts_table {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows pending.selection.allowCoerced) :
    (pending.complete_receipts roots closures).table = pending.table := rfl

theorem Pending.complete_receipts_selection {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows pending.selection.allowCoerced) :
    (pending.complete_receipts roots closures).selection = pending.selection := rfl

end Solcore.SourceSemantics.CoreLowering.AcceptedProgramClosureCompletion
