import Solcore.SourceSemantics.CoreLowering.AcceptedProgramClosureCompletion

/-! Original method-owned rows are completed from actual compiler receipts.
The ordinary roots and closure sources retain their indexed checks, and the
method catalog keeps its independent formation and evidence-origin checks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProgramMethodCompletion
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

open AcceptedProgramClosureCompletion (Row)

/-- Both sets of positions refer to the complete actual cache. A deferred
closure source must later account for every original node in that same row. -/
structure Pending (compiled : SourceCoreUnifiedCompilation.Compiled)
    (rootPositions closurePositions : List Nat) where
  rootsSelected : ∀ position ∈ rootPositions,
    ∃ named, compiled.indexed.base.functions[position]? = some named
  closuresSelected : ∀ position ∈ closurePositions,
    ∃ named, compiled.indexed.base.functions[position]? = some named
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled
  rows : ∀ pair ∈ compiled.indexed.base.functions.zipIdx,
    Nonempty (Row compiled rootPositions closurePositions pair.2 pair.1 table.rows false)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (rootPositions closurePositions : List Nat) (position : Nat)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) :
    Option (Row compiled rootPositions closurePositions position named directRows allowCoerced) := do
  let root ← if member : position ∈ rootPositions then pure (.chosen member) else do
    if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
        decide (named.specialized.declaration ≠ signature.id)) = true then
      pure (.checked (.excluded (fun signature member =>
        of_decide_eq_true (List.all_eq_true.mp absent signature member))))
    else do
      let checked ← CallableIndexedOwnedPreparedProgramAdmission.certifyRoot compiled named directRows fuel
      pure (.checked checked)
  let closures ← if member : position ∈ closurePositions then pure (.chosen member) else do
    let ⟨checked⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource
      compiled named directRows allowCoerced fuel
    pure (.checked checked)
  pure ⟨root, closures⟩

/-- Deferral is authenticated by actual cache index before row checks. Direct
inventory, method catalog, profile and diagnostics retain their original checks. -/
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
      let ⟨catalog⟩ ← CallableIndexedOwnedPreparedOriginsMethodAdmission.certify compiled
      let ⟨rows⟩ ← allProof?
        (fun pair : SourceCoreGeneralFunctions.Function × Nat =>
          Nonempty (Row compiled rootPositions closurePositions pair.2 pair.1 table.rows false))
        (fun pair => do
          let row ← certifyRow compiled rootPositions closurePositions pair.2 pair.1 table.rows false fuel
          pure ⟨⟨row⟩⟩) compiled.indexed.base.functions.zipIdx
      pure ⟨rootsSelected, closuresSelected, table, catalog, rows, profile, diagnostics, present⟩
  else none

/-- Each supplied receipt belongs to its actual indexed row. Closure receipts
cover every original node and use the same direct inventory and original method-origin lane. Every method receipt retains its actual cache lookup. -/
def Pending.complete_receipts {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows false)
    (methods : ∀ (position : Nat) named, compiled.indexed.base.functions[position]? = some named →
      CallableIndexedOwnedPreparedScopedMethodAdmission.RowCase compiled named pending.table.rows) :
    Certificate compiled := {
  table := pending.table
  selection := .origins ⟨by
    intro named member
    obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
    exact methods position named found⟩ pending.catalog
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    have closed : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
        compiled named pending.table.rows false := by
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
          compiled named pending.table.rows false)
    (methods : ∀ (position : Nat) named, compiled.indexed.base.functions[position]? = some named →
      CallableIndexedOwnedPreparedScopedMethodAdmission.RowCase compiled named pending.table.rows) :
    (pending.complete_receipts roots closures methods).table = pending.table := rfl

theorem Pending.complete_receipts_operatorCatalog {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows false)
    (methods : ∀ (position : Nat) named, compiled.indexed.base.functions[position]? = some named →
      CallableIndexedOwnedPreparedScopedMethodAdmission.RowCase compiled named pending.table.rows) :
    (pending.complete_receipts roots closures methods).selection.operatorCatalog = .origins pending.catalog := rfl

end Solcore.SourceSemantics.CoreLowering.AcceptedProgramMethodCompletion
