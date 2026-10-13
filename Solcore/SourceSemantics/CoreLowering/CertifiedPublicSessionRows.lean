import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession

/-! A full eligible cached row and its singleton physical slot identify the
actual first matching public root, including when unrelated keys repeat. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog Eligible)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

structure EligibleRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (key : SourceCoreIndexedSession.Key) where
  named : SourceCoreGeneralFunctions.Function
  index : Nat
  global : SourceCoreCalls.Signature
  cached : compiled.indexed.base.functions[index]? = some named
  slot : CallableNamedMetadata.Slot compiled.indexed.base.globals index global
  globalKey : global.key = key
  eligible : Eligible compiled named.specialized

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {key : SourceCoreIndexedSession.Key}

/-- The singleton global slot fixes the entire selected cache row and index. -/
theorem EligibleRow.first_eq (row : EligibleRow compiled key)
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (found : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = key)) = some (named, index)) :
    named = row.named ∧ index = row.index := by
  have cached := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have global := CallableIndexedPreparedInventories.cached_global_at compiled cached
  have selectedKey : named.signature.key = key := of_decide_eq_true (List.find?_some
    (p := fun item : SourceCoreGeneralFunctions.Function × Nat => decide (item.1.signature.key = key)) found)
  have member : (named.signature, index) ∈ compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = row.global.key)) := by
    apply List.mem_filter.mpr
    exact ⟨List.mk_mem_zipIdx_iff_getElem?.mpr global,
      by simp only [selectedKey, row.globalKey, decide_true]⟩
  rw [row.slot] at member
  have same : (named.signature, index) = (row.global, row.index) := by simpa only [List.mem_singleton] using member
  have indexEq := (Prod.mk.inj same).2
  have namedEq : named = row.named := Option.some.inj ((indexEq ▸ cached).symm.trans row.cached)
  exact ⟨namedEq, indexEq⟩

theorem EligibleRow.selected (row : EligibleRow compiled key) (catalog : Catalog compiled)
    {root : SourceCoreIndexedSession.Root compiled} (issued : root.Issued compiled)
    (rootKey : root.key = key) :
    ∃ header, RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers catalog.rows) root header ∧
      header.named = row.named := by
  obtain ⟨entry, member, shape⟩ := issued
  have factory := shape
  obtain ⟨named, index, found, _namedKey, entryKey, _rest⟩ := factory
  have actual := found
  rw [← entryKey, rootKey] at actual
  obtain ⟨namedEq, indexEq⟩ := row.first_eq actual
  obtain ⟨header, retained, slot, same⟩ := catalog.header_at row.cached row.eligible
  refine ⟨header, RecursiveNamedPublicRootMeaning.selection_at retained member shape found ?_, same⟩
  exact slot.trans indexEq.symm

variable {recipe : SourceCoreIndexedSession.Recipe}

theorem Issued.recover_start_row (issued : Issued recipe)
    {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : issued.State anchor session entries)
    {publicArguments : List SourceCorePublicValues.Value} {options : SourceCoreExecution.RunOptions}
    (call : StartedCall session key publicArguments options) (row : EligibleRow recipe.compiled key) :
    ∃ request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store,
      request.header.named = row.named := by
  apply RecursiveNamedPublicPhysicalFrontdoor.recover_start_at_with issued.prepared
    issued.catalog.inputs issued.catalog.rows state.atRecipe state.history.semantic.current.1 state.atSession
    (fun _ header => header.named = row.named) _ call.started
  intro root selected
  have rootKey : root.key = key := of_decide_eq_true (List.find?_some
    (p := fun candidate : SourceCoreIndexedSession.Root recipe.compiled => decide (candidate.key = key)) selected)
  exact row.selected issued.catalog
    (SourceCoreIndexedSession.Recipe.prepare_roots issued.prepared (List.mem_of_find?_eq_some selected)) rootKey

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
