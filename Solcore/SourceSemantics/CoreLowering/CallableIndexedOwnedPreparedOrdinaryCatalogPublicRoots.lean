import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning

/-! An eligible actual public root selects a Header from the filtered ordinary
catalog. The real factory and first-match equations retain the original root,
physical slot and complete cached row. Unrelated roots need no coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
open Core Frontend SourceInference
open RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts

/-- Exact first-match provenance selects a member of any ordinary Header
inventory. Its retained physical position identifies the complete cached row. -/
theorem selection_at
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program}
    {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
    {header : Header compiled.indexed.ancestry values ambient.definitions program}
    (member : header ∈ headers)
    {root : SourceCoreIndexedSession.Root compiled}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (entryMember : entry ∈ compiled.indexed.entries)
    (shape : root.FactoryShape compiled entry)
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (found : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) = some (named, index))
    (slot : header.slot = index) : RootSelection headers root header := by
  have row : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have selected : compiled.indexed.base.functions[index]? = some header.named := slot ▸ header.selected
  have same : header.named = named := Option.some.inj (selected.symm.trans row)
  refine ⟨member, entry, entryMember, shape, ?_⟩
  simpa only [same, slot] using found

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicRootMeaning (RootSelection)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- One actual eligible cache row is sufficient for Source root selection. -/
theorem Catalog.selected_at (catalog : Catalog compiled)
    {root : SourceCoreIndexedSession.Root compiled}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (shape : root.FactoryShape compiled entry)
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (found : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) = some (named, index))
    (eligible : Eligible compiled named.specialized) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram)
      (headers catalog.rows) root header := by
  have selected : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, retained, slot, _same⟩ := catalog.header_at selected eligible
  exact ⟨header, RecursiveNamedPublicRootMeaning.selection_at retained member shape found slot⟩

/-- Apply eligibility only to the first matching cache row of this actual
issued root. A caller may derive it from independent Source entry admission. -/
theorem Catalog.selected_of_issued (catalog : Catalog compiled)
    {root : SourceCoreIndexedSession.Root compiled}
    (issued : root.Issued compiled)
    (eligible : ∀ entry, entry ∈ compiled.indexed.entries → root.FactoryShape compiled entry →
      ∀ named index, compiled.indexed.base.functions.zipIdx.find?
        (fun item => decide (item.1.signature.key = entry.key)) = some (named, index) →
        Eligible compiled named.specialized) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram)
      (headers catalog.rows) root header := by
  obtain ⟨entry, member, shape⟩ := issued
  have factory := shape
  obtain ⟨named, index, found, _rest⟩ := factory
  exact catalog.selected_at member shape found (eligible entry member shape named index found)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
