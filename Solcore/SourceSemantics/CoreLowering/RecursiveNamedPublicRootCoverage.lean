import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning

/-! Public Source selection covers actual public entries only. Cached method
rows remain in the physical inventory and need no ordinary Source Header. The
original first-match equation still determines the selected complete row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts RecursiveNamedPublicRootMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}

def Coverage (headers : Inventory compiled.indexed.ancestry values ambient.definitions program) : Prop :=
  ∀ entry, entry ∈ compiled.indexed.entries → ∀ named slot,
    compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) = some (named, slot) →
    ∃ header, header ∈ headers ∧ header.slot = slot

theorem Coverage.of_complete (complete : Complete headers) : Coverage headers := by
  intro _entry _member named slot found
  have selected : compiled.indexed.base.functions[slot]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, member, slot, _signature⟩ := complete slot named.signature
    (CallableIndexedPreparedInventories.cached_global_at compiled selected)
  exact ⟨header, member, slot⟩

theorem selection_of_issued {root : SourceCoreIndexedSession.Root compiled}
    (issued : root.Issued compiled) (coverage : Coverage headers) :
    ∃ header, RootSelection headers root header := by
  obtain ⟨entry, entryMember, shape⟩ := issued
  obtain ⟨named, index, found, rest⟩ := shape
  have row : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, member, slot⟩ := coverage entry entryMember named index found
  have selected : compiled.indexed.base.functions[index]? = some header.named := slot ▸ header.selected
  have same : header.named = named := Option.some.inj (selected.symm.trans row)
  refine ⟨header, member, entry, entryMember, ⟨named, index, found, rest⟩, ?_⟩
  simpa only [slot, same] using found

theorem selection_of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {root : SourceCoreIndexedSession.Root recipe.compiled} (member : root ∈ recipe.roots)
    {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    (coverage : Coverage headers) : ∃ header, RootSelection headers root header :=
  selection_of_issued (SourceCoreIndexedSession.Recipe.prepare_roots accepted member) coverage

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
