import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogPublicRoots
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor

/-! Independent Source entry admission supplies the eligible actual public row.
The exact target equation and successful public start determine its first
matching root and cached Header. Source arguments, dictionaries and heap
representation remain separate from this static selection receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicHistoryFrontdoor
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicRootMeaning (RootSelection)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Admission is required only for the actual first matching cache row. -/
theorem Catalog.selected_at_entry (catalog : Catalog compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {root : Root compiled}
    {publicEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : publicEntry ∈ compiled.indexed.entries)
    (shape : root.FactoryShape compiled publicEntry)
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (found : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = publicEntry.key)) = some (named, index))
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (matched : CallableNamedMetadata.Matches named.specialized entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers catalog.rows) root header ∧
      CallableNamedMetadata.Matches header.named.specialized entry.instantiation := by
  have selected : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, retained, slot, same⟩ := catalog.header_at selected
    (CallableIndexedOwnedPreparedOrdinaryCatalog.eligible_of_entry wellFormed selected matched valid
      ordinaryReturn ordinaryParameters)
  exact ⟨header, RecursiveNamedPublicRootMeaning.selection_at retained member shape found slot,
    by simpa only [same] using matched⟩

/-- The actual target equation identifies the Source entry's complete cached
row. No caller-supplied Header or whole-root coverage is needed. -/
theorem Catalog.selected_entry (catalog : Catalog compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {root : Root compiled} (issued : root.Issued compiled)
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok root.key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers catalog.rows) root header ∧
      CallableNamedMetadata.Matches header.named.specialized entry.instantiation := by
  obtain ⟨publicEntry, member, shape⟩ := issued
  have factory := shape
  obtain ⟨named, index, found, key, rootKey, _rest⟩ := factory
  have selected : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have matched := CallableNamedMetadata.matches_of_exact
    (show SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok named.signature.key by simpa only [rootKey, key] using target)
    (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled selected)
  exact catalog.selected_at_entry wellFormed member shape found matched valid ordinaryReturn ordinaryParameters

/-- Recover one successful public start using independent Source entry
admission and its real compiled target. The returned receipt retains the exact
current native state and the Source match for its actual selected Header. -/
theorem Catalog.recover_start_entry (catalog : Catalog compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false)
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    ∃ request : Started (headers catalog.rows) prepared publicCheckpoint session key publicArguments fuel world store,
      CallableNamedMetadata.Matches request.header.named.specialized entry.instantiation := by
  apply RecursiveNamedPublicPhysicalFrontdoor.recover_start_at_with prepared catalog.inputs catalog.rows
    atRecipe native atSession (fun _ header =>
      CallableNamedMetadata.Matches header.named.specialized entry.instantiation) _ accepted
  intro root selected
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  change recipe.roots.find? (fun candidate => decide (candidate.key = key)) = some root at selected
  have issued := Recipe.prepare_roots prepared (List.mem_of_find?_eq_some selected)
  have keyEq : root.key = key := by simpa only [decide_eq_true_eq] using (List.find?_some selected)
  exact catalog.selected_entry wellFormed issued (by simpa only [keyEq] using target)
    valid ordinaryReturn ordinaryParameters

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicHistoryFrontdoor
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

/-- Accepted compilation and independent Source entry admission produce the
ordinary catalog and recover this actual public start in one endpoint. -/
theorem recover_start_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false)
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    ∃ catalog : Catalog compiled,
      ∃ request : Started (headers catalog.rows) prepared publicCheckpoint session key publicArguments fuel world store,
      CallableNamedMetadata.Matches request.header.named.specialized entry.instantiation := by
  obtain ⟨catalog⟩ := of_compiled compiled wellFormed
  obtain ⟨request, matched⟩ := catalog.recover_start_entry wellFormed prepared atRecipe native atSession
    target valid ordinaryReturn ordinaryParameters accepted
  exact ⟨catalog, request, matched⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
