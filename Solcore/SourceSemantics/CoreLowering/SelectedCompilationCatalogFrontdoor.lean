import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogPublicAdmission

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalogFrontdoor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicHistoryFrontdoor
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicRootMeaning (RootSelection)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

theorem eligible_of_admissible {compiled : SourceCoreUnifiedCompilation.Compiled}
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {context : Context} {instantiation : DeclarationInstantiation}
    (matched : CallableNamedMetadata.Matches named.specialized instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ instantiation.parameterComptime, flag = false) :
    Eligible compiled named.specialized := by
  obtain ⟨signature, member, declaration⟩ := admissible.signature_id
  have origin := SelectedCompilationCatalog.ordinary_origin compiled formed
    (RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl)
    (by simpa only [signatures] using member) (matched.declaration.trans declaration.symm)
  apply Eligible.of_admissible origin matched admissible signatures
    (matched.returnComptime.trans ordinaryReturn)
  intro binder member
  apply ordinaryParameters binder.comptime
  rw [← matched.parameterComptime]
  exact List.mem_map.mpr ⟨binder, member, rfl⟩

theorem eligible_of_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (matched : CallableNamedMetadata.Matches named.specialized entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    Eligible compiled named.specialized := by
  cases valid.instantiates with
  | intro _ _ _ _ admitted _ _ _ =>
    exact eligible_of_admissible formed selected matched admitted.toAdmissible rfl
      ordinaryReturn ordinaryParameters

/-- A reached direct target obtains its Header from the actual final cache and
the original Source declaration admission. Other cached rows need no admission. -/
theorem covers_direct {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled)
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {context : Context} {instantiation : DeclarationInstantiation}
    {index : Nat} {signature : SourceCoreGeneralFunctions.Signature}
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ instantiation.parameterComptime, flag = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
      .ok signature.key)
    (global : compiled.indexed.base.globals[index]? = some signature) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers catalog.rows,
      header.slot = index ∧ header.named.signature = signature := by
  rw [CallableIndexedPreparedInventories.cached_globals, List.getElem?_map] at global
  cases selected : compiled.indexed.base.functions[index]? with
  | none => simp [selected] at global
  | some named =>
    have same : named.signature = signature := by simpa [selected] using global
    have matched := CallableNamedMetadata.matches_of_exact
      (show SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
        .ok named.signature.key by simpa only [same] using target)
      (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled selected)
    obtain ⟨header, member, slot, namedAt⟩ := catalog.header_at selected
      (eligible_of_admissible formed selected matched admissible signatures
        ordinaryReturn ordinaryParameters)
    exact ⟨header, member, slot, by rw [namedAt]; exact same⟩

/-- Admission is required only for the actual first matching cache row. -/
theorem selected_at_entry (catalog : Catalog compiled)
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
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
    (eligible_of_entry formed selected matched valid
      ordinaryReturn ordinaryParameters)
  exact ⟨header, RecursiveNamedPublicRootMeaning.selection_at retained member shape found slot,
    by simpa only [same] using matched⟩

/-- The actual target equation identifies the Source entry's complete cached
row. No caller-supplied Header or whole-root coverage is needed. -/
theorem selected_entry (catalog : Catalog compiled)
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
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
  exact selected_at_entry catalog formed member shape found matched valid ordinaryReturn ordinaryParameters

/-- Recover one successful public start using independent Source entry
admission and its real compiled target. The returned receipt retains the exact
current native state and the Source match for its actual selected Header. -/
theorem recover_start_entry (catalog : Catalog compiled)
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
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
  exact selected_entry catalog formed issued (by simpa only [keyEq] using target)
    valid ordinaryReturn ordinaryParameters


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalogFrontdoor
