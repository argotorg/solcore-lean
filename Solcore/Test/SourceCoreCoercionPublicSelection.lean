import Solcore.Test.SourceCoreCoercionPublicInventory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogPublicRoots
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedRow.keys_ne {fixture : CompiledFixture} {leftSignature rightSignature : ProgramFunctionSignature}
    (left : ObservedRow fixture leftSignature) (right : ObservedRow fixture rightSignature)
    (distinct : left.index ≠ right.index) : left.row.key ≠ right.row.key := by
  intro same
  have globals : left.global.key = right.global.key := left.globalKey.trans (same.trans right.globalKey.symm)
  exact distinct (left.slot.unique right.slot globals).2

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {root : SourceCoreIndexedSession.Root compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RootSelection (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers root header) :
    header.named.signature.key = root.key := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, namedKey, rootKey, _⟩ := shape
  obtain ⟨namedEq, _⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  rw [namedEq]
  exact namedKey.trans rootKey.symm

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

/-- An actual issued root needs only its selected Header in the local inventory. -/
theorem OrdinaryInventory.selected_row_issued {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (given : OrdinaryInventory fixture observed) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) (header : ActualHeader fixture row.row)
    (member : header.header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers given.rows)
    (slot : header.header.slot = row.index)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    (issued : root.Issued fixture.recipe.compiled) (key : root.key = row.row.key) :
    RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers given.rows) root header.header := by
  obtain ⟨entry, entryMember, shape⟩ := issued
  obtain ⟨named, index, first, namedKey, rootKey, rest⟩ := shape
  have cached := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some first)
  have atSlot := row.global_slot (CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled cached)
    (namedKey.trans (rootKey.symm.trans key))
  exact RecursiveNamedPublicRootMeaning.selection_at member entryMember
    ⟨named, index, first, namedKey, rootKey, rest⟩ first (slot.trans atSlot.2.symm)

/-- Only the actual first matching public root is selected here. Other public
entries and physical method slots do not require a coverage premise. -/
theorem OrdinaryInventory.selected_row {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (given : OrdinaryInventory fixture observed) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) (header : ActualHeader fixture row.row)
    (member : header.header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers given.rows)
    (slot : header.header.slot = row.index)
    (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
    (found : fixture.recipe.roots.find? (fun candidate => decide (candidate.key = row.row.key)) =
      some ((SourceCoreIndexedSession.Recipe.prepare_compiled fixture.recipePrepared).symm ▸ root)) :
    RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers given.rows) root header.header := by
  have key : root.key = row.row.key := by
    have key := of_decide_eq_true (List.find?_some
      (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled => decide (candidate.key = row.row.key)) found)
    exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled fixture.recipePrepared).symm root).symm.trans key
  have issued : root.Issued fixture.recipe.compiled := by
    have actual := SourceCoreIndexedSession.Recipe.prepare_roots fixture.recipePrepared
      (List.mem_of_find?_eq_some found)
    cases SourceCoreIndexedSession.Recipe.prepare_compiled fixture.recipePrepared
    exact actual
  exact given.selected_row_issued row header member slot issued key

private theorem started_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {recipe : SourceCoreIndexedSession.Recipe}
    {prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe}
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    (request : Started headers prepared publicCheckpoint session key arguments fuel world store) :
    request.root.key = key := by
  have keyEq := of_decide_eq_true (List.find?_some
    (p := fun root : SourceCoreIndexedSession.Root recipe.compiled => decide (root.key = key))
    request.started.selected)
  exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm request.root).symm.trans keyEq

theorem selected_make_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (useHeader : ActualHeader fixture observed.useRow.row)
    (keepHeader : ActualHeader fixture observed.keepRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, useHeader.header, keepHeader.header] root header)
    (key : root.key = observed.makeRow.row.key) : header = makeHeader.header := by
  have member : header ∈ [makeHeader.header, useHeader.header, keepHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, useHeader.key] at headerKey
    have distinct : observed.makeRow.index ≠ observed.useRow.index := by
      intro equal
      have impossible : 0 = 1 := (List.getElem_inj
        (i := 0) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.makeRow.toObservedRow.keys_ne observed.useRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, keepHeader.key] at headerKey
    have distinct : observed.makeRow.index ≠ observed.keepRow.index := by
      intro equal
      have impossible : 0 = 2 := (List.getElem_inj
        (i := 0) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.makeRow.toObservedRow.keys_ne observed.keepRow distinct) headerKey.symm)

theorem selected_use_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (useHeader : ActualHeader fixture observed.useRow.row)
    (keepHeader : ActualHeader fixture observed.keepRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, useHeader.header, keepHeader.header] root header)
    (key : root.key = observed.useRow.row.key) : header = useHeader.header := by
  have member : header ∈ [makeHeader.header, useHeader.header, keepHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, makeHeader.key] at headerKey
    have distinct : observed.useRow.index ≠ observed.makeRow.index := by
      intro equal
      have impossible : 1 = 0 := (List.getElem_inj
        (i := 1) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useRow.toObservedRow.keys_ne observed.makeRow.toObservedRow distinct) headerKey.symm)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, keepHeader.key] at headerKey
    have distinct : observed.useRow.index ≠ observed.keepRow.index := by
      intro equal
      have impossible : 1 = 2 := (List.getElem_inj
        (i := 1) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useRow.toObservedRow.keys_ne observed.keepRow distinct) headerKey.symm)

section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (useHeader : ActualHeader fixture observed.useRow.row)
    (keepHeader : ActualHeader fixture observed.keepRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}

theorem selected_make_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, useHeader.header, keepHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.makeRow.row.key arguments fuel world store) : request.header = makeHeader.header := by
  subst headers
  exact selected_make_root makeHeader useHeader keepHeader request.selected (started_key request)

theorem selected_use_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, useHeader.header, keepHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.useRow.row.key arguments fuel world store) : request.header = useHeader.header := by
  subst headers
  exact selected_use_root makeHeader useHeader keepHeader request.selected (started_key request)

end StartedSelection

theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.makeShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.makeInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.make_input_types

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.function.resultType = closureType .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.makeResultType

theorem ActualHeader.make_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.output = Core.CallableContract.functionType .unit .word := by
  have projected := actual.aligned.projection
  rw [actual.make_result_type] at projected
  simpa [closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile] using (Except.ok.inj projected).symm

theorem ActualHeader.use_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [closureType .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.useShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.useInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.use_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useRow.row) : actual.header.types = [closureType .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.use_input_types

theorem ActualHeader.use_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useRow.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.useResultType

theorem ActualHeader.use_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.use_result_type] at projected
  exact (Except.ok.inj projected).symm

def ObservedStages.descriptor_at {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (stages : ObservedStages fixture observed)
    (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.key]
  exact stages.descriptor

theorem OrdinaryInventory.header_list {fixture observed} (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedFiniteNamedInventories.headers inventory.rows =
      [inventory.makeHeader.header, inventory.useHeader.header, inventory.keepHeader.header] := by
  simp only [OrdinaryInventory.rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers,
    inventory.makeAligned, inventory.useAligned, inventory.keepAligned]

theorem OrdinaryInventory.indices {fixture observed} (given : OrdinaryInventory fixture observed) :
    [given.makeInput, given.useInput, given.keepInput].map (fun input => input.prepared.index) =
      [observed.makeRow.index, observed.useRow.index, observed.keepRow.index] := by
  have make : given.makeInput.prepared.index = observed.makeRow.index := by
    have same : given.makeHeader.header.slot = given.makeInput.prepared.index := by
      rw [given.makeAligned]; exact given.makePacket.aligned.slot
    exact same.symm.trans given.makeSlot
  have use : given.useInput.prepared.index = observed.useRow.index := by
    have same : given.useHeader.header.slot = given.useInput.prepared.index := by
      rw [given.useAligned]; exact given.usePacket.aligned.slot
    exact same.symm.trans given.useSlot
  have keep : given.keepInput.prepared.index = observed.keepRow.index := by
    have same : given.keepHeader.header.slot = given.keepInput.prepared.index := by
      rw [given.keepAligned]; exact given.keepPacket.aligned.slot
    exact same.symm.trans given.keepSlot
  simp only [List.map_cons, List.map_nil, make, use, keep]

theorem OrdinaryInventory.distinct {fixture observed} (given : OrdinaryInventory fixture observed) :
    ([given.makeInput, given.useInput, given.keepInput].map (fun input => input.prepared.index)).Nodup := by
  rw [given.indices]
  exact observed.ordinarySlotsDistinct

end Tests.SourceCoreCoercionPublic
