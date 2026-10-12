import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.Test.SourceCoreOperatorCallsSupports
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor

/-! The original first-match receipts select the exact member of the two-row
inventory. Raw types come from checked Source signatures and the accepted
specialization, independently of execution or native type tags. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ObservedProgram.keys_distinct {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) : observed.identityRow.row.key ≠ observed.selectRow.row.key := by
  intro same
  have globals : observed.identityRow.global.key = observed.selectRow.global.key :=
    observed.identityRow.globalKey.trans (same.trans observed.selectRow.globalKey.symm)
  exact observed.distinctSlots (observed.identityRow.slot.unique observed.selectRow.slot globals).2

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

theorem selected_identity_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [identityHeader.header, selectHeader.header] root header)
    (key : root.key = observed.identityRow.row.key) : header = identityHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · exact same
  · have same := List.mem_singleton.mp rest
    have headerKey := (selected_key selected).trans key
    rw [same, selectHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey.symm)

theorem selected_select_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [identityHeader.header, selectHeader.header] root header)
    (key : root.key = observed.selectRow.row.key) : header = selectHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · have headerKey := (selected_key selected).trans key
    rw [same, identityHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey)
  · exact List.mem_singleton.mp rest

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

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

section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (identityHeader : ActualHeader fixture observed.identityRow.row)
  (selectHeader : ActualHeader fixture observed.selectRow.row)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {session : SourceCoreIndexedSession.Session nativeArtifact}
  {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
  {world : Core.StoreTyping} {store : Core.Store}

theorem selected_identity (request : Started [identityHeader.header, selectHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.identityRow.row.key arguments fuel world store) :
    request.header = identityHeader.header :=
  selected_identity_root identityHeader selectHeader request.selected (started_key request)

theorem selected_select (request : Started [identityHeader.header, selectHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.selectRow.row.key arguments fuel world store) :
    request.header = selectHeader.header :=
  selected_select_root identityHeader selectHeader request.selected (started_key request)

theorem selected_identity_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [identityHeader.header, selectHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.identityRow.row.key arguments fuel world store) : request.header = identityHeader.header := by
  subst headers
  exact selected_identity identityHeader selectHeader request

theorem selected_select_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [identityHeader.header, selectHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.selectRow.row.key arguments fuel world store) : request.header = selectHeader.header := by
  subst headers
  exact selected_select identityHeader selectHeader request
end StartedSelection

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows =
      [support.identityHeader.header, support.selectHeader.header] := by
  rw [support.rowsEq]
  simp only [CallableIndexedOwnedPreparedFiniteNamedInventories.headers, support.identityEq, support.selectEq]



end Tests.SourceCoreOperatorCalls
