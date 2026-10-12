import Solcore.Test.SourceCoreInitialLexicalFailureSupports
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor

/-! The original first-match receipts select the exact member of the two-row
inventory. Raw types come from checked Source signatures and the accepted
specialization, independently of execution or native type tags. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedProgram.keys_distinct {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) : observed.failedRow.row.key ≠ observed.identityRow.row.key := by
  intro same
  have globals : observed.failedRow.global.key = observed.identityRow.global.key :=
    observed.failedRow.globalKey.trans (same.trans observed.identityRow.globalKey.symm)
  exact observed.distinctSlots (observed.failedRow.slot.unique observed.identityRow.slot globals).2

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

theorem selected_failed_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (failedHeader : ActualHeader fixture observed.failedRow.row)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [failedHeader.header, identityHeader.header] root header)
    (key : root.key = observed.failedRow.row.key) : header = failedHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · exact same
  · have same := List.mem_singleton.mp rest
    have headerKey := (selected_key selected).trans key
    rw [same, identityHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey.symm)

theorem selected_identity_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (failedHeader : ActualHeader fixture observed.failedRow.row)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [failedHeader.header, identityHeader.header] root header)
    (key : root.key = observed.identityRow.row.key) : header = identityHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · have headerKey := (selected_key selected).trans key
    rw [same, failedHeader.key] at headerKey
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
  (failedHeader : ActualHeader fixture observed.failedRow.row)
  (identityHeader : ActualHeader fixture observed.identityRow.row)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {session : SourceCoreIndexedSession.Session nativeArtifact}
  {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
  {world : Core.StoreTyping} {store : Core.Store}

theorem selected_failed (request : Started [failedHeader.header, identityHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.failedRow.row.key arguments fuel world store) :
    request.header = failedHeader.header :=
  selected_failed_root failedHeader identityHeader request.selected (started_key request)

theorem selected_identity (request : Started [failedHeader.header, identityHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.identityRow.row.key arguments fuel world store) :
    request.header = identityHeader.header :=
  selected_identity_root failedHeader identityHeader request.selected (started_key request)

theorem selected_failed_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [failedHeader.header, identityHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.failedRow.row.key arguments fuel world store) : request.header = failedHeader.header := by
  subst headers
  exact selected_failed failedHeader identityHeader request

theorem selected_identity_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [failedHeader.header, identityHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.identityRow.row.key arguments fuel world store) : request.header = identityHeader.header := by
  subst headers
  exact selected_identity failedHeader identityHeader request
end StartedSelection

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : SourceCoreCallableIndexedPrograms.Completion fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows =
      [support.failedHeader.header, support.identityHeader.header] := by
  rw [support.rowsEq]
  simp only [CallableIndexedOwnedPreparedFiniteNamedInventories.headers, support.failedEq, support.identityEq]




theorem ActualHeader.failed_inputs {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [] := by
  have raw := (observed.failedRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
  rw [observed.failedShape.inputTypes] at raw
  rw [← actual.source, actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.failed_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.failed_result_type] at projected
  exact (Except.ok.inj projected).symm

theorem ActualHeader.identity_inputs {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.identityShape.inputTypes] at raw
  rw [← actual.source, actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.identity_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.identity_result_type] at projected
  exact (Except.ok.inj projected).symm

end Tests.SourceCoreInitialLexicalFailure
