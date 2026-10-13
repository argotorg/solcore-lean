import Solcore.Test.SourceCoreMethodScopedInventory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
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

theorem selected_word_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] root header)
    (key : root.key = observed.wordRow.row.key) : header = wordHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.boolRow.index := by
      intro equal
      have impossible : 0 = 1 := (List.getElem_inj
        (i := 0) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.boolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 0 = 2 := (List.getElem_inj
        (i := 0) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 0 = 3 := (List.getElem_inj
        (i := 0) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useWordHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.useWordRow.index := by
      intro equal
      have impossible : 0 = 4 := (List.getElem_inj
        (i := 0) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.useWordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useBoolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.useBoolRow.index := by
      intro equal
      have impossible : 0 = 5 := (List.getElem_inj
        (i := 0) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.useBoolRow.toObservedRow distinct) headerKey.symm)
theorem selected_bool_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] root header)
    (key : root.key = observed.boolRow.row.key) : header = boolHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.wordRow.index := by
      intro equal
      have impossible : 1 = 0 := (List.getElem_inj
        (i := 1) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.wordRow.toObservedRow distinct) headerKey.symm)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 1 = 2 := (List.getElem_inj
        (i := 1) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 1 = 3 := (List.getElem_inj
        (i := 1) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useWordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.useWordRow.index := by
      intro equal
      have impossible : 1 = 4 := (List.getElem_inj
        (i := 1) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.useWordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useBoolHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.useBoolRow.index := by
      intro equal
      have impossible : 1 = 5 := (List.getElem_inj
        (i := 1) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.useBoolRow.toObservedRow distinct) headerKey.symm)
theorem selected_useWord_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] root header)
    (key : root.key = observed.useWordRow.row.key) : header = useWordHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.wordRow.index := by
      intro equal
      have impossible : 4 = 0 := (List.getElem_inj
        (i := 4) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.wordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.boolRow.index := by
      intro equal
      have impossible : 4 = 1 := (List.getElem_inj
        (i := 4) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.boolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 4 = 2 := (List.getElem_inj
        (i := 4) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 4 = 3 := (List.getElem_inj
        (i := 4) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, useBoolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.useBoolRow.index := by
      intro equal
      have impossible : 4 = 5 := (List.getElem_inj
        (i := 4) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.useBoolRow.toObservedRow distinct) headerKey.symm)
theorem selected_useBool_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] root header)
    (key : root.key = observed.useBoolRow.row.key) : header = useBoolHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.wordRow.index := by
      intro equal
      have impossible : 5 = 0 := (List.getElem_inj
        (i := 5) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.wordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.boolRow.index := by
      intro equal
      have impossible : 5 = 1 := (List.getElem_inj
        (i := 5) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.boolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 5 = 2 := (List.getElem_inj
        (i := 5) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 5 = 3 := (List.getElem_inj
        (i := 5) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useWordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.useWordRow.index := by
      intro equal
      have impossible : 5 = 4 := (List.getElem_inj
        (i := 5) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.useWordRow.toObservedRow distinct) headerKey.symm)
  · exact same
section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}

theorem selected_word_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.wordRow.row.key arguments fuel world store) : request.header = wordHeader.header := by
  subst headers
  exact selected_word_root wordHeader boolHeader makeWordHeader makeBoolHeader useWordHeader useBoolHeader request.selected (started_key request)

theorem selected_bool_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.boolRow.row.key arguments fuel world store) : request.header = boolHeader.header := by
  subst headers
  exact selected_bool_root wordHeader boolHeader makeWordHeader makeBoolHeader useWordHeader useBoolHeader request.selected (started_key request)

theorem selected_useWord_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.useWordRow.row.key arguments fuel world store) : request.header = useWordHeader.header := by
  subst headers
  exact selected_useWord_root wordHeader boolHeader makeWordHeader makeBoolHeader useWordHeader useBoolHeader request.selected (started_key request)

theorem selected_useBool_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.useBoolRow.row.key arguments fuel world store) : request.header = useBoolHeader.header := by
  subst headers
  exact selected_useBool_root wordHeader boolHeader makeWordHeader makeBoolHeader useWordHeader useBoolHeader request.selected (started_key request)
end StartedSelection

theorem ActualHeader.word_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word, .word, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.wordShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.wordShape.firstScheme, observed.wordShape.secondScheme,
    observed.wordShape.flagScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.word_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.types = [.word, .word, .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.word_input_types

theorem ActualHeader.word_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.function.resultType = closureType .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.wordResultType

theorem ActualHeader.word_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.output = Core.CallableContract.functionType .unit .word := by
  have projected := actual.aligned.projection
  rw [actual.word_result_type] at projected
  simpa [closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile] using (Except.ok.inj projected).symm

theorem ActualHeader.bool_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool, .bool, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.boolShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.boolShape.firstScheme, observed.boolShape.secondScheme,
    observed.boolShape.flagScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.bool_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.types = [.bool, .bool, .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.bool_input_types

theorem ActualHeader.bool_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.function.resultType = closureType .bool := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.boolResultType

theorem ActualHeader.bool_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.output = Core.CallableContract.functionType .unit .bool := by
  have projected := actual.aligned.projection
  rw [actual.bool_result_type] at projected
  simpa [closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile] using (Except.ok.inj projected).symm

theorem ActualHeader.useWord_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [closureType .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.useWordShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.useWordInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.useWord_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) : actual.header.types = [closureType .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.useWord_input_types

theorem ActualHeader.useWord_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.useWordResultType

theorem ActualHeader.useWord_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.useWord_result_type] at projected
  exact (Except.ok.inj projected).symm

theorem ActualHeader.useBool_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [closureType .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.useBoolShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.useBoolInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.useBool_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) : actual.header.types = [closureType .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.useBool_input_types

theorem ActualHeader.useBool_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) : actual.header.function.resultType = .bool := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.useBoolResultType

theorem ActualHeader.useBool_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) : actual.header.output = .bool := by
  have projected := actual.aligned.projection
  rw [actual.useBool_result_type] at projected
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
      [inventory.wordHeader.header, inventory.boolHeader.header, inventory.makeWordHeader.header, inventory.makeBoolHeader.header, inventory.useWordHeader.header, inventory.useBoolHeader.header] := by
  simp only [OrdinaryInventory.rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers,
    inventory.wordAligned, inventory.boolAligned, inventory.makeWordAligned, inventory.makeBoolAligned, inventory.useWordAligned, inventory.useBoolAligned]

theorem OrdinaryInventory.indices {fixture observed} (given : OrdinaryInventory fixture observed) :
    [given.wordInput, given.boolInput, given.makeWordInput, given.makeBoolInput, given.useWordInput, given.useBoolInput].map (fun input => input.prepared.index) =
      [observed.wordRow.index, observed.boolRow.index, observed.makeWordRow.index, observed.makeBoolRow.index, observed.useWordRow.index, observed.useBoolRow.index] := by
  have word : given.wordInput.prepared.index = observed.wordRow.index := by
    have same : given.wordHeader.header.slot = given.wordInput.prepared.index := by
      rw [given.wordAligned]; exact given.wordPacket.aligned.slot
    exact same.symm.trans given.wordSlot
  have bool : given.boolInput.prepared.index = observed.boolRow.index := by
    have same : given.boolHeader.header.slot = given.boolInput.prepared.index := by
      rw [given.boolAligned]; exact given.boolPacket.aligned.slot
    exact same.symm.trans given.boolSlot
  have makeWord : given.makeWordInput.prepared.index = observed.makeWordRow.index := by
    have same : given.makeWordHeader.header.slot = given.makeWordInput.prepared.index := by
      rw [given.makeWordAligned]; exact given.makeWordPacket.aligned.slot
    exact same.symm.trans given.makeWordSlot
  have makeBool : given.makeBoolInput.prepared.index = observed.makeBoolRow.index := by
    have same : given.makeBoolHeader.header.slot = given.makeBoolInput.prepared.index := by
      rw [given.makeBoolAligned]; exact given.makeBoolPacket.aligned.slot
    exact same.symm.trans given.makeBoolSlot
  have useWord : given.useWordInput.prepared.index = observed.useWordRow.index := by
    have same : given.useWordHeader.header.slot = given.useWordInput.prepared.index := by
      rw [given.useWordAligned]; exact given.useWordPacket.aligned.slot
    exact same.symm.trans given.useWordSlot
  have useBool : given.useBoolInput.prepared.index = observed.useBoolRow.index := by
    have same : given.useBoolHeader.header.slot = given.useBoolInput.prepared.index := by
      rw [given.useBoolAligned]; exact given.useBoolPacket.aligned.slot
    exact same.symm.trans given.useBoolSlot
  simp only [List.map_cons, List.map_nil, word, bool, makeWord, makeBool, useWord, useBool]

theorem OrdinaryInventory.distinct {fixture observed} (given : OrdinaryInventory fixture observed) :
    ([given.wordInput, given.boolInput, given.makeWordInput, given.makeBoolInput, given.useWordInput, given.useBoolInput].map (fun input => input.prepared.index)).Nodup := by
  rw [given.indices]
  exact observed.ordinarySlotsDistinct

end Tests.SourceCoreMethodScoped
