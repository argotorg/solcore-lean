import Solcore.Test.SourceCoreRecursiveIndexMakeSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
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

theorem selected_make_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header] root header)
    (key : root.key = observed.makeRow.row.key) : header = makeHeader.header := by
  have headerKey := (selected_key selected).trans key
  have member : header ∈ [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · exact same
  · rw [same, echoHeader.key] at headerKey
    exact False.elim (observed.makeRow.keys_ne observed.echoRow observed.makeEcho headerKey.symm)
  · rw [same, chooseHeader.key] at headerKey
    exact False.elim (observed.makeRow.keys_ne observed.chooseRow observed.makeChoose headerKey.symm)
  · rw [same, selectHeader.key] at headerKey
    exact False.elim (observed.makeRow.keys_ne observed.selectRow observed.makeSelect headerKey.symm)

theorem selected_select_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header] root header)
    (key : root.key = observed.selectRow.row.key) : header = selectHeader.header := by
  have headerKey := (selected_key selected).trans key
  have member : header ∈ [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · rw [same, makeHeader.key] at headerKey
    exact False.elim (observed.makeRow.keys_ne observed.selectRow observed.makeSelect headerKey)
  · rw [same, echoHeader.key] at headerKey
    exact False.elim (observed.echoRow.keys_ne observed.selectRow observed.echoSelect headerKey)
  · rw [same, chooseHeader.key] at headerKey
    exact False.elim (observed.chooseRow.keys_ne observed.selectRow observed.chooseSelect headerKey)
  · exact same

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

theorem selected_make_at {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.makeRow.row.key arguments fuel world store) : request.header = makeHeader.header := by
  subst headers
  exact selected_make_root makeHeader echoHeader chooseHeader selectHeader request.selected (started_key request)

theorem selected_select_at {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.selectRow.row.key arguments fuel world store) : request.header = selectHeader.header := by
  subst headers
  exact selected_select_root makeHeader echoHeader chooseHeader selectHeader request.selected (started_key request)

private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply,
    TypeSystem.ParameterSubstitution.lookup?]

theorem ObservedRow.source_types {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    (actual : ActualHeader fixture observed.row) :
    observed.row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = signature.parameterTypes ∧
      observed.row.function.inferredBodyType = TypeSystem.Ty.productMany signature.returnTypes := by
  obtain ⟨request, original, generic, originalMember, genericMember, _, accepted⟩ := actual.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have owner := congrArg (fun source => source.owner) body
  change observed.row.function.typedBody.owner = generic.typedBody.owner at owner
  have originalEq : original = signature :=
    eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids originalMember signatureMember
      (identities.1.trans (identities.2.1.symm.trans (owner.symm.trans observed.sourceOwner)))
  subst original
  have valid := fixture.source_wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases valid with
  | @intro typedSignature facts typedMember typedOwner bodyValid =>
    have same : typedSignature = signature :=
      eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids typedMember signatureMember
        (typedOwner.symm.trans identities.1.symm)
    subst typedSignature
    cases bodyValid with
    | intro _ _ _ _ _ result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      have fields := (CallableCoercionBodyProvenance.specialization_fields accepted).1
      rw [fields, observed.parameters]
      simp only [SourceSpecialization.applyCheckedFunction, SourceSpecialization.applyTypedSource,
        List.map_map, Function.comp_def, SourceSpecialization.applyBinder,
        SourceSpecialization.applyScheme, parameter_nil]
      exact ⟨inputs, result⟩

theorem ActualHeader.make_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
  rw [observed.makeShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.make_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.function.resultType = closureType := by
  have result := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.makeShape.returns]
  rfl

theorem ActualHeader.echo_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.echoRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [containerType] := by
  have raw := (observed.echoRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.echoShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.echo_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.echoRow.row) : actual.header.types = [containerType] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.echo_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.echo_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.echoRow.row) : actual.header.function.resultType = containerType := by
  have result := (observed.echoRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.echoShape.returns]
  rfl

theorem ActualHeader.choose_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.chooseRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.chooseRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).1
  rw [observed.chooseShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.choose_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.chooseRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.choose_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.choose_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.chooseRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.chooseRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.chooseShape.returns]
  rfl

theorem ActualHeader.select_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.selectRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [containerType, .word] := by
  have raw := (observed.selectRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.tail _ (.head _)))) actual).1
  rw [observed.selectShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.select_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.selectRow.row) : actual.header.types = [containerType, .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.select_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.select_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.selectRow.row) : actual.header.function.resultType = closureType := by
  have result := (observed.selectRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.tail _ (.head _)))) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.selectShape.returns]
  rfl

end Tests.SourceCoreRecursiveIndex
