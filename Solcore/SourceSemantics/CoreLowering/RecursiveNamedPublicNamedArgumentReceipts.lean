import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedFunctionInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds

/-! An actual named issuance reaches its independent Source function through
one retained finite inventory row and the same initialized owned pool. The
factory's physical slot identifies its whole installed closure, including all
captured values. Source typing comes from the retained declaration frame and
evidence; no function representation or input typing is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNamedArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt NamedCapture NamedInstalledCode)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionState (State)

/-- Each actual named declaration frame provides a compatible receiving type
context, including its residual variable mode and complete program catalog. -/
private theorem header_supports {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    Dynamic.TypeContextSupports (Context.ofSignatures compiled.sourceProgram.signatures)
      header.function.context := by
  have fields : header.function.context.signatures = compiled.sourceProgram.signatures ∧
      header.function.context.typeParameters = [] ∧
      header.function.context.residualTypeVariables = true := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq =>
        rw [contextEq]
        exact ⟨rfl, rfl, rfl⟩
  exact .ofClosed fields.1 rfl fields.2.1 rfl fields.2.2

/-- The actual Source frame provides declaration validity and full evidence
coverage. Its retained substitution order is preserved verbatim. -/
private theorem source_typed {compiled : SourceCoreUnifiedCompilation.Compiled}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD source)
    (caller : Header compiled (Program.ofChecked compiled.sourceProgram)) (heap : Dynamic.Heap) :
    Dynamic.ValueHasType caller.function.context heap (.global source)
      header.named.specialized.function.type := by
  have valid : SourceSemantics.DeclarationInstantiation.Valid
      (Context.ofSignatures compiled.sourceProgram.signatures) source.instantiation := by
    cases sourceAt.frame.instantiated with
    | intro _ _ _ _ valid _ _ _ => exact valid
  have covers : source.evidence.Covers
      ((Context.ofSignatures compiled.sourceProgram.signatures).withAssumptions source.instantiation.predicates) := by
    rw [← sourceAt.dictionary]
    have covered := sourceAt.frame.covers
    cases sourceAt.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq =>
        rw [contextEq] at covered
        exact covered
  have typed : Dynamic.ValueHasType (Context.ofSignatures compiled.sourceProgram.signatures)
      heap (.global source) source.instantiation.type := .global valid covers
  have actualType : source.instantiation.type = header.named.specialized.function.type := by
    rw [sourceAt.retained]
    rfl
  rw [actualType] at typed
  exact typed.transportContext (header_supports caller)

/-- The single Source inventory row fixes the actual cached factory index,
including when unrelated global signatures have identical native types. -/
private theorem selected_slot {compiled : SourceCoreUnifiedCompilation.Compiled}
    {input : Input compiled} (packet : Issued input)
    {signature : SourceCoreCalls.Signature} {index : Nat}
    (found : compiled.indexed.base.globals[index]? = some signature)
    (key : signature.key = packet.header.named.signature.key) :
    signature = packet.header.named.signature ∧ index = packet.header.slot := by
  have present : (signature, index) ∈ compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = packet.header.named.signature.key)) :=
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr found, by simpa using key⟩
  rw [packet.sourceAt.row.slot] at present
  exact Prod.mk.inj (List.mem_singleton.mp present)

/-- A real named issuance constructs the whole receiving function value from
the initialized owned capture. Its handle encoding survives further issuances
without depending on a top-level argument position. -/
theorem Session.named_value_represents_after
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : State (headers rows) (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (callerHeader : Header compiled (Program.ofChecked compiled.sourceProgram))
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact} {issuanceFuel : Nat}
    (issuance : before.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    (atRecipe : ArtifactRecipe artifact recipe)
    {handle : Handle} (handleValue : issued.value = .function handle)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ callable, session.EncodesAt issuanceFuel packet.header.named.specialized.function.type
      (.function handle) callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        [] ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
        packet.header.named.specialized.function.type
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available))) callable
        (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) ∧
      Dynamic.ValueHasType callerHeader.function.context ⟨[]⟩
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available))) packet.header.named.specialized.function.type := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨expected, callable, _same, _sourceType, _budget, encoded, factory⟩ := issuance.receipt
  rw [handleValue] at encoded
  have imported := continued.encodes_function encoded
  have actualFactory : recipe.NamedCallableAt packet.header.named.signature.key expected callable := by
    cases artifact
    rename_i authority actualRecipe
    change actualRecipe = recipe at atRecipe
    subst recipe
    exact factory
  obtain ⟨signature, slot, specialized, location, closure, identity, descriptor,
      signatureAt, keyAt, record, sourceType, slotAt, number, literal, projection⟩ :=
    actualFactory.prepared prepared
  obtain ⟨signatureEq, slotEq⟩ := selected_slot packet signatureAt keyAt
  subst signature
  subst slot
  have specializedEq : specialized = packet.header.named.specialized :=
    Except.ok.inj (record.symm.trans (CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled packet.header))
  subst specialized
  have headerMember := Inventory.header_member member
  obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller (owner recipe.compiled) headerMember
  have cached := CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.cache inputs rows packet.header headerMember
  have installed := NamedInstalledCode.of_bootstrap capture rfl cached
  have slotLocation := recipe.native_global_location slotAt
  have originalRead := RecursiveNamedPublicBootstrapGlobals.native_slot recipe.compiled recipe.templates
    (List.mem_of_getElem? slotAt)
  have locationEq : location = (owner recipe.compiled).key.locations packet.header := by
    change location = RecursiveNamedCatalogInitialization.location recipe.compiled.indexed.base.globals packet.header.slot
    have inside := (List.getElem?_eq_some_iff.mp signatureAt).1
    simp only [RecursiveNamedCatalogInitialization.location]
    omega
  rw [locationEq] at originalRead
  have samePayload := Option.some.inj (originalRead.symm.trans capture.read)
  have closureEq : closure = .closure packet.header.named.signature.parameterType
      (LanguageResult.resultType packet.header.named.signature.resultType)
      (packet.header.code.rename capture.embedding.lift) capture.captured := by
    cases samePayload
    rfl
  rw [closureEq] at literal
  obtain ⟨actualWorld, typedStore⟩ := RecursiveNamedCatalogPreparedInitialization.typed prepared
  have actualWorldEq := typedStore.world_eq
  rw [actualWorldEq] at typedStore
  obtain ⟨capturedContext, capturedTyped, bodyTyped⟩ :=
    RecursiveGlobalInitializationTyping.stored_closure typedStore capture.read
  have closureTyped : RuntimeValueHasType
      ((RecursiveNamedCatalogPreparedInitialization.store recipe.compiled).map Core.Value.type)
      (.closure packet.header.named.signature.parameterType
        (LanguageResult.resultType packet.header.named.signature.resultType)
        (packet.header.code.rename capture.embedding.lift) capture.captured)
      packet.header.named.signature.functionType recipe.compiled.indexed.layouts.definitions :=
    .closure capturedTyped bodyTyped
  have projected : recipe.compiled.compatible.checked.catalog.project packet.header.named.specialized.function.type =
      .ok (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) := by
    rw [sourceType, literal] at projection
    exact projection
  refine ⟨callable, sourceType ▸ imported, ?_, source_typed packet.sourceAt callerHeader ⟨[]⟩⟩
  have related : CallableIndexedOwnedContextualCellOrigins.FunctionOrigins
      (headers rows) (keys recipe.compiled) bodyRegistry faults []
      ((RecursiveNamedCatalogPreparedInitialization.store recipe.compiled).map Core.Value.type)
      packet.header.named.specialized.function.type
      (.global (CallableNamedReversal.global (CallableNamedMetadata.global
        packet.header.named.specialized input.prepared.available))) callable
      (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) := by
    rw [literal]
    exact .global (.prior (.prior (.named (owner recipe.compiled) headerMember
      packet.sourceAt (NamedCapture.of_capture capture) installed number projected descriptor closureTyped)))
  obtain ⟨_facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate packet.sourceAt wellFormed
  have sourceTypeEq : packet.header.named.specialized.function.type =
      (CallableNamedReversal.global (CallableNamedMetadata.global
        packet.header.named.specialized input.prepared.available)).instantiation.type := rfl
  rw [sourceTypeEq.trans certified.callable_type] at related ⊢
  exact .function related

/-- Actual named issuance, startup and the bootstrap-owned capture construct
one complete receiving function representation. Raw Source typing is derived
for the selected caller's declaration context. -/
theorem StartAt.named_argument_represents_after
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : State (headers rows) (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (callerHeader : Header compiled (Program.ofChecked compiled.sourceProgram))
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact} {issuanceFuel : Nat}
    (issuance : before.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root recipe.compiled}
    {native : Environment} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ callable, native[index]? = some callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        [] ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
        packet.header.named.specialized.function.type
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available))) callable
        (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) ∧
      Dynamic.ValueHasType callerHeader.function.context ⟨[]⟩
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available))) packet.header.named.specialized.function.type := by
  obtain ⟨callable, imported, represented, typed⟩ :=
    Session.named_value_represents_after prepared inputs rows packet member bodyRegistry registry faults profile
      caller callerHeader issuance continued started.recipe_eq handleValue wellFormed
  exact ⟨callable, RecursiveNamedPublicIssuedFunctionInputs.StartAt.imported_function started imported found,
    represented, typed⟩

/-- The original single-issuance interface is the empty continuation case. -/
theorem StartAt.named_argument_represents
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : State (headers rows) (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (callerHeader : Header compiled (Program.ofChecked compiled.sourceProgram))
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact} {issuanceFuel : Nat}
    (issuance : before.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root recipe.compiled}
    {native : Environment} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe root
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ callable, native[index]? = some callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        [] ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
        packet.header.named.specialized.function.type
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available))) callable
        (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) ∧
      Dynamic.ValueHasType callerHeader.function.context ⟨[]⟩
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available))) packet.header.named.specialized.function.type := by
  exact StartAt.named_argument_represents_after prepared inputs rows packet member bodyRegistry registry faults profile
    caller callerHeader issuance (.refl _) started handleValue found wellFormed

/-- The actual single named handle is passed through the root's complete raw
parameter signature. The receiving argument relation and Source typing are
constructed from issuance and preparation, with no argument proof premise. -/
theorem StartAt.named_arguments_receiving
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    {input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled}
    (packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input)
    (member : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory.HasRow packet rows)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : CallableIndexedOwnedFunctionState.State
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {issuanceFuel : Nat}
    (issuance : before.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root compiled}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe
      ((Recipe.prepare_compiled prepared).symm ▸ root) ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) root header)
    {binding : CallableIndexedParameterCertificates.Binding}
    (sole : header.bindings = [binding]) (rawType : binding.1.scheme.body = packet.header.named.specialized.function.type)
    (publicValues : arguments = [issued.value])
    {handle : Handle} (handleValue : issued.value = .function handle)
    (programTyped : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
          (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled) bodyRegistry faults profile))
      [] ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      header.bindings [.global (CallableNamedReversal.global
        (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available))] native ∧
    Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ [.global (CallableNamedReversal.global
      (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available))] header.types := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨callable, argument, represented, sourceTyped⟩ :=
    StartAt.named_argument_represents prepared inputs rows packet member bodyRegistry registry faults profile
      caller header issuance started handleValue
      (show arguments[0]? = some (.function handle) by rw [publicValues, handleValue]; rfl) programTyped
  have arity := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map, sole, List.length_cons, List.length_nil] at arity
  have nativeLength := congrArg List.length started.typed.type_tags
  rw [selected.shape.1] at nativeLength
  simp only [List.length_map] at nativeLength
  have nativeOne : native.length = 1 := nativeLength.trans arity.symm
  have nativeEq : native = [callable] := by
    cases native with
    | nil => simp at nativeOne
    | cons first rest =>
        have firstEq : first = callable := Option.some.inj argument
        have restNil : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using nativeOne)
        rw [firstEq, restNil]
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header rfl programTyped record
  rw [sole] at projected
  obtain ⟨actualType, remaining, projectedHead, _projectedTail, nativeTypes⟩ :=
    CompatibleEncoding.project_cons projected
  have actualTypeEq : actualType = binding.2 := (List.cons.inj nativeTypes).1.symm
  have projectedNamed : recipe.compiled.compatible.checked.catalog.project packet.header.named.specialized.function.type = .ok binding.2 := by
    simpa only [rawType, actualTypeEq, SourceCoreCompatibleValues.Context.initial] using projectedHead
  have payloadType := Except.ok.inj (represented.projection.symm.trans projectedNamed)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  constructor
  · rw [sole, nativeEq]
    exact .cons (rawType.symm ▸ payloadType ▸ represented) .nil
  · rw [← typesEq, sole, List.map_cons, List.map_nil, rawType]
    exact .cons sourceTyped .nil

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNamedArgumentReceipts
