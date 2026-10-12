import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedFunctionInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds

/-! An actual named issuance reaches its independent Source function through
one retained finite inventory row and the actual current owned pool. The
factory's physical slot identifies its whole installed closure, including all
captured values. Source typing comes from the retained declaration frame and
evidence; no function representation or input typing is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCurrentFactoryValues
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
theorem source_typed {compiled : SourceCoreUnifiedCompilation.Compiled}
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
the current owned capture. Its handle encoding survives further issuances
without depending on a top-level argument position. -/
theorem Session.named_value_represents_current
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (caller : State (headers rows) (keys compiled)
      ⟨[], mapping, world, heap, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (callerHeader : Header compiled (Program.ofChecked compiled.sourceProgram))
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact} {issuanceFuel : Nat}
    (issuance : before.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
    (atNative : before.NativeAt world store)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    (atRecipe : ArtifactRecipe artifact recipe)
    {handle : Handle} (handleValue : issued.value = .function handle)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ callable, session.EncodesAt issuanceFuel packet.header.named.specialized.function.type
      (.function handle) callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        mapping world
        packet.header.named.specialized.function.type
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available))) callable
        (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) ∧
      Dynamic.ValueHasType callerHeader.function.context heap
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
  have slotLocation := recipe.native_global_location slotAt
  have originalRead := RecursiveNamedPublicBootstrapGlobals.native_slot recipe.compiled recipe.templates
    (List.mem_of_getElem? slotAt)
  have locationEq : location = (owner recipe.compiled).key.locations packet.header := by
    change location = RecursiveNamedCatalogInitialization.location recipe.compiled.indexed.base.globals packet.header.slot
    have inside := (List.getElem?_eq_some_iff.mp signatureAt).1
    simp only [RecursiveNamedCatalogInitialization.location]
    omega
  have frontendRecipe : artifact.RecipeAt recipe := by
    cases artifact
    exact atRecipe
  have currentRead := issuance.native_global_read frontendRecipe atNative (List.mem_of_getElem? slotAt)
  rw [locationEq] at originalRead currentRead
  have samePayload := Option.some.inj (currentRead.symm.trans capture.read)
  have closureEq : closure = .closure packet.header.named.signature.parameterType
      (LanguageResult.resultType packet.header.named.signature.resultType)
      (packet.header.code.rename capture.embedding.lift) capture.captured := by
    cases samePayload
    rfl
  rw [closureEq] at literal originalRead
  let originalCapture : RecursiveNamedCatalog.Capture
      (prepared := recipe.compiled.indexed.ancestry)
      (values := .initial recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
      (headers rows) (owner recipe.compiled).key.locations (owner recipe.compiled).key.capturePrefix
      (owner recipe.compiled).key.frameLocation packet.header mapping world heap
      (RecursiveNamedCatalogPreparedInitialization.store recipe.compiled) :=
    { capture with read := originalRead }
  have installed : NamedInstalledCode (NamedCapture.of_capture capture) :=
    NamedInstalledCode.of_bootstrap originalCapture rfl cached
  have typedStore := atNative.heap_typed frontendRecipe
  obtain ⟨capturedContext, capturedTyped, bodyTyped⟩ :=
    RecursiveGlobalInitializationTyping.stored_closure typedStore capture.read
  have closureTyped : RuntimeValueHasType
      world
      (.closure packet.header.named.signature.parameterType
        (LanguageResult.resultType packet.header.named.signature.resultType)
        (packet.header.code.rename capture.embedding.lift) capture.captured)
      packet.header.named.signature.functionType recipe.compiled.indexed.layouts.definitions :=
    .closure capturedTyped bodyTyped
  have projected : recipe.compiled.compatible.checked.catalog.project packet.header.named.specialized.function.type =
      .ok (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) := by
    rw [sourceType, literal] at projection
    exact projection
  refine ⟨callable, sourceType ▸ imported, ?_, source_typed packet.sourceAt callerHeader heap⟩
  have related : CallableIndexedOwnedContextualCellOrigins.FunctionOrigins
      (headers rows) (keys recipe.compiled) bodyRegistry faults mapping
      world
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


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCurrentFactoryValues
