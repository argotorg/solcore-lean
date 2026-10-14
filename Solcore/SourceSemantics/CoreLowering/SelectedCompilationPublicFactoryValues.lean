import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCurrentFactoryValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBuiltinArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap

/-! Actual public issuance supplies the complete original cached capture.
The positive named leaf retains every physical slot, and builtin issuance
retains its genuine closed compiler factory. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicFactoryValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt NamedInstalledCode)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionState (State)

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

/-- The selected real factory keeps the full original raw callable type. -/
theorem Session.named_source_type
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    {input : Input compiled} (packet : Issued input)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
    (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
    (atRecipe : ArtifactRecipe artifact recipe) :
    issued.sourceType = packet.header.named.specialized.function.type := by
  obtain ⟨expected, callable, _same, sourceType, _budget, _encoded, factory⟩ := issuance.receipt
  have actualFactory : recipe.NamedCallableAt packet.header.named.signature.key expected callable := by
    cases artifact
    rename_i authority actualRecipe
    change actualRecipe = recipe at atRecipe
    subst recipe
    exact factory
  obtain ⟨signature, slot, specialized, location, closure, identity, descriptor,
      signatureAt, keyAt, record, actualType, _slotAt, _number, _literal, _projection⟩ :=
    actualFactory.prepared prepared
  obtain ⟨signatureEq, _slotEq⟩ := selected_slot packet signatureAt keyAt
  subst signature
  have specializedEq : specialized = packet.header.named.specialized :=
    Except.ok.inj (record.symm.trans (CallableIndexedActualNamedSourceReceipts.header_record compiled packet.header))
  subst specialized
  exact sourceType.trans actualType

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
    (certified : SelectedCompilationNamedArgumentRows.CertifiedAt (header := packet.header) (function := CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available))) :
    ∃ callable, session.EncodesAt issuanceFuel packet.header.named.specialized.function.type
      (.function handle) callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedPhysicalCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
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
  have cached := CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.cache inputs rows packet.header headerMember
  have slotLocation := recipe.native_global_location slotAt
  have originalRead := RecursiveNamedPublicBootstrapGlobals.native_slot recipe.compiled recipe.templates
    (List.mem_of_getElem? slotAt)
  have locationEq : location = CallableIndexedOwnedPhysicalGlobals.location recipe.compiled packet.header.slot := by
    have inside := (List.getElem?_eq_some_iff.mp signatureAt).1
    simp only [CallableIndexedOwnedPhysicalGlobals.location, RecursiveNamedCatalogInitialization.location]
    omega
  rw [locationEq] at originalRead
  have originalPhysical := ((CallableIndexedOwnedPhysicalGlobals.initial recipe.compiled).cached cached).2
  have closureEq : closure = .closure packet.header.named.signature.parameterType
      (LanguageResult.resultType packet.header.named.signature.resultType)
      (packet.header.code.rename (RecursiveGlobalInitializationMeaning.shift packet.header.slot).lift)
      (List.replicate packet.header.slot .unit ++ CallableIndexedOwnedPhysicalGlobals.environment recipe.compiled) := by
    have same := Option.some.inj (originalRead.symm.trans originalPhysical)
    exact Value.inRight.inj same |>.2
  have frontendRecipe : artifact.RecipeAt recipe := by
    cases artifact
    exact atRecipe
  have currentRead := issuance.native_global_read frontendRecipe atNative (List.mem_of_getElem? slotAt)
  rw [locationEq, closureEq] at currentRead
  have typedStore := atNative.heap_typed frontendRecipe
  have keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical recipe.compiled (headers rows)
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_read (mapping := mapping)
    headerMember keyPhysical.frame keyPhysical.prefixZero keyPhysical.locations packet.aligned.globals currentRead typedStore
  have installed : NamedInstalledCode capture.named :=
    NamedInstalledCode.of_cached capture.named cached capture.embedding_eq
  obtain ⟨capturedContext, capturedTyped, bodyTyped⟩ :=
    RecursiveGlobalInitializationTyping.stored_closure typedStore capture.read
  have closureTyped : RuntimeValueHasType world
      (.closure packet.header.named.signature.parameterType
        (LanguageResult.resultType packet.header.named.signature.resultType)
        (packet.header.code.rename capture.named.embedding.lift) capture.named.captured)
      packet.header.named.signature.functionType recipe.compiled.indexed.layouts.definitions :=
    .closure capturedTyped bodyTyped
  have actualClosure : closure = .closure packet.header.named.signature.parameterType
      (LanguageResult.resultType packet.header.named.signature.resultType)
      (packet.header.code.rename capture.named.embedding.lift) capture.named.captured := by
    rw [capture.embedding_eq, capture.captured_eq]
    exact closureEq
  rw [actualClosure] at literal
  have projected : recipe.compiled.compatible.checked.catalog.project packet.header.named.specialized.function.type =
      .ok (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) := by
    rw [sourceType, literal] at projection
    exact projection
  refine ⟨callable, sourceType ▸ imported, ?_, RecursiveNamedPublicCurrentFactoryValues.source_typed packet.sourceAt callerHeader heap⟩
  have related : CallableIndexedOwnedPhysicalCellOrigins.FunctionOrigins
      (headers rows) (keys recipe.compiled) bodyRegistry faults mapping
      world
      packet.header.named.specialized.function.type
      (.global (CallableNamedReversal.global (CallableNamedMetadata.global
        packet.header.named.specialized input.prepared.available))) callable
      (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) := by
    rw [literal]
    exact .global ⟨CallableIndexedOwnedPhysicalNamedAssociation.of_capture
      (owner recipe.compiled) packet.header capture packet.sourceAt headerMember installed
      identity number projected descriptor closureTyped⟩
  obtain ⟨_facts, certified⟩ :=
    certified
  have sourceTypeEq : packet.header.named.specialized.function.type =
      (CallableNamedReversal.global (CallableNamedMetadata.global
        packet.header.named.specialized input.prepared.available)).instantiation.type := rfl
  rw [sourceTypeEq.trans certified.callable_type] at related ⊢
  exact .function related


theorem Session.builtin_value_represents_after
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (context : SourceSemantics.Context) (heap : Dynamic.Heap)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    (atRecipe : ArtifactRecipe artifact recipe)
    {world : StoreTyping}
    {handle : Handle} (handleValue : issued.value = .function handle) :
    ∃ callable, before.SameRuntime issued.session ∧ issued.sourceType = function.type ∧
      session.EncodesAt issuanceFuel function.type (.function handle) callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world function.type (.builtin ⟨function⟩) callable
        (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)) ∧
      Dynamic.ValueHasType context heap (.builtin ⟨function⟩) function.type := by
  obtain ⟨expected, callable, same, sourceType, _budget, encoded, factory⟩ := issuance.receipt
  rw [handleValue] at encoded
  have imported := continued.encodes_function encoded
  have actualFactory : recipe.BuiltinCallableAt function expected callable := by
    cases artifact
    rename_i authority actualRecipe
    change actualRecipe = recipe at atRecipe
    subst recipe
    exact factory
  obtain ⟨actualType, builtinIndex, identity, descriptor, inventory, number, literal⟩ :=
    actualFactory.prepared prepared
  refine ⟨callable, same, sourceType.trans actualType, actualType ▸ imported, ?_, .builtin ⟨function⟩⟩
  rw [literal]
  exact .function (.builtin (.prior (.prior (.builtin
    (CallableIndexedBuiltinValues.Represents.builtin inventory number descriptor .nil)))))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicFactoryValues
