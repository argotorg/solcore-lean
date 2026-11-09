import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots

/-!
# Recursive named public results: argument receipts

Receipts of simple, data, named, builtin and mixed arguments, returned and factory values, and scalar results.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedValues
/-! A successful public payload retains the actual semantic result and the
returned owned pool. The Source heap, closure captures and stable history come
from the preceding execution; exporting a handle does not construct them. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  {owner : OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : NamedCapture headers owner.key header mapping world}
  {payloads : List Value} {context : SourceSemantics.Context}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
  {native payload : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

/-- The successful result keeps its original Source value and physical caller
state. Its heap typing fixes the returned native world exactly. -/
theorem returned_value
    (result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := registry) (payloads := payloads) functions owner caller header capture
      context outcome after native finalStore finalMap finalWorld faults)
    (decoded : LanguageResult.decode? native = some (.succeeded payload)) :
    ∃ source, outcome = .value source ∧
      ValueRep compiled.compatible.checked registry functions finalMap finalWorld
        header.function.resultType source payload header.output ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      finalWorld = finalStore.map Value.type ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧ StableRows returned ∧
        Dynamic.HeapWellTyped context after ∧
        Dynamic.ValueHasType context after source header.function.resultType := by
  obtain ⟨_evaluated, represented, heaps, _maps, _worlds, _administrative, _metadata,
    returned, related, post⟩ := result
  cases represented with
  | value represented =>
      simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
      subst payload
      have admission := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value post
      exact ⟨_, rfl, represented, heaps, heaps.runtime_hasTypes.world_eq,
        returned, related, admission.2.rows, admission.2.heap, admission.1⟩
  | fault represented => cases decoded

/-- Real instantiated headers share the program catalog and have closed rigid
and lexical variable scopes. Both the declaration and its parameter context
therefore support the next declaration's actual runtime type context. -/
theorem header_context_supports
    (first next : Header compiled (Program.ofChecked compiled.sourceProgram))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Dynamic.TypeContextSupports first.function.context next.function.context ∧
      Dynamic.TypeContextSupports first.context next.function.context := by
  obtain ⟨_firstFacts, firstTyped⟩ := RecursiveNamedHeaderSourceTyping.certificate first wellFormed
  obtain ⟨_nextFacts, nextTyped⟩ := RecursiveNamedHeaderSourceTyping.certificate next wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields first.extended
  have signatures : first.function.context.signatures = (Program.ofChecked compiled.sourceProgram).signatures :=
    (congrArg (fun context : SourceSemantics.Context => context.signatures) first.frame.context).trans
      firstTyped.signatures_eq
  have closed : first.function.context.typeParameters = [] :=
    (congrArg (fun context : SourceSemantics.Context => context.typeParameters) first.frame.context).trans
      firstTyped.type_parameters_empty
  have variables : first.function.context.typeVariables = [] :=
    (congrArg (fun context : SourceSemantics.Context => context.typeVariables) first.frame.context).trans
      firstTyped.type_variables_empty
  rw [next.frame.context]
  exact ⟨Dynamic.TypeContextSupports.ofClosed (nextTyped.signatures_eq.trans signatures.symm)
      closed nextTyped.type_parameters_empty variables nextTyped.residual_type_variables_open,
    Dynamic.TypeContextSupports.ofClosed (nextTyped.signatures_eq.trans (fields.signatures.trans signatures).symm)
      (fields.typeParameters.trans closed) nextTyped.type_parameters_empty
      (fields.typeVariables.trans variables) nextTyped.residual_type_variables_open⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCurrentFactoryValues
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBuiltinArgumentReceipts
/-! An actual builtin issuance, successful cached recipe preparation, and the
original startup encoder jointly establish the builtin argument's Source
meaning. The exact closed code, nonwrapping identity and descriptor come from
the compiler-owned factory. The receiving body's function model and metadata
registry are retained; neither authentication nor native type tags determine
Source function meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBuiltinArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionValues (Header Key)

/-- Actual builtin issuance constructs the receiving representation before
selecting any argument position. Its accepted handle encoding remains valid
after the retained issuance sequence, including use inside nested inputs. -/
theorem Session.builtin_value_represents_after
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
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
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
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

/-- A builtin argument at its actual startup index has the complete receiving
function representation and deep Source typing, for any Source heap/context.
The caller still selects its actual raw parameter type independently. -/
theorem StartAt.builtin_argument_represents_after
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (context : SourceSemantics.Context) (heap : Dynamic.Heap)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ callable, before.SameRuntime issued.session ∧ issued.sourceType = function.type ∧
      native[index]? = some callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world function.type (.builtin ⟨function⟩) callable
        (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)) ∧
      Dynamic.ValueHasType context heap (.builtin ⟨function⟩) function.type := by
  obtain ⟨callable, same, sourceType, imported, represented, typed⟩ :=
    Session.builtin_value_represents_after prepared headers keys bodyRegistry registry faults profile
      mapping context heap issuance continued started.recipe_eq handleValue (world := world)
  exact ⟨callable, same, sourceType,
    RecursiveNamedPublicIssuedFunctionInputs.StartAt.imported_function started imported found, represented, typed⟩

/-- The original single-issuance interface is the empty continuation case. -/
theorem StartAt.builtin_argument_represents
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (context : SourceSemantics.Context) (heap : Dynamic.Heap)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ callable, before.SameRuntime issued.session ∧ issued.sourceType = function.type ∧
      native[index]? = some callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world function.type (.builtin ⟨function⟩) callable
        (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)) ∧
      Dynamic.ValueHasType context heap (.builtin ⟨function⟩) function.type := by
  exact StartAt.builtin_argument_represents_after prepared headers keys bodyRegistry registry faults profile mapping
    context heap issuance (.refl _) started handleValue found

/-- The actual single builtin handle is passed through the root's complete raw
parameter signature. The receiving argument relation and Source typing are
constructed from issuance and preparation, with no argument proof premise. -/
theorem StartAt.builtin_arguments_receiving
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (heap : Dynamic.Heap)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root compiled}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe
      ((Recipe.prepare_compiled prepared).symm ▸ root) world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    {binding : CallableIndexedParameterCertificates.Binding}
    (sole : header.bindings = [binding]) (rawType : binding.1.scheme.body = function.type)
    (publicValues : arguments = [issued.value])
    {handle : Handle} (handleValue : issued.value = .function handle)
    (programTyped : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      mapping world header.bindings [.builtin ⟨function⟩] native ∧
    Dynamic.ValuesHaveTypes header.function.context heap [.builtin ⟨function⟩] header.types := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨callable, _same, _sourceType, argument, represented, sourceTyped⟩ :=
    StartAt.builtin_argument_represents prepared headers keys bodyRegistry registry faults profile mapping
      header.function.context heap issuance started handleValue
      (show arguments[0]? = some (.function handle) by rw [publicValues, handleValue]; rfl)
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
  have projectedBuiltin : recipe.compiled.compatible.checked.catalog.project function.type = .ok binding.2 := by
    simpa only [rawType, actualTypeEq, SourceCoreCompatibleValues.Context.initial] using projectedHead
  have payloadType := Except.ok.inj (represented.projection.symm.trans projectedBuiltin)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  constructor
  · rw [sole, nativeEq]
    exact .cons (rawType.symm ▸ payloadType ▸ represented) .nil
  · rw [← typesEq, sole, List.map_cons, List.map_nil, rawType]
    exact .cons sourceTyped .nil

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBuiltinArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataArgumentReceipts
/-! Metadata-bearing input arguments come from the original successful public
encoder. Their exact metadata words are transported by a genuine extension of
the encoded registry to the receiving registry. This extension remains an
explicit static condition; two extensions of a common registry do not imply it.

The independent structural input certificate retains raw proxy inner types,
constructor instantiations, mapping types and ordered duplicate entries. It
does not contain a Source value typing judgment or a body execution law.
Accepted encoding alone permits more inputs because runtimeType erases nested
comptime annotations. The certificate rules out those raw mismatches.

The two final endpoints are consumed by initialized public success/failure and
Word bounds. Handles remain outside this recursively data-only input family.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open CallableIndexedParameterCertificates (Binding)

mutual
  /-- Raw structural typing of a public data carrier, independent of heaps,
  native tags, payload representations and Source execution. -/
  inductive DataTyped (context : SourceSemantics.Context) :
      SourceCoreDataValues.Value → TypeSystem.Ty → Prop where
    | unit : DataTyped context .unit .unit
    | bool (value : Bool) : DataTyped context (.bool value) .bool
    | word (value : Word) : DataTyped context (.word value) .word
    | integer (value : Int) : DataTyped context (.integer value) .integer
    | product {left right : SourceCoreDataValues.Value} {leftType rightType : TypeSystem.Ty}
        (first : DataTyped context left leftType) (second : DataTyped context right rightType) :
        DataTyped context (.product left right) (.product leftType rightType)
    | proxy (inner : TypeSystem.Ty) : DataTyped context (.proxy inner) (.proxy inner)
    | constructed {metadata : DataConstructorInstantiation} {payloads : List SourceCoreDataValues.Value}
        (valid : DataConstructorInstantiation.Valid context metadata)
        (typed : DataTypes context payloads metadata.payloadTypes) :
        DataTyped context (.constructed metadata payloads) metadata.resultType
    | mapping {key value : TypeSystem.Ty}
        {entries : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)}
        (typed : DataEntriesTyped context key value entries) :
        DataTyped context (.mapping key value entries) (.mapping key value)
    | comptime {value : SourceCoreDataValues.Value} {type : TypeSystem.Ty}
        (typed : DataTyped context value type) : DataTyped context value (.comptime type)

  inductive DataTypes (context : SourceSemantics.Context) :
      List SourceCoreDataValues.Value → List TypeSystem.Ty → Prop where
    | nil : DataTypes context [] []
    | cons {value : SourceCoreDataValues.Value} {values : List SourceCoreDataValues.Value}
        {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
        (head : DataTyped context value type) (tail : DataTypes context values types) :
        DataTypes context (value :: values) (type :: types)

  inductive DataEntriesTyped (context : SourceSemantics.Context) :
      TypeSystem.Ty → TypeSystem.Ty → List (SourceCoreDataValues.Value × SourceCoreDataValues.Value) → Prop where
    | empty (key value : TypeSystem.Ty) : DataEntriesTyped context key value []
    | entry {key value : TypeSystem.Ty} {first second : SourceCoreDataValues.Value}
        {rest : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)}
        (firstTyped : DataTyped context first key) (secondTyped : DataTyped context second value)
        (restTyped : DataEntriesTyped context key value rest) :
        DataEntriesTyped context key value ((first, second) :: rest)
end

/-- The structural certificate constructs an independent Source interpretation
and its raw typing at any heap. No compiler or encoder result is used here. -/
theorem DataTyped.meaning_typed {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {carrier : SourceCoreDataValues.Value} {type : TypeSystem.Ty}
    (typed : DataTyped context carrier type) :
    ∃ source, DataPayloadEncoding.Means carrier source ∧
      Dynamic.ValueHasType context heap source type := by
  induction typed using DataTyped.rec
    (motive_2 := fun carriers types _ => ∃ sources,
      DataPayloadEncoding.Meanings carriers sources ∧ Dynamic.ValuesHaveTypes context heap sources types)
    (motive_3 := fun key value carriers _ => ∃ sources,
      DataPayloadEncoding.EntryMeanings carriers sources ∧
        Dynamic.MappingEntriesHaveTypes context heap sources key value) with
  | unit => exact ⟨.unit, .unit, .unit⟩
  | bool value => exact ⟨.bool value, .bool value, .bool value⟩
  | word value => exact ⟨.word value, .word value, .word value⟩
  | integer value => exact ⟨.integer value, .integer value, .integer value⟩
  | product _ _ first second =>
      obtain ⟨left, leftMeaning, leftTyped⟩ := first
      obtain ⟨right, rightMeaning, rightTyped⟩ := second
      exact ⟨.product left right, .product leftMeaning rightMeaning, .product leftTyped rightTyped⟩
  | proxy inner => exact ⟨.proxy inner, .proxy inner, .proxy inner⟩
  | constructed valid _ ih =>
      obtain ⟨sources, meanings, typed⟩ := ih
      exact ⟨.constructed _ sources, .constructed meanings, .constructed valid typed⟩
  | mapping _ ih =>
      obtain ⟨sources, meanings, typed⟩ := ih
      exact ⟨.mapping _ _ sources, .mapping meanings, .mapping typed⟩
  | comptime _ ih =>
      obtain ⟨source, meaning, typed⟩ := ih
      exact ⟨source, meaning, .comptime typed⟩
  | nil => exact ⟨[], .nil, .nil⟩
  | cons _ _ head tail =>
      obtain ⟨source, meaning, typed⟩ := head
      obtain ⟨sources, meanings, typings⟩ := tail
      exact ⟨source :: sources, .cons meaning meanings, .cons typed typings⟩
  | empty key value => exact ⟨[], .empty, .nil key value⟩
  | entry _ _ _ first second rest =>
      obtain ⟨left, leftMeaning, leftTyped⟩ := first
      obtain ⟨right, rightMeaning, rightTyped⟩ := second
      obtain ⟨sources, meanings, typings⟩ := rest
      exact ⟨(left, right) :: sources, .prepend leftMeaning rightMeaning meanings,
        .cons leftTyped rightTyped typings⟩

/-- Exact raw data typing of one public value. This records its literal public
carrier, rather than wrapping a desired Dynamic.ValueHasType judgment. -/
def PublicDataTyped (context : SourceSemantics.Context) (value : SourceCorePublicValues.Value)
    (type : TypeSystem.Ty) : Prop :=
  ∃ carrier, value = DataInput.publicValue carrier ∧ DataTyped context carrier type

inductive PublicDataTypes (context : SourceSemantics.Context) :
    List SourceCorePublicValues.Value → List TypeSystem.Ty → Prop where
  | nil : PublicDataTypes context [] []
  | cons {value : SourceCorePublicValues.Value} {values : List SourceCorePublicValues.Value}
      {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
      (head : PublicDataTyped context value type) (tail : PublicDataTypes context values types) :
      PublicDataTypes context (value :: values) (type :: types)

theorem PublicDataTypes.data {context : SourceSemantics.Context}
    {values : List SourceCorePublicValues.Value} {types : List TypeSystem.Ty}
    (typed : PublicDataTypes context values types) : ∀ value ∈ values, DataPublic value := by
  induction typed with
  | nil => intro value member; cases member
  | cons head _ ih =>
      intro value member
      rcases List.mem_cons.mp member with same | member
      · subst value
        obtain ⟨carrier, image, _⟩ := head
        exact ⟨carrier, image⟩
      · exact ih value member

theorem PublicDataTyped.source_hasType {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : SourceCorePublicValues.Value} {type : TypeSystem.Ty} {source : Dynamic.Value}
    (typed : PublicDataTyped context value type)
    (meaning : RecursiveNamedPublicDataInputs.Means value source) :
    Dynamic.ValueHasType context heap source type := by
  obtain ⟨carrier, image, typed⟩ := typed
  obtain ⟨actual, interpreted, actualTyped⟩ := typed.meaning_typed (heap := heap)
  have same := RecursiveNamedPublicRuntimeMeaning.means_functional
    (show RecursiveNamedPublicDataInputs.Means value actual from ⟨carrier, image, interpreted⟩) meaning
  cases same
  exact actualTyped

theorem PublicDataTypes.source_haveTypes {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {values : List SourceCorePublicValues.Value} {types : List TypeSystem.Ty}
    {sources : List Dynamic.Value} (typed : PublicDataTypes context values types)
    (meanings : RecursiveNamedPublicDataInputs.Meanings values sources) :
    Dynamic.ValuesHaveTypes context heap sources types := by
  induction typed generalizing sources with
  | nil => cases meanings; exact .nil
  | cons head _ ih =>
      cases meanings with
      | cons meaning rest => exact .cons (head.source_hasType meaning) (ih rest)

private theorem arguments_metadata {checked : SourceCoreCompatibleCatalog.Checked}
    {encoded receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {bindings : List Binding} {sources : List Dynamic.Value} {native : Environment}
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked encoded functions) mapping world bindings sources native)
    (metadata : SourceCoreRawMetadata.Extends encoded receiving) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked receiving functions) mapping world bindings sources native := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons (CompatiblePayload.ValueRep.extend head metadata (.refl _) (.refl _)) ih

/-- The original encoder supplies both source meaning and payload representation.
Raw input correctness and exact registry extension construct the two argument
premises at the receiving metadata used by the initialized public bounds. -/
theorem data_arguments_receiving
    {artifact : Artifact} {session : Session artifact}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
    (functions : FunctionModel values.checked.catalog ambient)
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (before : Dynamic.Heap)
    (started : StartAt session key publicArguments fuel checkpoint recipe root world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (programTyped : ProgramWellFormed program)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (typed : PublicDataTypes header.function.context publicArguments header.types) :
    ∃ arguments, RecursiveNamedPublicDataInputs.Meanings publicArguments arguments ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
        mapping world header.bindings arguments native ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  obtain ⟨arguments, meanings, represented⟩ :=
    RecursiveNamedPublicDataInputs.StartAt.data_arguments functions mapping started selected
      typed.data sameChecked programTyped record
  exact ⟨arguments, meanings, arguments_metadata represented metadata, typed.source_haveTypes meanings⟩

/-- Match caller-supplied independent Source arguments to the actual encoder's
arguments before the initialized public Word preservation theorem is applied. -/
theorem data_arguments_at_receiving
    {artifact : Artifact} {session : Session artifact}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
    (functions : FunctionModel values.checked.catalog ambient)
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (before : Dynamic.Heap)
    (started : StartAt session key publicArguments fuel checkpoint recipe root world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (programTyped : ProgramWellFormed program)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (typed : PublicDataTypes header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
      mapping world header.bindings arguments native ∧
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  obtain ⟨actual, interpreted, represented, actualTyped⟩ :=
    data_arguments_receiving functions receiving mapping before started selected sameChecked programTyped metadata typed
  have same := RecursiveNamedPublicRuntimeMeaning.meanings_functional interpreted meanings
  cases same
  exact ⟨represented, actualTyped⟩

/-- The encoder's erased comparison cannot justify raw proxy typing. -/
example : SourceCoreRawMetadata.runtimeType (.proxy (.comptime .word)) =
    SourceCoreRawMetadata.runtimeType (.proxy .word) := rfl

example (context : SourceSemantics.Context) :
    ¬ PublicDataTyped context (.proxy (.comptime .word)) (.proxy .word) := by
  intro typed
  have meaning : RecursiveNamedPublicDataInputs.Means (.proxy (.comptime .word))
      (.proxy (.comptime .word)) :=
    ⟨.proxy (.comptime .word), by simp only [DataInput.publicValue], .proxy _⟩
  have impossible := typed.source_hasType (heap := ⟨[]⟩) meaning
  cases impossible

/-- Matching raw proxy annotations have a genuine structural certificate. -/
example (context : SourceSemantics.Context) :
    PublicDataTyped context (.proxy (.comptime .word)) (.proxy (.comptime .word)) :=
  ⟨.proxy (.comptime .word), by simp only [DataInput.publicValue], .proxy _⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNamedArgumentReceipts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedDataArgumentReceipts
/-! A selected data argument is interpreted through its original codec inside
an arbitrary mixed input list. Adjacent handles do not change its Source
meaning. Native position, raw parameter type and final metadata all come from
the same actual startup. Ordered duplicate entries and raw annotations remain
those of the public data carrier. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedDataArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- Identify one exact encoded position without requiring other arguments to
be recursively data-only. Both native types and raw types retain that index. -/
theorem StartAt.data_input
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {index : Nat} {expected : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    (rawType : root.inputs[index]? = some expected)
    (found : arguments[index]? = some value) (data : DataPublic value) :
    ∃ payload type, native[index]? = some payload ∧ root.types[index]? = some type ∧
      recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
      EncodedDataInput recipe.compiled.compatible.checked encodedValues.registry expected value payload := by
  have receipt := started.original.data_input found data
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  obtain ⟨actualRoot, encodedPrefix, selected, atIndex, initial⟩ := receipt
  have sameRoot := Option.some.inj (started.selected.symm.trans selected)
  subst actualRoot
  obtain ⟨payload, type, payloadAt, typeAt, projected, encodedAt⟩ := atIndex expected rawType
  have original := started.initial
  have actualValues := started.values
  cases checkpoint
  rename_i origin request checkpointWorld state stored typed extension registry values owner
  change values = encodedValues at actualValues
  change EncodedDataInput actualRecipe.compiled.compatible.checked values.registry expected value payload at encodedAt
  rw [actualValues] at encodedAt
  change state = Core.State.initial root.body
    (native.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment actualRecipe.compiled.indexed) store at original
  have sameState := initial.symm.trans original
  have sameControl := congrArg Core.State.control sameState
  have sameEnvironment := (Core.Control.eval.inj sameControl).2
  have samePrefix : encodedPrefix = native := by
    have reversed := congrArg List.reverse (List.append_inj_left' sameEnvironment rfl)
    simpa only [List.reverse_reverse] using reversed
  subst encodedPrefix
  exact ⟨payload, type, payloadAt, typeAt, projected, encodedAt⟩

/-- Actual mixed startup supplies the selected data payload's representation.
Independent raw input typing supplies Source typing; the actual metadata
extension retains every encoded tag word at the receiving registry. -/
theorem StartAt.data_argument_represents
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    (functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap)
    (context : SourceSemantics.Context) (heap : Dynamic.Heap)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    {index : Nat} {expected : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (rawType : root.inputs[index]? = some expected) (found : arguments[index]? = some value)
    (inputTyped : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value expected)
    (meaning : RecursiveNamedPublicDataInputs.Means value source) :
    ∃ payload type, native[index]? = some payload ∧ root.types[index]? = some type ∧
      recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
      ValueRep recipe.compiled.compatible.checked receiving functions mapping world expected source payload type ∧
      Dynamic.ValueHasType context heap source expected := by
  have sourceTyped := RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped.source_hasType inputTyped meaning (heap := heap)
  obtain ⟨carrier, image, _typed⟩ := inputTyped
  obtain ⟨payload, type, payloadAt, typeAt, projected, encodedAt⟩ :=
    StartAt.data_input started rawType found ⟨carrier, image⟩
  obtain ⟨actual, actualAt, typed⟩ := started.typed.lookup typeAt
  have same : actual = payload := Option.some.inj (actualAt.symm.trans payloadAt)
  subst actual
  obtain ⟨interpreted, interpretedAt, represented⟩ :=
    RecursiveNamedPublicDataInputs.EncodedDataInput.represents functions mapping world encodedAt projected
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).basePrefix typed
  have sameSource := RecursiveNamedPublicRuntimeMeaning.means_functional interpretedAt meaning
  subst interpreted
  exact ⟨payload, type, payloadAt, typeAt, projected,
    represented.extend metadata (.refl _) (.refl _), sourceTyped⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedDataArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedArgumentReceipts
/-! Ordered mixed public inputs retain their actual issuance histories and raw
Source types. A data leaf carries only independent structural typing and its
public interpretation; a named or builtin leaf carries genuine issuance and a
finite continuation of that session's issuances. The whole argument relation
is constructed at the real startup, preserving positions and repeated values.
Nested function carriers and previously executed sessions are separate work. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionState (State)
open CallableIndexedParameterCertificates (Binding)

/-- Each leaf names its independent Source value without assuming its runtime
representation, Source typing judgment or execution behavior. -/
inductive Input {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
    (context : SourceSemantics.Context) :
    TypeSystem.Ty → SourceCorePublicValues.Value → Dynamic.Value → Prop where
  | data {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
      (typed : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value type)
      (meaning : RecursiveNamedPublicDataInputs.Means value source) :
      Input rows session context type value source
  | named {input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled}
      (packet : Issued input) (member : Inventory.HasRow packet rows)
      {before : Session artifact} {issued : Completion artifact} {issuanceFuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
      (continued : issued.session.IssuanceChain session)
      {handle : Handle} (handleValue : issued.value = .function handle) :
      Input rows session context packet.header.named.specialized.function.type issued.value
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available)))
  | builtin {function : BuiltinFunctionId}
      {before : Session artifact} {issued : Completion artifact} {issuanceFuel : Nat}
      (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
      (continued : issued.session.IssuanceChain session)
      {handle : Handle} (handleValue : issued.value = .function handle) :
      Input rows session context function.type issued.value (.builtin ⟨function⟩)

/-- Argument positions and duplicates remain explicit list structure. -/
inductive Inputs {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
    (context : SourceSemantics.Context) :
    List TypeSystem.Ty → List SourceCorePublicValues.Value → List Dynamic.Value → Prop where
  | nil : Inputs rows session context [] [] []
  | cons {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
      {value : SourceCorePublicValues.Value} {values : List SourceCorePublicValues.Value}
      {source : Dynamic.Value} {sources : List Dynamic.Value}
      (head : Input rows session context type value source)
      (tail : Inputs rows session context types values sources) :
      Inputs rows session context (type :: types) (value :: values) (source :: sources)

private theorem Inputs.source_length {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    {rows : Inventory inputs} {artifact : Artifact} {session : Session artifact}
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs rows session context types values sources) : sources.length = types.length := by
  induction receipts with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem Inputs.lookup {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    {rows : Inventory inputs} {artifact : Artifact} {session : Session artifact}
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs rows session context types values sources)
    {index : Nat} {type : TypeSystem.Ty} (found : types[index]? = some type) :
    ∃ value source, values[index]? = some value ∧ sources[index]? = some source ∧
      Input rows session context type value source := by
  induction receipts generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact ⟨_, _, rfl, rfl, head⟩
      | succ index =>
          obtain ⟨value, source, valueAt, sourceAt, receipt⟩ := ih found
          exact ⟨value, source, valueAt, sourceAt, receipt⟩

private theorem projected_at {checked : SourceCoreCompatibleCatalog.Checked}
    {bindings : List Binding} {index : Nat} {binding : Binding}
    (projected : (bindings.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
      .ok (bindings.map Prod.snd))
    (found : bindings[index]? = some binding) :
    checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  induction bindings generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      simp only [List.map_cons] at projected
      obtain ⟨type, types, headProjected, tailProjected, shape⟩ := CompatibleEncoding.project_cons projected
      have parts := List.cons.inj shape
      have headActual : checked.catalog.project head.1.scheme.body = .ok head.2 := by
        simpa only [← parts.1] using headProjected
      have tailActual : (tail.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
          .ok (tail.map Prod.snd) := by
        simpa only [← parts.2] using tailProjected
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact headActual
      | succ index => exact ih tailActual found

/-- Reconstruct both complete lists from their original positions. Exact
lengths exclude silently discarded native or Source suffixes. -/
private theorem arguments_of_positions
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {bindings : List Binding} {sources : List Dynamic.Value} {native : Environment}
    (sourceLength : sources.length = bindings.length) (nativeLength : native.length = bindings.length)
    (positions : ∀ {index : Nat} {binding : Binding}, bindings[index]? = some binding →
      ∃ source value, sources[index]? = some source ∧ native[index]? = some value ∧
        ValueRep checked registry functions mapping world binding.1.scheme.body source value binding.2 ∧
        Dynamic.ValueHasType context heap source binding.1.scheme.body) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world bindings sources native ∧
      Dynamic.ValuesHaveTypes context heap sources (bindings.map (fun binding => binding.1.scheme.body)) := by
  induction bindings generalizing sources native with
  | nil =>
      have sourceNil := List.eq_nil_of_length_eq_zero sourceLength
      have nativeNil := List.eq_nil_of_length_eq_zero nativeLength
      subst sources
      subst native
      exact ⟨.nil, .nil⟩
  | cons binding bindings ih =>
      cases sources with
      | nil => simp at sourceLength
      | cons source sources =>
          cases native with
          | nil => simp at nativeLength
          | cons value native =>
              obtain ⟨actualSource, actualValue, sourceAt, valueAt, represented, typed⟩ :=
                positions (index := 0) rfl
              have sameSource : source = actualSource := Option.some.inj sourceAt
              have sameValue : value = actualValue := Option.some.inj valueAt
              subst actualSource
              subst actualValue
              simp only [List.length_cons] at sourceLength nativeLength
              have remaining := ih (Nat.succ.inj sourceLength) (Nat.succ.inj nativeLength) (by
                intro index next found
                exact positions (index := index + 1) found)
              exact ⟨.cons represented remaining.1, .cons typed remaining.2⟩

/-- Actual mixed startup constructs all argument representation and Source
value typing at the body's receiving registry. Only raw public input receipts,
genuine issuance chains and the actual metadata extension are supplied. -/
theorem StartAt.mixed_arguments_receiving
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : Inventory inputs)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : State (headers rows) (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    {artifact : Artifact} {session : Session artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root compiled}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {native : Environment} {arguments : List Dynamic.Value}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key publicArguments fuel checkpoint recipe
      ((Recipe.prepare_compiled prepared).symm ▸ root)
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
    (receipts : Inputs rows session header.function.context
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
          bodyRegistry faults profile))
      [] ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      header.bindings arguments native ∧
    Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ arguments header.types := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  have arity := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map] at arity
  have nativeLength := congrArg List.length started.typed.type_tags
  rw [selected.shape.1] at nativeLength
  simp only [List.length_map] at nativeLength
  have nativeCount : native.length = header.bindings.length := nativeLength.trans arity.symm
  have sourceCount : arguments.length = header.bindings.length := by
    simpa only [List.length_map] using receipts.source_length
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header rfl wellFormed record
  have rawInputs := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1
  have assembled := arguments_of_positions (functions :=
      CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry faults profile) (registry := registry) (mapping := [])
      (world := (RecursiveNamedCatalogPreparedInitialization.store recipe.compiled).map Core.Value.type)
      (context := header.function.context) (heap := ⟨[]⟩)
      sourceCount nativeCount (by
        intro index binding bindingAt
        have rawAt : (header.bindings.map (fun binding => binding.1.scheme.body))[index]? =
            some binding.1.scheme.body := by
          simp only [List.getElem?_map, bindingAt, Option.map_some]
        obtain ⟨publicValue, source, publicAt, sourceAt, receipt⟩ := receipts.lookup rawAt
        have bindingProjected := projected_at projected bindingAt
        have rawRoot : root.inputs[index]? = some binding.1.scheme.body := by
          rw [rawInputs]
          exact rawAt
        generalize rawEq : binding.1.scheme.body = raw at receipt rawRoot bindingProjected ⊢
        cases receipt with
        | data inputTyped meaning =>
            obtain ⟨value, type, valueAt, _typeAt, _projection, represented, typed⟩ :=
              RecursiveNamedPublicMixedDataArgumentReceipts.StartAt.data_argument_represents started
                (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
                  bodyRegistry faults profile) registry [] header.function.context ⟨[]⟩ metadata
                rawRoot publicAt inputTyped meaning
            have typeEq := Except.ok.inj (represented.projection.symm.trans bindingProjected)
            exact ⟨source, value, sourceAt, valueAt, typeEq ▸ represented, typed⟩
        | named packet member issuance continued handleValue =>
            have handleAt := publicAt
            rw [handleValue] at handleAt
            obtain ⟨value, valueAt, represented, typed⟩ :=
              RecursiveNamedPublicNamedArgumentReceipts.StartAt.named_argument_represents_after
                prepared inputs rows packet member bodyRegistry registry faults profile caller header
                issuance continued started handleValue handleAt wellFormed
            have typeEq := Except.ok.inj (represented.projection.symm.trans bindingProjected)
            exact ⟨_, value, sourceAt, valueAt, typeEq ▸ represented, typed⟩
        | builtin issuance continued handleValue =>
            have handleAt := publicAt
            rw [handleValue] at handleAt
            obtain ⟨value, _same, _sourceType, valueAt, represented, typed⟩ :=
              RecursiveNamedPublicBuiltinArgumentReceipts.StartAt.builtin_argument_represents_after
                prepared (headers rows) (keys recipe.compiled) bodyRegistry registry faults profile
                [] header.function.context ⟨[]⟩ issuance continued started handleValue handleAt
            have typeEq := Except.ok.inj (represented.projection.symm.trans bindingProjected)
            exact ⟨_, value, sourceAt, valueAt, typeEq ▸ represented, typed⟩)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  exact ⟨assembled.1, typesEq ▸ assembled.2⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleArgumentReceipts
/-! The original successful public encoder supplies scalar/product arguments
at the selected Header's raw types. Deep Source typing follows structurally
from the same SimpleInput receipt, including nested comptime wrappers.
The representation uses the receiving body's registry directly: these values
carry no metadata tags, so no equality or extension of encoder and receiving
registries is needed. Handles and metadata-bearing data are outside this unit.
The final endpoint matches supplied independent data meanings, allowing the
initialized public consumer to supply neither argument typing nor representation.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicSimpleInputs (Means Meanings)
open CallableIndexedParameterCertificates (Binding)

/-- Removing comptime from a scalar/product type preserves its shape; restoring
the original raw type uses genuine Source constructors rather than Core typing. -/
private theorem restore_simple_type
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {type : TypeSystem.Ty} {encoded : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (meaning : Means encoded source)
    (typed : Dynamic.ValueHasType context heap source (SourceCoreRawMetadata.runtimeType type)) :
    Dynamic.ValueHasType context heap source type := by
  induction type generalizing encoded source with
  | «variable» id => exact typed
  | parameter id => exact typed
  | constructor id => exact typed
  | error => exact typed
  | application function argument _functionIH _argumentIH =>
      cases meaning <;> cases typed
  | function parameter result _parameterIH _resultIH =>
      cases meaning <;> cases typed
  | mapping key value _keyIH _valueIH =>
      cases meaning <;> cases typed
  | proxy inner _ih =>
      cases meaning <;> cases typed
  | product left right leftIH rightIH =>
      cases meaning with
      | unit => cases typed
      | bool => cases typed
      | word => cases typed
      | integer => cases typed
      | product first second =>
          cases typed with
          | product leftTyped rightTyped =>
              exact .product (leftIH first leftTyped) (rightIH second rightTyped)
  | comptime inner ih => exact .comptime (ih meaning typed)

/-- The raw Source type comes from the original accepted SimpleInput, at any
Source heap and context. No heap lookup or native-value typing is assumed. -/
theorem simple_input_hasType
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {expected : TypeSystem.Ty} {encoded : SourceCorePublicValues.Value}
    {native : Core.Value} {source : Dynamic.Value}
    (input : SimpleInput expected encoded native) (meaning : Means encoded source) :
    Dynamic.ValueHasType context heap source expected := by
  induction input generalizing source with
  | unit view =>
      cases meaning
      exact restore_simple_type .unit (view.symm ▸ .unit)
  | bool value view =>
      cases meaning
      exact restore_simple_type (.bool value) (view.symm ▸ .bool value)
  | word value view =>
      cases meaning
      exact restore_simple_type (.word value) (view.symm ▸ .word value)
  | fixed value view canonical =>
      cases meaning
      exact restore_simple_type (.word value) (view.symm ▸ .fixed value canonical)
  | integer value view =>
      cases meaning
      exact restore_simple_type (.integer value) (view.symm ▸ .integer value)
  | product view _left _right leftIH rightIH =>
      cases meaning with
      | product first second =>
          exact restore_simple_type (.product first second)
            (view.symm ▸ .product (leftIH first) (rightIH second))

theorem simple_inputs_haveTypes
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {types : List TypeSystem.Ty} {encoded : List SourceCorePublicValues.Value}
    {native : Core.Environment} {sources : List Dynamic.Value}
    (inputs : SimpleInputs types encoded native) (meanings : Meanings encoded sources) :
    Dynamic.ValuesHaveTypes context heap sources types := by
  induction inputs generalizing sources with
  | nil => cases meanings; exact .nil
  | cons head _tail ih =>
      cases meanings with
      | cons first rest => exact .cons (simple_input_hasType head first) (ih rest)

private theorem simple_means_data
    {encoded : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (meaning : Means encoded source) : RecursiveNamedPublicDataInputs.Means encoded source := by
  induction meaning with
  | unit => exact ⟨.unit, by simp only [DataInput.publicValue], .unit⟩
  | bool value => exact ⟨.bool value, by simp only [DataInput.publicValue], .bool value⟩
  | word value => exact ⟨.word value, by simp only [DataInput.publicValue], .word value⟩
  | integer value => exact ⟨.integer value, by simp only [DataInput.publicValue], .integer value⟩
  | product _first _second firstIH secondIH =>
      obtain ⟨left, leftEq, leftMeaning⟩ := firstIH
      obtain ⟨right, rightEq, rightMeaning⟩ := secondIH
      refine ⟨.product left right, ?_, .product leftMeaning rightMeaning⟩
      rw [leftEq, rightEq]
      simp only [DataInput.publicValue]

private theorem simple_meanings_data
    {encoded : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (meanings : Meanings encoded sources) : RecursiveNamedPublicDataInputs.Meanings encoded sources := by
  induction meanings with
  | nil => exact .nil
  | cons head _tail ih => exact .cons (simple_means_data head) ih

/-- The original StartAt and selected raw signature construct both argument
premises for the receiving model. Its registry is independent of encodedValues. -/
theorem simple_arguments_receiving
    {artifact : Artifact} {session : Session artifact}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
    (functions : FunctionModel values.checked.catalog ambient)
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (before : Dynamic.Heap)
    (started : StartAt session key publicArguments fuel checkpoint recipe root world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
    (simple : ∀ argument ∈ publicArguments, SimplePublic argument)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (programTyped : ProgramWellFormed program) :
    ∃ arguments, Meanings publicArguments arguments ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
        mapping world header.bindings arguments native ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have inputs := RecursiveNamedPublicSimpleInputs.StartAt.simple_inputs started simple
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1] at inputs
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header sameChecked programTyped record
  obtain ⟨arguments, meanings, represented⟩ :=
    RecursiveNamedPublicSimpleInputs.SimpleInputs.arguments (registry := receiving)
      functions mapping world inputs projected
  have typed := simple_inputs_haveTypes (context := header.function.context) (heap := before) inputs meanings
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  exact ⟨arguments, meanings, represented, typesEq ▸ typed⟩

/-- Match independently supplied data arguments to those issued by the original
simple encoder, so the actual public Word trace needs no opaque argument premise. -/
theorem simple_arguments_at_receiving
    {artifact : Artifact} {session : Session artifact}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
    (functions : FunctionModel values.checked.catalog ambient)
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (before : Dynamic.Heap)
    (started : StartAt session key publicArguments fuel checkpoint recipe root world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
    (simple : ∀ argument ∈ publicArguments, SimplePublic argument)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (programTyped : ProgramWellFormed program)
    {arguments : List Dynamic.Value}
    (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
      mapping world header.bindings arguments native ∧
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  obtain ⟨actual, interpreted, represented, typed⟩ :=
    simple_arguments_receiving functions receiving mapping before started selected simple sameChecked programTyped
  have same := RecursiveNamedPublicRuntimeMeaning.meanings_functional
    (simple_meanings_data interpreted) meanings
  cases same
  exact ⟨represented, typed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults
/-! Exact Bool output follows from the actual public encoder and the independent
Source/native result. No decoder success or Source value law is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults
open Frontend SourceInference
open Core GeneralHeap CompatiblePayload
open SourceCoreIndexedSession

private theorem encoded_bool_value {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {publicValue : SourceCorePublicValues.Value} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    {value : Bool}
    (accepted : session.RawEncodedAt fuel registry .bool publicValue encoded)
    (payload : encoded.value = .bool value) : publicValue = .bool value := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases publicValue <;> try cases accepted
      case bool.refl =>
        exact congrArg SourceCorePublicValues.Value.bool (Core.Value.bool.inj payload)
      case constructed metadata values =>
        obtain ⟨_, _, _, _, _, _, _, _, same⟩ := accepted.constructed
        rw [same] at payload
        cases payload

theorem succeeded_bool_value {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {store : Core.Store} {completion : Completion artifact} {value : Bool}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation
      (.inRight .word (.bool value)) store completion)
    (requested : checkpoint.ResultTypeAt .bool) : completion.value = .bool value := by
  obtain ⟨_sourceType, encoded, accepted, payload⟩ := succeeded.reimports_payload requested rfl
  exact encoded_bool_value accepted payload

theorem represented_bool
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome}
    {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Core.Value} {store : Core.Store} {completion : Completion artifact} {value : Bool}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt .bool)
    (exported : completion.value = .bool value)
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world rawType .bool
      faults outcome native) : outcome = .value (.bool value) := by
  obtain ⟨payload, decoded, _⟩ := succeeded.reimports
  cases represented with
  | value related =>
    obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.bool_fields related
    have actualOutput := succeeded_bool_value succeeded requested
    have same := SourceCorePublicValues.Value.bool.inj (actualOutput.symm.trans exported)
    rw [same]
  | fault related =>
    simp only [LanguageResult.decode?, Option.some.injEq] at decoded
    cases decoded

/-- Exact public result profiles for Word and Bool calls. -/
inductive ScalarOutput where
  | word (value : Core.Word)
  | bool (value : Bool)

def ScalarOutput.sourceType : ScalarOutput → TypeSystem.Ty
  | .word _ => .word
  | .bool _ => .bool

def ScalarOutput.nativeType : ScalarOutput → Core.Ty
  | .word _ => .word
  | .bool _ => .bool

def ScalarOutput.source : ScalarOutput → Dynamic.Value
  | .word value => .word value
  | .bool value => .bool value

def ScalarOutput.native : ScalarOutput → Core.Value
  | .word value => .word value
  | .bool value => .bool value

def ScalarOutput.publicValue : ScalarOutput → SourceCorePublicValues.Value
  | .word value => .word value
  | .bool value => .bool value

theorem ScalarOutput.succeeded_value (scalar : ScalarOutput)
    {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {store : Core.Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation
      (.inRight .word scalar.native) store completion)
    (requested : checkpoint.ResultTypeAt scalar.sourceType) :
    completion.value = scalar.publicValue := by
  cases scalar with
  | word value => exact succeeded.word_value requested
  | bool value => exact succeeded_bool_value succeeded requested

theorem ScalarOutput.source_value (scalar : ScalarOutput)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome}
    {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Core.Value} {store : Core.Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt scalar.sourceType)
    (exported : completion.value = scalar.publicValue)
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world rawType scalar.nativeType
      faults outcome native) : outcome = .value scalar.source := by
  cases scalar with
  | word value => exact RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested exported represented
  | bool value => exact represented_bool succeeded requested exported represented

theorem ScalarOutput.native_value (scalar : ScalarOutput)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {payload : Core.Value}
    (represented : ValueRep checked registry functions mapping world rawType scalar.source payload scalar.nativeType) :
    payload = scalar.native := by
  cases scalar with
  | word value =>
    obtain ⟨actual, same, native⟩ := CompatibleExpressionPrimitives.word_fields represented
    exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  | bool value =>
    obtain ⟨actual, same, native⟩ := CompatibleExpressionPrimitives.bool_fields represented
    exact native.trans (congrArg Core.Value.bool (Dynamic.Value.bool.inj same).symm)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults
end
