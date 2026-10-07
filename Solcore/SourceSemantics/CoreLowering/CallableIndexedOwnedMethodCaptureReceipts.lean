import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals

/-! An actual fresh bootstrap supplies complete method captures and canonical
named slots. Source attribution comes from the genuine method selector; cached
code or native typing supplies no Source body. Nonempty Source heap prefixes
require their separate initialization receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCaptureReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallablePreparedMethodRuntimeMeaning
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
  (dictionary : Dynamic.EvidenceEnvironment)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

abbrev sourceBody := CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method

/-- Every native field comes from the actual initialized cache, while the
complete independent Source method frame remains a separate receipt. -/
structure BootstrapCapture (world : StoreTyping) where
  administrative : Core.Context
  installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := sourceBody (compiled := compiled) (method := method))
    (administrative := administrative) functions [] world ⟨[]⟩
    (RecursiveNamedCatalogPreparedInitialization.store compiled)
    (RecursiveNamedCatalogPreparedInitialization.environment compiled)
  sourceFrame : CallableCoercionMethodFrame.Frame (sourceBody (compiled := compiled) (method := method))
    (methodFunction cached.compilation (sourceBody (compiled := compiled) (method := method)) dictionary)
  canonical_eq : installed.canonical = RecursiveNamedCatalogPreparedInitialization.environment compiled
  captured_eq : installed.captured = List.replicate cached.index (Value.unit) ++
    RecursiveNamedCatalogPreparedInitialization.environment compiled
  embedding_eq : installed.embedding = shift cached.index
  frame_eq : installed.frameLocation = 0
  globals : ∀ header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram),
    installed.canonical[header.slot]? = some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
      (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot))

private theorem installed_of_typed {world : StoreTyping}
    (typed : RuntimeStoreHasTypes world (RecursiveNamedCatalogPreparedInitialization.store compiled) compiled.indexed.layouts.definitions)
    (localsEmpty : (sourceBody (compiled := compiled) (method := method)).context.locals = []) :
    ∃ administrative, ∃ installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := sourceBody (compiled := compiled) (method := method))
      (administrative := administrative) functions [] world ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled),
      installed.canonical = RecursiveNamedCatalogPreparedInitialization.environment compiled ∧
      installed.captured = List.replicate cached.index (Value.unit) ++ RecursiveNamedCatalogPreparedInitialization.environment compiled ∧
      installed.embedding = shift cached.index ∧ installed.frameLocation = 0 := by
  have cachedCode : compiled.indexed.secondPass.closures[cached.index]? = some
      (.lambda cached.named.signature.parameterType (LanguageResult.resultType cached.named.signature.resultType) cached.compilation.output) := by
    simpa only [cached.compilation.emitted] using cached.cached
  obtain ⟨row, _rowFound, same, read⟩ := RecursiveNamedPublicBootstrapGlobals.cached_slot compiled cachedCode
  rcases row with ⟨parameter, result, body⟩
  change Expr.lambda _ _ _ = Expr.lambda parameter result body at same
  cases same
  rw [← RecursiveNamedPublicBootstrapGlobals.environment_eq] at read
  obtain ⟨capturedContext, capturedTyped, _bodyTyped⟩ := stored_closure typed read
  obtain ⟨administrative, canonicalTyped⟩ := drop_installer_units cached.index capturedTyped
  have captureLayout : EnvironmentsAgree (shift cached.index)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (List.replicate cached.index (Value.unit) ++ RecursiveNamedCatalogPreparedInitialization.environment compiled) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have frameReference := RecursiveNamedCatalogInitialization.frame_reference compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  have frameRead := RecursiveNamedCatalogInitialization.frame_read compiled.indexed.base.globals
    (RecursiveNamedCachedRows.rows compiled) compiled.indexed.ancestry.layout.frame
  have frameType : world[0]? = some compiled.indexed.ancestry.layout.frame.type := by
    rw [typed.world_eq, List.getElem?_map]
    change Option.map Value.type ((RecursiveNamedCatalogPreparedInitialization.store compiled).read? 0) = _
    change Option.map Value.type ((initialStore compiled.indexed.base.globals (RecursiveNamedCachedRows.rows compiled) compiled.indexed.ancestry.layout.frame).read? 0) = _
    rw [frameRead]
    rfl
  have globalReference := RecursiveNamedCatalogInitialization.global_reference compiled.indexed.base.globals
    compiled.indexed.ancestry.layout.frame (CallableIndexedPreparedInventories.cached_global_at compiled cached.selected)
  let installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := sourceBody (compiled := compiled) (method := method))
      (administrative := administrative) functions [] world ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled) := {
    canonical := RecursiveNamedCatalogPreparedInitialization.environment compiled
    captured := List.replicate cached.index (Value.unit) ++ RecursiveNamedCatalogPreparedInitialization.environment compiled
    capturedContext := capturedContext, embedding := shift cached.index
    environments := .nil canonicalTyped
    locals := by rw [localsEmpty]; exact .nil
    captureLayout := captureLayout, captureTyped := capturedTyped
    frameLocation := 0, canonicalReference := frameReference, capturedReference := captureLayout frameReference
    unmapped := by simp, frameTyped := frameType
    current := .empty, currentGhost := .empty, caller := ⟨frameRead, .stable .empty⟩
    records := [], snapshots := by simp [CallableIndexedSnapshots.All]
    globalIndex := cached.index
    globalLocation := RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals cached.index
    globalUnmapped := by simp, globalReference := globalReference, globalRead := by simpa only [installedValue, Store.read?] using read }
  exact ⟨administrative, installed, rfl, rfl, rfl, rfl⟩

/-- Actual preparation and the whole Source method selector construct this
capture packet without a body execution or arbitrary captured-slot premise. -/
theorem of_selected {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ world, Nonempty (BootstrapCapture cached dictionary functions world) := by
  obtain ⟨world, typed⟩ := RecursiveNamedCatalogPreparedInitialization.typed accepted
  obtain ⟨_types, _context, _facts, certified, _valid⟩ := CallablePreparedMethodSelection.selected_typed selected wellFormed
  obtain ⟨administrative, installed, canonical, captured, embedding, frame⟩ :=
    installed_of_typed cached functions typed certified.locals_empty
  refine ⟨world, ⟨⟨administrative, installed, cached.frame selected, canonical, captured, embedding, frame, ?_⟩⟩⟩
  intro header
  rw [canonical]
  exact CallableIndexedOwnedNamedHeaderReceipts.bootstrap_slot header

/-- An actual bootstrap owner's complete location association identifies the
same canonical slots. Physical pool ownership alone cannot supply this map. -/
theorem BootstrapCapture.globals_for_owner {world : StoreTyping}
    (capture : BootstrapCapture cached dictionary functions world)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (locations : ∀ header, header ∈ headers → owner.key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot) :
    CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] capture.installed.canonical := by
  intro header member
  simpa only [List.length_nil, Nat.zero_add, locations header member] using capture.globals header

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCaptureReceipts
