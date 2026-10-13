import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCaptureReceipts

/-! Selected methods recover their authentic installed captures at the reached
heap. Complete physical cache authority supplies native code; the independent
operator selector supplies the method Source frame and dictionary. The current
owner supplies the live frame and full ordered snapshots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPhysicalCaptures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallablePreparedMethodRuntimeMeaning
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open CallableIndexedOwnedPhysicalGlobals

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
  (dictionary : Dynamic.EvidenceEnvironment)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

abbrev sourceBody := CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method

structure Capture (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap)
    (store : Store) (caller : Environment) where
  administrative : Core.Context
  installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := sourceBody (compiled := compiled) (method := method))
    (administrative := administrative) functions mapping world heap store caller
  sourceFrame : CallableCoercionMethodFrame.Frame (sourceBody (compiled := compiled) (method := method))
    (methodFunction cached.compilation (sourceBody (compiled := compiled) (method := method)) dictionary)
  canonical_eq : installed.canonical = environment compiled
  captured_eq : installed.captured = List.replicate cached.index .unit ++ environment compiled
  embedding_eq : installed.embedding = shift cached.index
  frame_eq : installed.frameLocation = 0

theorem of_selected
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {scope : SourceCoreLocalCell.Scope} {caller : Environment} {callerPrefix : Nat}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (pool : CallableIndexedOwnedFunctionState.State headers keys ⟨scope, mapping, world, heap, store, caller⟩)
    (ownerFrame : owner.key.frameLocation = 0)
    (physical : Authority compiled mapping store)
    (typed : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (slots : Slots compiled callerPrefix scope caller)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (Capture cached dictionary functions mapping world heap store caller) := by
  have cachedCode : compiled.indexed.secondPass.closures[cached.index]? = some
      (.lambda cached.named.signature.parameterType (LanguageResult.resultType cached.named.signature.resultType) cached.compilation.output) := by
    simpa only [cached.compilation.emitted] using cached.cached
  obtain ⟨globalUnmapped, globalRead⟩ := physical.cached cachedCode
  obtain ⟨capturedContext, capturedTyped, _bodyTyped⟩ := stored_closure typed globalRead
  obtain ⟨administrative, canonicalTyped⟩ := drop_installer_units cached.index capturedTyped
  have captureLayout : EnvironmentsAgree (shift cached.index) (environment compiled)
      (List.replicate cached.index .unit ++ environment compiled) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have frameReference := RecursiveNamedCatalogInitialization.frame_reference compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  change (RecursiveNamedCatalogPreparedInitialization.environment compiled)[compiled.indexed.base.globals.length]? = _ at frameReference
  rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at frameReference
  let row := pool.rows owner.position
  have frameEq : row.authority.frameLocation = 0 := row.frame_eq.trans ownerFrame
  have frameType := row.authority.typed
  have unmapped := row.authority.unmapped
  have frame := row.authority.frame
  rw [frameEq] at frameType unmapped frame
  obtain ⟨_types, _context, _facts, certified, _valid⟩ := CallablePreparedMethodSelection.selected_typed selected wellFormed
  let installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := sourceBody (compiled := compiled) (method := method))
      (administrative := administrative) functions mapping world heap store caller := {
    canonical := environment compiled
    captured := List.replicate cached.index .unit ++ environment compiled
    capturedContext := capturedContext, embedding := shift cached.index
    environments := .nil canonicalTyped
    locals := by rw [certified.locals_empty]; exact .nil
    captureLayout := captureLayout, captureTyped := capturedTyped
    frameLocation := 0, canonicalReference := frameReference, capturedReference := captureLayout frameReference
    unmapped := unmapped, frameTyped := frameType
    current := row.authority.current, currentGhost := row.authority.ghost, caller := frame
    records := row.authority.records, snapshots := row.authority.snapshots
    globalIndex := scope.length + callerPrefix + cached.index
    globalLocation := location compiled cached.index
    globalUnmapped := globalUnmapped
    globalReference := slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled cached.selected)
    globalRead := globalRead }
  exact ⟨⟨administrative, installed, cached.frame selected, rfl, rfl, rfl, rfl⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPhysicalCaptures
