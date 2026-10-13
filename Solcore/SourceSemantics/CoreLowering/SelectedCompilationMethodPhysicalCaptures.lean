import Solcore.SourceSemantics.SelectedOperatorTypingCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPhysicalCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCaptureReceipts

/-! Selected methods recover their authentic installed captures at the reached
heap. Complete physical cache authority supplies native code; the independent
operator selector supplies the method Source frame and dictionary. The current
owner supplies the live frame and full ordered snapshots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPhysicalCaptures
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

open CallableIndexedOwnedMethodPhysicalCaptures (sourceBody Capture)

theorem of_certificate
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
    (certificate : ∃ types lexical facts,
      Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (sourceBody (compiled := compiled) (method := method)) types lexical facts)
    :
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
  obtain ⟨_types, _context, _facts, certified⟩ := certificate
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

theorem of_typed
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
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    :
    Nonempty (Capture cached dictionary functions mapping world heap store caller) := by
  apply of_certificate cached dictionary functions owner pool ownerFrame physical typed slots selected.selected
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ certificate =>
    obtain ⟨types, lexical, facts, certified⟩ := certificate
    exact ⟨types, lexical, facts, certified.toBodyInstanceTypingCertificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPhysicalCaptures
