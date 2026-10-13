import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders

/-! Ordinary named entries can use the same complete physical capture as
methods. The actual Header and cached lambda retain Source provenance; the
canonical environment is the literal installed one with all physical slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPhysicalGlobals RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open CallableIndexedOwnedFunctionValues (Header Key NamedCapture)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {key : Key compiled program}
  {header : Header compiled program} {mapping : LocationMap} {world : StoreTyping} {store : Store}

/-- The genuine initialized owner keeps one frame and the physical locations
of every ordinary semantic header in its catalog. -/
structure KeyPhysical (key : Key compiled program) (headers : List (Header compiled program)) : Prop where
  frame : key.frameLocation = 0
  prefixZero : key.capturePrefix = 0
  locations : ∀ target, target ∈ headers → key.locations target = location compiled target.slot

structure Capture (headers : List (Header compiled program)) (key : Key compiled program)
    (header : Header compiled program) (mapping : LocationMap) (world : StoreTyping) (store : Store) where
  keyPhysical : KeyPhysical key headers
  named : NamedCapture headers key header mapping world
  read : store.read? (key.locations header) = some (.inRight .unit
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename named.embedding.lift) named.captured))
  canonical_eq : named.canonical = environment compiled
  captured_eq : named.captured = List.replicate header.slot .unit ++ environment compiled
  embedding_eq : named.embedding = shift header.slot
  slots : Slots compiled 0 [] named.canonical

theorem of_cached
    (member : header ∈ headers)
    (frameZero : key.frameLocation = 0) (prefixZero : key.capturePrefix = 0)
    (locations : ∀ target, target ∈ headers → key.locations target = location compiled target.slot)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code))
    (physical : Authority compiled mapping store)
    (typed : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Nonempty (Capture headers key header mapping world store) := by
  obtain ⟨_unmapped, read⟩ := physical.cached cached
  obtain ⟨capturedContext, capturedTyped, _bodyTyped⟩ := stored_closure typed read
  obtain ⟨administrative, canonicalTyped⟩ := drop_installer_units header.slot capturedTyped
  have layout : EnvironmentsAgree (shift header.slot) (environment compiled)
      (List.replicate header.slot .unit ++ environment compiled) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have frameReference := RecursiveNamedCatalogInitialization.frame_reference compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  change (RecursiveNamedCatalogPreparedInitialization.environment compiled)[compiled.indexed.base.globals.length]? = _ at frameReference
  rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at frameReference
  let named : NamedCapture headers key header mapping world := {
    administrative := administrative, canonical := environment compiled
    captured := List.replicate header.slot .unit ++ environment compiled
    capturedContext := capturedContext, embedding := shift header.slot
    environments := .nil canonicalTyped, layout := layout, typed := capturedTyped
    reference := by simpa only [globals, frameZero] using frameReference
    capturedReference := by simpa only [frameZero] using layout frameReference
    coherent := by
      intro target targetMember
      rw [prefixZero, locations target targetMember]
      simpa only [List.length_nil, Nat.zero_add] using environment_slots compiled target.slot target.named.signature
        (CallableIndexedPreparedInventories.cached_global_at compiled target.selected) }
  refine ⟨⟨⟨frameZero, prefixZero, locations⟩, named, ?_, rfl, rfl, rfl, environment_slots compiled⟩⟩
  simpa only [locations header member] using read

/-- An actual prepared inventory row supplies the exact cache equation and all
header alignment; callers do not separately assume a cached body. -/
theorem of_headerAt
    {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {key : Key compiled (Program.ofChecked compiled.sourceProgram)}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (member : header ∈ headers) (keyPhysical : KeyPhysical key headers)
    (physical : Authority compiled mapping store)
    (typed : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Nonempty (Capture headers key header mapping world store) := by
  have cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code) := by
    rw [aligned.slot, aligned.named, aligned.code]
    exact prepared.cached.trans (congrArg some prepared.compilation.emitted)
  exact of_cached member keyPhysical.frame keyPhysical.prefixZero keyPhysical.locations
    aligned.globals cached physical typed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures
