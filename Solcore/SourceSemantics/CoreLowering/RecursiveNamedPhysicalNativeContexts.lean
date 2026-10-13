import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalGlobals

/-! Native context transport requires every physical reference type, while
ordinary Source headers serve a separate semantic purpose. This interface
accepts genuine complete physical slots and retains the old inventory adapter. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPhysicalNativeContexts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts NativeExpressionContextSupport

def Layout (globals : List SourceCoreCalls.Signature) (offset : Nat) (canonical : Environment) : Prop :=
  ∀ slot signature, globals[slot]? = some signature →
    ∃ location, canonical[offset + slot]? = some
      (.cellRef (OptionalCell.cellType signature.functionType) location)

theorem Layout.of_physical {compiled : SourceCoreUnifiedCompilation.Compiled}
    {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix scope canonical) :
    Layout compiled.indexed.base.globals (scope.length + callerPrefix) canonical := by
  intro slot signature found
  exact ⟨_, slots slot signature found⟩

/-- Runtime tags establish only the used native prefix. They provide no Source
function, parameter representation or method implementation selection. -/
theorem administrative_prefix {globals : List SourceCoreCalls.Signature}
    {locals administrative : Core.Context} {canonical : Environment} {bundle frameType : Ty}
    {frameLocation : Location}
    (types : canonical.map Value.type = locals ++ administrative)
    (packed : (canonical.map Value.type)[locals.length]? = some bundle)
    (slots : Layout globals (locals.length + 1) canonical)
    (frame : canonical[locals.length + 1 + globals.length]? = some (.cellRef frameType frameLocation)) :
    Agrees (bundle :: globals.map SourceCoreCalls.Signature.referenceType ++ [Ty.cell frameType]).length
      (bundle :: globals.map (·.referenceType) ++ [.cell frameType]) administrative := by
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (locals ++ administrative)[index]? = some value.type := by
    rw [← types]
    simp [found]
  intro index smaller
  cases index with
  | zero =>
    rw [types] at packed
    simpa [List.getElem?_append] using packed
  | succ slot =>
    have bound : slot < globals.length + 1 := by simp at smaller; omega
    by_cases globalSlot : slot < globals.length
    · let signature := globals[slot]
      have selected : globals[slot]? = some signature := List.getElem?_eq_getElem globalSlot
      obtain ⟨location, found⟩ := slots slot signature selected
      have atType := tag found
      have outside : ¬ locals.length + 1 + slot < locals.length := by omega
      have offset : locals.length + 1 + slot - locals.length = slot + 1 := by omega
      simpa [List.getElem?_append, outside, offset, globalSlot, selected, signature,
        SourceCoreCalls.Signature.referenceType, OptionalCell.referenceType, Value.type] using atType
    · have last : slot = globals.length := by omega
      have atType := tag frame
      have outside : ¬ locals.length + 1 + globals.length < locals.length := by omega
      have offset : locals.length + 1 + globals.length - locals.length = globals.length + 1 := by omega
      simpa [List.getElem?_append, outside, offset, last, Value.type] using atType

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {header : Header prepared values ambient.definitions program}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}

/-- Legacy complete ordinary inventories still provide exactly this native
layout; their Source headers are not required by the new transport theorem. -/
theorem layout_of_complete (complete : Complete headers)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    Layout base.globals ((bodyScope header).length + 1) entry.canonical := by
  intro slot signature selected
  obtain ⟨target, member, sameSlot, sameSignature⟩ := complete slot signature selected
  have found := entry.catalog.globals target member
  refine ⟨locations target, ?_⟩
  change entry.canonical[(bodyScope header).length + (0 + 1) + target.slot]? = _ at found
  simpa only [sameSlot, sameSignature] using found

theorem entry_prefix
    (globals : header.globals = base.globals.length)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (slots : Layout base.globals ((bodyScope header).length + 1) entry.canonical)
    (suffix : Core.Context) :
    Agrees (bodyPrefix header).length (bodyPrefix header ++ suffix)
      (SourceCoreLocalCell.coreContext (bodyScope header) ++
        SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) := by
  let localTypes := SourceCoreLocalCell.coreContext (bodyScope header)
  let bundle := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd)
  have localLength : localTypes.length = header.bindings.length := by
    simp [localTypes, SourceCoreLocalCell.coreContext, bodyScope]
  have tag {index : Nat} {value : Value} (found : entry.canonical[index]? = some value) :
      (localTypes ++ bundle :: administrative)[index]? = some value.type := by
    have types := entry.environments.runtime_hasTypes.type_tags
    change entry.canonical.map Value.type = localTypes ++ bundle :: administrative at types
    rw [← types]
    simp [found]
  intro index smaller
  change (localTypes ++ bundle :: administrative)[index]? =
    (localTypes ++ bundle :: base.globals.map (·.referenceType) ++ [.cell prepared.layout.frame.type] ++ suffix)[index]?
  by_cases localSlot : index < localTypes.length
  · simp [List.getElem?_append, localSlot]
  · let offset := index - localTypes.length
    have indexEq : index = localTypes.length + offset := by omega
    rw [indexEq]
    have prefixLength : (bodyPrefix header).length = localTypes.length + base.globals.length + 2 := by simp [bodyPrefix, localTypes]; omega
    rw [prefixLength] at smaller
    have offsetBound : offset < base.globals.length + 2 := by omega
    cases offsetEq : offset with
    | zero => simp [List.getElem?_append]
    | succ slot =>
      have bound : slot < base.globals.length + 1 := by omega
      have outside : ¬ localTypes.length + (slot + 1) < localTypes.length := by omega
      by_cases globalSlot : slot < base.globals.length
      · let signature := base.globals[slot]
        have selected : base.globals[slot]? = some signature := List.getElem?_eq_getElem globalSlot
        obtain ⟨location, found⟩ := slots slot signature selected
        have idx : (bodyScope header).length + 1 + slot = localTypes.length + (slot + 1) := by
          simp only [bodyScope, List.length_map, List.length_reverse, localLength]; omega
        have typed := tag found
        rw [idx] at typed
        simpa [List.getElem?_append, outside, globalSlot, selected, signature,
          SourceCoreCalls.Signature.referenceType, OptionalCell.referenceType, Value.type] using typed
      · have last : slot = base.globals.length := by omega
        have typed := tag entry.reference
        have idx : header.bindings.length + 1 + header.globals = localTypes.length + (slot + 1) := by omega
        rw [idx] at typed
        simpa [List.getElem?_append, outside, last, Value.type] using typed

theorem canonical_body {suffix : Core.Context}
    (globals : header.globals = base.globals.length)
    (typed : HasType (bodyPrefix header ++ suffix) header.body (LanguageResult.resultType header.output) ambient.definitions)
    (support : supported header.body (bodyPrefix header).length = true)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (slots : Layout base.globals ((bodyScope header).length + 1) entry.canonical) :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions :=
  typing typed support (entry_prefix globals entry slots suffix)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPhysicalNativeContexts
