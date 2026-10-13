import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState

/-! Actual captured slot references determine the complete administrative prefix,
including method rows. Ordinary Source headers remain a separate subset. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues RecursiveNamedCatalog
open RecursiveNamedLambdaFormationHeads CallableIndexedOwnedPhysicalGlobals
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {scope : SourceCoreLocalCell.Scope}

theorem entry_prefix_for
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    {context : Core.Context} {environment : Dynamic.Environment}
    (allSlots : Slots compiled 1 scope canonical)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world context scope environment canonical compiled.indexed.layouts.definitions) :
    NativeExpressionContextSupport.Agrees (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller).length (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller) context := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext scope ++ context)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero =>
    have bundle := entry.bundle
    rw [typed] at bundle
    simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append] using bundle
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map,
        List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature := List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      have found := allSlots slot signature selected
      have atType := tag found
      have outside : ¬ scope.length + 1 + slot < scope.length := by omega
      have offset : scope.length + 1 + slot - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag entry.reference
      rw [globals] at atType
      have outside : ¬ scope.length + 1 + compiled.indexed.base.globals.length < scope.length := by omega
      have offset : scope.length + 1 + compiled.indexed.base.globals.length - scope.length = compiled.indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType


def captures_for
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (allSlots : Slots compiled 1 scope canonical)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world context scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    Captures compiled.indexed mapping world scope environment actual := by
  let represented := environments_prefix related (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller) (entry_prefix_for allSlots globals entry related)
  let same : EnvironmentsAgree ξ (canonical.take (scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller).length)) actual :=
    agrees_prefix agrees (scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller).length)
  exact {
    administrative := nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller
    canonical := canonical.take (scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller).length)
    actualContext := actualContext
    embedding := ξ
    represented := represented
    agrees := same
    respects := TypedLexicalWhile.environment_respects represented.runtime_hasTypes typed same
    typed := typed }


theorem capture_globals_for
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (allSlots : Slots compiled 1 scope canonical)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world context scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope
      (captures_for allSlots globals entry related agrees typed).canonical entry.catalog.authority.frameLocation := by
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope canonical
      entry.catalog.authority.frameLocation :=
    ⟨entry.catalog.globals, by simpa only [globals] using entry.reference⟩
  apply observed.take
  · intro header member
    have bound := slots header member
    simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega


theorem capture_slots_for
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (allSlots : Slots compiled 1 scope canonical)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world context scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    Slots compiled 1 scope (captures_for allSlots globals entry related agrees typed).canonical := by
  intro slot signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have within : scope.length + 1 + slot <
      scope.length + (nativePrefix (values := .initial compiled.compatible.checked)
        (indexed := compiled.indexed) caller).length := by
    simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  change (canonical.take _)[_]? = _
  rw [List.getElem?_take, if_pos within]
  exact allSlots slot signature found

/-- The real parameter spine prepends local cells to the same captured suffix. -/
theorem append_locals {callerPrefix : Nat} {capturedScope parameterScope : SourceCoreLocalCell.Scope}
    {captured added : Environment}
    (slots : Slots compiled callerPrefix capturedScope captured)
    (length : added.length = parameterScope.length) :
    Slots compiled callerPrefix (parameterScope ++ capturedScope) (added ++ captured) := by
  intro slot signature found
  have outside : added.length ≤ (parameterScope ++ capturedScope).length + callerPrefix + slot := by
    simp only [List.length_append]
    omega
  rw [List.getElem?_append_right outside]
  have offset : (parameterScope ++ capturedScope).length + callerPrefix + slot - added.length =
      capturedScope.length + callerPrefix + slot := by
    simp only [List.length_append]
    omega
  rw [offset]
  exact slots slot signature found

/-- Actual frame installation and parameter allocation retain the complete cache
and the exact captured global references in the stronger caller state. -/
def of_closure_spine
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {mapping : LocationMap} {store : Store} {frameLocation : Location} {native : NativeFrame}
    (physical : Authority compiled mapping store)
    (frameRead : store.read? frameLocation = some
      (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (next : NativeFrame) {index : ProtectedStateTransition.Index}
    (frame : AdministrativePreserved mapping
      (store.set frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))
      index.mapping index.store)
    (pool : CallableIndexedOwnedFunctionState.State headers keys index)
    {capturedScope parameterScope : SourceCoreLocalCell.Scope} {captured added : Environment}
    (slots : Slots compiled 1 capturedScope captured)
    (length : added.length = parameterScope.length)
    (scopeEq : index.scope = parameterScope ++ capturedScope)
    (spine : index.canonical = added ++ captured) :
    (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State index :=
  ⟨⟨pool, by rw [scopeEq, spine]; exact append_locals slots length⟩,
    (physical.install frameRead next).extend frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
