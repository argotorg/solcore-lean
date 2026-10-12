import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads

/-! The actual named packet determines the compiler's used administrative
prefix. Truncating only the canonical view preserves every global, the argument
bundle and the original frame, with the same owned pool and runtime environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open RecursiveNamedLambdaFormationHeads (nativePrefix)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  {administrative : Core.Context} {environment : Dynamic.Environment}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)

include packet complete related in
/-- Only actual bundle/global/frame observations determine this prefix. -/
theorem entry_prefix : NativeExpressionContextSupport.Agrees
    (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) header).length (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) header) administrative := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero =>
    have bundle := packet.bundle
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
      obtain ⟨target, member, sameSlot, sameSignature⟩ := complete slot signature selected
      have found := packet.globals target member
      have atType := tag found
      rw [sameSlot] at atType
      have outside : ¬ scope.length + 1 + slot < scope.length := by omega
      have offset : scope.length + 1 + slot - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, sameSignature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag packet.reference
      have outside : ¬ scope.length + 1 + compiled.indexed.base.globals.length < scope.length := by omega
      have offset : scope.length + 1 + compiled.indexed.base.globals.length - scope.length = compiled.indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType

include packet in
/-- The retained prefix contains each genuine catalog slot and the frame.
The pool itself is identical, since canonical views do not index its contents. -/
theorem packet_take
    (slots : ∀ target, target ∈ headers → target.slot < compiled.indexed.base.globals.length) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner header
      ⟨scope, mapping, world, heap, store,
        canonical.take (scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) header).length)⟩ initial := by
  have observed := (packet.observed owner header).take
    (count := scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) header).length)
    (by
      intro target member
      have bound := slots target member
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega)
    (by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega)
  refine ⟨observed.globals, observed.reference, ?_, packet.carried⟩
  rw [List.map_take, List.getElem?_take, if_pos]
  · exact packet.bundle
  · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix
