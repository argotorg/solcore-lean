import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFormationReceipts

/-! A genuine method-principal packet fixes its captured native bundle,
globals and frame prefix at the real input environment. Source locations remain
related independently by EnvRepresents. Prefix capture retains the original
full native environment and the identical underlying owned pool. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalCaptures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open RecursiveNamedLambdaFormationHeads (environments_prefix agrees_prefix)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named _ initial)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)

/-- These are precisely the compiler's method bundle, globals and frame slots. -/
def nativePrefix : Core.Context :=
  principal.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
    [.cell compiled.indexed.ancestry.layout.frame.type]

include packet complete related in
/-- Actual environment tags identify only the genuine used native prefix.
Source authority remains the independent principal and packet history. -/
theorem entry_prefix_at : NativeExpressionContextSupport.Agrees
    (nativePrefix principal).length (nativePrefix principal) administrative := by
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

include packet complete related agrees typed in
/-- Capture construction retains all actual native captures, their typing and
embedding. Only canonical unused administrative suffixes are projected away. -/
def captures : Captures compiled.indexed mapping world scope environment actual := by
  let represented := environments_prefix related (nativePrefix principal)
    (entry_prefix_at principal owner initial packet complete related)
  let same : EnvironmentsAgree ξ (canonical.take (scope.length + (nativePrefix principal).length)) actual :=
    agrees_prefix agrees (scope.length + (nativePrefix principal).length)
  exact {
    administrative := nativePrefix principal
    canonical := canonical.take (scope.length + (nativePrefix principal).length)
    actualContext := actualContext
    embedding := ξ
    represented := represented
    agrees := same
    respects := TypedLexicalWhile.environment_respects represented.runtime_hasTypes typed same
    typed := typed }

include packet complete related agrees typed in
/-- The real global/frame observations remain inside the canonical prefix. -/
theorem captured_globals
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope
      (captures principal owner initial packet complete related agrees typed).canonical owner.key.frameLocation := by
  apply packet.observed.take
  · intro header member
    have bound := slots header member
    simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega

include packet complete related agrees typed in
/-- The exact original pool acquires only the projected canonical observations;
its carried metadata and every original ordered row remain identical. -/
theorem captured_packet
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named
      ⟨scope, mapping, world, heap, store,
        (captures principal owner initial packet complete related agrees typed).canonical⟩ initial := by
  have observed := captured_globals principal owner initial packet complete related agrees typed slots
  refine ⟨observed.globals, observed.reference, ?_, packet.carried⟩
  have tags := (captures principal owner initial packet complete related agrees typed).represented.runtime_hasTypes.type_tags
  rw [tags]
  change (SourceCoreLocalCell.coreContext scope ++ nativePrefix principal)[scope.length]? = some principal.named.signature.parameterType
  simpa [SourceCoreLocalCell.coreContext, List.getElem?_append] using
    (show (nativePrefix principal)[0]? = some principal.named.signature.parameterType from rfl)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalCaptures
