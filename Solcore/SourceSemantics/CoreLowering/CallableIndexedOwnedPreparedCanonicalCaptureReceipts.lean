import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! Authentic canonical bundle/global/frame observations and EnvRepresents
construct the used capture prefix. The owner's complete capture prefix and
ordered pool stay intact. Source history comes from the actual Nested or
Principal packet; native tags identify only the corresponding prefix types.
The selected method Site must separately match this prefix. No arbitrary
native environment or bare pool acquires Source authority here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalCaptureReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration (Named)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}

def «prefix» (named : Named) : Core.Context :=
  named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
    [.cell compiled.indexed.ancestry.layout.frame.type]

variable (named : Named) (owner : OwnedKey keys)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope canonical owner.key.frameLocation)
  (bundle : (canonical.map Value.type)[scope.length]? = some named.signature.parameterType)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)

include complete observed bundle related in
/-- Every used slot follows the real packet and finite compiled inventory.
No global closure authority is cast to a different capture-prefix index. -/
theorem prefix_agrees : NativeExpressionContextSupport.Agrees
    («prefix» (compiled := compiled) named).length («prefix» (compiled := compiled) named) administrative := by
  have tags := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? = some value.type := by
    rw [← tags]
    simp [found]
  intro index smaller
  cases index with
  | zero =>
    rw [tags] at bundle
    simpa [SourceCoreLocalCell.coreContext, «prefix», List.getElem?_append] using bundle
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [«prefix», List.length_cons, List.length_append, List.length_map, List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature :=
        List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      obtain ⟨target, member, sameSlot, sameSignature⟩ := complete slot signature selected
      have atType := tag (observed.globals target member)
      rw [sameSlot] at atType
      have outside : ¬ scope.length + 1 + slot < scope.length := by omega
      have offset : scope.length + 1 + slot - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, «prefix», List.getElem?_append, outside, offset,
        globalSlot, selected, signature, sameSignature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag observed.reference
      have outside : ¬ scope.length + 1 + compiled.indexed.base.globals.length < scope.length := by omega
      have offset : scope.length + 1 + compiled.indexed.base.globals.length - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, «prefix», List.getElem?_append, outside, offset,
        last, Value.type] using atType

include complete observed bundle related agrees typed in
/-- Only the used canonical administrative suffix is shortened. The complete
actual environment, Source cells, embedding and runtime typing stay original. -/
def capture : Captures compiled.indexed mapping world scope environment actual := by
  let represented := RecursiveNamedLambdaFormationHeads.environments_prefix related («prefix» (compiled := compiled) named)
    (prefix_agrees named owner complete observed bundle related)
  let same : EnvironmentsAgree ξ (canonical.take (scope.length + («prefix» (compiled := compiled) named).length)) actual :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix agrees (scope.length + («prefix» (compiled := compiled) named).length)
  exact {
    administrative := «prefix» (compiled := compiled) named
    canonical := canonical.take (scope.length + («prefix» (compiled := compiled) named).length)
    actualContext := actualContext, embedding := ξ, represented := represented, agrees := same
    respects := TypedLexicalWhile.environment_respects represented.runtime_hasTypes typed same
    typed := typed }

/-- Original finite slot bounds keep every actual global and physical frame
in the capture. No empty catalog or zero owner-prefix assumption is used. -/
theorem capture_globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope (capture named owner complete observed bundle related agrees typed).canonical
    owner.key.frameLocation := by
  apply observed.take
  · intro header member
    have bound := RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers header member
    simp only [«prefix», List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  · simp only [«prefix», List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega

namespace Ordinary
variable (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)

include complete related agrees typed packet in
/-- The exact original packet constructs its own capture; no new state or
semantic capture-producing callback is supplied. -/
def captured : Captures compiled.indexed mapping world scope environment actual :=
  capture caller.named owner complete packet.observed packet.bundle related agrees typed

theorem captured_prefix : (captured owner complete related agrees typed caller initial packet).administrative =
    RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller := rfl

/-- The same owned pool is reindexed only by the shortened canonical suffix.
Its own history and exact ordered rows authenticate the resulting packet. -/
theorem packet_at_capture : CallableIndexedOwnedNestedCanonicalState.Packet owner caller
    ⟨scope, mapping, world, heap, store, (captured owner complete related agrees typed caller initial packet).canonical⟩ initial := by
  exact CallableIndexedOwnedNestedCanonicalState.packet_of_stable_read owner caller
    (canonical := (captured owner complete related agrees typed caller initial packet).canonical) initial
    (capture_globals caller.named owner complete packet.observed packet.bundle related agrees typed)
    (captured owner complete related agrees typed caller initial packet).represented (by rfl)
    packet.carried (CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position)

/-- Source admission keeps its original deep heap and every row's stable
history because the projected pool is definitionally the same witness. -/
theorem admission_at_capture (context : SourceSemantics.Context)
    (admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) context ⟨initial, packet⟩) :
    CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) context
      (index := ⟨scope, mapping, world, heap, store, (captured owner complete related agrees typed caller initial packet).canonical⟩)
      ⟨initial, packet_at_capture owner complete related agrees typed caller initial packet⟩ :=
  ⟨admitted.heap, admitted.rows⟩
end Ordinary

namespace Principal
variable (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner named _ initial)

include complete related agrees typed packet in
/-- The genuine selected Named and its own dictionary-bearing Source seed
remain in the packet. Prefix types do not manufacture that authority. -/
def captured : Captures compiled.indexed mapping world scope environment actual :=
  capture named owner complete packet.observed packet.bundle related agrees typed

theorem captured_prefix : (captured named owner complete related agrees typed initial packet).administrative =
    «prefix» (compiled := compiled) named := rfl

/-- Matching a selected method Site's administrative context to this prefix
remains an authentic static producer obligation; this proof keeps only the
same existing pool and its original Principal history. -/
theorem packet_at_capture : CallableIndexedOwnedOriginCanonicalState.Packet owner named
    ⟨scope, mapping, world, heap, store, (captured named owner complete related agrees typed initial packet).canonical⟩ initial := by
  exact CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner named
    (canonical := (captured named owner complete related agrees typed initial packet).canonical) initial
    (capture_globals named owner complete packet.observed packet.bundle related agrees typed)
    (captured named owner complete related agrees typed initial packet).represented (by rfl)
    packet.carried (CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position)

theorem admission_at_capture (context : SourceSemantics.Context)
    (admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner named) context ⟨initial, packet⟩) :
    CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner named) context
      (index := ⟨scope, mapping, world, heap, store, (captured named owner complete related agrees typed initial packet).canonical⟩)
      ⟨initial, packet_at_capture named owner complete related agrees typed initial packet⟩ :=
  ⟨admitted.heap, admitted.rows⟩
end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalCaptureReceipts
