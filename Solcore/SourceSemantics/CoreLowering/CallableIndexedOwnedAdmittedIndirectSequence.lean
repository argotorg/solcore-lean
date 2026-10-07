import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence

/-! Admitted ordered arguments instantiate the neutral selected-call sequence
providers at their exact real input. The original Source typing row is independent
of the compiler parameter type vector. The same reached witness and relation
survive when the extra admission receipt is forgotten. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedIndirectSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {callerScope : SourceCoreLocalCell.Scope}
  {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  {originalSourceTypes : List TypeSystem.Ty}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (receipt : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)
  (children : DataExpressionSequence.Tree source certificate callerScope ids
    (receipt.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) codes)
  (unique : NodeOccurrencesUnique source)
  (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative callerScope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (initial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include receipt children unique typing environments heaps locals agrees typed admitted in
/-- Both original Source sequence outcomes use the actual admitted input. Success
and fault discard only the extra post receipt, retaining the identical state. -/
theorem preserves (budget : Nat)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults size) :
    SequencePreserves (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := receipt) (codes := codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) initial budget := by
  constructor
  · intro size arguments after execution bounded
    obtain ⟨payloads, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget children unique typing meaning
        environments heaps locals
        (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
        (.cons .unit (.cons receipt.typed typed)) initial admitted execution bounded
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
    exact ⟨payloads, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩
  · intro size reason after execution bounded
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_fault_bounded bridge budget children unique typing meaning
        environments heaps locals
        (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
        (.cons .unit (.cons receipt.typed typed)) initial admitted execution bounded
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩

include receipt children unique typing environments heaps locals agrees typed admitted in
/-- Native completion keeps its independent Source grade and the same actual
success or fault post; only the additional admission packet is forgotten. -/
theorem reflects (budget : Nat)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults size) :
    SequenceReflects (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := receipt) (codes := codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) initial budget := by
  intro size value finalStore evaluated bounded
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget children unique typing meaning
      environments heaps locals
      (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
      (.cons .unit (.cons receipt.typed typed)) initial admitted evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedIndirectSequence
