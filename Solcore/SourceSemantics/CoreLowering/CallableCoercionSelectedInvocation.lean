import Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectionIdentity
import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEvidenceInvariant

/-! Actual compiler selection fixes the complete independent source body.
An arbitrary selected dictionary is kept unchanged by the body theorem; no
semantic law is stored in the static receipt or runtime Entry. The concrete
body certificate and saved closure/capture authority remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectedInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram} {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {method : MethodProfile (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  {rest : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {callerFunction : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
  {ξ : Renaming} {input output : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input (method :: rest) output calls)

include checkedAccepted ledger emitted in
/-- The complete source body, including context and ordered retained ledger,
is fixed. Actual emitted records and dictionaries are retained by `emitted`. -/
theorem source_body {selectedBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compilerProgram) context evidence "Coerce" "coerce"
      method.step.requirements selectedBody dictionary) : selectedBody = method.sourceBody := by
  cases emitted with
  | cons actual _ _ _ tail =>
    obtain ⟨receipt⟩ := CallableCoercionMethodCertificates.of_accepted actual.selectedMethod
    exact CallableCoercionSelectionIdentity.body_eq (CallableCoercionSelectionIdentity.Catalog.of_checked checkedAccepted)
      (CallableCoercionSelectionIdentity.primary_unique ledger receipt.primarySelected) selected method.selected

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {value : Dynamic.Value} {native : Value}
  (entry : Entry methods ambient.definitions caller mapping world before store)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (represented : ValueRep values.checked registry functions mapping world method.step.source value native method.call.signature.parameterType)

include checkedAccepted ledger emitted extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- Independent selection and body evaluation drive the actual call. Neither
the source body nor the dictionary is required equal to a compiler annotation. -/
theorem preserves {selectedBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compilerProgram) context evidence "Coerce" "coerce"
      method.step.requirements selectedBody dictionary)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : BodyOutcome (Program.ofChecked compilerProgram) selectedBody dictionary before [value] outcome after)
    (reason : Word) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  have same := source_body checkedAccepted ledger emitted selected
  subst selectedBody
  have covers : dictionary.Covers method.sourceBody.context := by
    cases selected with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers => exact covers
  exact CallableCoercionMethodEvidenceInvariant.preserves functions extension definitions registered faithful observations runtimeViews
    uninitialized missing member entry heaps represented dictionary covers trace reason

include checkedAccepted ledger emitted extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- A completed actual call reflects at any independently selected source body
and dictionary. Its source outcome and heap are existential, not identified by
evidence equality or by a source/native fuel comparison. -/
theorem reflects {selectedBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compilerProgram) context evidence "Coerce" "coerce"
      method.step.requirements selectedBody dictionary)
    {result : Value} {finalStore : Store} {reason : Word}
    (completed : CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) result finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome (Program.ofChecked compilerProgram) selectedBody dictionary before [value] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  have same := source_body checkedAccepted ledger emitted selected
  subst selectedBody
  have covers : dictionary.Covers method.sourceBody.context := by
    cases selected with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers => exact covers
  exact CallableCoercionMethodEvidenceInvariant.reflects functions extension definitions registered faithful observations runtimeViews
    uninitialized missing member entry heaps represented dictionary covers completed

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectedInvocation
