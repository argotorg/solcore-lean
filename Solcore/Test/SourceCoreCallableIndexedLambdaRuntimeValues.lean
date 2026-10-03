import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! Static consumers keep the body for the actual generated lambda, including
its source frame and full ledger. Registry extension changes the ghost value
parameter while the runtime model's body registry remains fixed. The existing
actual lambda runtime suite is reused once at whole registration. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaRuntimeValues
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedLambdaValues CallableIndexedLambdaRuntimeValues

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {program : SourceSemantics.Program} {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : values.checked.catalog.callableContracts = true)

theorem actual_observations :
    FunctionObservations values.checked.catalog
      (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile) (Identity prepared) :=
  CallableIndexedLambdaRuntimeValues.observations prepared program bodyRegistry faults profile

theorem actual_runtime_views :
    FunctionRuntimeViews (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile) :=
  CallableIndexedLambdaRuntimeValues.runtime_views prepared program bodyRegistry faults profile

/-- Independent source validity is carried by the body itself. -/
theorem actual_source_frame {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).Represents
      registry mapping world sourceType (.closure function) native type) :
    Dynamic.ClosureFrame program function :=
  CallableIndexedLambdaRuntimeValues.Represents.closure_frame prepared program bodyRegistry faults related

/-- The fixed body registry is still the one named in the receipt, even when
FunctionModel.extend changes its independent ghost registry argument. -/
theorem receipt_after_extension {registry futureRegistry : SourceCoreRawMetadata.Registry}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).Represents
      registry mapping world sourceType (.closure function) native type)
    (registries : SourceCoreRawMetadata.Extends registry futureRegistry)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).Represents
      futureRegistry futureMapping futureWorld sourceType (.closure function) native type ∧
    ∃ scope actual, ∃ (captured : Captures prepared futureMapping futureWorld scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code),
      Nonempty (CallableIndexedLambdaRuntimeBody.Body code program bodyRegistry faults) ∧
      sourceType = FunctionValues.sourceType function ∧
      native = value code captured.embedding history.native actual ∧
      type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  have extended := (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).extend related registries maps worlds
  exact ⟨extended, CallableIndexedLambdaRuntimeValues.Represents.closure_inv prepared program bodyRegistry faults extended⟩

/-- A weak value receipt alone cannot discharge the independent body premise. -/
theorem absent_body_forbids_strong_value {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty}
    (missing : ∀ scope actual (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative),
      ¬ Nonempty (CallableIndexedLambdaRuntimeBody.Body code program bodyRegistry faults)) :
    ¬ (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).Represents
      registry mapping world sourceType (.closure function) native type := by
  intro related
  obtain ⟨scope, actual, captured, code, _, body, _⟩ :=
    CallableIndexedLambdaRuntimeValues.Represents.closure_inv prepared program bodyRegistry faults related
  exact missing scope actual captured code body

abbrev actual_formation := @CallableIndexedLambdaRuntimeValues.formation
abbrev actual_reflection := @CallableIndexedLambdaRuntimeValues.reflects
abbrev accepted_site_formation := @CallableIndexedLambdaRuntimeValues.accepted_site_formation
abbrev accepted_site_reflection := @CallableIndexedLambdaRuntimeValues.accepted_site_reflection
abbrev same_model_preservation := @CallableIndexedLambdaRuntimePreservation.preserves_for
abbrev same_model_reflection := @CallableIndexedLambdaRuntimeEntry.reflects_for

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaRuntimeValues
