import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! Selection uses the exact shared function model at the actual successful
callee post. Compatible payload wrappers retain the original raw Source type
view. The same reached state supplies Source value typing and all owned rows;
no model inclusion is inverted and no runtime traversal is introduced. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedObservedGeneralCallee
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {function : Dynamic.Closure} {native : Value} {type : Ty}

/-- The selected raw function type and complete provenance describe the same
Source closure and native value at the original reached map and world. -/
def Selected : Prop :=
  ∃ parameter result,
    SourceCoreRawMetadata.runtimeType raw = SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (.function parameter result) (.closure function) native type

private theorem selected_of_representation {raw : TypeSystem.Ty} {sourceValue : Dynamic.Value}
    (related : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world raw sourceValue native type) (closure : sourceValue = .closure function) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit => cases closure
  | bool => cases closure
  | word => cases closure
  | integer => cases closure
  | product => cases closure
  | proxy => cases closure
  | constructed => cases closure
  | mappingValue => cases closure
  | function value =>
    cases closure
    exact ⟨_, _, rfl, CallableIndexedOwnedGeneralFunctionSelection.of_model profile value⟩
  | compatible same inner ih =>
    obtain ⟨parameter, result, view, selected⟩ := ih closure
    exact ⟨parameter, result, same.trans view, selected⟩
  | nil | cons | empty | entry | absent | present => trivial

/-- Only compatible representation wrappers are traversed. The function leaf
uses the exact model relation, retaining every original selected receipt. -/
theorem of_representation
    (related : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) :=
  selected_of_representation profile related rfl

universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)
  {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)

/-- Real successful callee admission pairs complete selected provenance with
original Source typing and the actual reached owned pool. No captured history
is substituted for the current row and no argument/body meaning is assumed. -/
theorem at_success
    (post : PostAdmission bridge context raw (.value (.closure function)) reached)
    (related : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      index.mapping index.world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := index.mapping) (world := index.world) (raw := raw)
      (function := function) (native := native) (type := type) ∧
    Dynamic.ValueHasType context index.heap (.closure function) raw ∧ Admission bridge context reached := by
  exact ⟨of_representation (profile := profile) related, post.at_value⟩

/-- At an ordinary raw function type, the original Source post exposes exact
parameter/result types, complete code validity and capture agreement at this
same heap. These facts are independent of the selected native type vector. -/
theorem at_function_success {parameter result : TypeSystem.Ty}
    (post : PostAdmission bridge context (.function parameter result) (.value (.closure function)) reached)
    (related : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      index.mapping index.world (.function parameter result) (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := index.mapping) (world := index.world) (raw := .function parameter result)
      (function := function) (native := native) (type := type) ∧
    Admission bridge context reached ∧
    parameter = TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)) ∧
    result = function.resultType ∧
    function.context.signatures = context.signatures ∧
    Dynamic.ClosureCodeValid function.context function ∧
    function.evidence.Covers function.context ∧
    Dynamic.EnvironmentAgrees index.heap function.context.locals function.captured := by
  obtain ⟨selected, typed, admitted⟩ := at_success profile bridge context reached post related
  exact ⟨selected, admitted, typed.closure_function_inv⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedObservedGeneralCallee
