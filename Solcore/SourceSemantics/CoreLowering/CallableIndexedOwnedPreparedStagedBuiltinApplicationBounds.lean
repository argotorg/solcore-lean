import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds

/-! A builtin applies at the actual heap and store reached by its arguments.
Ordered scalar representations exclude physical arity and type faults. The
literal contracted primitive runs once and keeps both endpoints unchanged.
Source and Core grades are independent. User applications and their staged
body hypotheses are separate from these three builtin constructors. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open BuiltinBodyMeaning CallableIndexedBuiltinValues BuiltinCalls
open CallableIndexedOwnedFunctionState
universe u

private theorem payload_evaluates {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (inputs : InputRep function arguments input)
    (identity contract : Word) (captured : Environment) (store : Store) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates [BuiltinCalls.Protocol.contractedValue function identity contract captured, input]
        store CallableIndexedLambdaCalls.applyPayload (.inRight .word nativeResult) store := by
  obtain ⟨sourceResult, nativeResult, applied, represented, body⟩ := inputs.body_meaning captured store
  exact ⟨sourceResult, nativeResult, applied, represented,
    .apply (.second (.first (.var rfl))) (.var rfl) body⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {registry : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : BuiltinFunctionId}
  {native : Value} {nativeType : Ty}
  (builtin : Represents compiled.indexed world function.type (.builtin ⟨function⟩) native nativeType)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : ValuesRep compiled.compatible.checked registry functions mapping world
    function.parameterTypes arguments payloads (CompatibleBuiltinMeaning.argumentTypes function))
  {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {before : Dynamic.Heap} {store : Store}

include observations represented in
/-- All three original builtin rules are inspected. The actual represented
inputs rule out both fault constructors without an accepted gate premise. -/
theorem source_value {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies program stages size invocation context
      before (.builtin ⟨function⟩) arguments outcome after) :
    ∃ value, outcome = .value value ∧ after = before ∧
      size = Staging.Recursive.Size.stepSize [] ∧ Dynamic.BuiltinApplies function arguments value := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  cases called with
  | builtin applied => exact ⟨_, rfl, rfl, rfl, applied⟩
  | builtinArity mismatch =>
    exact False.elim (InputRep.excludes_callable_fault inputs
      (program := program) (context := context) (before := before)
      (caller := []) (invocation := []) (.builtinArity mismatch))
  | builtinType arity mismatch =>
    exact False.elim (InputRep.excludes_callable_fault inputs
      (program := program) (context := context) (before := before)
      (caller := []) (invocation := []) (.builtinArgumentType arity mismatch))

include observations builtin represented in
/-- The actual primitive yields a finite native trace at the argument store.
Its grade is recorded independently of the original Source grade. -/
theorem preserves {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies program stages sourceSize invocation context
      before (.builtin ⟨function⟩) arguments outcome after) :
    ∃ nativeSize value,
      EvaluationSize nativeSize [native, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value store ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world function.returnType (SourceCoreInteger.builtinResult function) faults outcome value ∧
      after = before ∧ sourceSize = Staging.Recursive.Size.stepSize [] := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  obtain ⟨sourceResult, sameOutcome, sameHeap, sourceGrade, applied⟩ :=
    source_value functions observations represented called
  subst outcome
  generalize typeEq : function.type = sourceType at builtin
  cases builtin with
  | builtin selected number descriptor typed =>
    obtain ⟨actualResult, nativeResult, actual, related, evaluated⟩ :=
      payload_evaluates inputs _ descriptor.id _ store
    have same := actual.functional applied
    subst actualResult
    obtain ⟨nativeSize, sized⟩ := evaluation_has_size evaluated
    exact ⟨nativeSize, _, sized,
      .value (CompatibleBuiltinMeaning.result_represents inputs applied related), sameHeap, sourceGrade⟩

include observations builtin represented in
/-- Original native completion determines the same primitive value and store.
The reflected Source constructor has its own constant application grade. -/
theorem reflects {nativeSize : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize nativeSize [native, DataPatternValues.packValues payloads]
      store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceResult,
      Staging.Recursive.Size.Applies program stages (Staging.Recursive.Size.stepSize [])
        invocation context before (.builtin ⟨function⟩) arguments (.value sourceResult) before ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world function.returnType (SourceCoreInteger.builtinResult function) faults
        (.value sourceResult) value ∧
      Dynamic.BuiltinApplies function arguments sourceResult ∧ finalStore = store := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  generalize typeEq : function.type = sourceType at builtin
  cases builtin with
  | builtin selected number descriptor typed =>
    obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ :=
      payload_evaluates inputs _ descriptor.id _ store
    obtain ⟨same, sameStore⟩ := evaluation_deterministic completed.sound evaluated
    subst value
    exact ⟨sourceResult, .builtin applied,
      .value (CompatibleBuiltinMeaning.result_represents inputs applied related), applied, sameStore⟩

section Caller
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (argumentState : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : CallableIndexedOwnedSourceAdmission.Admission bridge context argumentState)

include admitted in
/-- The same reached caller witness is the primitive post. Value typing comes
from the actual scalar Source primitive, and deep heap typing is unchanged. -/
theorem argument_post {sourceResult : Dynamic.Value}
    (applied : Dynamic.BuiltinApplies function arguments sourceResult) :
    ∃ reached : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      reached = argumentState ∧ callerProtocol.Relates argumentState reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        function.returnType (.value sourceResult) reached := by
  refine ⟨argumentState, rfl, callerProtocol.refl argumentState, admitted.rows, ?_⟩
  intro value same
  cases same
  exact ⟨applied.preserves.2, admitted.heap⟩
end Caller

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds
