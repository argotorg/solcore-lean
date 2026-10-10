import Solcore.Frontend.SourceCoreUnifiedCompilation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues
import Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning
import Solcore.SourceSemantics.CoreLowering.BuiltinCallSource
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls

/-! The builtin alternative of the accepted indirect payload invocation uses
the literal contracted builtin carrier and ordered represented scalar inputs.
The actual primitive body runs once at the argument store. It has no F child,
and preserves that whole store and the original Source heap. The enclosing
parent supplies the two genuine dispatch gates and ordered E children. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open BuiltinBodyMeaning CallableIndexedBuiltinValues BuiltinCalls

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
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : BuiltinFunctionId}
  {native : Value} {nativeType : Ty}
  (builtin : Represents compiled.indexed world function.type (.builtin ⟨function⟩) native nativeType)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : ValuesRep compiled.compatible.checked registry functions mapping world
    function.parameterTypes arguments payloads (CompatibleBuiltinMeaning.argumentTypes function))
  {program : Program} {context : SourceSemantics.Context}
  {caller invocation : Dynamic.EvidenceEnvironment} {before : Dynamic.Heap} {store : Store}

include observations builtin represented in
/-- Invalid builtin application is excluded by its actual ordered scalar
inputs. The original Source application fixes the result; native execution
uses the same real contracted carrier rather than a reconstructed closure. -/
theorem preserves {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome program size context caller invocation
      before (.builtin ⟨function⟩) arguments outcome after) :
    ∃ value,
      Evaluates [native, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value store ∧
      FunctionCalls.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world function.returnType (SourceCoreInteger.builtinResult function) faults outcome value ∧
      after = before := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  cases called with
  | value applied =>
    cases applied with
    | builtin applied =>
      generalize typeEq : function.type = sourceType at builtin
      cases builtin with
      | builtin selected number descriptor typed =>
        obtain ⟨sourceResult, nativeResult, actual, related, evaluated⟩ :=
          payload_evaluates inputs _ descriptor.id _ store
        have same := actual.functional applied
        subst sourceResult
        exact ⟨_, evaluated, .value (CompatibleBuiltinMeaning.result_represents inputs applied related), rfl⟩
  | fault failed =>
    exact False.elim (InputRep.excludes_callable_fault inputs failed.sound)

include observations builtin represented in
/-- Native completion determines the same primitive result and store. Its
Source application has its own genuine constant grade; reflection uses no
preservation theorem or semantic body callback. -/
theorem reflects {size : Nat} {value : Value} {finalStore : Store}
    (completed : CoreProof.EvaluationSize size [native, DataPatternValues.packValues payloads]
      store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceSize outcome,
      RecursiveNamedCallBounds.CallOutcome program sourceSize context caller invocation
        before (.builtin ⟨function⟩) arguments outcome before ∧
      FunctionCalls.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world function.returnType (SourceCoreInteger.builtinResult function) faults outcome value ∧
      finalStore = store := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  generalize typeEq : function.type = sourceType at builtin
  cases builtin with
  | builtin selected number descriptor typed =>
    obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ :=
      payload_evaluates inputs _ descriptor.id _ store
    obtain ⟨same, sameStore⟩ := evaluation_deterministic completed.sound evaluated
    subst value
    exact ⟨_, .value sourceResult, .value (.builtin applied),
      .value (CompatibleBuiltinMeaning.result_represents inputs applied related), sameStore⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds
