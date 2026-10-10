import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Successful staged arguments retain their original raw Source typing at
the reached heap. Each actual value child uses its ordinary value projection;
the same heap extension then admits the selected closure and its captures.
No statement or application meaning is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {program : Program} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {ids : List ExpressionId} {types : List TypeSystem.Ty} {values : List Dynamic.Value}

/-- Actual successful children retain both ordered types and the independent
Source heap extension. No stage failure is projected to a semantic fault. -/
theorem values_at (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types) {size : Nat}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context
      environment before ids (.values values) after) :
    Dynamic.ValuesHaveTypes context after values types ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapTypesExtend before after := by
  induction ids generalizing types before after size values with
  | nil =>
      cases trace
      cases typing
      exact ⟨.nil, heap, .refl before⟩
  | cons id ids ih =>
      cases typing with
      | cons headTyping tailTyping =>
          cases trace with
          | cons head tail =>
              have first := wellFormed.wholeLanguagePreservation.expression
                context invocation.evidence invocation.source environment _ _ _ _ _
                runtime covers locals heap headTyping head.sound.value_plain
              obtain ⟨rest, finalHeap, extension⟩ :=
                ih (locals.mono first.heap_extends) first.heap_typed tailTyping tail
              exact ⟨.cons (first.value_typed.mono extension) rest,
                finalHeap, first.heap_extends.trans extension⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)
  {function : Dynamic.Closure} {parameter result : TypeSystem.Ty}

/-- The successful trace and same reached admission construct raw closure
arguments and its authentic Source frame. Captures stay at that reached heap. -/
theorem closure_at (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types)
    (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : values.length = function.parameters.length)
    (admitted : Admission bridge context reached) {size : Nat}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context
      environment before ids (.values values) index.heap) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function index.heap values ∧
      Dynamic.ClosureFrame program function := by
  obtain ⟨argumentsTyped, _finalHeap, extension⟩ :=
    values_at wellFormed runtime covers locals heap typing trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack values
  obtain ⟨raw, _rows⟩ :=
    CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
      bridge reached runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  obtain ⟨_parameters, _result, signatures, code, evidence, _captures⟩ := calleeTyped.closure_function_inv
  exact ⟨raw, signatures.trans runtime.signatures, code.owner, code,
    code.requirement_ledger.idsUnique, evidence⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping
