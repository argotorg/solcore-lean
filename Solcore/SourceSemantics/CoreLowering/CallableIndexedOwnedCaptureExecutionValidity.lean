import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureValidity
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-! A successful callee expression obtains raw Source capture validity from the
already proved whole Source preservation theorem. Its admission premises are
static Source typing and actual initial heap validity, with no child or body
execution law supplied by a compiler caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureExecutionValidity
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues CallableIndexedOwnedCaptureValidity

variable {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : ExpressionId} {function : Dynamic.Closure} {parameter result : TypeSystem.Ty}

/-- Every successful Source callee form, including generalized local reads,
returns capture agreement at the actual callee heap under Source admission. -/
theorem captures_of_expression
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType source context id (.function parameter result))
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before
      id (.closure function) after) :
    FunctionValues.SourceCapturesValid after (.closure function) ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapMetadataExtend before after := by
  have reached := wellFormed.wholeLanguagePreservation.expression context evidence source environment
    before after id (.closure function) (.function parameter result)
    runtime covers locals heapTyped typed evaluated
  exact ⟨captures_of_source_typed reached.value_typed, reached.heap_typed, reached.heap_extends⟩

/-- The Source preservation receipt is paired with the same actual owned
callee relation returned by Core correspondence, rather than a new carrier. -/
theorem valid_of_expression
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (Header compiled program)} {keys : List (Key compiled program)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {native : Value} {type : Ty}
    (related : Represents headers keys registry faults mapping world sourceType (.closure function) native type)
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType source context id (.function parameter result))
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before
      id (.closure function) after) :
    Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := after) ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨captures, reachedTyped, metadata⟩ :=
    captures_of_expression wellFormed runtime covers locals heapTyped typed evaluated
  exact ⟨⟨related, captures⟩, reachedTyped, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureExecutionValidity
