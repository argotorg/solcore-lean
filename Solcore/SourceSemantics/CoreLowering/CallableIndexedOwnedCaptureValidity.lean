import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
import Solcore.SourceSemantics.CoreLowering.FunctionValues

/-! Raw Source capture validity accompanies the owned closure relation at its
actual heap. Formation obtains it from the original lexical environment; later
effects transport it using the same Source heap metadata extension. Projected
native typing does not supply Source cell declarations or generalized storage. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureValidity
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues CallableIndexedLambdaValues

/-- The actual Source lambda captures precisely its caller's lexical environment
and leaves the heap unchanged. No child or body execution premise is needed. -/
theorem captures_of_formation
    {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId} {requirements : List RequirementId}
    {coercions : List CoercionStep} {function : Dynamic.Closure}
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (evaluated : Dynamic.ExpressionFormEvaluates program context evidence source environment before
      (.lambda parameters result statements) requirements coercions (.closure function) after) :
    after = before ∧ FunctionValues.SourceCapturesValid after (.closure function) := by
  cases evaluated with
  | lambda _ => exact ⟨rfl, locals⟩

/-- Source typing at the actual callee heap exposes the complete raw capture
scope, including generalized descriptors, independently of the native carrier. -/
theorem captures_of_source_typed
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {function : Dynamic.Closure} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap (.closure function) (.function parameter result)) :
    FunctionValues.SourceCapturesValid heap (.closure function) :=
  typed.closure_function_inv.2.2.2.2.2

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {function : Dynamic.Closure} {native : Value} {type : Ty} {heap : Dynamic.Heap}

/-- These two receipts refer to the same complete Source closure. Ownership,
code, evidence and native captures stay in the original relation. -/
structure Valid where
  related : Represents headers keys registry faults mapping world sourceType (.closure function) native type
  captures : FunctionValues.SourceCapturesValid heap (.closure function)

theorem Valid.of_formation
    (related : Represents headers keys registry faults mapping world sourceType (.closure function) native type)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (evaluated : Dynamic.ExpressionFormEvaluates program context evidence source environment before
      (.lambda parameters result statements) requirements coercions (.closure function) heap) :
    Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := heap) :=
  ⟨related, (captures_of_formation locals evaluated).2⟩

theorem Valid.of_source_typed
    (related : Represents headers keys registry faults mapping world sourceType (.closure function) native type)
    {context : SourceSemantics.Context} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap (.closure function) (.function parameter result)) :
    Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := heap) :=
  ⟨related, captures_of_source_typed typed⟩

theorem Valid.extend
    (valid : Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := heap))
    {futureMap : LocationMap} {futureWorld : StoreTyping} {futureHeap : Dynamic.Heap}
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (metadata : Dynamic.HeapMetadataExtend heap futureHeap) :
    Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := futureMap) (world := futureWorld) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := futureHeap) := by
  refine ⟨?_, valid.captures.extend metadata⟩
  cases valid.related with
  | builtin prior => cases prior
  | lambda owner captured code history body origin globals referenceIndex typed =>
    exact .lambda owner (captured.extend maps worlds) code history body origin globals referenceIndex (typed.weaken worlds)

/-- Real Source validity and authentic static body support together imply
Source value typing. The entire original capture environment remains present. -/
theorem Valid.source_hasType
    (valid : Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := heap))
    {context : SourceSemantics.Context} (signatures : context.signatures = program.signatures) :
    Dynamic.ValueHasType context heap (.closure function) sourceType := by
  cases valid.related with
  | builtin prior => cases prior
  | lambda owner captured code history body origin globals referenceIndex typed =>
    have frame := body.2.2.receipt.body.frame
    exact .closure (frame.signatures.trans signatures.symm) frame.code frame.evidence_covers valid.captures

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureValidity
