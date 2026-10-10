import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityBoundary
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalArityReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCallableDiagnostics
import Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning

/-! After-arguments rejection ports. The existing recursive staged
grammar already has physical closure, named and builtin arity failures. These
are its semantic failure constructors, and retain the actual argument heap.
The first-stage guard failure keeps its separate stage failure constructor.

Original selected metadata identifies each physical count and the exact second
gate word. No count is inferred from a packed type. Native completion keeps an
earlier argument failure separate from a successful argument computation and
pure arity rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSecondCallGateRejection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)

section Selected
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {row : SourceCoreStageCodebook.Decision}

/-- The retained generated request fixes the actual physical argument count. -/
theorem rejected_row (selected : Selected sidecar site callee ids metadata node row)
    (different : row.entry.parameterCount ≠ ids.length) :
    row.afterArguments = .error (.argumentArityMismatch row.entry.parameterCount ids.length) := by
  have mismatch : row.entry.parameterCount ≠ row.argumentCount := by
    rw [selected.argument_count]
    exact different
  simpa only [selected.argument_count] using row.afterArguments_mismatch mismatch

/-- The word retains the same caller, call, descriptor, phase and runtime error. -/
theorem rejected_gate (selected : Selected sidecar site callee ids metadata node row)
    {tag : Word} (found : site.rowAt? tag = some row)
    (different : row.entry.parameterCount ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown tag =
      some (site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length)) := by
  rw [site.decision_known .beforeApplication unknown tag row found]
  exact SourceCoreCallableContracts.reason_rejected row site.reasonAt .beforeApplication _
    (rejected_row selected different)

theorem closure_gate {function : Dynamic.Closure} {native : Value}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.closure function) native)
    (selected : Selected sidecar site callee ids metadata node dispatch.row)
    (different : function.parameters.length ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown dispatch.contract =
      some (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
        (.argumentArityMismatch function.parameters.length ids.length)) :=
  CallableIndexedOwnedStoredClosureArityBoundary.rejected_gate dispatch selected different unknown

theorem named_gate {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {function : Dynamic.GlobalFunction} {native : Value}
    (sourceAt : NamedSourceAt header rawD function)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : Selected sidecar site callee ids metadata node dispatch.row)
    (different : header.function.parameters.length ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown dispatch.contract =
      some (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
        (.argumentArityMismatch header.function.parameters.length ids.length)) := by
  have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
    sourceAt caller dispatch selected
  have mismatch : dispatch.row.entry.parameterCount ≠ ids.length := by
    rw [physical]
    exact different
  simpa only [physical] using rejected_gate selected dispatch.found mismatch unknown

theorem builtin_gate {function : Dynamic.BuiltinFunction} {native : Value}
    (builtin : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids metadata node function native row)
    (different : function.id.parameterTypes.length ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown row.entry.id =
      some (site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch function.id.parameterTypes.length ids.length)) := by
  have physical := builtin.parameter_count
  have mismatch : row.entry.parameterCount ≠ ids.length := by
    rw [physical]
    exact different
  simpa only [physical] using rejected_gate builtin.selected builtin.selected.found mismatch unknown
end Selected

section Source
variable {program : Program} {registry : Staging.Recursive.Registry}
  {scope : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {calleeSize argumentsSize : Nat} {values : List Dynamic.Value}

/-- The actual ordered staged trace preserves its list length by constructor
inversion, independently of packed Source or native product types. -/
theorem values_count {size : Nat} {first last : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expressions program registry size scope context environment
      first ids (.values values) last) : values.length = ids.length := by
  induction ids generalizing size first last values with
  | nil => cases trace with | nil => rfl
  | cons id ids ih =>
    cases trace with
    | cons head tail =>
      have count := ih tail
      simpa only [List.length_cons] using congrArg Nat.succ count

variable (occurrence : Staging.Recursive.Occurrence scope call (.call callee ids (.indirect metadata)))
  (uncoerced : metadata.argumentCoercions = [])
  (sourceArity : ids.length = metadata.argumentCount)
  (arguments : Staging.Recursive.Size.Expressions program registry argumentsSize scope context environment
    middle ids (.values values) after)

include occurrence uncoerced sourceArity arguments in
/-- Physical closure rejection happens at the existing application rule, after
the actual successful argument trace, and invokes no closure body. -/
theorem closure_source {function : Dynamic.Closure}
    (child : Staging.Recursive.Size.Expression program registry calleeSize scope context environment
      before callee (.value (.closure function)) middle)
    (accepted : Staging.CallBoundary.GuardAccepts scope.guards call ids (.closure function))
    (different : function.parameters.length ≠ ids.length) :
    Staging.Recursive.Size.Expression program registry
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []])
      scope context environment before call
      (.fault (.semantic (.argumentArityMismatch function.parameters.length ids.length))) after := by
  have count := values_count arguments
  have mismatch : function.parameters.length ≠ values.length := by
    rw [count]
    exact different
  have invocation : Staging.Recursive.Size.Applies program registry
      (Staging.Recursive.Size.stepSize []) scope context after (.closure function) values
      (.fault (.semantic (.argumentArityMismatch function.parameters.length ids.length))) after := by
    simpa only [count] using (Staging.Recursive.Size.Applies.closureArity
      (program := program) (registry := registry) (scope := scope) (context := context) (heap := after) mismatch)
  exact .applied occurrence uncoerced child accepted arguments sourceArity invocation

include occurrence uncoerced sourceArity arguments in
/-- Genuine NamedSourceAt retains the same original BodyInstance and ordered
parameters. The staged global arity constructor uses that exact instantiation. -/
theorem named_source {compiled : SourceCoreUnifiedCompilation.Compiled}
    {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {function : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD function)
    (child : Staging.Recursive.Size.Expression program registry calleeSize scope context environment
      before callee (.value (.global function)) middle)
    (accepted : Staging.CallBoundary.GuardAccepts scope.guards call ids (.global function))
    (different : header.function.parameters.length ≠ ids.length) :
    Staging.Recursive.Size.Expression program registry
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []])
      scope context environment before call
      (.fault (.semantic (.argumentArityMismatch header.function.parameters.length ids.length))) after := by
  have count := values_count arguments
  have mismatch : header.sourceBody.source.inputs.length ≠ values.length := by
    rw [← sourceAt.frame.parameters, count]
    exact different
  have invocation : Staging.Recursive.Size.Applies program registry
      (Staging.Recursive.Size.stepSize []) scope context after (.global function) values
      (.fault (.semantic (.argumentArityMismatch header.function.parameters.length ids.length))) after := by
    simpa only [← sourceAt.frame.parameters, count] using
      (Staging.Recursive.Size.Applies.globalArity (registry := registry) (scope := scope)
        (context := context) (heap := after) sourceAt.frame.instantiated mismatch)
  exact .applied occurrence uncoerced child accepted arguments sourceArity invocation

include occurrence uncoerced sourceArity arguments in
/-- Builtin physical arity uses its original parameter list. It needs no user
stage acceptance premise because the existing grammar bypasses that guard. -/
theorem builtin_source {function : Dynamic.BuiltinFunction}
    (child : Staging.Recursive.Size.Expression program registry calleeSize scope context environment
      before callee (.value (.builtin function)) middle)
    (different : function.id.parameterTypes.length ≠ ids.length) :
    Staging.Recursive.Size.Expression program registry
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []])
      scope context environment before call
      (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length ids.length))) after := by
  have count := values_count arguments
  have mismatch : function.id.parameterTypes.length ≠ values.length := by
    rw [count]
    exact different
  have invocation : Staging.Recursive.Size.Applies program registry
      (Staging.Recursive.Size.stepSize []) scope context after (.builtin function) values
      (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length ids.length))) after := by
    simpa only [count] using (Staging.Recursive.Size.Applies.builtinArity
      (program := program) (registry := registry) (scope := scope) (context := context) (heap := after) mismatch)
  exact .applied occurrence uncoerced child (.builtin function) arguments sourceArity invocation
end Source

section Native
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {sourceValue : Dynamic.Value} {native : Value}
  {actual : Environment} {before middle after : Store}
  {result : Ty} {calleeCode argumentCode : Expr} {argument : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids sourceValue native)
  (selected : Selected sidecar site callee ids metadata node dispatch.row)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids sourceValue)
  (different : dispatch.row.entry.parameterCount ≠ ids.length)
  (unknown : Word)

include selected accepted different in
/-- Both effectful prefixes are the actual traces. The pure second gate keeps
the argument's final store; the real Source first guard derives its gate. -/
theorem user_native_preserves
    (calleeTrace : Evaluates actual before calleeCode (.inRight .word native) middle)
    (argumentsTrace : Evaluates (.unit :: native :: actual) middle
      ((argumentCode.weakenAt 0).weakenAt 0) (.inRight .word argument) after) :
    Evaluates actual before (site.lower unknown result calleeCode argumentCode)
      (.inLeft result (.word (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
        .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))) after := by
  rw [dispatch.shape] at calleeTrace argumentsTrace
  exact site.lower_arity_failure unknown dispatch.row _ dispatch.found
    (dispatch.accepted accepted) (rejected_row selected different) calleeTrace argumentsTrace

include selected accepted different in
/-- The original finite bind inversion retains either an earlier argument
failure or the successful argument trace at the exact arity-rejection store.
No application trace or called-body hypothesis is consumed. -/
theorem user_native_completion {budget size : Nat} {value : Value} {last : Store}
    (calleeTrace : Evaluates actual before calleeCode (.inRight .word native) middle)
    (completed : EvaluationSize size actual before (site.lower unknown result calleeCode argumentCode) value last)
    (within : size ≤ budget) :
    CallableIndexedOwnedStoredClosureArityBoundary.Completion
      (actual := actual) (calleeStore := middle) (native := native)
      (token := site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
        (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))
      budget result argumentCode value last := by
  have stage : CallableContract.decision site.gates .beforeArguments unknown dispatch.contract = none := by
    rw [site.decision_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found]
    exact SourceCoreCallableContracts.reason_accepted dispatch.row site.reasonAt .beforeArguments
      (dispatch.accepted accepted)
  exact CallableIndexedOwnedStoredClosureArityBoundary.completed dispatch.shape calleeTrace stage
    (rejected_gate selected dispatch.found different unknown) completed within

theorem builtin_native_preserves {function : Dynamic.BuiltinFunction} {row : SourceCoreStageCodebook.Decision}
    (builtin : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids metadata node function native row)
    (mismatch : function.id.parameterTypes.length ≠ ids.length)
    (calleeTrace : Evaluates actual before calleeCode (.inRight .word native) middle)
    (argumentsTrace : Evaluates (.unit :: native :: actual) middle
      ((argumentCode.weakenAt 0).weakenAt 0) (.inRight .word argument) after) :
    Evaluates actual before (site.lower unknown result calleeCode argumentCode)
      (.inLeft result (.word (site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length)))) after := by
  have physical : row.entry.parameterCount ≠ ids.length := by
    rw [builtin.parameter_count]
    exact mismatch
  have passed : row.beforeArguments = .ok () := by
    simp only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      builtin.unguarded]
  obtain ⟨raw, shape⟩ := builtin.shape
  rw [shape] at calleeTrace argumentsTrace
  exact site.lower_arity_failure unknown row _ builtin.selected.found passed
    (rejected_row builtin.selected physical) calleeTrace argumentsTrace

theorem builtin_native_completion {function : Dynamic.BuiltinFunction} {row : SourceCoreStageCodebook.Decision}
    (builtin : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids metadata node function native row)
    (mismatch : function.id.parameterTypes.length ≠ ids.length)
    {budget size : Nat} {value : Value} {last : Store}
    (calleeTrace : Evaluates actual before calleeCode (.inRight .word native) middle)
    (completed : EvaluationSize size actual before (site.lower unknown result calleeCode argumentCode) value last)
    (within : size ≤ budget) :
    CallableIndexedOwnedStoredClosureArityBoundary.Completion
      (actual := actual) (calleeStore := middle) (native := native)
      (token := site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length))
      budget result argumentCode value last := by
  have physical : row.entry.parameterCount ≠ ids.length := by
    rw [builtin.parameter_count]
    exact mismatch
  have passed : row.beforeArguments = .ok () := by
    simp only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      builtin.unguarded]
  have stage : CallableContract.decision site.gates .beforeArguments unknown row.entry.id = none := by
    rw [site.decision_known .beforeArguments unknown row.entry.id row builtin.selected.found]
    exact SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeArguments passed
  obtain ⟨raw, shape⟩ := builtin.shape
  exact CallableIndexedOwnedStoredClosureArityBoundary.completed shape calleeTrace stage
    (rejected_gate builtin.selected builtin.selected.found physical unknown) completed within
end Native

section Diagnostic
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}
  (selected : Selected sidecar prepared.site callee ids metadata compiler.original row)

/-- The concrete relation decodes only the actual physical arity category.
It cannot represent a first-stage Failure.stage or an unrelated child fault. -/
def arityFaults (table : SourceCoreFaultSites.Table) : FunctionCalls.FaultRep :=
  fun reason token => ∃ expected actual diagnostic,
    reason = .argumentArityMismatch expected actual ∧
    table.diagnostic? token = some diagnostic ∧
    diagnostic.error = .argumentArityMismatch expected actual

/-- Only the original semantic arity constructor is represented here. The
first guard's stage failure remains a separate Source rule and relation. -/
def stagedArityFaults (table : SourceCoreFaultSites.Table) : RecursiveStageMeaning.FaultRep :=
  fun failure token => match failure with
    | .semantic reason => arityFaults table reason token
    | .stage .. => False

private theorem issued_reason {table : SourceCoreStageCodebook.Table}
    {caller : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {actualReason : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table caller call actualReason = .ok site) :
    site.reasonAt = actualReason := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

include stages selected in
/-- The sealed public compiler supplies the factory. The actual selected row
supplies membership; neither decoder success nor a FaultRep inclusion is given. -/
theorem public_diagnostic (different : row.entry.parameterCount ≠ ids.length) :
    ∃ diagnostic,
      native.diagnostics.rootTable.diagnostic?
        (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
          (.argumentArityMismatch row.entry.parameterCount ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch row.entry.parameterCount ids.length := by
  have member := List.mem_of_find?_eq_some selected.found
  change row ∈ prepared.site.table.casesAt prepared.site.caller prepared.site.call at member
  have contained := (List.mem_filter.mp member).1
  rw [prepared.table] at contained
  obtain ⟨_issuer, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have decoded := CallableFaultDiagnosticPreparation.prepared_after_arguments allocated contained
    (rejected_row selected different)
  rw [issued_reason prepared.prepared]
  exact decoded

include stages selected in
/-- A pure word rejection returns the argument's actual state and complete
heap relation unchanged, with its concrete same-table fault representation.
Transport to a later rebuilt Session table is a separate indexed obligation. -/
theorem public_argument_post
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    {registry : SourceCoreRawMetadata.Registry}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (argumentState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (different : row.entry.parameterCount ≠ ids.length) :
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world sourceResult resultCore (arityFaults native.diagnostics.rootTable)
      (.fault (.argumentArityMismatch row.entry.parameterCount ids.length))
      (.inLeft resultCore (.word (prepared.site.reasonAt row.caller row.call row.entry.id
        .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = argumentState := by
  obtain ⟨diagnostic, decoded, error⟩ := public_diagnostic compiler prepared stages selected different
  exact ⟨.fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩,
    heaps, argumentState, rfl⟩

include stages selected in
/-- The same concrete word also represents the exact staged semantic failure,
at the same argument heap/store and the same dependent caller state. -/
theorem public_staged_argument_post
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    {registry : SourceCoreRawMetadata.Registry}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (argumentState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (different : row.entry.parameterCount ≠ ids.length) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world sourceResult resultCore (stagedArityFaults native.diagnostics.rootTable)
      (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)))
      (.inLeft resultCore (.word (prepared.site.reasonAt row.caller row.call row.entry.id
        .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = argumentState := by
  obtain ⟨diagnostic, decoded, error⟩ := public_diagnostic compiler prepared stages selected different
  exact ⟨.fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩,
    heaps, argumentState, rfl⟩
end Diagnostic

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSecondCallGateRejection
