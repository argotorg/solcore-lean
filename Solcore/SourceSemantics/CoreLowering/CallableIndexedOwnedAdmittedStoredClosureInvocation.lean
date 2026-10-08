import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments

/-! The actual argument-post caller Admission and genuine Source callee/argument
typing derive raw closure-context heap, binder and capture facts internally.
Actual Source heap extension retains callee typing from its success post.
Packed bundle equality and arity stay authentic Source call-site receipts.
The finite selected association and original strict body IH then invoke the
same payload producer and return the same actual caller pool. Stage/coercion
gates and the full parent expression remain a separate composition. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStoredClosureInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {slots : ProtectedStateTransition.Index → Prop}
  (carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  {mapping : LocationMap} {world : StoreTyping} {before calleeHeap : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}
  (association : CallableIndexedOwnedStoredClosureInvocation.Association
    headers keys registry faults mapping world function native bindings parameterCore resultCore)
  (initial : callerProtocol.State ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots carrier) context initial)
  {parameter result : TypeSystem.Ty}
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
  (extension : Dynamic.HeapTypesExtend calleeHeap before)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  {types : List TypeSystem.Ty} {packed : Dynamic.Value}
  (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments types)
  (packing : Dynamic.ValuesPack arguments packed)
  (bundle : TypeSystem.Ty.productMany types = parameter)
  (arity : arguments.length = function.parameters.length)

include wellFormed runtime association admitted calleeTyped extension represented heaps argumentsTyped packing bundle arity in
/-- Every raw callee input is derived at the actual argument post. The original
invocation selects only its strict body child and restores the current caller. -/
theorem preserves_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedStoredClosureInvocation.CallerResultAt
        (registry := registry) (faults := faults) functions carrier initial
        function resultCore outcome after value finalStore := by
  obtain ⟨raw, stable⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    (CallableIndexedOwnedIndirectCallerProtocol.forget_slots carrier) initial runtime admitted calleeTyped extension
    argumentsTyped packing bundle arity
  exact CallableIndexedOwnedStoredClosureInvocation.preserves_for functions carrier wellFormed association initial
    represented heaps raw.heaps raw.arguments raw.captures stable budget below trace within

include wellFormed runtime association admitted calleeTyped extension represented heaps argumentsTyped packing bundle arity in
/-- Native reflection retains the independently sized Source call and the
same actual caller restoration. Raw argument typing never comes from Core types. -/
theorem reflects_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedStoredClosureInvocation.CallerResultAt
        (registry := registry) (faults := faults) functions carrier initial
        function resultCore outcome after value finalStore := by
  obtain ⟨raw, stable⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    (CallableIndexedOwnedIndirectCallerProtocol.forget_slots carrier) initial runtime admitted calleeTyped extension
    argumentsTyped packing bundle arity
  exact CallableIndexedOwnedStoredClosureInvocation.reflects_for functions carrier wellFormed association initial
    represented heaps raw.heaps raw.arguments raw.captures stable budget below completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStoredClosureInvocation
