import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArgumentReceipts

/-! The successful stored-call prefix starts at the authentic original caller
heap and environment. Original Source preservation supplies callee typing,
heap validity and true extension at the actual callee success post. The real
ordered argument trace supplies the corresponding facts at its actual post.
Only an authentic selected binder receipt proves arity. Current owned rows,
body Syntax, compiler pack alignment, stage gates and nonempty argument or
output coercions remain separate. Native reflection must recover both actual
Source traces before using these receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredCallSourcePrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedStoredClosureArgumentReceipts

/-- Every dynamic field refers to the two actual successful Source heaps;
the independent static row and application remain attached to the parent. -/
def Receipts (source : TypedSource) (context : SourceSemantics.Context)
    (callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution)
    (environment : Dynamic.Environment) (before calleeHeap argumentsHeap : Dynamic.Heap)
    (function : Dynamic.Closure) (arguments : List Dynamic.Value) : Prop :=
  ∃ parameter result types,
    ExpressionHasType source context callee (.function parameter result) ∧
    ExpressionsHaveTypes source context ids types ∧
    IndirectApplicationValid context metadata types parameter ∧
    Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result) ∧
    Dynamic.HeapWellTyped context calleeHeap ∧ Dynamic.HeapTypesExtend before calleeHeap ∧
    Dynamic.EnvironmentAgrees calleeHeap context.locals environment ∧
    Dynamic.ValuesHaveTypes context argumentsHeap arguments types ∧
    Dynamic.HeapWellTyped context argumentsHeap ∧ Dynamic.HeapTypesExtend calleeHeap argumentsHeap ∧
    Dynamic.EnvironmentAgrees argumentsHeap context.locals environment ∧
    Dynamic.HeapTypesExtend before argumentsHeap ∧
    arguments.length = function.parameters.length ∧
    ∃ packed, Dynamic.ValuesPack arguments packed ∧
      Dynamic.ValueHasType context argumentsHeap packed parameter ∧
      CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function argumentsHeap arguments

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before calleeHeap argumentsHeap : Dynamic.Heap}
  {root callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {type : TypeSystem.Ty} {function : Dynamic.Closure}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {calleeSize argumentsSize : Nat}

/-- Original parent typing and both actual successful measured Source children
close the callee and raw argument receipts internally. No execution law or
native-to-Source typing conversion is supplied. -/
theorem from_traces
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type)
    (empty : metadata.argumentCoercions = [])
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings arguments nativeArguments)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee (.closure function) calleeHeap)
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments argumentsHeap) :
    Receipts source context callee ids metadata environment before calleeHeap argumentsHeap function arguments := by
  obtain ⟨parameter, result, types, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique found form typed
  obtain ⟨calleeTyped, calleeHeapTyped, calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before calleeHeap callee (.closure function) (.function parameter result)
      runtime covers locals heapTyped calleeTyping calleeTrace.sound
  have calleeLocals := locals.mono calleeExtension
  obtain ⟨packed, packing, argumentsTyped, argumentsHeapTyped, argumentsExtension, packedTyped⟩ :=
    after_trace wellFormed runtime covers calleeLocals calleeHeapTyped argumentsTyping argumentsTrace
  have bundle := empty_bundle application empty
  have packedParameter : Dynamic.ValueHasType context argumentsHeap packed parameter := by
    rw [← bundle]
    exact packedTyped
  have arity := arity_of_association association represented
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime
    (calleeTyped.mono argumentsExtension) argumentsHeapTyped argumentsTyped packing bundle arity
  exact ⟨parameter, result, types, calleeTyping, argumentsTyping, application,
    calleeTyped, calleeHeapTyped, calleeExtension, calleeLocals, argumentsTyped,
    argumentsHeapTyped, argumentsExtension, calleeLocals.mono argumentsExtension,
    calleeExtension.trans argumentsExtension, arity, packed, packing, packedParameter, raw⟩

universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)

/-- Initial Source heap admission is consumed at that exact initial state.
Owned-row admission at the later argument state remains its own real receipt. -/
theorem from_admission
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees index.heap context.locals environment)
    (admitted : CallableIndexedOwnedSourceAdmission.Admission bridge context initial)
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type)
    (empty : metadata.argumentCoercions = [])
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings arguments nativeArguments)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment index.heap callee (.closure function) calleeHeap)
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments argumentsHeap) :
    Receipts source context callee ids metadata environment index.heap calleeHeap argumentsHeap function arguments :=
  from_traces wellFormed runtime covers locals admitted.heap unique found form typed empty association represented
    calleeTrace argumentsTrace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredCallSourcePrefix
