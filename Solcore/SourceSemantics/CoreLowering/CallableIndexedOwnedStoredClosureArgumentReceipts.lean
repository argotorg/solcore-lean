import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments

/-! Original indirect-call Source typing and the actual successful ordered
argument trace retain independent raw types and true Source heap extension.
The empty argument-coercion specialization uses the original valid path.
Arity comes from the selected closure's genuine binder representation.
Current owned rows and later admission remain separate actual-state receipts;
native reflection must first obtain its real Source argument trace. Body
Syntax, compiler pack alignment, stage gates and nonempty coercions remain
separate static and semantic cuts. No execution law is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof

/-- One authentic parent inversion retains both the callee and the original
ordered raw argument row, including the original application certificate. -/
theorem original_facts {source : TypedSource} {context : SourceSemantics.Context}
    {root callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type) :
    ∃ parameter result types,
      ExpressionHasType source context callee (.function parameter result) ∧
      ExpressionsHaveTypes source context ids types ∧
      IndirectApplicationValid context metadata types parameter := by
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    rw [form] at raw
    cases raw with
    | indirectCall calleeTyped argumentsTyped application =>
      exact ⟨_, _, _, calleeTyped, argumentsTyped, application⟩

/-- Empty coercions identify the real Source bundle through the valid path;
no native parameter vector or packed-type injectivity is used. -/
theorem empty_bundle {context : SourceSemantics.Context} {metadata : IndirectCallResolution}
    {types : List TypeSystem.Ty} {parameter : TypeSystem.Ty}
    (application : IndirectApplicationValid context metadata types parameter)
    (empty : metadata.argumentCoercions = []) :
    TypeSystem.Ty.productMany types = parameter := by
  cases application with
  | intro _ before _ path =>
    have endpoint := path.foldl_target
    rw [empty, List.foldl_nil] at endpoint
    exact before.symm.trans endpoint

/-- The same actual Source trace supplies raw values, deep heap typing and
true heap-type extension. The packed value is constructed from those values. -/
theorem after_trace {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {size : Nat} {arguments : List Dynamic.Value}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionsHaveTypes source context ids types)
    (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment
      before ids arguments after) :
    ∃ packed, Dynamic.ValuesPack arguments packed ∧
      Dynamic.ValuesHaveTypes context after arguments types ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapTypesExtend before after ∧
      Dynamic.ValueHasType context after packed (TypeSystem.Ty.productMany types) := by
  have preserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before after id value type runtime covers locals heapTyped typed evaluated
  obtain ⟨valuesTyped, reachedTyped, extension⟩ :=
    Dynamic.ExpressionsEvaluate.preserves preserves covers locals heapTyped typed trace.sound
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  exact ⟨packed, packing, valuesTyped, reachedTyped, extension, packing.hasType valuesTyped⟩

/-- Actual selected binder representation fixes arity independently of the
Source bundle equation. Both constructors retain the real Code receipt. -/
theorem arity_of_association {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings arguments nativeArguments) :
    arguments.length = function.parameters.length := by
  cases association with
  | ordinary _ _ code _ _ _ _ _ _ _ _ _ =>
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code,
      List.length_map]
    exact represented.length.1.symm
  | principal _ _ code _ _ _ _ _ _ _ _ _ =>
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code,
      List.length_map]
    exact represented.length.1.symm

/-- Genuine callee typing is carried along the actual argument extension,
then the original closed-context transport derives raw closure inputs at that
same heap. Current owned rows are supplied by the later admitted state. -/
theorem closure_after_trace {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {size : Nat} {arguments : List Dynamic.Value} {function : Dynamic.Closure}
    {parameter result : TypeSystem.Ty} {metadata : IndirectCallResolution}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionsHaveTypes source context ids types)
    (application : IndirectApplicationValid context metadata types parameter)
    (empty : metadata.argumentCoercions = [])
    (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
    (arity : arguments.length = function.parameters.length)
    (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment
      before ids arguments after) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function after arguments ∧
      Dynamic.HeapTypesExtend before after := by
  obtain ⟨packed, packing, valuesTyped, reachedTyped, extension, _⟩ :=
    after_trace wellFormed runtime covers locals heapTyped typed trace
  exact ⟨CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime
    (calleeTyped.mono extension) reachedTyped valuesTyped packing (empty_bundle application empty) arity,
    extension⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArgumentReceipts
