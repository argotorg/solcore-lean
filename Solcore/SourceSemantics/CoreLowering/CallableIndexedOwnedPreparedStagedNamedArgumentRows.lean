import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAcceptedIndirectPhysicalArity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts

/-! The same authentic Header and actual argument state retain the original
raw Source row and ordered native values. Selected physical arity is derived
before packed rows are aligned. Successful staged children supply heap typing;
no body execution, application result or equality between grades is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)

include sourceAt in
/-- The real Source certificate and its monomorphic binder extension transport
the Header's body typing back to this original caller context. -/
theorem caller_supports
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {context : SourceSemantics.Context} {source : TypedSource}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source) :
    Dynamic.TypeContextSupports header.context context := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
  have inherited := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have signatures : header.context.signatures = (Program.ofChecked compiled.sourceProgram).signatures :=
    inherited.signatures.trans
      ((congrArg (fun current : SourceSemantics.Context => current.signatures) sourceAt.frame.context).trans certified.signatures_eq)
  have closed : header.context.typeParameters = [] :=
    inherited.typeParameters.trans
      ((congrArg (fun current : SourceSemantics.Context => current.typeParameters) sourceAt.frame.context).trans certified.type_parameters_empty)
  have variables : header.context.typeVariables = [] :=
    inherited.typeVariables.trans
      ((congrArg (fun current : SourceSemantics.Context => current.typeVariables) sourceAt.frame.context).trans certified.type_variables_empty)
  exact Dynamic.TypeContextSupports.ofClosed (runtime.signatures.trans signatures.symm)
    closed runtime.closed variables runtime.residual_variables_open

section Rows
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping} {sourceTypes : List TypeSystem.Ty}
  {sources : List Dynamic.Value} {payloads : List Value}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  {native : Value} {unknown : Word} {context : SourceSemantics.Context} {heap : Dynamic.Heap}
  {parameter result : TypeSystem.Ty}

include sourceAt compiler in
/-- Authentic callable typing supplies literal raw signature equality. The
selected second gate supplies count independently, then both genuine compiler
bundles align the original represented values with this Header's binders. -/
theorem accepted_rows
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids originalMetadata
      originalNode dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none)
    (calleeTyped : Dynamic.ValueHasType context heap (.global function) (.function parameter result))
    (nativeType : compiler.calleeCode.type =
      CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
    (represented : DataExpressionSequence.Values model mapping world
      sourceTypes (compiler.codes.map (·.type)) sources payloads)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes = parameter) :
    CallableIndexedParameterMeaning.Arguments model mapping world header.bindings sources payloads ∧
      header.function.parameters.length = sources.length ∧ result = header.function.resultType := by
  rcases calleeTyped.global_inv with ordinary | staged
  · obtain ⟨typeEq, valid, evidence⟩ := ordinary
    obtain ⟨facts, certified⟩ :=
      CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
    have signature := TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)
    have bindingTypes : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
      have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
      rw [header.parameters] at bodyTypes
      simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
    have nativeSignature : compiler.parameterType = header.named.signature.parameterType ∧
        compiler.resultType = header.named.signature.resultType := by
      have acceptedType := compiler.callableType
      rw [actualFunctionType] at acceptedType
      exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (acceptedType.trans nativeType)
    have physical := CallableIndexedOwnedAcceptedIndirectPhysicalArity.named_count
      sourceAt caller dispatch selected accepted
    have ordered := compiler.ordered_children.1
    have representedCount : compiler.codes.length = sources.length := by
      simpa only [List.length_map] using represented.length.1
    have arity : header.function.parameters.length = sources.length :=
      physical.trans (ordered.trans representedCount)
    have parameterCount : header.function.parameters.length = header.bindings.length := by
      simpa only [List.length_map] using congrArg List.length header.parameters
    have binderCount : sources.length = header.bindings.length := arity.symm.trans parameterCount
    have sourcePacked := sourceBundle.trans
      (signature.1.trans (congrArg TypeSystem.Ty.productMany bindingTypes))
    have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
        SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :=
      (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
        (compiler.packedType.symm.trans (nativeSignature.1.trans header.parameterType))
    exact ⟨CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
      header.bindings represented binderCount sourcePacked nativePacked,
      arity, signature.2.trans sourceAt.frame.result.symm⟩
  · obtain ⟨inner, impossible, innerTyped⟩ := staged
    cases impossible
end Rows

section Successful
variable {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {ids : List ExpressionId} {types : List TypeSystem.Ty}
  {arguments : List Dynamic.Value} {parameter result : TypeSystem.Ty}

include sourceAt in
/-- The actual successful staged argument trace constructs raw Header admission
at its reached heap. The separate physical receipt supplies only arity, and the
same heap extension admits the genuine global callable without a body law. -/
theorem at_successful_arguments
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types)
    (calleeTyped : Dynamic.ValueHasType context before (.global function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : header.function.parameters.length = arguments.length)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before ids (.values arguments) after) :
    Dynamic.HeapWellTyped header.function.context after ∧
      Dynamic.ValuesHaveTypes header.function.context after arguments header.types ∧
      Dynamic.TypeContextSupports header.context context := by
  obtain ⟨argumentsTyped, finalHeap, extension⟩ :=
    CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping.values_at
      wellFormed runtime covers locals heapTyped typing trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have packedTyped : Dynamic.ValueHasType context after packed parameter :=
    bundle ▸ packing.hasType argumentsTyped
  obtain ⟨bodyHeap, bodyArguments⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.arguments_at_global
      sourceAt wellFormed runtime finalHeap (calleeTyped.mono extension) packing packedTyped arity
  exact ⟨bodyHeap, bodyArguments, caller_supports sourceAt wellFormed runtime⟩
end Successful
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows
