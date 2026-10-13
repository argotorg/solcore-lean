import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows

/-! Exact selected definitions type the retained named handle, including its
complete substitution and dictionary, before argument bundles are aligned. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)

/-- The certificate concerns this actual handle and the original selected body. -/
def CertifiedAt : Prop :=
  ∃ facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    function.instantiation header.sourceBody header.types header.context facts

include sourceAt in
theorem certified_at (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    CertifiedAt (header := header) (function := function) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, resolved, accepted⟩ := prepared.origin
  have valid := bodies.ordinary generic
    ⟨prepared.index, prepared.named, signature, request.parameterSubstitution, prepared.selected,
      signatureMember, genericMember, by simpa only [prepared.same] using accepted⟩
  have owner : (FunctionDefinition.ofChecked generic).body.owner = function.instantiation.declaration := by
    rw [sourceAt.retained]
    change generic.declaration = header.named.specialized.declaration
    rw [aligned.named, prepared.same]
    exact ((RecursiveNamedSpecializationBodyFacts.identities accepted).2.2).symm
  obtain ⟨types, lexical, facts, certificate⟩ :=
    sourceAt.frame.instantiated.certificate_of_valid bodies.signatures bodies.function_ids
      (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) owner valid
  have extended := header.extended
  rw [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] at extended
  have contextEq := Dynamic.MonoBindersExtend.functional certificate.typing.inputs_extend extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ certificate⟩

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
    (certifiedAt : CertifiedAt (header := header) (function := function))
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
      certifiedAt
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

include sourceAt in
/-- Original packed typing and actual physical arity fix the complete input row. -/
theorem arguments_at (certifiedAt : CertifiedAt (header := header) (function := function))
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {context : SourceSemantics.Context} {source : TypedSource} {heap : Dynamic.Heap}
    {values : List Dynamic.Value} {types : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap values types)
    (calleeTyped : Dynamic.ValueHasType context heap (.global function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : header.function.parameters.length = values.length) :
    Dynamic.HeapWellTyped header.function.context heap ∧
      Dynamic.ValuesHaveTypes header.function.context heap values header.types ∧
      Dynamic.TypeContextSupports header.context context := by
  obtain ⟨facts, certificate⟩ := certifiedAt
  rcases calleeTyped.global_inv with ordinary | staged
  · obtain ⟨typeEq, _, _⟩ := ordinary
    obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack values
    have packedTyped := bundle ▸ packing.hasType argumentsTyped
    have parameterEq := (TypeSystem.Ty.function.inj (typeEq.trans certificate.callable_type)).1
    rw [parameterEq] at packedTyped
    have signatures := certificate.signatures_eq.trans runtime.signatures.symm
    have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
      runtime.variables_closed certificate.residual_type_variables_open
    have bodyPacked := packedTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
      runtime.variables_closed certificate.residual_type_variables_open
    have length : values.length = header.types.length := arity.symm.trans
      ((congrArg List.length sourceAt.frame.parameters).trans certificate.typing.inputs_extend.length_eq)
    have bodyArguments := packing.unpackTypes bodyPacked length
    exact ⟨sourceAt.frame.context.symm ▸ bodyHeap, sourceAt.frame.context.symm ▸ bodyArguments,
      SelectedCompilationNamedAdmission.caller_supports certified runtime⟩
  · obtain ⟨inner, impossible, _⟩ := staged
    cases impossible

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
