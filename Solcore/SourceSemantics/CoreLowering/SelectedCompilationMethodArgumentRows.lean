import Solcore.SourceSemantics.SelectedOperatorTypingCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOperatorSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment

/-! Actual operator typing fixes the raw method argument vector before native
packing. The selected method carries the same result and reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context caller stages)

/-- Empty output coercions identify the complete owned requirement row. -/
theorem requirements : receipt.operator.requirements = receipt.node.requirements := by
  have layout := CallableCallRequirementLayouts.ordinary_owned receipt.operator.ordinary
  simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm

/-- The independent parent judgment supplies the real trait profile and its
ordered operand types. This uses no equality of native packed types. -/
theorem source_facts (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ∃ operand parameterTypes returnTypes predicates,
      ExpressionsHaveTypes source context receipt.arguments parameterTypes ∧
      OperatorProfileInstantiates context port.principal.traitName port.principal.methodName
        operand parameterTypes returnTypes predicates ∧
      RequirementSequenceProves context receipt.node.requirements predicates ∧
      receipt.node.type = TypeSystem.Ty.productMany returnTypes := by
  obtain ⟨selected⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted receipt.operator
  have names : selected.traitName = port.principal.traitName ∧
      selected.methodName = port.principal.methodName := by
    rcases port.dispatch with ⟨operator, operand, form, dispatch⟩ |
      ⟨operator, left, right, form, dispatch⟩
    · have actual := selected.dispatch
      rw [form] at actual
      exact CallablePreparedOperatorSourceBounds.unary_dispatch_unique actual dispatch
    · have actual := selected.dispatch
      rw [form] at actual
      exact CallablePreparedOperatorSourceBounds.binary_dispatch_unique actual dispatch
  obtain ⟨operand, parameterTypes, returnTypes, predicates, children, profile, proves, result⟩ :=
    CallableIndexedOwnedOperatorSourceAdmission.source_facts selected unique receipt.metadata.coercions typed
  exact ⟨operand, parameterTypes, returnTypes, predicates, children,
    names.1 ▸ names.2 ▸ profile, requirements receipt ▸ proves, result⟩

/-- Full Source typing identifies raw parameters and the result of the same
selected method, including the one-Unit versus no-argument distinction. -/
theorem raw_types
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller
      port.principal.traitName port.principal.methodName receipt.node.requirements
      port.principal.sourceBody port.principal.dictionary)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ExpressionsHaveTypes source context receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) ∧
      port.principal.sourceBody.resultType = receipt.node.type := by
  obtain ⟨operand, parameterTypes, returnTypes, predicates, children, profile, proves, result⟩ :=
    source_facts receipt port unique typed
  obtain ⟨lexical, facts, certificate, bodyResult⟩ := selected.certificateOfProfile catalog
    runtime.signatures runtime.requirements.idsUnique profile proves
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend
  rw [port.sourceAt.parameters, List.map_map] at types
  exact ⟨types ▸ children, bodyResult.trans result.symm⟩

/-- The genuinely reached operand heap is transported to the selected method's
Source context. The full dictionary remains the one retained by the port. -/
theorem at_values
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller
      port.principal.traitName port.principal.methodName receipt.node.requirements
      port.principal.sourceBody port.principal.dictionary)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    {heap : Dynamic.Heap} {arguments : List Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body))) :
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap ∧
      Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types ∧
      port.principal.sourceBody.resultType = receipt.node.type := by
  obtain ⟨operand, parameterTypes, returnTypes, predicates, _, profile, proves, result⟩ :=
    source_facts receipt port unique typed
  obtain ⟨lexical, facts, certificate, bodyResult⟩ := selected.certificateOfProfile catalog
    runtime.signatures runtime.requirements.idsUnique profile proves
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := argumentsTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq port.sourceAt.extended
  rw [port.sourceAt.parameters, List.map_map] at types
  exact ⟨port.principal.source_frame.context.symm ▸ bodyHeap,
    port.principal.source_frame.context.symm ▸ (types ▸ bodyArguments), bodyResult.trans result.symm⟩

/-- Successful method result typing is returned to the actual caller context. -/
theorem result_at_values
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller
      port.principal.traitName port.principal.methodName receipt.node.requirements
      port.principal.sourceBody port.principal.dictionary)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    {before after : Dynamic.Heap} {value : Dynamic.Value}
    (preserved : Dynamic.ExpressionEvaluationPreserved port.principal.sourceBody.context before after
      value port.principal.sourceBody.resultType) :
    Dynamic.ValueHasType context after value receipt.node.type ∧ Dynamic.HeapWellTyped context after := by
  obtain ⟨operand, parameterTypes, returnTypes, predicates, _children, profile, proves, result⟩ :=
    source_facts receipt port unique typed
  obtain ⟨lexical, facts, certificate, bodyResult⟩ := selected.certificateOfProfile catalog
    runtime.signatures runtime.requirements.idsUnique profile proves
  have signatures := runtime.signatures.trans certificate.signatures_eq.symm
  have resultTyped := preserved.value_typed.transportClosed signatures certificate.type_parameters_empty
    runtime.closed certificate.type_variables_empty runtime.residual_variables_open
  have heapTyped := preserved.heap_typed.transportClosed signatures certificate.type_parameters_empty
    runtime.closed certificate.type_variables_empty runtime.residual_variables_open
  exact ⟨(bodyResult.trans result.symm) ▸ resultTyped, heapTyped⟩

/-- Native bundles are aligned only after the raw row has fixed the arity. -/
theorem represented_arguments
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body))
      (receipt.codes.map (·.type)) arguments payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads := by
  have binderCount : arguments.length = port.principal.named.inputs.length := by
    simpa only [List.length_map] using
      (CallableIndexedOwnedStoredArgumentAlignment.source_length represented).symm
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (port.principal.named.inputs.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type receipt.codes).symm.trans
      (receipt.parameter.symm.trans
        ((congrArg SourceCoreCalls.Signature.parameterType port.signature).symm.trans port.sourceAt.parameterType))
  exact CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    port.principal.named.inputs represented binderCount rfl nativePacked

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentRows
