import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
import Solcore.SourceSemantics.CoreLowering.RecursivePublicCallableArity

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPackedNamedArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
section SourceAdmission
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}

theorem arguments_at_global (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (certifiedAt : SelectedCompilationNamedArgumentRows.CertifiedAt (header := header) (function := source))
    {context : SourceSemantics.Context} {bodySource : TypedSource} {before : Dynamic.Heap}
    {arguments : List Dynamic.Value} {packed : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context bodySource)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (callableTyped : Dynamic.ValueHasType context before (.global source) (.function parameter result))
    (packing : Dynamic.ValuesPack arguments packed)
    (packedTyped : Dynamic.ValueHasType context before packed parameter)
    (arity : header.function.parameters.length = arguments.length) :
    Dynamic.HeapWellTyped header.function.context before ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  rcases callableTyped.global_inv with ordinary | staged
  · rcases ordinary with ⟨typeEq, _valid, _evidence⟩
    obtain ⟨facts, certified⟩ := certifiedAt
    have parameterEq := (TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)).1
    rw [parameterEq] at packedTyped
    have signatures := certified.signatures_eq.trans runtime.signatures.symm
    have bodyHeap := heapTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have bodyPacked := packedTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have length : arguments.length = header.types.length := arity.symm.trans
      ((congrArg List.length sourceAt.frame.parameters).trans certified.typing.inputs_extend.length_eq)
    have bodyArguments := packing.unpackTypes bodyPacked length
    exact ⟨sourceAt.frame.context.symm ▸ bodyHeap, sourceAt.frame.context.symm ▸ bodyArguments⟩
  · rcases staged with ⟨inner, impossible, innerTyped⟩
    cases impossible

end SourceAdmission

theorem global_count {program : Program} {function : Dynamic.GlobalFunction} {count : Nat}
    (arity : RecursivePublicCallableArity.Arity program (.global function) count)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    {body : Dynamic.BodyInstance}
    (actual : Dynamic.FunctionInstantiates program function.instantiation body) :
    body.source.inputs.length = count := by
  cases arity with
  | global instantiates =>
    cases BuiltinNamedCalls.instantiation_unique owners actual instantiates
    rfl

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPackedNamedArguments
