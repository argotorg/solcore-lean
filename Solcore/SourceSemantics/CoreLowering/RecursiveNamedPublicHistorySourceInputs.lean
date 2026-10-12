import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCurrentFactoryValues

/-! Actual declaration frames supply the callable type and independent Source
runtime needed to preserve the state of a failed public invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistorySourceInputs
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include wellFormed

theorem header_runtime
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  rw [header.frame.context, header.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

theorem source_function_type
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD source) :
    header.named.specialized.function.type =
      .function (TypeSystem.Ty.productMany header.types) header.function.resultType := by
  obtain ⟨types, context, facts, certificate⟩ := sourceAt.frame.instantiated.certificate wellFormed
  have extended := header.extended
  rw [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] at extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  have actualType : source.instantiation.type = header.named.specialized.function.type := by
    rw [sourceAt.retained]
    rfl
  rw [← actualType, certificate.callable_type, typesEq, sourceAt.frame.result]

theorem source_typed
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD source)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram)) (heap : Dynamic.Heap) :
    Dynamic.ValueHasType anchor.function.context heap (.global source)
      (.function (TypeSystem.Ty.productMany header.types) header.function.resultType) := by
  rw [← source_function_type wellFormed sourceAt]
  exact RecursiveNamedPublicCurrentFactoryValues.source_typed sourceAt anchor heap

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistorySourceInputs
