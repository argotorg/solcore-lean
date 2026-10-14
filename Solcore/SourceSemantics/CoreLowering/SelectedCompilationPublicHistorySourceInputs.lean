import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCurrentFactoryValues

/-! Actual declaration frames supply the callable type and independent Source
runtime needed to preserve the state of a failed public invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicHistorySourceInputs
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)

include bodyTyping

theorem header_runtime
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
  obtain ⟨_, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping header
  rw [header.frame.context, header.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

theorem source_function_type
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD source) :
    header.named.specialized.function.type =
      .function (TypeSystem.Ty.productMany header.types) header.function.resultType := by
  have _actual := sourceAt.retained
  obtain ⟨_, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping header
  have matched := CallableNamedMetadata.matches_of_exact header.target
    (CallableIndexedActualNamedSourceReceipts.header_record compiled header)
  rw [matched.type, certificate.callable_type, header.frame.result]


theorem source_typed
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD source)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram)) (heap : Dynamic.Heap) :
    Dynamic.ValueHasType anchor.function.context heap (.global source)
      (.function (TypeSystem.Ty.productMany header.types) header.function.resultType) := by
  rw [← source_function_type bodyTyping sourceAt]
  exact RecursiveNamedPublicCurrentFactoryValues.source_typed sourceAt anchor heap

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicHistorySourceInputs
