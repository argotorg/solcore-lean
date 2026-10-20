import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservation

/-! Actual parameter allocation and the reached staged fault determine deep
heap typing. Both semantic faults and earlier stage stops use the same original
Source body certificate; native result shapes supply no typing premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedFaultHeap
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedAdmittedBodyEntries

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (support : SelectedCompilationNamedSupport.Support compiled)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {scope : Staging.Recursive.Scope}
  (selected : (SelectedCompilationPhysicalProgramSupport.stages compiled).Closure header.function scope)
  {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
  (heapTyped : Dynamic.HeapWellTyped header.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)

include support selected heapTyped argumentsTyped allocated in
theorem after_fault_selected {size : Nat} {finalContext : SourceSemantics.Context} {failure : Staging.Recursive.Failure}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled) size scope header.context environment bound
      header.function.body finalContext (.fault failure) after) :
    Dynamic.HeapWellTyped header.context after := by
  have receipt := SelectedCompilationNamedAdmission.parameter_source (support.certified header) allocated heapTyped argumentsTyped
  have sourceEq := (SelectedCompilationPhysicalProgramSupport.stages compiled).source selected
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context scope.source := by
    simpa only [sourceEq] using receipt.runtime
  have covers : scope.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages compiled).evidence selected] using receipt.covers
  obtain ⟨final, facts, typed, _complete⟩ := receipt.bodyTyped
  have actualTyped : StatementsHaveType scope.source { returnType := header.function.resultType }
      header.context header.function.body final facts := by
    simpa only [sourceEq] using typed
  exact (Staging.Recursive.SelectedPreservation.statements support.registryBodies
    runtime covers receipt.locals receipt.heapTyped actualTyped trace).heap_typed

/- Compatibility adapters for callers with a whole-program receipt. -/
include wellFormed selected heapTyped argumentsTyped allocated in
theorem after_fault {size : Nat} {finalContext : SourceSemantics.Context} {failure : Staging.Recursive.Failure}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled) size scope header.context environment bound
      header.function.body finalContext (.fault failure) after) :
    Dynamic.HeapWellTyped header.context after := by
  apply after_fault_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (selected := selected) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (allocated := allocated) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedFaultHeap
