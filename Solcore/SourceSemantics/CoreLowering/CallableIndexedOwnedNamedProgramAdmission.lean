import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramEntrySource
import Solcore.SourceSemantics.Dynamic.ProgramOutcome

/-! Actual named program outcomes supply successful Source value and heap
admission at the returned caller state. Saved stable rows follow the actual
administrative effects. The original program derivation identifies the
Header body and retains independent Source execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedProgramAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission (PostAdmission)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)

/-- Genuine program success supplies raw typing at this returned state.
Fault outcomes retain every actual row's stable history. -/
theorem after_program_outcome
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    {initial final : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State final)
    (stable : StableRows (bridge.pool first))
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (executed : Dynamic.ProgramOutcome program
      (RecursiveNamedProgramEntrySource.entry header arguments) initial.heap outcome final.heap)
    (frame : AdministrativePreserved initial.mapping initial.store final.mapping final.store) :
    PostAdmission bridge header.function.context header.function.resultType outcome last := by
  refine ⟨StableRows.after_administrative (bridge.pool first) (bridge.pool last) stable frame, ?_⟩
  intro value same
  cases executed with
  | value evaluated =>
    cases same
    obtain ⟨bodyInstance, valid, preserved⟩ := evaluated.preserves
    have sameBody := BuiltinNamedCalls.instantiation_unique_of_wellFormed
      evaluated.program_well_formed valid.instantiates header.frame.instantiated
    cases sameBody
    exact ⟨by simpa only [← header.frame.context, ← header.frame.result] using preserved.result_typed,
      by simpa only [← header.frame.context] using preserved.heap_typed⟩
  | fault _ => cases same

/-- Eliminate the original transition once and retain that same returned
state, its actual relation and the program-derived post-admission. -/
theorem after_program_transition
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    {initial final : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial)
    (stable : StableRows (bridge.pool first))
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (executed : Dynamic.ProgramOutcome program
      (RecursiveNamedProgramEntrySource.entry header arguments) initial.heap outcome final.heap)
    (frame : AdministrativePreserved initial.mapping initial.store final.mapping final.store)
    (transition : ProtectedStateTransition.Transition callerProtocol first final) :
    ∃ last : callerProtocol.State final,
      callerProtocol.Relates first last ∧
        PostAdmission bridge header.function.context header.function.resultType outcome last := by
  obtain ⟨last, related⟩ := transition
  exact ⟨last, related, after_program_outcome bridge header first last stable executed frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedProgramAdmission
