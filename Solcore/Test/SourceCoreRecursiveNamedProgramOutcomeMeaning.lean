import Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramOutcomeMeaning

/-! The consumer covers both native result branches and keeps all actual
initial input, catalog authority and profile conditions in its signature. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedProgramOutcomeMeaning
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap

abbrev program_has_sufficient_native_fuel :=
  @RecursiveNamedProgramOutcomeMeaning.program_has_sufficient_native_fuel

abbrev completed_run_reflects_program :=
  @RecursiveNamedProgramOutcomeMeaning.completed_run_reflects_program

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty}
  {faults : FunctionCalls.FaultRep} {program : SourceSemantics.Program} {entry : Dynamic.ProgramEntry}
  {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}

theorem successful_result_observes_source_value {payload : Core.Value}
    (executed : Dynamic.ProgramOutcome program entry before outcome after)
    (represented : FunctionCalls.ResultRepresents model mapping world sourceType type faults
      outcome (.inRight .word payload)) :
    ∃ value, Dynamic.ProgramEvaluates program entry before value after ∧
      model.Represents mapping world sourceType value payload type := by
  cases represented with
  | value payload =>
    cases executed with
    | value evaluated => exact ⟨_, evaluated, payload⟩

theorem failed_result_observes_source_fault {token : Word}
    (executed : Dynamic.ProgramOutcome program entry before outcome after)
    (represented : FunctionCalls.ResultRepresents model mapping world sourceType type faults
      outcome (.inLeft type (.word token))) :
    ∃ reason, Dynamic.ProgramFaults program entry before reason after ∧ faults reason token := by
  cases represented with
  | fault related =>
    cases executed with
    | fault failed => exact ⟨_, failed, related⟩

end Tests.SourceCoreRecursiveNamedProgramOutcomeMeaning
