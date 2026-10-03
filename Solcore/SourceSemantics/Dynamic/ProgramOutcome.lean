import Solcore.SourceSemantics.Dynamic.Program
import Solcore.SourceSemantics.Dynamic.Fault

/-! Admitted program observations include language failures and their exact
final heap. This source relation uses the independent body fault semantics;
it makes no claim that every well-typed invocation terminates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Dynamic
open Frontend.SourceInference TypeSystem

inductive ProgramFaults (program : Program) (entry : ProgramEntry) :
    Heap → SemanticFault → Heap → Prop where
  | run {initial final : Heap} {reason : SemanticFault} {bodyInstance : BodyInstance}
      (admitted : Staging.ProgramHasStages program)
      (entry_valid : ProgramEntryValid program entry initial bodyInstance)
      (faults : BodyFaults program bodyInstance entry.evidence initial entry.arguments reason final) :
      ProgramFaults program entry initial reason final

namespace ProgramFaults

theorem program_has_stages {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {reason : SemanticFault}
    (faults : ProgramFaults program entry initial reason final) :
    Staging.ProgramHasStages program := by
  cases faults with
  | run admitted => exact admitted

theorem program_well_formed {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {reason : SemanticFault}
    (faults : ProgramFaults program entry initial reason final) :
    ProgramWellFormed program :=
  faults.program_has_stages.staticallyValid

end ProgramFaults

inductive ProgramOutcome (program : Program) (entry : ProgramEntry) :
    Heap → ExpressionOutcome → Heap → Prop where
  | value {initial final : Heap} {result : Value}
      (evaluates : ProgramEvaluates program entry initial result final) :
      ProgramOutcome program entry initial (.value result) final
  | fault {initial final : Heap} {reason : SemanticFault}
      (faults : ProgramFaults program entry initial reason final) :
      ProgramOutcome program entry initial (.fault reason) final

namespace ProgramOutcome

theorem program_has_stages {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {outcome : ExpressionOutcome}
    (execution : ProgramOutcome program entry initial outcome final) :
    Staging.ProgramHasStages program := by
  cases execution with
  | value evaluated => exact evaluated.program_has_stages
  | fault faults => exact faults.program_has_stages

theorem program_well_formed {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {outcome : ExpressionOutcome}
    (execution : ProgramOutcome program entry initial outcome final) :
    ProgramWellFormed program :=
  execution.program_has_stages.staticallyValid

end ProgramOutcome
end Solcore.SourceSemantics.Dynamic
