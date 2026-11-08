import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.Dynamic.Typing
import Solcore.SourceSemantics.Staging.Program
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.SourceSemantics.Dynamic.Fault

/-!
# Whole-program execution

The admitted entry of a program, its outcome, and the preservation of a whole run. Main
declarations: `Dynamic.ProgramEntry`, `Dynamic.ProgramEvaluates`, `Dynamic.ProgramFaults`,
`Dynamic.ProgramOutcome`. Main theorem: `Dynamic.ProgramEvaluates.preserves`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Dynamic.Program
/-!
Whole-program entry and execution for the declarative resolved-source
semantics.

This layer closes the gap between the mutually recursive expression/body
relations and an executable program judgment.  An entry point names one exact
generic function instance, supplies closed trait dictionaries and typed
arguments, and starts in a deeply well-typed heap.  Program admission includes
both static well-formedness and whole-program staging.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend.SourceInference
open TypeSystem

/-- External inputs for one resolved-source program invocation. -/
structure ProgramEntry where
  instantiation : DeclarationInstantiation
  evidence : EvidenceEnvironment
  arguments : List Value
  deriving Repr

/-- An entry point is ready to invoke one exact body instance in the supplied
initial heap.  The argument types are read from the instantiated source
binders, rather than duplicated in this carrier. -/
structure ProgramEntryValid (program : Program) (entry : ProgramEntry)
    (initial : Heap) (bodyInstance : BodyInstance) : Prop where
  instantiates : FunctionInstantiates program entry.instantiation bodyInstance
  evidence_covers : entry.evidence.Covers bodyInstance.context
  heap_typed : HeapWellTyped bodyInstance.context initial
  arguments_typed : ValuesHaveTypes bodyInstance.context initial entry.arguments
    (bodyInstance.source.inputs.map fun binder => binder.scheme.body)

/-- Successful whole-program execution from an explicitly supplied initial
heap.  Unlike an executable driver this relation is fuel-free, and unlike the
body relation it records the static/staging admission proof at the semantic
boundary. -/
inductive ProgramEvaluates (program : Program) (entry : ProgramEntry) :
    Heap → Value → Heap → Prop where
  | run
      {initial final : Heap} {result : Value} {bodyInstance : BodyInstance}
      (admitted : Staging.ProgramHasStages program)
      (entry_valid : ProgramEntryValid program entry initial bodyInstance)
      (invokes : BodyInvokes program bodyInstance entry.evidence initial
        entry.arguments result final) :
      ProgramEvaluates program entry initial result final

/-- The ordinary closed-program observation starts with no allocated cells. -/
def ClosedProgramEvaluates (program : Program) (entry : ProgramEntry)
    (result : Value) (final : Heap) : Prop :=
  ProgramEvaluates program entry ⟨[]⟩ result final

namespace ProgramEvaluates

theorem program_has_stages
    {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {result : Value}
    (evaluates : ProgramEvaluates program entry initial result final) :
    Staging.ProgramHasStages program := by
  cases evaluates with
  | run admitted => exact admitted

theorem program_well_formed
    {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {result : Value}
    (evaluates : ProgramEvaluates program entry initial result final) :
    ProgramWellFormed program :=
  evaluates.program_has_stages.staticallyValid

end ProgramEvaluates

end Solcore.SourceSemantics.Dynamic

/-!
## Consolidated module: `Solcore.SourceSemantics.Dynamic.ProgramPreservation`
-/

/-!
Whole-program preservation for the declarative resolved-source semantics.

The core mutual preservation proof is packaged as
`WholeLanguagePreservation`.  This module connects that package to the
observable `ProgramEvaluates` boundary: the entry-point instantiation supplies
the exact static body certificate, and its source binders determine the
argument types consumed by the invocation theorem.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

namespace ProgramEvaluates

/-- A successful, admitted program execution preserves the instantiated entry
body whenever the whole-language preservation package is supplied.  The body
instance is retained existentially because it is intentionally hidden by the
public program-evaluation judgment. -/
theorem preservesWith
    {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {result : Value}
    (preservation : WholeLanguagePreservation program)
    (evaluates : ProgramEvaluates program entry initial result final) :
    exists bodyInstance,
      ProgramEntryValid program entry initial bodyInstance /\
        BodyInvocationPreserved bodyInstance initial final result := by
  cases evaluates with
  | run admitted entryValid invokes =>
      obtain ⟨inputTypes, lexicalContext, facts, certificate⟩ :=
        entryValid.instantiates.certificate preservation.program_well_formed
      refine ⟨_, entryValid, preservation.invoke (bodyInstance := _)
        (evidence := entry.evidence) (before := initial) (after := final)
        (arguments := entry.arguments) (result := result)
        (inputTypes := inputTypes) (lexicalContext := lexicalContext)
        (facts := facts) certificate.toBodyInstanceTypingCertificate
        entryValid.evidence_covers
        entryValid.heap_typed ?_ invokes⟩
      rw [← Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
        certificate.toBodyInstanceTypingCertificate.typing.inputs_extend]
      exact entryValid.arguments_typed

/-- Successful whole-program execution preserves the exact instantiated entry
body.  Unlike `preservesWith`, this theorem constructs the whole-language
preservation package directly from the static admission carried by the
program-evaluation derivation. -/
theorem preserves
    {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {result : Value}
    (evaluates : ProgramEvaluates program entry initial result final) :
    exists bodyInstance,
      ProgramEntryValid program entry initial bodyInstance /\
        BodyInvocationPreserved bodyInstance initial final result :=
  evaluates.preservesWith
    evaluates.program_well_formed.wholeLanguagePreservation

end ProgramEvaluates

end Solcore.SourceSemantics.Dynamic
end

section
-- leanmerge: from Solcore.SourceSemantics.Dynamic.ProgramOutcome
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
end
