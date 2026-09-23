import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.Dynamic.Typing
import Solcore.SourceSemantics.Staging.Program

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
