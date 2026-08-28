import Solcore.Semantics.FrameCheckpointedWorkingPair
import Solcore.Semantics.FrameTraceExtension

/-! Parent-indexed construction of initial frame state values. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

/-- Caller-supplied initial state values relative to one parent working pair. -/
structure ParentIndexedFrameInitialization
    (RollbackState : Type u) (Event : Type v)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :
    Type (max u v) where
  initialWorld : WorldState
  workingRollback : RollbackState

namespace ParentIndexedFrameInitialization

/-- Start an event-only trace extension at the indexed parent trace. -/
def initialTraceExtension
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (_initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    FrameTrace.ExtensionFrom parentWorking.2.trace :=
  FrameTrace.ExtensionFrom.start parentWorking.2.trace

/-- Build checkpointed values from the parent and caller-supplied state. -/
def toCheckpointedWorkingPair
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    FrameCheckpointedWorkingPair RollbackState (FrameTrace Event) :=
  ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
    (initialization.initialWorld,
      ⟨initialization.workingRollback,
        initialization.initialTraceExtension.toTrace⟩)⟩

end ParentIndexedFrameInitialization

end Solcore.Semantics
