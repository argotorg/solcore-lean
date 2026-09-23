import Solcore.ContractRuntime.OneLevelNestedCreationState

/-! Active modes of the one-level checked-Core scheduler. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

/-- The currently active machine in the one-level scheduler. -/
inductive Mode
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  | root (frame : RootFrame initialWorld rootContract rootInvocation)
  | child (frame : ChildFrame initialWorld rootContract rootInvocation)
  | initializer
      (frame :
        PreparedInitializerFrame initialWorld rootContract rootInvocation)

namespace Mode

/-- Construct the initial active-root mode from exact installation evidence. -/
def initialRoot
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract) :
    Mode initialWorld rootContract rootInvocation :=
  .root (RootFrame.initial rootContract rootInvocation installed)

/-- Construct an active root over a prepared post-transfer working world. -/
def preparedRoot
    {checkpointWorld workingWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    Mode checkpointWorld rootContract rootInvocation :=
  .root
    (RootFrame.prepared
      (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed)

/-- Administrative rank used with shared fuel to justify mode switching. -/
def rank
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation} :
    Mode initialWorld rootContract rootInvocation → Nat
  | .root _ => 0
  | .child _ => 1
  | .initializer _ => 1

theorem rank_le_one
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (mode : Mode initialWorld rootContract rootInvocation) :
    mode.rank ≤ 1 := by
  cases mode <;> simp [rank]

end Mode

end Solcore.ContractRuntime.OneLevelNestedExecution
