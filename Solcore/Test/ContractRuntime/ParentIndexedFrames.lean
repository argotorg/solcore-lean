import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction
import Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
import Solcore.ContractRuntime.FrameTrace
import Solcore.ContractRuntime.ParentIndexedFrameInitialization
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
import Solcore.ContractRuntime.ParentIndexedFrameResolutionFold
import Solcore.ContractRuntime.ParentIndexedFrameResolutionView
import Solcore.ContractRuntime.FrameResolutionResult
import Solcore.ContractRuntime.ParentIndexedFrameTrapPropagationPayload
import Solcore.ContractRuntime.ParentIndexedFrameTrapRollback

/-!
# Parent-indexed frame tests

Parent-indexed frames: construction, initialization, the resolution view and fold, and trap
propagation and rollback.
-/

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameContinuationConstruction
/-! Definition-only tests for trace-extension parent-context construction. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ConstructionEvent where
  | parent
  | nested

private inductive ConstructionReason where
  | marker

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩
private def parentValue : Core.Word := ⟨0xaa, by decide⟩
private def nestedValue : Core.Word := ⟨0xbb, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def parentTrace : FrameTrace ConstructionEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace ConstructionEvent) :=
  (stateWith parentValue, ⟨10, parentTrace⟩)

private def extension : FrameTrace.ExtensionFrom parentWorking.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking.2.trace).record .nested

private def result : FrameRunResult ConstructionReason :=
  ⟨stateWith nestedValue, .returned [0x12].toByteArray⟩

private def context :
    ParentIndexedFrameContinuationContext Nat ConstructionEvent
      ConstructionReason parentWorking :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking 20 extension result

private def isParentTrace : List ConstructionEvent → Bool
  | [.parent] => true
  | _ => false

private def isExtendedTrace : List ConstructionEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesCheckpoints : Bool :=
  observedValue? context.stateCheckpoint == some parentValue &&
    context.effectCheckpoint.rollback == 10 &&
    isParentTrace context.effectCheckpoint.trace.toList

private def matchesWorkingEffects : Bool :=
  context.effectWorking.rollback == 20 &&
    isExtendedTrace context.effectWorking.trace.toList

private def matchesResult : Bool :=
  observedValue? context.result.working == some nestedValue &&
    match context.result.outcome with
    | .returned data => data == [0x12].toByteArray
    | _ => false

def testParentIndexedFrameContinuationConstruction : IO Unit := do
  assertTrue matchesCheckpoints
    "construction must copy the observed parent checkpoints"

  assertTrue matchesWorkingEffects
    "construction must combine working rollback with one exact trace extension"

  assertTrue matchesResult
    "construction must preserve the supplied frame result"

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameContinuationContext
/-! Definition-only tests for parent-indexed frame continuation contexts. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ParentIndexedEvent where
  | parent
  | nested

private inductive ParentIndexedReason where
  | marker

private def parentTrace_variant : FrameTrace ParentIndexedEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking_variant :
    WorldState × FrameEffectJournal Nat (FrameTrace ParentIndexedEvent) :=
  (stateWith parentValue, ⟨10, parentTrace_variant⟩)

private def extension_variant : FrameTrace.ExtensionFrom parentWorking_variant.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking_variant.2.trace).record .nested

private def contextWith (outcome : FrameOutcome ParentIndexedReason) :
    ParentIndexedFrameContinuationContext Nat ParentIndexedEvent
      ParentIndexedReason parentWorking_variant :=
  let base :
      FrameContinuationContext Nat (FrameTrace ParentIndexedEvent)
        ParentIndexedReason :=
    ⟨parentWorking_variant.1, parentWorking_variant.2, ⟨20, extension_variant.toTrace⟩,
      ⟨stateWith nestedValue, outcome⟩⟩
  let prefixed :
      FrameContinuationContextWithTracePrefix Nat ParentIndexedEvent
        ParentIndexedReason :=
    ⟨base, extension_variant.earlier_isPrefixOf_toTrace⟩
  ⟨prefixed, rfl⟩

private def matchesTrace : List ParentIndexedEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesReturn? :
    FrameResolutionResult Nat (FrameTrace ParentIndexedEvent)
      ParentIndexedReason → Bool
  | .returned state effects data =>
      observedValue? state == some nestedValue &&
        effects.rollback == 20 && matchesTrace effects.trace.toList &&
        data == [0x12].toByteArray
  | _ => false

private def matchesRevert? :
    FrameResolutionResult Nat (FrameTrace ParentIndexedEvent)
      ParentIndexedReason → Bool
  | .reverted state effects data =>
      observedValue? state == some parentValue &&
        effects.rollback == 10 && matchesTrace effects.trace.toList &&
        data == [0x34].toByteArray
  | _ => false

private def matchesTrap? :
    FrameResolutionResult Nat (FrameTrace ParentIndexedEvent)
      ParentIndexedReason → Bool
  | .trapped .marker => true
  | _ => false

def testParentIndexedFrameContinuationContext : IO Unit := do
  assertTrue
    (matchesReturn? (contextWith (.returned [0x12].toByteArray)).resolve)
    "return must select nested working state, effects, trace, and payload"

  assertTrue
    (matchesRevert? (contextWith (.reverted [0x34].toByteArray)).resolve)
    "revert must restore the indexed parent pair and keep the accumulated trace"

  assertTrue
    (matchesTrap? (contextWith (.trapped .marker)).resolve)
    "trap must preserve only the concrete reason"

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameContinuationContextTrapReasonMap
/-! Definition-only compile regressions for parent-indexed reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

universe u v w x

private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason)
    (checkpointEq :
      (context.stateCheckpoint, context.effectCheckpoint) = parentWorking) :
    ParentIndexedFrameContinuationContext.mapTrapReason mapReason
        (⟨context, checkpointEq⟩ :
          ParentIndexedFrameContinuationContext
            RollbackState Event TrapReason parentWorking) =
      (⟨context.mapTrapReason mapReason, checkpointEq⟩ :
        ParentIndexedFrameContinuationContext
          RollbackState Event MappedTrapReason parentWorking) := by
  rfl

private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.stateCheckpoint, context.effectCheckpoint) = parentWorking :=
  (context.mapTrapReason mapReason).checkpoint_eq_parentWorking

private inductive SourceReason where
  | marker
  | other

private inductive TargetReason where
  | mapped
  | other

private def mapReason : SourceReason → TargetReason
  | .marker => .mapped
  | .other => .other

private inductive Event where
  | parent
  | nested

private def parentTrace_variant2 : FrameTrace Event :=
  FrameTrace.record FrameTrace.empty .parent

private def nestedFragment : FrameTrace Event :=
  FrameTrace.record FrameTrace.empty .nested

private def nestedTrace : FrameTrace Event :=
  FrameTrace.append parentTrace_variant2 nestedFragment

private def parentJournal : FrameEffectJournal Nat (FrameTrace Event) :=
  ⟨10, parentTrace_variant2⟩

private def nestedJournal : FrameEffectJournal Nat (FrameTrace Event) :=
  ⟨20, nestedTrace⟩

private def parentWorking_variant2 :
    WorldState × FrameEffectJournal Nat (FrameTrace Event) :=
  (stateWith parentValue, parentJournal)

private theorem prefixEvidence :
    FrameTrace.IsPrefixOf parentTrace_variant2 nestedTrace :=
  ⟨nestedFragment, rfl⟩

private def concreteContext :
    ParentIndexedFrameContinuationContext
      Nat Event SourceReason parentWorking_variant2 :=
  ⟨⟨⟨stateWith parentValue, parentJournal, nestedJournal,
        ⟨stateWith nestedValue, .trapped .marker⟩⟩,
      prefixEvidence⟩,
    rfl⟩

private example :
    concreteContext.mapTrapReason mapReason =
      (⟨⟨⟨stateWith parentValue, parentJournal, nestedJournal,
            ⟨stateWith nestedValue, FrameOutcome.trapped .mapped⟩⟩,
          prefixEvidence⟩,
        rfl⟩ :
        ParentIndexedFrameContinuationContext
          Nat Event TargetReason parentWorking_variant2) := by
  rfl

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameInitialization
/-! Compile-only regressions for parent-indexed frame initialization. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.initialTraceExtension.toTrace =
      parentWorking.2.trace := by
  simp

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.toCheckpointedWorkingPair =
      ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
        (initialization.initialWorld,
          ⟨initialization.workingRollback, parentWorking.2.trace⟩)⟩ := by
  simp

private example
    {RollbackState Event Result : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (consume :
      FrameCheckpointedWorkingPair RollbackState (FrameTrace Event) → Result) :
    consume initialization.toCheckpointedWorkingPair =
      consume
        ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
          (initialization.initialWorld,
            ⟨initialization.workingRollback, parentWorking.2.trace⟩)⟩ := by
  simp

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameInitializationContinuationContextCoherence
/-! Compile-only regressions for initialization continuation-context coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x

private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (outcome : FrameOutcome TrapReason) :
    (ParentIndexedFrameContinuationContext.fromTraceExtension
      parentWorking initialization.workingRollback
      initialization.initialTraceExtension
      ⟨initialization.initialWorld, outcome⟩).toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        initialization.toCheckpointedWorkingPair outcome := by
  exact
    ParentIndexedFrameInitialization.toFrameContinuationContext_fromTraceExtension_eq_fromCheckpointedWorkingPair
      initialization outcome

private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (outcome : FrameOutcome TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Option Next) :
    (ParentIndexedFrameContinuationContext.fromTraceExtension
      parentWorking initialization.workingRollback
      initialization.initialTraceExtension
      ⟨initialization.initialWorld, outcome⟩).toFrameContinuationContext.continue?
        next =
      (FrameContinuationContext.fromCheckpointedWorkingPair
        initialization.toCheckpointedWorkingPair outcome).continue? next := by
  exact congrArg (fun context => context.continue? next)
    (ParentIndexedFrameInitialization.toFrameContinuationContext_fromTraceExtension_eq_fromCheckpointedWorkingPair
      initialization outcome)

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameInitializationPresentStorageAccount
/-! Compile-only regressions for initialized present-storage refinement. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState Event : Type}
    {parentWorking :
      Solcore.ContractRuntime.WorldState ×
        Solcore.ContractRuntime.FrameEffectJournal RollbackState
          (Solcore.ContractRuntime.FrameTrace Event)}
    (initialization :
      Solcore.ContractRuntime.ParentIndexedFrameInitialization
        RollbackState Event parentWorking)
    (storageAddress : Solcore.ContractRuntime.Address)
    (absent :
      initialization.initialWorld.account? storageAddress = none) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = none := by
  exact
    Solcore.ContractRuntime.ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
      initialization storageAddress absent

private example
    {RollbackState Event : Type}
    {parentWorking :
      Solcore.ContractRuntime.WorldState ×
        Solcore.ContractRuntime.FrameEffectJournal RollbackState
          (Solcore.ContractRuntime.FrameTrace Event)}
    (initialization :
      Solcore.ContractRuntime.ParentIndexedFrameInitialization
        RollbackState Event parentWorking)
    (storageAddress : Solcore.ContractRuntime.Address)
    (account : Solcore.ContractRuntime.Account)
    (present :
      initialization.initialWorld.account? storageAddress = some account) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress =
      some
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          present⟩ := by
  exact
    Solcore.ContractRuntime.ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
      initialization storageAddress account present

private example
    {RollbackState Event : Type}
    {parentWorking :
      Solcore.ContractRuntime.WorldState ×
        Solcore.ContractRuntime.FrameEffectJournal RollbackState
          (Solcore.ContractRuntime.FrameTrace Event)}
    (initialization :
      Solcore.ContractRuntime.ParentIndexedFrameInitialization
        RollbackState Event parentWorking)
    (storageAddress : Solcore.ContractRuntime.Address)
    (account : Solcore.ContractRuntime.Account)
    (present :
      initialization.initialWorld.account? storageAddress = some account)
    (slot value : Solcore.Core.Word) :
    (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress).map
        (fun context =>
          (context.writeStorage slot value).readStorage slot) =
      some value := by
  rw [
    Solcore.ContractRuntime.ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
      initialization storageAddress account present]
  exact
    congrArg some
      (Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          present⟩
        slot value)

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameInitializationStorageAddress
/-! Compile-only regressions for storage-address initialization wiring. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).storageAddress = storageAddress := by
  simp

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).values = initialization.toCheckpointedWorkingPair := by
  simp

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) (slot value : Core.Word) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).writeStorage? slot value =
      (initialization.toCheckpointedWorkingPair.writeWorkingStorage?
        storageAddress slot value).map fun values =>
          ⟨storageAddress, values⟩ := by
  simp only [FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?,
    ParentIndexedFrameInitialization.storageAddress_toCheckpointedWorkingPairWithStorageAddress,
    ParentIndexedFrameInitialization.values_toCheckpointedWorkingPairWithStorageAddress]

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameResolutionFold
/-! Definition-only tests for the parent-indexed resolution fold. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ResolutionFoldEvent where
  | parent
  | nested

private inductive ResolutionFoldReason where
  | marker
  | other

private inductive ResolutionFoldMarker where
  | returned
  | reverted
  | trapped
  | mismatch
  deriving BEq

private def workingValue : Core.Word := ⟨0xbb, by decide⟩

private def parentTrace_variant3 : FrameTrace ResolutionFoldEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def nestedFragment_variant : FrameTrace ResolutionFoldEvent :=
  FrameTrace.record FrameTrace.empty .nested

private def nestedTrace_variant : FrameTrace ResolutionFoldEvent :=
  FrameTrace.append parentTrace_variant3 nestedFragment_variant

private def parentJournal_variant :
    FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent) :=
  ⟨10, parentTrace_variant3⟩

private def workingJournal :
    FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent) :=
  ⟨20, nestedTrace_variant⟩

private def parentWorking_variant3 :
    WorldState × FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent) :=
  (stateWith parentValue, parentJournal_variant)

private theorem tracePrefix :
    FrameTrace.IsPrefixOf parentTrace_variant3 nestedTrace_variant :=
  ⟨nestedFragment_variant, rfl⟩

private def contextWith_variant (outcome : FrameOutcome ResolutionFoldReason) :
    ParentIndexedFrameContinuationContext Nat ResolutionFoldEvent
      ResolutionFoldReason parentWorking_variant3 :=
  ⟨⟨⟨parentWorking_variant3.1, parentWorking_variant3.2, workingJournal,
        ⟨stateWith workingValue, outcome⟩⟩,
      tracePrefix⟩,
    rfl⟩

private def isNestedTrace : List ResolutionFoldEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesValues
    (expectedValue : Core.Word) (expectedRollback : Nat)
    (values :
      WorldState ×
        FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent)) : Bool :=
  observedValue? values.1 == some expectedValue &&
    values.2.rollback == expectedRollback &&
    isNestedTrace values.2.trace.toList

private def onReturned
    (values :
      WorldState ×
        FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent))
    (data : Bytes) : ResolutionFoldMarker :=
  if matchesValues workingValue 20 values && data == [0x12].toByteArray then
    .returned
  else
    .mismatch

private def onReverted
    (values :
      WorldState ×
        FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent))
    (data : Bytes) : ResolutionFoldMarker :=
  if matchesValues parentValue 10 values && data == [0x34].toByteArray then
    .reverted
  else
    .mismatch

private def onTrapped
    (values :
      WorldState ×
        FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent))
    (reason : ResolutionFoldReason) : ResolutionFoldMarker :=
  if matchesValues parentValue 10 values then
    match reason with
    | .marker => .trapped
    | .other => .mismatch
  else
    .mismatch

def testParentIndexedFrameResolutionFold : IO Unit := do
  assertTrue
    ((contextWith_variant (.returned [0x12].toByteArray)).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped == .returned)
    "return must select the terminal working pair and exact bytes"

  assertTrue
    ((contextWith_variant (.reverted [0x34].toByteArray)).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped == .reverted)
    "revert must select the parent rollback pair, working trace, and bytes"

  assertTrue
    ((contextWith_variant (.trapped .marker)).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped == .trapped)
    "trap must select the parent rollback pair and exact reason"

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameResolutionFoldProperties
/-! Compile-only consumers of parent-indexed resolution-fold laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x

/-- The returned branch law is consumed without unfolding the fold. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReturned (context.result.working, context.effectWorking) data := by
  exact context.foldResolutionWithTrapRollback_returned data outcomeEq
    onReturned onReverted onTrapped

/-- The reverted branch law exposes the exact indexed parent rollback pair. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReverted
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) data := by
  exact context.foldResolutionWithTrapRollback_reverted data outcomeEq
    onReturned onReverted onTrapped

private inductive ResolutionFoldCompileMarker where
  | trapped

/-- Choosing an optional result does not make the fold reject a trapped branch. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.foldResolutionWithTrapRollback
        (fun _ _ => none)
        (fun _ _ => none)
        (fun _ _ => some ResolutionFoldCompileMarker.trapped) =
      some ResolutionFoldCompileMarker.trapped := by
  rw [context.foldResolutionWithTrapRollback_trapped reason outcomeEq]

/-- The fourth law reconstructs the complete ADR-0127 view directly. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    context.foldResolutionWithTrapRollback
        (fun values data =>
          (FrameResolutionResult.returned values.1 values.2 data, none))
        (fun values data =>
          (FrameResolutionResult.reverted values.1 values.2 data, none))
        (fun values reason =>
          (FrameResolutionResult.trapped reason, some values)) =
      context.resolveWithTrapRollback := by
  exact context.foldResolutionWithTrapRollback_reconstructs_view

/-- ADR-0125 completion exposes the exact plain context and reconstructed view. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation))) :
    ∃ context continuation,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation) ∧
      parentContinuation.toFrameContinuationContext = continuation ∧
      parentContinuation.foldResolutionWithTrapRollback
          (fun values data =>
            (FrameResolutionResult.returned values.1 values.2 data, none))
          (fun values data =>
            (FrameResolutionResult.reverted values.1 values.2 data, none))
          (fun values reason =>
            (FrameResolutionResult.trapped reason, some values)) =
        parentContinuation.resolveWithTrapRollback := by
  obtain ⟨context, continuation, refined, lowerCompleted, coherent⟩ :=
    initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_toFrameContinuationContext
      storageAddress inputs fuel doneOutcome parentContinuation completed
  exact ⟨context, continuation, refined, lowerCompleted, coherent,
    parentContinuation.foldResolutionWithTrapRollback_reconstructs_view⟩

/-- Additional fuel preserves both the nested boundary and exact fold result. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking}
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next)
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)))
    (more : fuel ≤ largerFuel) :
    ∃ largerContinuation,
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs largerFuel doneOutcome =
        some (some (some largerContinuation)) ∧
      largerContinuation.foldResolutionWithTrapRollback
          onReturned onReverted onTrapped =
        parentContinuation.foldResolutionWithTrapRollback
          onReturned onReverted onTrapped := by
  refine ⟨parentContinuation, ?_, rfl⟩
  exact
    initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
      storageAddress inputs doneOutcome completed more

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameResolutionFoldTrapReasonMap
/-! Compile-only consumers of resolution-fold reason-mapping naturality. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y z

/-- One heterogeneous mapping uses the fold law directly. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        MappedTrapReason → Next) :
    (context.mapTrapReason mapReason).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      context.foldResolutionWithTrapRollback
        onReturned onReverted
        (fun values reason => onTrapped values (mapReason reason)) := by
  exact context.foldResolutionWithTrapRollback_mapTrapReason
    mapReason onReturned onReverted onTrapped

/-- Identity reason mapping normalizes to the original fold. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    (context.mapTrapReason (fun reason => reason)
        ).foldResolutionWithTrapRollback
          onReturned onReverted onTrapped =
      context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped := by
  simp

/-- Nested mappings normalize to one composed trap function. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y} {Next : Type z}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        MappedTrapReason → Next) :
    ((context.mapTrapReason first).mapTrapReason second
        ).foldResolutionWithTrapRollback
          onReturned onReverted onTrapped =
      context.foldResolutionWithTrapRollback
        onReturned onReverted
        (fun values reason => onTrapped values (second (first reason))) := by
  simp

/-- Fold reconstruction commutes with resolution-view reason mapping. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.mapTrapReason mapReason).foldResolutionWithTrapRollback
        (fun values data =>
          (FrameResolutionResult.returned values.1 values.2 data, none))
        (fun values data =>
          (FrameResolutionResult.reverted values.1 values.2 data, none))
        (fun values reason =>
          (FrameResolutionResult.trapped reason, some values)) =
      (FrameResolutionResult.mapTrapReason mapReason
          (context.resolveWithTrapRollback).1,
        (context.resolveWithTrapRollback).2) := by
  rw [(context.mapTrapReason mapReason
    ).foldResolutionWithTrapRollback_reconstructs_view]
  exact context.resolveWithTrapRollback_mapTrapReason mapReason

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameResolutionView
/-! Compile-only consumers of the parent-indexed resolution view. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x

/-- Returned resolution selects the returned callback and no trap rollback. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    (context.resolveWithTrapRollback).1.continue?
          onReturned onReverted =
        onReturned
          (context.result.working, context.effectWorking) data ∧
      (context.resolveWithTrapRollback).2 = none ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have branch := context.resolveWithTrapRollback_returned data outcomeEq
  constructor
  · simp only [branch.1, FrameResolutionResult.continue?_returned]
  · constructor
    · simp only [branch.1]
    · exact branch.2

/-- Reverted resolution selects the reverted callback and no trap rollback. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    (context.resolveWithTrapRollback).1.continue?
          onReturned onReverted =
        onReverted
          (parentWorking.1,
            ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) data ∧
      (context.resolveWithTrapRollback).2 = none ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have branch := context.resolveWithTrapRollback_reverted data outcomeEq
  constructor
  · simp only [branch.1, FrameResolutionResult.continue?_reverted]
  · constructor
    · simp only [branch.1]
    · exact branch.2

/-- Trap rejects both callbacks while selecting the exact parent rollback. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    (context.resolveWithTrapRollback).1.continue?
          onReturned onReverted = none ∧
      (context.resolveWithTrapRollback).2 =
        some
          (parentWorking.1,
            ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have branch := context.resolveWithTrapRollback_trapped reason outcomeEq
  constructor
  · simp only [branch.1, FrameResolutionResult.continue?_trapped]
  · constructor
    · simp only [branch.1]
    · exact branch.2

/-- The public inverse law recovers exactly the trapped rollback selection. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (values :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :
    (context.resolveWithTrapRollback).2 = some values ↔
      ∃ reason,
        context.result.outcome = FrameOutcome.trapped reason ∧
          values =
            (parentWorking.1,
              ⟨parentWorking.2.rollback,
                context.effectWorking.trace⟩) := by
  exact context.resolveWithTrapRollback_snd_eq_some_iff values

/-- ADR-0125 whole-context coherence transports through the first component. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation))) :
    ∃ context continuation,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation) ∧
      parentContinuation.toFrameContinuationContext = continuation ∧
      (parentContinuation.resolveWithTrapRollback).1 =
        continuation.resolve := by
  obtain ⟨context, continuation, refined, lowerCompleted, coherent⟩ :=
    initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_toFrameContinuationContext
      storageAddress inputs fuel doneOutcome parentContinuation completed
  exact ⟨context, continuation, refined, lowerCompleted, coherent, by
    simpa only [
      ParentIndexedFrameContinuationContext.resolveWithTrapRollback] using
      congrArg FrameContinuationContext.resolve coherent⟩

/-- Additional fuel preserves the completed optional boundary and exact view. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking}
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)))
    (more : fuel ≤ largerFuel) :
    ∃ largerContinuation,
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs largerFuel doneOutcome =
        some (some (some largerContinuation)) ∧
      largerContinuation.resolveWithTrapRollback =
        parentContinuation.resolveWithTrapRollback := by
  refine ⟨parentContinuation, ?_, rfl⟩
  exact
    initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
      storageAddress inputs doneOutcome completed more

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameResolutionViewTrapReasonMap
/-! Compile-only consumers of resolution-view reason-mapping naturality. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y z

/-- One heterogeneous mapping uses the whole-product public law directly. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.mapTrapReason mapReason).resolveWithTrapRollback =
      (FrameResolutionResult.mapTrapReason mapReason
          (context.resolveWithTrapRollback).1,
        (context.resolveWithTrapRollback).2) := by
  exact
    ParentIndexedFrameContinuationContext.resolveWithTrapRollback_mapTrapReason
      mapReason context

/-- Nested and composed heterogeneous mappings normalize to the same view. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    ((context.mapTrapReason first).mapTrapReason second
        ).resolveWithTrapRollback =
      (FrameResolutionResult.mapTrapReason
          (fun reason => second (first reason))
          (context.resolveWithTrapRollback).1,
        (context.resolveWithTrapRollback).2) := by
  simp

/-- Identity reason mapping normalizes to the original complete view. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.mapTrapReason (fun reason => reason)).resolveWithTrapRollback =
      context.resolveWithTrapRollback := by
  simp

/-- Callback selection and rollback observation are invariant together. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type z}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    ((((context.mapTrapReason mapReason).resolveWithTrapRollback).1.continue?
        onReturned onReverted),
      ((context.mapTrapReason mapReason).resolveWithTrapRollback).2) =
    (((context.resolveWithTrapRollback).1.continue?
        onReturned onReverted),
      (context.resolveWithTrapRollback).2) := by
  simp

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameTrapPropagationPayload
/-! Definition-only tests for parent-indexed trap propagation payloads. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive TrapPropagationEvent where
  | parent
  | nested

private inductive TrapPropagationReason where
  | marker
  | other

private def parentTrace_variant4 : FrameTrace TrapPropagationEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking_variant4 :
    WorldState × FrameEffectJournal Nat (FrameTrace TrapPropagationEvent) :=
  (stateWith parentValue, ⟨10, parentTrace_variant4⟩)

private def extension_variant2 : FrameTrace.ExtensionFrom parentWorking_variant4.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking_variant4.2.trace).record .nested

private def contextWith_variant2 (outcome : FrameOutcome TrapPropagationReason) :
    ParentIndexedFrameContinuationContext Nat TrapPropagationEvent
      TrapPropagationReason parentWorking_variant4 :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking_variant4 20 extension_variant2 ⟨stateWith nestedValue, outcome⟩

private def isNone {α : Type} : Option α → Bool
  | none => true
  | some _ => false

private def isMarkerTrap : FrameOutcome TrapPropagationReason → Bool
  | .trapped .marker => true
  | _ => false

private def isExtendedTrace_variant : List TrapPropagationEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesTrapPropagationPayload :
    Option
      (FrameRunResult TrapPropagationReason ×
        FrameEffectJournal Nat (FrameTrace TrapPropagationEvent)) → Bool
  | some (result, effects) =>
      observedValue? result.working == some parentValue &&
        isMarkerTrap result.outcome && effects.rollback == 10 &&
        isExtendedTrace_variant effects.trace.toList
  | none => false

def testParentIndexedFrameTrapPropagationPayload : IO Unit := do
  assertTrue
    (isNone
      (contextWith_variant2 (.returned [0x12].toByteArray)).trapPropagationPayload?)
    "return must not select a trap propagation payload"

  assertTrue
    (isNone
      (contextWith_variant2 (.reverted [0x34].toByteArray)).trapPropagationPayload?)
    "revert must not select a trap propagation payload"

  assertTrue
    (matchesTrapPropagationPayload
      (contextWith_variant2 (.trapped .marker)).trapPropagationPayload?)
    "trap must select parent state and rollback with its reason and exact trace"

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameTrapPropagationPayloadCoherence
/-! Compile regressions for parent-indexed trap payload coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive TrapPayloadCoherenceEvent where
  | parent
  | nested

private inductive TrapPayloadCoherenceReason where
  | marker
  | other

private def parentTrace_variant5 : FrameTrace TrapPayloadCoherenceEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking_variant5 :
    WorldState ×
      FrameEffectJournal Nat (FrameTrace TrapPayloadCoherenceEvent) :=
  (stateWith parentValue, ⟨10, parentTrace_variant5⟩)

private def extension_variant3 :
    FrameTrace.ExtensionFrom parentWorking_variant5.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking_variant5.2.trace).record .nested

private def context_variant :
    ParentIndexedFrameContinuationContext Nat TrapPayloadCoherenceEvent
      TrapPayloadCoherenceReason parentWorking_variant5 :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking_variant5 20 extension_variant3
      ⟨stateWith nestedValue, FrameOutcome.trapped .marker⟩

private def expectedPayload :
    FrameRunResult TrapPayloadCoherenceReason ×
      FrameEffectJournal Nat (FrameTrace TrapPayloadCoherenceEvent) :=
  (⟨parentWorking_variant5.1, FrameOutcome.trapped .marker⟩,
    ⟨parentWorking_variant5.2.rollback, extension_variant3.toTrace⟩)

private example :
    context_variant.trapPropagationPayload? = some expectedPayload ∧
      ∃ reason,
        context_variant.result.outcome = FrameOutcome.trapped reason ∧
        expectedPayload =
          (⟨parentWorking_variant5.1, FrameOutcome.trapped reason⟩,
            ⟨parentWorking_variant5.2.rollback, context_variant.effectWorking.trace⟩) := by
  have payloadEq : context_variant.trapPropagationPayload? = some expectedPayload := by
    rfl
  have characterization :=
    (context_variant.trapPropagationPayload?_eq_some_iff expectedPayload).mp payloadEq
  have reconstructed :=
    (context_variant.trapPropagationPayload?_eq_some_iff expectedPayload).mpr
      characterization
  exact ⟨reconstructed, characterization⟩

private example :
    FrameTrace.IsPrefixOf
        parentWorking_variant5.2.trace expectedPayload.2.trace ∧
      expectedPayload.2.trace.toList = [.parent, .nested] := by
  constructor
  · exact context_variant.trapPropagationPayload?_some_tracePrefix expectedPayload rfl
  · rfl

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedFrameTrapRollback
/-! Definition-only tests for parent-indexed trapped-frame rollback selection. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive TrapRollbackEvent where
  | parent
  | nested

private inductive TrapRollbackReason where
  | marker

private def parentTrace_variant6 : FrameTrace TrapRollbackEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking_variant6 :
    WorldState × FrameEffectJournal Nat (FrameTrace TrapRollbackEvent) :=
  (stateWith parentValue, ⟨10, parentTrace_variant6⟩)

private def extension_variant4 : FrameTrace.ExtensionFrom parentWorking_variant6.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking_variant6.2.trace).record .nested

private def contextWith_variant3 (outcome : FrameOutcome TrapRollbackReason) :
    ParentIndexedFrameContinuationContext Nat TrapRollbackEvent
      TrapRollbackReason parentWorking_variant6 :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking_variant6 20 extension_variant4 ⟨stateWith nestedValue, outcome⟩

private def isExtendedTrace_variant2 : List TrapRollbackEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesTrapRollback :
    Option
      (WorldState ×
        FrameEffectJournal Nat (FrameTrace TrapRollbackEvent)) → Bool
  | some (state, effects) =>
      observedValue? state == some parentValue &&
        effects.rollback == 10 && isExtendedTrace_variant2 effects.trace.toList
  | none => false

def testParentIndexedFrameTrapRollback : IO Unit := do
  assertTrue
    (isNone
      (contextWith_variant3 (.returned [0x12].toByteArray)).trapRollback?)
    "return must not select a trapped-frame rollback pair"

  assertTrue
    (isNone
      (contextWith_variant3 (.reverted [0x34].toByteArray)).trapRollback?)
    "revert must not select a trapped-frame rollback pair"

  assertTrue
    (matchesTrapRollback (contextWith_variant3 (.trapped .marker)).trapRollback?)
    "trap must select parent state and rollback with the working trace"

end Tests
end
