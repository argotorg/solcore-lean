import Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
import Solcore.Frontend.RustHull.AccountCallModeRunCorrespondence
import Solcore.Frontend.RustHull.NestedChildCallbackContextCorrespondence

/-! A finite source child tree reaches the actual selected catalog closure.
The smaller-height frame theorem supplies execution, while refreshed captures
retain the real dispatcher for any nested call made by that child. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence

/-- Additional immutable callback observations strengthen the invocation
precondition without changing the selected code or its execution relation. -/
theorem ChildRunPreservation.strengthen {mode : AccountCallSemantics.Mode}
    {anchors : List CatalogWorldCorrespondence.Anchor}
    {locations : AccountCallCorrespondence.SharedLocations}
    {shared : AccountRuntime.References} {runFrame : CodeBuilder.Code → CodeBuilder.Code → CodeBuilder.Code}
    {children : AccountCallSemantics.Children} {valid stronger : Core.Store → Prop}
    {depth : Nat} {captured : Core.Environment}
    (preserved : ChildRunPreservation mode anchors locations shared runFrame children valid depth captured)
    (implies : ∀ store, stronger store → valid store) :
    ChildRunPreservation mode anchors locations shared runFrame children stronger depth captured := by
  intro source request state result finalState computed extra store extended precompiled references argument related ready
  exact preserved computed extra references argument related (implies store ready)

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence

namespace Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)
open AccountCallCorrespondence hiding ChildRunPreservation childRequest_value
open AccountCallModeCorrespondence (ChildRunPreservation childRequest_value)

theorem child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    (frameExecution : FrameExecution sourceCatalog catalog anchors effects)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creatorLocation : Nat}
    {layout : Layout} {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells layout.dispatcher creatorLocation initial)
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (mode : AccountCallSemantics.Mode) (parent : RuntimeCallModeSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    ChildRunPreservation mode anchors (sharedLocations layout) capture.shared
      (RuntimeCatalogDispatchCorrespondence.runFrame (RuntimeExtendedInitializedEffects.slots true)
        (others.length + 1) capture.functions capture.shared capture.dispatcher capture.creator)
      (ChildFrameModeSemantics.Children sourceCatalog effects parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (NestedChildCallbackContextCorrespondence.context inventory capture.closure))
      capture.depth capture.environment := by
  intro caller request initialShared response finalShared computed extra store extended precompiled sharedReferences argument related ready
  cases computed with
  | @executed _ caller request initialShared account source status finalSource response ordinary found selected known evaluated responded =>
    obtain ⟨index, expression, value, anchored, nonzero, first, accepted, eligible, capturedFrame, functionRelated⟩ :=
      selected_frame connection compiled closures capture.functionValues selected
    obtain ⟨accounts, actualAccount, sameWorld, links, worldRead, sourceFound, actualFound, code⟩ :=
      RuntimeLinkedWorldCorrespondence.selected related.linked anchored
    have sameAccount : actualAccount = account := Option.some.inj (sourceFound.symm.trans found)
    subst actualAccount
    let baseDepth := capture.depth + extra.length
    let baseEnvironment := extra ++ capture.environment
    let afterLookup := StorageCorrespondence.getStore accounts request.target initialShared.complete baseEnvironment store
    have retained : StoreRetains store afterLookup := StoreRetains.append _ _
    have afterReady := RuntimeChildCallEffectsCorrespondence.childReady_preserved
      (SharedFrame.ofRetains retained) ready
    obtain ⟨freshAccounts, creatorValue, freshWorld, _, stored, signature, separate, observed, creatorRead, creatorSeparate⟩ :=
      ChildCallbackContextCorrespondence.refresh_ready inventory.base afterReady.1 afterReady.2.1
        parent (ChildFrameModeSemantics.executionRequest mode caller request) initialShared source.bytes ambient (related.linked.retained retained) (related.shared.retained retained)
    let recordValue := StorageCorrespondence.record account (index + 2)
    let recordCode : Code := fun here => .var (here - baseDepth - 1)
    have recordRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment) recordCode recordValue :=
      CodeValue.bound baseDepth baseEnvironment recordValue
    have frameRelated := (childRequest_value argument).prepend [recordValue]
    have gasRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (present (part 5 8 (childRequest extended))) (optionalWordValue (some request.gas)) := by
      intro prefixValues current
      exact .inRight ((frameRelated.part (index := 5) rfl) prefixValues current)
    have codeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 4 9 recordCode) (WordMapping.encode (Memory.packBytes source.bytes)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 4) rfl
    have sizeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 5 9 recordCode) (.word (Word.ofNatModulo source.bytes.length)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 5) rfl
    have knownRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 6 9 recordCode) (.bool true) := by
      simpa only [StorageCorrespondence.record, known, Option.isSome_some, List.length_cons, List.length_nil] using recordRelated.part (index := 6) rfl
    have refreshedReferences := ChildFrameCorrespondence.refresh_references
      ((capture.references.prepend extra).prepend [recordValue]) afterLookup
    let refreshedCapture := NestedChildCallbackContextCorrespondence.refreshCapture capture afterLookup
      (NestedChildCallbackContextCorrespondence.dispatcher_read afterReady.2)
    have dispatcherSeparate : ∀ cell ∈ ChildFrameCorrespondence.refresh afterLookup cells,
        cell.location ≠ layout.dispatcher := by
      intro cell member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact inventory.dispatcherSeparate original present
    obtain ⟨target, final, invoked, resultRelated, finalRelated, frame⟩ :=
      frameExecution accepted eligible compiled connection closures refreshedCapture capturedFrame
        ((functionRelated.prepend extra).prepend [recordValue]) parent (ChildFrameModeSemantics.executionRequest mode caller request) initialShared freshWorld
        refreshedReferences signature stored separate observed
        ((capture.creatorValue.prepend extra).prepend [recordValue]) ⟨creatorValue, creatorRead⟩ creatorSeparate
        ((capture.dispatcherValue.prepend extra).prepend [recordValue]) dispatcherSeparate inventory.creatorDispatcher
        frameRelated gasRelated codeRelated sizeRelated knownRelated
        (sharedReferences.prepend [recordValue]) (related.linked.retained retained) evaluated responded
        (dispatcher := capture.dispatcher)
    have selectedRun := RuntimeCatalogDispatchCorrespondence.runFrame_evaluates first recordRelated invoked
    refine ⟨target, final, ?_, resultRelated, finalRelated, (SharedFrame.ofRetains retained).trans frame⟩
    exact accountRun_child_evaluates sharedReferences
      ((argument.part (index := 0) rfl).part (index := 0) rfl) worldRead related.shared.complete
      ordinary actualFound nonzero selectedRun

/-- The refreshed proof inventory does not replace the installed dispatcher;
this wrapper refers to the closure constructed by the real object initializer. -/
theorem captured_child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    (frameExecution : FrameExecution sourceCatalog catalog anchors effects)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creatorLocation : Nat}
    {layout : Layout} {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells layout.dispatcher creatorLocation initial)
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (sharedReferences : SharedReferences capture.depth capture.environment capture.shared (sharedLocations layout))
    (mode : AccountCallSemantics.Mode) (parent : RuntimeCallModeSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture (sharedLocations layout) sharedReferences
    ChildRunPreservation mode anchors (sharedLocations layout) dispatcher.shared dispatcher.runFrame
      (ChildFrameModeSemantics.Children sourceCatalog effects parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (NestedChildCallbackContextCorrespondence.context inventory capture.closure))
      dispatcher.depth dispatcher.captured :=
  child_runs_preserves connection frameExecution compiled closures capture inventory mode parent ambient

end Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
