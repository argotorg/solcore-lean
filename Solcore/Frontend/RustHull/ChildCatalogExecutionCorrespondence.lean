import Solcore.Frontend.RustHull.ChildFrameInvokeCorrespondence
import Solcore.Frontend.RustHull.ChildCallbackContextCorrespondence
import Solcore.Frontend.RustHull.RuntimeCatalogDispatchCorrespondence
import Solcore.Frontend.RustHull.RuntimeChildCallCallbackCorrespondence

/-! Source catalog selection is connected to compiled closure indices and the
actual account dispatch lookup. Each selected child receives a fresh frame and
current shared resources; the proof does not assume child evaluation in Core. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)
open AccountCallCorrespondence

/-- All conditions concern source selection, compilation structure and runtime
identity representation. Child execution is derived separately below. -/
def CatalogConnection (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  ∀ address source, ChildFrameSemantics.select sourceCatalog address = some source →
    ∃ index definition, catalog[index]? = some definition ∧ source.program = definition.program ∧
      AccountRuntime.select definition.program.objects definition.path = .ok source.body ∧
      source.bytes = definition.bytes ∧
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (catalog.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      DerivationCorrespondence.ExecutableProgram (ContractReturnDataCorrespondence.supported true) source.functions

theorem selected_frame {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured environment : Environment} {values : List Value} {closure : Value} {depth : Nat} {functions : Code}
    (closures : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {address : Word} {source : ChildFrameSemantics.Code}
    (selected : ChildFrameSemantics.select sourceCatalog address = some source) :
    ∃ index expression value,
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (others.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok expression ∧
      DerivationCorrespondence.ExecutableProgram (ContractReturnDataCorrespondence.supported true) source.functions ∧
      CapturedClosure expression captured value ∧
      CodeValue depth environment (part (index + 1) (others.length + 1) functions) value := by
  obtain ⟨index, definition, found, program, body, _, anchored, nonzero, first, eligible⟩ := connection address source selected
  obtain ⟨code, expression, value, codeSelected, accepted, captured, referenced⟩ :=
    ContractCatalogCorrespondence.catalog_reference compiled closures functionsRelated found
  have same : code = source.body := Except.ok.inj (codeSelected.symm.trans body)
  subst code
  refine ⟨index, expression, value, anchored, nonzero, ?_, ?_, eligible, captured, referenced⟩
  · simpa only [compiled.length] using first
  · simpa only [program] using accepted

theorem child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured environment : Environment} {values : List Value} {closure : Value} {depth : Nat}
    {functions dispatcher creator : Code} {shared : AccountRuntime.References}
    (closures : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {layout : Layout} {cells : List InitializedCell} {creatorLocation : Nat}
    (inventory : ChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (references : RuntimeReferences depth environment shared cells)
    (creatorRelated : CodeValue depth environment creator (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation))
    (parent : RuntimeCallEffectsSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    ChildRunPreservation anchors (sharedLocations layout) shared
      (RuntimeCatalogDispatchCorrespondence.runFrame (RuntimeExtendedInitializedEffects.slots true)
        (others.length + 1) functions shared dispatcher creator)
      (ChildFrameSemantics.CallFree sourceCatalog parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout (ChildCallbackContextCorrespondence.context inventory))
      depth environment := by
  intro caller request initialShared response finalShared computed extra store extended precompiled sharedReferences argument related ready
  cases computed with
  | @executed caller request initialShared account source status finalSource response ordinary found selected known evaluated responded =>
    obtain ⟨index, expression, value, anchored, nonzero, first, accepted, eligible, capturedFrame, functionRelated⟩ :=
      selected_frame connection compiled closures functionsRelated selected
    obtain ⟨accounts, actualAccount, sameWorld, links, worldRead, sourceFound, actualFound, code⟩ :=
      RuntimeLinkedWorldCorrespondence.selected related.linked anchored
    have sameAccount : actualAccount = account := Option.some.inj (sourceFound.symm.trans found)
    subst actualAccount
    let baseDepth := depth + extra.length
    let baseEnvironment := extra ++ environment
    let afterLookup := StorageCorrespondence.getStore accounts request.target initialShared.complete baseEnvironment store
    have retained : StoreRetains store afterLookup := StoreRetains.append _ _
    have afterReady := RuntimeChildCallEffectsCorrespondence.childReady_preserved
      (SharedFrame.ofRetains retained) ready
    obtain ⟨freshAccounts, creatorValue, freshWorld, _, stored, signature, separate, observed, creatorRead, creatorSeparate⟩ :=
      ChildCallbackContextCorrespondence.refresh_ready inventory afterReady.1 afterReady.2
        parent request initialShared source.bytes ambient (related.linked.retained retained) (related.shared.retained retained)
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
      ((references.prepend extra).prepend [recordValue]) afterLookup
    obtain ⟨target, final, invoked, resultRelated, finalRelated, frame⟩ :=
      ChildFrameCorrespondence.invoke_evaluates accepted eligible capturedFrame
        ((functionRelated.prepend extra).prepend [recordValue]) parent request initialShared freshWorld
        refreshedReferences signature stored separate observed
        ((creatorRelated.prepend extra).prepend [recordValue]) creatorRead creatorSeparate
        frameRelated gasRelated codeRelated sizeRelated knownRelated
        (sharedReferences.prepend [recordValue]) (related.linked.retained retained) evaluated responded
        (dispatcher := dispatcher)
    have selectedRun := RuntimeCatalogDispatchCorrespondence.runFrame_evaluates first recordRelated invoked
    refine ⟨target, final, ?_, resultRelated, finalRelated, (SharedFrame.ofRetains retained).trans frame⟩
    exact accountRun_child_evaluates sharedReferences
      ((argument.part (index := 0) rfl).part (index := 0) rfl) worldRead related.shared.complete
      ordinary actualFound nonzero selectedRun

/-- Actual object initialization supplies the closure packet, immutable lexical
references and captured dispatcher body used by the child theorem. -/
theorem captured_child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {dispatcherLocation creatorLocation : Nat}
    {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells dispatcherLocation creatorLocation initial)
    {layout : Layout} (inventory : ChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (sharedReferences : SharedReferences capture.depth capture.environment capture.shared (sharedLocations layout))
    (parent : RuntimeCallEffectsSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture (sharedLocations layout) sharedReferences
    ChildRunPreservation anchors (sharedLocations layout) dispatcher.shared dispatcher.runFrame
      (ChildFrameSemantics.CallFree sourceCatalog parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout (ChildCallbackContextCorrespondence.context inventory))
      dispatcher.depth dispatcher.captured :=
  child_runs_preserves connection compiled closures capture.functionValues inventory capture.references
    capture.creatorValue parent ambient

end Solcore.Frontend.RustHull.ChildCatalogExecutionCorrespondence
