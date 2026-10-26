import Solcore.Frontend.RustHull.ChildCatalogExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported
import Solcore.Frontend.RustHull.ChildFrameModeSemantics
import Solcore.Frontend.RustHull.CreationHandlerCorrespondence

/-! Finite nested child execution uses the same compiled catalog identities.
Selected child programs may call the installed dispatcher; execution at the
next smaller height supplies the internal frame interface. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
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
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions

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
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions ∧
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

/-- Internal induction interface for one actual compiled frame invocation.
Every closure, reference and current shared read comes from the real object
capture and allocator; only the finite source derivation varies with height. -/
def FrameExecution (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State) : Prop :=
  ∀ {source : ChildFrameSemantics.Code} {fuel : Nat} {compiled : Core.Expr} {others : List Core.Expr},
    AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled →
    DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions →
    ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others →
    CatalogConnection sourceCatalog catalog anchors →
  ∀ {captured : Environment} {catalogValues : List Value} {rootClosure : Value},
    CapturedClosures captured others catalogValues →
  ∀ {images : List (Nat × List UInt8)} {sharedCells : List InitializedCell}
    {dispatcherLocation creatorLocation : Nat} {initial : Store},
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (rootClosure :: catalogValues) sharedCells dispatcherLocation creatorLocation initial) →
  ∀ {depth : Nat} {environment : Environment} {frame dispatcher creator gas code size known function : Code} {closure : Value},
    CapturedClosure compiled captured closure →
    CodeValue depth environment function closure →
    (parent : RuntimeCallModeSemantics.State) → (request : AccountCallSemantics.Request) →
    (sharedState : AccountCallSemantics.Shared) →
  ∀ {accounts : StorageCorrespondence.Accounts}, accounts.map Prod.fst = sharedState.world →
    RuntimeReferences depth environment capture.shared sharedCells →
    sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse →
    InitializedCells sharedCells initial → CellLocations sharedCells →
    (∀ cell ∈ sharedCells, ChildFrameCorrespondence.Observed accounts
      (ChildFrameCorrespondence.Initial parent request sharedState source.bytes) source.bytes cell) →
    CodeValue depth environment creator (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation) →
    (∃ value, initial.read? creatorLocation = some value) →
    (∀ cell ∈ sharedCells, cell.location ≠ creatorLocation) →
    CodeValue depth environment dispatcher
      (.cellRef (OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
    (∀ cell ∈ sharedCells, cell.location ≠ dispatcherLocation) → creatorLocation ≠ dispatcherLocation →
    CodeValue depth environment frame (CallTransportCorrespondence.requestValue request) →
    CodeValue depth environment gas (optionalWordValue (some request.gas)) →
    CodeValue depth environment code (WordMapping.encode (Memory.packBytes source.bytes)) →
    CodeValue depth environment size (.word (Word.ofNatModulo source.bytes.length)) →
    CodeValue depth environment known (.bool true) →
  ∀ {locations : AccountCallCorrespondence.SharedLocations},
    AccountCallCorrespondence.SharedReferences depth environment capture.shared locations →
    RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world locations.world initial →
  ∀ {createValue : Value}, initial.read? creatorLocation = some (.inRight .unit createValue) →
    CreationCorrespondence.HandlerClosure locations createValue →
  ∀ {status : Semantics.Result Semantics.Value} {finalSource : Semantics.State RuntimeCallModeSemantics.State}
    {response : Semantics.Result AccountCallSemantics.Response},
    Semantics.EvalFunction source.functions (effects (some source.bytes)) source.entry []
      ⟨[], ChildFrameSemantics.initial parent request sharedState source.bytes⟩ status finalSource →
    ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status finalSource.external.runtime.runtime.runtime.runtime.runtime)
      finalSource.external.runtime.runtime.runtime.runtime.runtime response →
    ∃ target final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) capture.shared frame dispatcher creator gas code size known
        (fun values => bind (apply function (packet values)) AccountRuntime.childResult) depth) target final ∧
      CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations (RuntimeCallModeSemantics.shared finalSource.external) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final

end Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
