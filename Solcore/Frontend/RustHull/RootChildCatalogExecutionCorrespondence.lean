import Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence

/-! Root reentry selects the actual packet-head closure. Its compilation and
capture are structural inputs to the finite-height frame induction, alongside
compiled catalog entries; none assumes that the root executes correctly. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RootChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

/-- The real root frame, compiled and captured in the same environment as the
catalog closures. This evidence is unchanged when shared runtime cells change. -/
def RootFrame (rootSource : ChildFrameSemantics.Code) (fuel : Nat)
    (captured : Environment) (closure : Value) : Prop :=
  ∃ expression,
    AccountRuntime.compileFrame rootSource.program rootSource.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok expression ∧
    DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) rootSource.functions ∧
    CapturedClosure expression captured closure

/-- A source selection either refers to the root's executable identity one,
or to one of the actual catalog identities after it. Both branches retain the
selected address's exact byte image through the same account anchor. -/
def CatalogConnection (rootSource : ChildFrameSemantics.Code) (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  ∀ address source, ChildFrameSemantics.select sourceCatalog address = some source →
    (source = rootSource ∧ CatalogWorldCorrespondence.Anchor.mk address rootSource.bytes 1 ∈ anchors) ∨
    ∃ index definition, catalog[index]? = some definition ∧ source.program = definition.program ∧
      AccountRuntime.select definition.program.objects definition.path = .ok source.body ∧
      source.bytes = definition.bytes ∧
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (catalog.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions

/-- Existing catalog-only links remain valid without adding a root entry. -/
theorem CatalogConnection.of_catalog {rootSource : ChildFrameSemantics.Code}
    {sourceCatalog : ChildFrameSemantics.Catalog} {catalog : List AccountRuntime.CodeDefinition}
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (connected : ModeChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors) :
    CatalogConnection rootSource sourceCatalog catalog anchors :=
  fun address source selected => .inr (connected address source selected)

theorem selected_frame {rootSource : ChildFrameSemantics.Code} {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection rootSource sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured environment : Environment} {values : List Value} {closure : Value} {depth : Nat} {functions : Code}
    (closures : CapturedClosures captured others values)
    (root : RootFrame rootSource fuel captured closure)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {address : Word} {source : ChildFrameSemantics.Code}
    (selected : ChildFrameSemantics.select sourceCatalog address = some source) :
    ∃ index expression value,
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 1) ∈ anchors ∧
      Word.ofNatModulo (index + 1) ≠ Word.zero ∧
      (List.range (others.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 1) == Word.ofNatModulo (candidate + 1)) = some index ∧
      AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok expression ∧
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions ∧
      CapturedClosure expression captured value ∧
      CodeValue depth environment (part index (others.length + 1) functions) value := by
  rcases connection address source selected with ⟨rfl, anchored⟩ | linked
  · obtain ⟨expression, accepted, eligible, capturedRoot⟩ := root
    refine ⟨0, expression, closure, anchored, ?_, ?_, accepted, eligible, capturedRoot,
      ContractCatalogCorrespondence.entry_reference closures functionsRelated⟩
    · decide +kernel
    · simp only [List.range_succ_eq_map, List.find?_cons, beq_self_eq_true]
  · obtain ⟨index, definition, found, program, body, _, anchored, nonzero, first, eligible⟩ := linked
    obtain ⟨code, expression, value, codeSelected, accepted, capturedFrame, referenced⟩ :=
      ContractCatalogCorrespondence.catalog_reference compiled closures functionsRelated found
    have same : code = source.body := Except.ok.inj (codeSelected.symm.trans body)
    subst code
    refine ⟨index + 1, expression, value, anchored, nonzero, ?_, ?_, eligible, capturedFrame, referenced⟩
    · simpa only [compiled.length] using first
    · simpa only [program] using accepted

/-- Internal induction interface for one actual compiled frame invocation.
Every closure, reference and current shared read comes from the real object
capture and allocator; only the finite source derivation varies with height. -/
def FrameExecution (rootSource : ChildFrameSemantics.Code) (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State) : Prop :=
  ∀ {source : ChildFrameSemantics.Code} {fuel : Nat} {compiled : Core.Expr} {others : List Core.Expr},
    AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled →
    DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions →
    ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others →
    CatalogConnection rootSource sourceCatalog catalog anchors →
  ∀ {captured : Environment} {catalogValues : List Value} {rootClosure : Value},
    CapturedClosures captured others catalogValues →
    RootFrame rootSource fuel captured rootClosure →
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


end Solcore.Frontend.RustHull.RootChildCatalogExecutionCorrespondence
