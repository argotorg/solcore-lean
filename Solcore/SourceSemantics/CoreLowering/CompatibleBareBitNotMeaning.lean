import Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotNative
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotMeaning

/-! Bare numeric snapshot assignments on the common compatible heap. The
source traces and native modifier/setter/write are constructed from a live
represented cell, without any source-child induction hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}

private theorem nonmapping {type : TypeSystem.Ty}
    (profile : SourceCoreRawMetadata.runtimeType type = .word ∨ SourceCoreRawMetadata.runtimeType type = .integer) :
    ∀ key value, type ≠ .mapping key value := by
  intro key value same
  subst type
  rcases profile with impossible | impossible <;> cases impossible

theorem resolves {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {place : PlaceResolution} {cell : Dynamic.Cell}
    {initial : Option Dynamic.Value}
    (bare : place.projections = []) (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (read : Dynamic.Heap.Reads heap location cell) (root : Dynamic.RootInitialValue cell initial) :
    Dynamic.SourcePlaceResolves program context evidence source environment heap place
      ⟨location, cell.type, place.type, [], initial⟩ heap := by
  exact .intro lookup read (bare ▸ .nil) read root .nil

/-- A present numeric root creates a single mapped write. Getter and setter
allocate no administrative cells, so both map and world are unchanged. -/
theorem initialized_commit (layout : Layout prepared)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    {sourceValue : Dynamic.Value} {value : Value} {environment : Environment}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨prepared.route.rootSourceType, some sourceValue, none⟩)
    (native : store.read? target = some (.inRight .unit value))
    (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType sourceValue value prepared.route.rootType)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ replacement after,
      Dynamic.BitNotSnapshot (some sourceValue) replacement ∧
      Dynamic.Heap.Writes heap location (some replacement) after ∧
      Nonempty (CompatiblePlaceBitNotCommit.Execution checked registry functions prepared [] environment store mapping world
        target [] value heap after replacement operator invalid) := by
  obtain ⟨replacement, changed, related, applies, modified, _⟩ :=
    CompatiblePlaceNumericBitNotModifier.success observations profile represented
      (environment := rhsEnvironment prepared.route.rootType target .unit (.inRight .unit value) .unit environment)
      (rhs := .var 0) (.var (index := 1) rfl) operator store invalid
  have written := DataPlaceCommitReflection.source_writes read replacement
  obtain ⟨finalStore, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read related written
  refine ⟨replacement, _, applies, written, ⟨{
    replacement := changed
    value := changed
    helperStore := store
    finalStore := finalStore
    finalWorld := world
    related := related
    heaps := finalHeaps
    worlds := .refl _
    frame := frame
    metadata := .of_write written
    modified := ?_
    setter := ?_
    read := ⟨_, native⟩
    written := coreWritten }⟩⟩
  · simpa only [← layout.sameType, packValues] using modified
  · exact CompatibleBareBitNotNative.setter_evaluates layout (.inRight .unit value) changed native

/-- Every live bare numeric root has exactly one generated phase: an absent
operand failure, or a source snapshot update with a real native commit. -/
theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {administrativeContext : Core.Context}
    {place : PlaceResolution} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {faults : FaultRep} {index : Nat}
    (layout : Layout prepared) (bare : place.projections = [])
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {operator : Option BinaryOp} {invalid : Word} {result : Value} {after : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalid)
    (completed : Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid) result after) :
    CompatiblePlaceBitNotMeaning.Result compilation.checked registry functions program context evidence source faults
      place environment coreEnvironment heap store mapping world next outputType result after := by
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨sourceLocation, cell, sourceLookup, sourceRead, cellType, _⟩ := locals.lookup schemeLookup
  have cellType := cellType.trans bodyEq
  obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible sourceLookup slot
  obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference sourceRead
  cases represented with
  | uninitialized projected =>
    have initial : Dynamic.RootInitialValue _ none := .uninitialized (by
      rintro ⟨key, value, same⟩
      exact nonmapping profile key value (cellType.symm.trans same))
    have trace := resolves (program := program) (context := context) (evidence := evidence) (source := source)
      bare sourceLookup sourceRead initial
    obtain ⟨resultEq, storeEq⟩ := CompatibleBareBitNotNative.absent_reflects layout nativeLookup nativeRead completed
    subst after
    exact .fault (.uninitialized trace rfl) resultEq token heaps (.refl _) (.refl _) (.refl _ _) (.refl _)
  | @initialized type _payload sourceValue value related =>
    simp only at cellType
    subst type
    have trace := resolves (program := program) (context := context) (evidence := evidence) (source := source)
      bare sourceLookup sourceRead Dynamic.RootInitialValue.initialized
    obtain ⟨replacement, sourceAfter, applies, written, ⟨commit⟩⟩ :=
      initialized_commit layout observations profile heaps reference sourceRead nativeRead related operator invalid
    have update : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment heap place replacement sourceAfter :=
      .intro trace (.intro sourceRead rfl .initialized (.leaf applies) written)
    have tail := CompatibleBareBitNotNative.prefix_reflects layout nativeLookup nativeRead completed
    exact .committed update commit.heaps (.refl _) commit.worlds commit.frame commit.metadata
      (slots := [.unit, commit.value, commit.replacement, .unit, .inRight .unit value,
        .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) target]) rfl (commit.reflects tail)

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
