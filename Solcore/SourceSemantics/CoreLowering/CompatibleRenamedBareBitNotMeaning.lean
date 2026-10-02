import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBareBitNotContracts

/-! A numeric bare snapshot creates a real mapped commit and an exact typed
seven-slot continuation in the actual renamed environment. Its Unit RHS has
no source child. Every native phase is constructed from a represented live cell. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {location : Dynamic.Location} {target : Location} {sourceValue : Dynamic.Value} {value : Value}
  {actual : Environment} {actualContext : Core.Context} {index : Nat} {ξ : Renaming}

/-- A source snapshot operation supplies no native execution witness. This
construction derives the modifier, setter, store write and both directions of
the continuation agreement from that independent operation. -/
theorem initialized_prefix (layout : Layout prepared)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨prepared.route.rootSourceType, some sourceValue, none⟩)
    (nativeRead : store.read? target = some (.inRight .unit value))
    (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType sourceValue value prepared.route.rootType)
    (lookup : actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ updated replacement after finalStore slots,
      Dynamic.BitNotSnapshot (some sourceValue) updated ∧
      Dynamic.Heap.Writes heap location (some updated) after ∧
      ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      HeapRepresents checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨updated, replacement, after, finalStore, slots, applies, written, related, finalHeaps,
    frame, metadata, count, typed, agreement, _⟩ :=
    initialized_prefix_sized layout observations profile heaps reference read nativeRead represented lookup actualTyped operator invalid
  exact ⟨updated, replacement, after, finalStore, slots, applies, written, related, finalHeaps,
    frame, metadata, count, typed, agreement⟩

/-- Absence returns the unary token in the actual environment and skips every
continuation. The physical store, including unrelated captured cells, is exact. -/
theorem absent_evaluates (layout : Layout prepared)
    (lookup : actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some (.inLeft prepared.route.rootType .unit))
    (next : Expr) (output : Ty) (operator : Option BinaryOp) (invalid : Word) :
    Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ) (.inLeft output (.word invalid)) store := by
  rw [execute_rename layout]
  exact CompatibleBareBitNotNative.absent_evaluates layout lookup read _ _ _ _

/-- Completed absent runs do not introduce a source child or a store change. -/
theorem absent_reflects (layout : Layout prepared)
    (lookup : actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some (.inLeft prepared.route.rootType .unit))
    {next : Expr} {output : Ty} {operator : Option BinaryOp} {invalid : Word} {result : Value} {after : Store}
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ) result after) :
    result = .inLeft output (.word invalid) ∧ after = store :=
  evaluation_deterministic completed (absent_evaluates layout lookup read next output operator invalid)

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
