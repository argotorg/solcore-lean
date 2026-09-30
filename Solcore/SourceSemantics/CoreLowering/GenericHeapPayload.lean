import Solcore.SourceSemantics.CoreLowering.DataEnvironment

/-! An interface for authenticated ordinary cell payload relations. Models may
refer to the finite location map and runtime typing world, so a captured source
location can correspond to a Core reference without recursively traversing a
cyclic store. These laws establish representation typing and extension only.
A function model still needs explicit source identity/code authentication and
call semantics; a mapping model still needs entry and comparison semantics.
-/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericHeap
open Frontend Frontend.SourceInference GeneralHeap

structure PayloadModel (catalog : SourceCoreDataCatalog.Catalog) where
  Represents : LocationMap → Core.StoreTyping → TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop
  projection : ∀ {mapping world sourceType sourceValue value payload},
    Represents mapping world sourceType sourceValue value payload → catalog.project sourceType = .ok payload
  runtime_hasType : ∀ {mapping world sourceType sourceValue value payload},
    Represents mapping world sourceType sourceValue value payload →
      Core.RuntimeValueHasType world value payload catalog.definitions
  extend : ∀ {mapping futureMapping world futureWorld sourceType sourceValue value payload},
    Represents mapping world sourceType sourceValue value payload →
    LocationMap.Extends mapping futureMapping → Core.WorldExtends world futureWorld →
    Represents futureMapping futureWorld sourceType sourceValue value payload

/-- Optional ordinary cells preserve the source declaration's type and reject
retained generalized-cell metadata. Their payload representation is supplied
by the model, not inferred from Core runtime typing. -/
inductive CellRepresents {catalog : SourceCoreDataCatalog.Catalog} (model : PayloadModel catalog)
    (mapping : LocationMap) (world : Core.StoreTyping) : Dynamic.Cell → Core.Value → Core.Ty → Prop where
  | uninitialized {sourceType : TypeSystem.Ty} {payload : Core.Ty}
      (projection : catalog.project sourceType = .ok payload) :
      CellRepresents model mapping world ⟨sourceType, none, none⟩ (.inLeft payload .unit) payload
  | initialized {sourceType : TypeSystem.Ty} {payload : Core.Ty} {source : Dynamic.Value} {value : Core.Value}
      (represented : model.Represents mapping world sourceType source value payload) :
      CellRepresents model mapping world ⟨sourceType, some source, none⟩ (.inRight .unit value) payload

variable {catalog : SourceCoreDataCatalog.Catalog} {model : PayloadModel catalog}

theorem CellRepresents.projection {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents model mapping world cell value payload) : catalog.project cell.type = .ok payload := by
  cases represented with
  | uninitialized projection => exact projection
  | initialized related => exact model.projection related

theorem CellRepresents.ordinary {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents model mapping world cell value payload) : cell.generalized = none := by
  cases represented <;> rfl

theorem CellRepresents.runtime_hasType {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents model mapping world cell value payload) :
    Core.RuntimeValueHasType world value (Core.OptionalCell.cellType payload) catalog.definitions := by
  cases represented with
  | uninitialized => exact .inLeft .unit
  | initialized related => exact .inRight (model.runtime_hasType related)

theorem CellRepresents.extend {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents model mapping world cell value payload)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    CellRepresents model futureMapping futureWorld cell value payload := by
  cases represented with
  | uninitialized projection => exact .uninitialized projection
  | initialized related => exact .initialized (model.extend related maps worlds)

/-- The previously proved finite unit/Bool/Word/Integer/product/nominal model.
The extra explicit projection records the payload type chosen for this cell. -/
def finitePayload (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) : PayloadModel catalog where
  Represents := fun _ _ sourceType source value payload =>
    catalog.project sourceType = .ok payload ∧
      DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value
  projection := fun related => related.1
  runtime_hasType := by
    intro mapping world sourceType source value payload related
    obtain ⟨type, projection, typed⟩ := DataValueTyping.TypedValueRep.project_typed related.2
    have same := Except.ok.inj (projection.symm.trans related.1)
    exact same ▸ typed world
  extend := fun related _ _ => related

theorem finiteCell_iff {signatures : ProgramSignatures} {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty} :
    CellRepresents (finitePayload catalog signatures) mapping world cell value payload ↔
      DataHeap.CellRepresents catalog signatures cell value payload := by
  constructor
  · intro represented
    cases represented with
    | uninitialized projection => exact .uninitialized projection
    | initialized related => exact .initialized related.1 related.2
  · intro represented
    cases represented with
    | uninitialized projection => exact .uninitialized projection
    | initialized projection related => exact .initialized ⟨projection, related⟩

end Solcore.SourceSemantics.CoreLowering.GenericHeap
