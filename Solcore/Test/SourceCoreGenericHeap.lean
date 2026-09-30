import Solcore.SourceSemantics.CoreLowering.GenericHeap

/-! Representation-interface regressions. The finite specialization is exactly
the existing DataHeap. A deliberately narrow, syntactically fixed closure model
also demonstrates cyclic captured references and world extension. This test
does not claim general source function-body or mapping semantics. -/

set_option autoImplicit false
namespace Tests.SourceCoreGenericHeap
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap GenericHeap

example {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    (old : DataHeap.HeapRepresents catalog signatures mapping world heap store) :
    GenericHeap.HeapRepresents (finitePayload catalog signatures) mapping world heap store := finiteHeap_iff.mpr old

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"generic_heap", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def self : Resolved.LocalId := ⟨owner, 0⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def sourceType : TypeSystem.Ty := .function .unit .unit
private def functionType : Core.Ty := Core.TaggedFunction.functionType .unit .unit
private def cellType : Core.Ty := Core.OptionalCell.cellType functionType
private def sourceClosure : Dynamic.Closure := {
  parameters := [], resultType := .unit, body := []
  source := { owner, inputs := [], roots := [], nodes := [] }
  captured := [(self, ⟨0⟩)]
  context := (SourceSemantics.Context.ofSignatures signatures).withLocal self (.mono sourceType) []
  evidence := []
}
private def coreClosure (location : Core.Location) : Core.Value :=
  .pair (.inLeft .word .unit)
    (.closure .unit (Core.LanguageResult.resultType .unit) (Core.LanguageResult.success .unit)
      [.cellRef cellType location])

private inductive Captured (mapping : LocationMap) (world : Core.StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | closure {location : Core.Location} (captured : ReferenceRepresents mapping world ⟨0⟩ location functionType) :
      Captured mapping world sourceType (.closure sourceClosure) (coreClosure location) functionType

private def model : PayloadModel catalog where
  Represents := Captured
  projection := by intro mapping world type source value payload represented; cases represented; rfl
  runtime_hasType := by
    intro mapping world type source value payload represented
    cases represented with
    | closure captured =>
      exact .pair (.inLeft .unit) (.closure (.cons (.cellRef captured.typed) .nil) (.inRight .word .unit))
  extend := by
    intro mapping futureMap world futureWorld type source value payload represented maps worlds
    cases represented with
    | closure captured => exact .closure (captured.extend maps worlds)

private def initialHeap : Dynamic.Heap := ⟨[⟨sourceType, none, none⟩]⟩
private def initialWorld : Core.StoreTyping := [cellType]
private def initialStore : Core.Store := [.inLeft functionType .unit]
private theorem initialRelated : GenericHeap.HeapRepresents model [0] initialWorld initialHeap initialStore :=
  (GenericHeap.HeapRepresents.empty.allocate (.uninitialized rfl) .append).1
private def installedHeap : Dynamic.Heap := ⟨[⟨sourceType, some (.closure sourceClosure), none⟩]⟩
private def installedStore : Core.Store := [.inRight .unit (coreClosure 0)]
private theorem closureRelated : model.Represents [0] initialWorld sourceType (.closure sourceClosure)
    (coreClosure 0) functionType := .closure ⟨rfl, rfl⟩

/-- The stored source closure captures source location zero, and the Core
closure captures its mapped cell zero. Neither proof recursively follows it. -/
private theorem installedRelated : GenericHeap.HeapRepresents model [0] initialWorld installedHeap installedStore := by
  obtain ⟨updated, written, related, _⟩ := initialRelated.write_initialized
    (reference := ⟨rfl, rfl⟩) (.intro .head) closureRelated (.intro (.intro .head) .head)
  have expected : initialStore.write? 0 (.inRight .unit (coreClosure 0)) = some installedStore := rfl
  have same := Option.some.inj (written.symm.trans expected)
  exact same ▸ related

example : Core.RuntimeStoreHasTypes initialWorld installedStore catalog.definitions := installedRelated.runtime_hasTypes

private def extendedWorld : Core.StoreTyping := initialWorld ++ [functionType]
private def extendedStore : Core.Store := installedStore ++ [coreClosure 0]
example : GenericHeap.HeapRepresents model [0] extendedWorld installedHeap extendedStore :=
  installedRelated.allocate_administrative (model.runtime_hasType closureRelated)
example : model.Represents [0] extendedWorld sourceType (.closure sourceClosure) (coreClosure 0) functionType :=
  model.extend closureRelated (.refl _) ⟨_, rfl⟩
example : GeneralHeap.AdministrativePreserved [0] installedStore [0] extendedStore :=
  GeneralHeap.AdministrativePreserved.allocate_administrative [0] installedStore (coreClosure 0)

end Tests.SourceCoreGenericHeap
