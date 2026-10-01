import Solcore.SourceSemantics.CoreLowering.DataPlaceSetterReflection
import Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog

/-! Live-root reconstruction retains a sibling changed before setter execution.
Reflection constructs the independent source update from actual generated Core
execution and authentic full payloads. The setter itself leaves the cell intact;
only the enclosing assignment's later storeCell may commit this value. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.SourceCoreDataPlaceSetterReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceRouteCertificates

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"setter_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "setter_reflection.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.bool, .bool], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.product .bool .bool]⟩, constructors := [⟨dataId, 0⟩] }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono boxType, [], false, none⟩
private def source : TypedSource := { owner, inputs := [binder], roots := [], nodes := [] }
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures functions
private theorem functionTypes : FunctionRuntimeTypes functions := fun impossible => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) := fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; trivial
  | succ index => simp [catalog] at selected
private def branches : List MemberBranch := [⟨⟨⟨0⟩, 0⟩, [.bool, .bool]⟩]
private def route : Route := ⟨boxType, .namedData ⟨0⟩, .bool, [.member ⟨0⟩ 0 branches .bool], none⟩
private def invalid : Word := ⟨23, by decide⟩
private def prepared : Prepared := ⟨route, [.member ⟨0⟩ 0 branches .bool], [], invalid⟩
private theorem preparedBy : prepare checked 5 route invalid (fun _ => Word.zero) = .ok prepared := by cbv
private def projections : List PlaceProjection := [.member "value" 0]
private theorem profile : Profile signatures source boxType projections .bool := by
  refine .member (field := .bool) (signature := signature) (arguments := []) rfl (by cbv) ?_ (.nil rfl)
  intro constructor member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  subst constructor
  rfl
private theorem raw : RawPath checked signatures source boxType (.namedData ⟨0⟩) route.steps projections .bool .bool [] := by
  obtain ⟨_, types, raw⟩ := raw_of_routeSteps profile (show catalog.project boxType = .ok (.namedData ⟨0⟩) by rfl)
    (show catalog.project TypeSystem.Ty.bool = .ok .bool by rfl)
    (show routeSteps checked signatures source (.binder binder.id) binder.id boxType projections = .ok (route.steps, TypeSystem.Ty.bool) by cbv)
  have keys : DataExpressionSequence.Tree source (fun _ _ _ => True) [] [] [] [] := .nil
  have same := raw.keyTypes.tree_types keys
  rw [← same] at raw
  exact raw
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [.bool, .bool], boxType⟩
private def sourceRoot : Dynamic.Value := .constructed metadata [.bool true, .bool false]
private def coreRoot : Value := .constructed ⟨⟨0⟩, 0⟩ (.pair (.bool true) (.bool false))
private theorem rootRelated {mapping : GeneralHeap.LocationMap} {world : StoreTyping} :
    ValueRep catalog signatures functions mapping world boxType sourceRoot coreRoot (.namedData ⟨0⟩) :=
  .constructed (metadata := metadata) (tag := ⟨⟨0⟩, 0⟩) (declaration := dataId) (arguments := [])
    rfl rfl (by cbv) rfl rfl (.cons (.bool true) (.cons (.bool false) .nil))
private def cell : Dynamic.Cell := ⟨boxType, some sourceRoot, none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [OptionalCell.cellType (.namedData ⟨0⟩), .integer]
private def store : Store := [.inRight .unit coreRoot, .integer 900]
private def environment : Environment := [.cellRef (OptionalCell.cellType (.namedData ⟨0⟩)) 0, .unit, .bool false]
private def context : Core.Context := [OptionalCell.referenceType (.namedData ⟨0⟩), .unit, .bool]
private theorem heapRelated : GenericHeap.HeapRepresents model [0] world heap store := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  exact (empty.allocate (.initialized rootRelated) .append).1.allocate_administrative .integer
private theorem environmentTyped : RuntimeEnvironmentHasTypes world environment context catalog.definitions :=
  .cons (.cellRef rfl) (.cons .unit (.cons .bool .nil))
private theorem nonMapping : ¬ ∃ key value, boxType = .mapping key value := by
  intro impossible; obtain ⟨_, _, same⟩ := impossible; cases same
private theorem rootLayout : DataPlaceSnapshot.RootLayout catalog prepared boxType := .ordinary nonMapping rfl
private def expression : Expr := .apply (setter prepared .unit) (.pair (.loadCell (.var 0)) (.pair (.var 1) (.var 2)))
private def updatedSource : Dynamic.Value := .constructed metadata [.bool false, .bool false]
private def updatedCore : Value := .constructed ⟨⟨0⟩, 0⟩ (.pair (.bool false) (.bool false))
private theorem expectedChange : Dynamic.ProjectionsUpdate (fun _ value => value = .bool false)
    (some sourceRoot) [.member "value" 0] updatedSource := .member .head (.leaf rfl) .head
private theorem ran : runStateful 100 (.initial expression environment store) = .done (.inRight .word updatedCore) store := by cbv

/-- The second field is taken from the latest root and survives the first-field
replacement. No source update trace is supplied to the reflection theorem. -/
example : ∃ futureWorld administrative,
    ValueRep catalog signatures functions [0] futureWorld boxType updatedSource updatedCore (.namedData ⟨0⟩) ∧
    Dynamic.ProjectionsUpdate (fun _ value => value = .bool false) (some sourceRoot) [.member "value" 0] updatedSource ∧
    GenericHeap.HeapRepresents model [0] futureWorld heap store ∧
    GeneralHeap.AdministrativePreserved [0] store [0] store ∧ store = store ++ administrative := by
  obtain ⟨futureWorld, administrative, result, _, heaps, _, frame, appended⟩ :=
    DataPlaceSetterReflection.reflects_at functionTypes layouts observations faithful (cell := cell) raw
      (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2 (.member .nil) .nil rfl rootLayout (.bool false)
      heapRelated ⟨rfl, rfl⟩ (.intro .head) environmentTyped (infer_sound (by cbv))
      (.var rfl) (.var (index := 1) rfl) (.var (index := 2) rfl) (runStateful_evaluation_sound ran)
  cases result with
  | updated root changed related =>
    cases root
    have same := changed.functional (fun _ _ _ left right => left.trans right.symm) expectedChange
    cases same
    exact ⟨futureWorld, administrative, related, changed, heaps, frame, appended⟩

/-- The source-only construction retains first-match duplicate position and
appends an absent key, using the language's own MappingLookup/Absent rules. -/
example : ∃ updated, Dynamic.ProjectionsUpdate (fun _ value => value = .bool false)
    (some (.mapping .bool .bool [(.bool true, .bool true), (.bool true, .bool true)])) [.index (.bool true)] updated :=
  DataPlaceUpdateTotality.read_update (.indexFound (.head ⟨rfl, .bool true⟩) .nil) (.bool false)

example : ∃ updated, Dynamic.ProjectionsUpdate (fun _ value => value = .bool true)
    (some (.mapping .bool .bool [])) [.index (.bool false)] updated :=
  DataPlaceUpdateTotality.read_update (.indexDefault .nil .bool .nil) (.bool true)

end Tests.SourceCoreDataPlaceSetterReflection
