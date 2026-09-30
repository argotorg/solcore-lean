import Solcore.SourceSemantics.CoreLowering.DataPlaceGetterReflection
import Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog

/-! A live ordinary absent cell is accepted as the snapshot of a bare place,
but a named member projection reports the invalid-projection token. Both are
actual checked helpers and finite Core runs; reflection supplies the independent
root/read outcome without requiring a source trace. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.SourceCoreDataPlaceGetterReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceRouteCertificates

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"getter_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "getter_reflection.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.bool], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.bool]⟩, constructors := [⟨dataId, 0⟩] }] }
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
private def branches : List MemberBranch := [⟨⟨⟨0⟩, 0⟩, [.bool]⟩]
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
private def cell : Dynamic.Cell := ⟨boxType, none, none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [OptionalCell.cellType (.namedData ⟨0⟩), .integer]
private def store : Store := [.inLeft (.namedData ⟨0⟩) .unit, .integer 900]
private def environment : Environment := [.cellRef (OptionalCell.cellType (.namedData ⟨0⟩)) 0, .unit]
private def context : Core.Context := [OptionalCell.referenceType (.namedData ⟨0⟩), .unit]
private theorem heapRelated : GenericHeap.HeapRepresents model [0] world heap store := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  exact (empty.allocate (.uninitialized rfl) .append).1.allocate_administrative .integer
private theorem environmentTyped : RuntimeEnvironmentHasTypes world environment context catalog.definitions :=
  .cons (.cellRef rfl) (.cons .unit .nil)
private theorem nonMapping : ¬ ∃ key value, boxType = .mapping key value := by
  intro impossible; obtain ⟨_, _, same⟩ := impossible; cases same
private theorem rootLayout : DataPlaceSnapshot.RootLayout catalog prepared boxType := .ordinary nonMapping rfl
private def expression : Expr := .apply (getter prepared .unit) (.pair (.loadCell (.var 0)) (.var 1))
private theorem ran : runStateful 40 (.initial expression environment store) =
    .done (.inLeft prepared.optionalLeaf (.word invalid)) store := by cbv

example : ∃ futureWorld administrative,
    DataPlaceGetterReflection.ResultRep catalog signatures functions [0] futureWorld prepared (fun _ => Word.zero)
      .bool cell [.member "value" 0] (.inLeft prepared.optionalLeaf (.word invalid)) ∧
    GenericHeap.HeapRepresents model [0] futureWorld heap store ∧
    GeneralHeap.AdministrativePreserved [0] store [0] store ∧ store = store ++ administrative := by
  obtain ⟨futureWorld, administrative, result, _, heaps, _, frame, appended⟩ :=
    DataPlaceGetterReflection.reflects_at functionTypes layouts observations faithful (cell := cell) raw
      (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2 (.member .nil) .nil rfl rootLayout
      heapRelated ⟨rfl, rfl⟩ (.intro .head) environmentTyped (infer_sound (by decide))
      (.var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound ran)
  exact ⟨futureWorld, administrative, result, heaps, frame, appended⟩

private def bareRoute : Route := ⟨boxType, .namedData ⟨0⟩, .namedData ⟨0⟩, [], none⟩
private def barePrepared : Prepared := ⟨bareRoute, [], [], invalid⟩
private def bareExpression : Expr := .apply (getter barePrepared .unit) (.pair (.loadCell (.var 0)) (.var 1))
private theorem bareRan : runStateful 30 (.initial bareExpression environment store) =
    .done (.inRight .word (.inLeft (.namedData ⟨0⟩) .unit)) store := by cbv

/-- An absent bare target is a valid snapshot for a subsequent initializing
assignment. It is not confused with a failure to project an absent value. -/
example : ∃ futureWorld administrative,
    DataPlaceGetterReflection.ResultRep catalog signatures functions [0] futureWorld barePrepared (fun _ => Word.zero)
      boxType cell [] (.inRight .word (.inLeft (.namedData ⟨0⟩) .unit)) ∧
    GenericHeap.HeapRepresents model [0] futureWorld heap store ∧ store = store ++ administrative := by
  obtain ⟨futureWorld, administrative, result, _, heaps, _, _, appended⟩ :=
    DataPlaceGetterReflection.reflects_at (checked := checked) functionTypes layouts observations faithful
      (source := source) (cell := cell) (prepared := barePrepared) (.nil rfl)
      (fuel := 5) (DataPlaceMappingPreparation.Steps.nil 0) .nil .nil rfl (.ordinary nonMapping rfl)
      heapRelated ⟨rfl, rfl⟩ (.intro .head) environmentTyped (infer_sound (by decide))
      (.var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound bareRan)
  exact ⟨futureWorld, administrative, result, heaps, appended⟩

end Tests.SourceCoreDataPlaceGetterReflection
