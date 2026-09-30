import Solcore.SourceSemantics.CoreLowering.DataPlaceGetterReflection
import Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog

/-! An outer missing mapping defaults to an empty inner mapping. The actual
selector and updater must report the inner unavailable-function default token,
without running an arbitrary replacement or rewriting the store prefix. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option cbv.maxSteps 2500000
namespace Tests.SourceCoreDataPlaceExactFault
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceRouteCertificates

private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"exact_fault", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "exact_fault.solc"⟩, 0, 1⟩
private def first : ExpressionId := ⟨⟨owner, 0⟩⟩
private def second : ExpressionId := ⟨⟨owner, 1⟩⟩
private def firstNode : ExpressionNode := { id := first, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def secondNode : ExpressionNode := { id := second, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def functionType : TypeSystem.Ty := .function .unit .unit
private def innerType : TypeSystem.Ty := .mapping .bool functionType
private def rootType : TypeSystem.Ty := .mapping .bool innerType
private def inner : Core.OrderedMapping.Layout := ⟨.bool, TaggedFunction.functionType .unit .unit, ⟨0⟩⟩
private def outer : Core.OrderedMapping.Layout := ⟨.bool, inner.type, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some inner.definition },
  { sourceType := rootType, definition := some outer.definition }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def source : TypedSource := { owner, inputs := [], roots := [.expression first, .expression second], nodes := [.expression firstNode, .expression secondNode] }
private def projections : List PlaceProjection := [.index first, .index second]
private def route : Route := ⟨rootType, outer.type, inner.valueType,
  [.index outer first innerType, .index inner second functionType], some outer⟩
private def missing (type : TypeSystem.Ty) : Word := if type = functionType then ⟨31, by decide⟩ else ⟨17, by decide⟩
private theorem existsPrepared : (prepare checked 15 route Word.zero missing).toOption.isSome = true := by cbv
private def prepared : Prepared := (prepare checked 15 route Word.zero missing).toOption.get existsPrepared
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok => rfl
private theorem preparedBy : prepare checked 15 route Word.zero missing = .ok prepared := except_get _ existsPrepared
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) := fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private theorem innerRegistered : inner.Registered catalog.definitions :=
  ⟨.bool, .product (.sum .unit .word) (.function .unit (.sum .word .unit)), rfl⟩
private theorem outerRegistered : outer.Registered catalog.definitions := ⟨.bool, .namedData rfl, rfl⟩
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; exact ⟨.bool, inner.valueType, rfl, rfl, innerRegistered⟩
  | succ index => cases index with
    | zero => cases selected; exact ⟨.bool, inner.type, rfl, rfl, outerRegistered⟩
    | succ index => simp [catalog] at selected
private theorem raw : RawPath checked signatures source rootType outer.type route.steps projections functionType inner.valueType [.bool, .bool] :=
  .index (layout := outer) rfl rfl rfl rfl (show source.lookupExpression? first = some firstNode by cbv) rfl
    (.index (layout := inner) rfl rfl rfl rfl (show source.lookupExpression? second = some secondNode by cbv) rfl (.nil rfl))
private theorem shaped : DataPlaceKeyOrder.Values projections [.bool true, .bool false] [.index (.bool true), .index (.bool false)] :=
  .index (.index .nil)
private theorem keyValues {mapping : GeneralHeap.LocationMap} {world : StoreTyping} : DataExpressionSequence.Values (payloadModel catalog signatures functions) mapping world [.bool, .bool]
    [.bool, .bool] [.bool true, .bool false] [.bool true, .bool false] := .cons (.bool true) (.cons (.bool false) .nil)
private def sourceRoot : Dynamic.Value := .mapping .bool innerType []
private def coreRoot : Value := .constructed outer.nilConstructor .unit
private theorem related : ValueRep catalog signatures functions [] [] rootType sourceRoot coreRoot outer.type :=
  .mapping rfl rfl rfl outerRegistered (.empty _ _ _ _)
private theorem sourceFault : Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true), .index (.bool false)]
    (.missingMappingDefault functionType) := by
  exact .indexDefault (.bool true) .nil (.mapping _ _)
    (.indexDefaultUnavailable (.bool false) .nil (by intro impossible; cases impossible))

example (environment : Environment) (store : Store) (replacement : Expr) :
    ∃ after administrative,
      Evaluates (coreRoot :: .pair (.bool true) (.bool false) :: environment) store
        (select prepared prepared.steps (.var 0) (.var 1))
        (.inLeft prepared.optionalLeaf (.word ⟨31, by decide⟩)) after ∧
      Evaluates (coreRoot :: .pair (.bool true) (.bool false) :: environment) store
        (update prepared prepared.steps outer.type (.var 0) (.var 1) replacement)
        (.inLeft outer.type (.word ⟨31, by decide⟩)) after ∧ after = store ++ administrative := by
  simpa only [DataPlaceExactFault.token, missing, ↓reduceIte] using
    DataPlaceExactFault.preserves observations faithful layouts raw
      (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2 shaped (keyValues (mapping := []) (world := []))
      (allKeys := [.bool true, .bool false]) (by intro i v selected; simpa using selected) (by cbv)
      related sourceFault (coreRoot :: .pair (.bool true) (.bool false) :: environment) store
      (.var 0) (.var 1) replacement (DataEquality.Selects.var rfl) (DataEquality.Selects.var (index := 1) rfl)

example : missing innerType ≠ missing functionType := by decide

private def model := payloadModel catalog signatures functions
private def cell : Dynamic.Cell := ⟨rootType, none, none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [OptionalCell.cellType outer.type, .integer]
private def before : Store := [.inLeft outer.type .unit, .integer 900]
private def environment : Environment := [.cellRef (OptionalCell.cellType outer.type) 0, .pair (.bool true) (.bool false)]
private def expression : Expr := .apply (getter prepared (.product .bool .bool))
  (.pair (.loadCell (.var 0)) (.var 1))
private theorem heapRelated : GenericHeap.HeapRepresents model [0] world heap before := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  exact (empty.allocate (.uninitialized rfl) .append).1.allocate_administrative .integer
private theorem functionTypes : FunctionRuntimeTypes functions := fun impossible => False.elim impossible
private theorem preparedRoute : prepared.route = route := (DataPlaceMappingPreparation.steps_of_prepare preparedBy).1
private theorem rawPrepared : RawPath checked signatures source rootType prepared.route.rootType route.steps projections functionType prepared.route.leafType [.bool, .bool] := by
  rw [preparedRoute]
  exact raw
private theorem rootLayout : DataPlaceSnapshot.RootLayout catalog prepared rootType :=
  .mapping (by rw [preparedRoute]; rfl) rfl rfl rfl outerRegistered
private def summary : StatefulRunResult → Option (Value × Nat × Store)
  | .done value store => some (value, store.length, store.take 2)
  | _ => none
private theorem actualRun : summary (runStateful 1000 (.initial expression environment before)) =
    some (.inLeft prepared.optionalLeaf (.word ⟨31, by decide⟩), 8, before) := by cbv

/-- The root remains uninitialized: both outer/inner mappings are virtual,
while the two lookup invocations append six ordinary helper cells. Reflection
constructs the independent source failure without an assumed source trace. -/
example : ∃ result after futureWorld administrative,
    runStateful 1000 (.initial expression environment before) = .done result after ∧
    result = .inLeft prepared.optionalLeaf (.word ⟨31, by decide⟩) ∧ after.length = 8 ∧
    DataPlaceGetterReflection.ResultRep catalog signatures functions [0] futureWorld prepared missing
      functionType cell [.index (.bool true), .index (.bool false)] result ∧
    GenericHeap.HeapRepresents model [0] futureWorld heap after ∧
    GeneralHeap.AdministrativePreserved [0] before [0] after ∧ after = before ++ administrative := by
  have measured := actualRun
  cases ran : runStateful 1000 (.initial expression environment before) with
  | outOfFuel => simp [ran, summary] at measured
  | fault => simp [ran, summary] at measured
  | done result after =>
    simp only [ran, summary, Option.some.injEq, Prod.mk.injEq] at measured
    obtain ⟨futureWorld, administrative, represented, _, heaps, _, frame, appended⟩ :=
      DataPlaceGetterReflection.reflects_at functionTypes layouts observations faithful (cell := cell) rawPrepared
        (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2 shaped keyValues (by cbv) rootLayout
        heapRelated (by rw [preparedRoute]; exact ⟨rfl, rfl⟩) (.intro .head)
        (show RuntimeEnvironmentHasTypes world environment [OptionalCell.referenceType outer.type, .product .bool .bool] catalog.definitions from
          .cons (.cellRef rfl) (.cons (.pair .bool .bool) .nil))
        (infer_sound (show infer? [OptionalCell.referenceType outer.type, .product .bool .bool] expression catalog.definitions =
          some (LanguageResult.resultType prepared.optionalLeaf) by cbv))
        (by rw [preparedRoute]; exact .var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound ran)
    exact ⟨result, after, futureWorld, administrative, rfl, measured.1, measured.2.1, represented, heaps, frame, appended⟩

end Tests.SourceCoreDataPlaceExactFault
