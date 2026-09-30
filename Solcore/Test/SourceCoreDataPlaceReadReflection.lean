import Solcore.SourceSemantics.CoreLowering.DataPlaceReadReflection
import Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog

/-! Actual mixed mapping/member selectors reflect both found values and
missing defaults. No independent source projection trace is supplied to the
reflection theorem. Administrative cells retain the input store prefix. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option cbv.maxSteps 2000000
namespace Tests.SourceCoreDataPlaceReadReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceRouteCertificates

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"read_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "read_reflection.solc"⟩, 0, 1⟩
private def keyId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def mappingType : TypeSystem.Ty := .mapping .bool boxType
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.integer], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def mapLayout : Core.OrderedMapping.Layout := ⟨.bool, .namedData ⟨0⟩, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.integer]⟩, constructors := [⟨dataId, 0⟩] },
  { sourceType := mappingType, definition := some mapLayout.definition }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono mappingType, [], false, none⟩
private def node : ExpressionNode := { id := keyId, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression keyId], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index keyId, .member "value" 0]
private def branches : List MemberBranch := [⟨⟨⟨0⟩, 0⟩, [.integer]⟩]
private def route : Route := ⟨mappingType, mapLayout.type, .integer,
  [.index mapLayout keyId boxType, .member ⟨0⟩ 0 branches .integer], some mapLayout⟩
private def token : Word := ⟨19, by decide⟩
private theorem preparationExists : (prepare checked 20 route Word.zero (fun _ => token)).toOption.isSome = true := by cbv
private def prepared : Prepared := (prepare checked 20 route Word.zero (fun _ => token)).toOption.get preparationExists
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok => rfl
private theorem preparedBy : prepare checked 20 route Word.zero (fun _ => token) = .ok prepared :=
  except_get _ preparationExists
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private theorem functionTypes : FunctionRuntimeTypes functions := fun impossible => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem registered : mapLayout.Registered catalog.definitions := ⟨.bool, .namedData rfl, rfl⟩
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; trivial
  | succ index => cases index with
    | zero => cases selected; exact ⟨.bool, .namedData ⟨0⟩, rfl, rfl, registered⟩
    | succ index => simp [catalog] at selected
private theorem profile : Profile signatures source mappingType projections .integer := by
  refine .index rfl (show source.lookupExpression? keyId = some node by cbv) rfl ?_
  refine .member (field := .integer) (signature := signature) (arguments := []) rfl (by cbv) ?_ (.nil rfl)
  intro constructor member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  subst constructor
  rfl
private theorem raw : RawPath checked signatures source mappingType mapLayout.type route.steps projections .integer .integer [.bool] := by
  obtain ⟨_, types, raw⟩ := raw_of_routeSteps profile (show catalog.project mappingType = .ok mapLayout.type by rfl)
    (show catalog.project TypeSystem.Ty.integer = .ok .integer by rfl)
    (show routeSteps checked signatures source (.occurrence keyId.occurrence) binder.id mappingType projections =
      .ok (route.steps, TypeSystem.Ty.integer) by cbv)
  have keyTree : DataExpressionSequence.Tree source (fun _ _ _ => True) [] [keyId] [.bool]
      [⟨.bool, LanguageResult.success (.bool true)⟩] := .single (show source.lookupExpression? keyId = some node by cbv) trivial
  have same := raw.keyTypes.tree_types keyTree
  rw [← same] at raw
  exact raw
private theorem shaped : DataPlaceKeyOrder.Values projections [.bool true] [.index (.bool true), .member "value" 0] :=
  .index (.member .nil)
private theorem keysRelated : DataExpressionSequence.Values (payloadModel catalog signatures functions) [] []
    [.bool] [.bool] [.bool true] [.bool true] := .cons (.bool true) .nil
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [.integer], boxType⟩
private def sourceBox : Dynamic.Value := .constructed metadata [.integer 7]
private def coreBox : Value := .constructed ⟨⟨0⟩, 0⟩ (.integer 7)
private theorem boxRelated : ValueRep catalog signatures functions [] [] boxType sourceBox coreBox (.namedData ⟨0⟩) :=
  .constructed (metadata := metadata) (tag := ⟨⟨0⟩, 0⟩) (declaration := dataId) (arguments := [])
    rfl rfl (by cbv) rfl rfl (.cons (.integer 7) .nil)
private def fullRoot : Dynamic.Value := .mapping .bool boxType [(.bool true, sourceBox)]
private def fullCore : Value := Core.OrderedMapping.encode mapLayout [(.bool true, coreBox)]
private theorem fullRelated : ValueRep catalog signatures functions [] [] mappingType fullRoot fullCore mapLayout.type :=
  .mapping rfl rfl rfl registered (.prepend (.bool true) boxRelated (.empty _ _ _ _))
private def emptyRoot : Dynamic.Value := .mapping .bool boxType []
private def emptyCore : Value := Core.OrderedMapping.encode mapLayout []
private theorem emptyRelated : ValueRep catalog signatures functions [] [] mappingType emptyRoot emptyCore mapLayout.type :=
  .mapping rfl rfl rfl registered (.empty _ _ _ _)
private def selector : Expr := select prepared prepared.steps (.var 0) (.var 1)
private def before : Store := [.integer 900]
private def finalStore (root : Value) : Store := match runStateful 500 (.initial selector [root, .bool true] before) with
  | .done _ store => store
  | _ => []
private theorem fullRan : runStateful 500 (.initial selector [fullCore, .bool true] before) =
    .done (.inRight .word (.inRight .unit (.integer 7))) (finalStore fullCore) := by cbv
private theorem emptyRan : runStateful 500 (.initial selector [emptyCore, .bool true] before) =
    .done (.inLeft prepared.optionalLeaf (.word token)) (finalStore emptyCore) := by cbv

/-- All source outcomes are inferred from the generated selector's run. -/
example : ∃ selected value,
    Dynamic.ProjectionsRead (some fullRoot) [.index (.bool true), .member "value" 0] (some selected) ∧
    ValueRep catalog signatures functions [] [] .integer selected value .integer ∧
    value = .integer 7 := by
  obtain ⟨administrative, count, appended, bound, path, reflected⟩ := DataPlaceReadReflection.reflects
    functionTypes layouts observations faithful raw (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2
    shaped keysRelated (by cbv) fullRelated (DataEquality.Selects.var rfl) (DataEquality.Selects.var (index := 1) rfl)
    (runStateful_evaluation_sound fullRan)
  rcases reflected with ⟨selected, value, read, related, same⟩ | ⟨reason, token, fault, impossible⟩
  · exact ⟨selected, value, read, related, (Value.inRight.inj (Value.inRight.inj same).2).2.symm⟩
  · cases impossible

example : ∃ reason, Dynamic.ProjectionsFaults (some emptyRoot) [.index (.bool true), .member "value" 0] reason := by
  obtain ⟨administrative, count, appended, bound, path, reflected⟩ := DataPlaceReadReflection.reflects
    functionTypes layouts observations faithful raw (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2
    shaped keysRelated (by cbv) emptyRelated (DataEquality.Selects.var rfl) (DataEquality.Selects.var (index := 1) rfl)
    (runStateful_evaluation_sound emptyRan)
  rcases reflected with ⟨selected, value, read, related, impossible⟩ | ⟨reason, token, fault, same⟩
  · cases impossible
  · exact ⟨reason, fault⟩

example : (finalStore fullCore).length = before.length + 3 := by cbv
example : (finalStore emptyCore)[0]? = some (.integer 900) := by cbv

/-- Metadata-only typing for both concrete closure models does not require
source captured-cell validity or an assumption about running the body. -/
example (catalog : SourceCoreDataCatalog.Catalog) (program : SourceSemantics.Program) (certificate : FunctionCode.BodyCertificate)
    (policy : SourceCoreFunctions.Policy) : FunctionRuntimeTypes (FunctionValues.model catalog program certificate policy) :=
  ordinary_function_runtimeTypes catalog program certificate policy
example (catalog : SourceCoreDataCatalog.Catalog) (program : SourceSemantics.Program) (certificate : FunctionCode.BodyCertificate)
    (table : SourceCoreStageCodebook.Table) : FunctionRuntimeTypes (ContractedFunctionValues.model catalog program certificate table) :=
  contracted_function_runtimeTypes catalog program certificate table

end Tests.SourceCoreDataPlaceReadReflection
