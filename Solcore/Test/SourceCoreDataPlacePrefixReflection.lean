import Solcore.SourceSemantics.CoreLowering.DataPlacePrefixReflection
import Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog

/-! The actual whole execute expression reflects its source target before RHS
evaluation. Empty-key certificates use a vacuous universal child theorem; named
member failure suppresses a visible RHS write, and bare initialization exposes
the actual three-slot continuation as an output witness. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.SourceCoreDataPlacePrefixReflection
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
private def scope : Scope := [(binder.id, .namedData ⟨0⟩)]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def sourceContext := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def place : PlaceResolution := ⟨binder.id, projections, .bool⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ _ _ => False
private def faults : GenericExpressionMeaning.FaultRep := fun _ _ => True
private theorem meaning (program : SourceSemantics.Program) :
    GenericExpressionMeaning.Reflects model program sourceContext [] source Child faults := by
  intro scope id lowered impossible
  exact impossible.elim
private theorem environments : DataHeap.EnvRepresents catalog [0] world [.unit] scope sourceEnvironment environment :=
  .cons ⟨rfl, rfl⟩ (.nil (.cons .unit .nil))
private theorem locals : Dynamic.EnvironmentAgrees heap sourceContext.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem targetLayout : DataPlaceResolvedTarget.Layout checked signatures functions source Child scope place
    prepared [] [] (SourceCoreLocalCell.coreContext scope ++ [.unit]) := by
  refine ⟨.nil, rfl, rootLayout, ?_, infer_sound (by decide)⟩
  intro mapping world sources values evaluated shaped related
  cases shaped with
  | member shaped =>
    cases shaped
    cases related
    exact raw.prepared_path (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2
      (.member .nil) .nil (allKeys := []) (by intro i value impossible; simp at impossible)
private def skippedRhs : Expr := .letE (.storeCell (.var 0) (.inRight .unit (.construct ⟨⟨0⟩, 0⟩ (.bool true))))
  (LanguageResult.success (.bool true))
private def expression : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) skippedRhs
  (LanguageResult.success .unit) .unit none false Word.zero
private theorem ran : runStateful 100 (.initial expression environment store) =
    .done (.inLeft .unit (.word invalid)) store := by cbv
private theorem reflected (program : SourceSemantics.Program) :
    DataPlacePrefixReflection.Result checked signatures functions program sourceContext [] source faults prepared [] [] place
      sourceEnvironment environment heap store [0] world skippedRhs (LanguageResult.success .unit) .unit none false Word.zero
      (.inLeft .unit (.word invalid)) store :=
  DataPlacePrefixReflection.reflects targetLayout raw (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2
    (meaning program) functionTypes layouts observations faithful (fun _ => trivial) environments heapRelated locals rfl
    .head (.intro .head) rfl trivial (runStateful_evaluation_sound ran)

/-- Both the ordinary source cell and sentinel remain untouched because target
resolution fails before entering the RHS's storeCell. The independent fault is
constructed by whole-prefix reflection, rather than supplied to it. -/
example (program : SourceSemantics.Program) :
    ∃ reason after finalMap finalWorld,
      Dynamic.SourcePlaceFaults program sourceContext [] source sourceEnvironment heap place reason after ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after store ∧
      GeneralHeap.AdministrativePreserved [0] store finalMap store := by
  have result := reflected program
  cases result with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata => exact ⟨_, _, _, _, sourceFault, heaps, frame⟩
  | resolved sourceTrace execution continuation =>
    cases sourceTrace with
    | intro lookup initialRead evaluate currentRead initialValue selection =>
      have locationEq := lookup.functional (show Dynamic.Environment.LooksUp sourceEnvironment place.root ⟨0⟩ from .head)
      cases locationEq
      cases evaluate with
      | member evaluate =>
        cases evaluate
        have cellEq := currentRead.functional (show Dynamic.Heap.Reads heap ⟨0⟩ cell from .intro .head)
        cases cellEq
        cases initialValue with
        | uninitialized => cases selection

private def bareRoute : Route := ⟨boxType, .namedData ⟨0⟩, .namedData ⟨0⟩, [], none⟩
private def barePrepared : Prepared := ⟨bareRoute, [], [], invalid⟩
private def barePlace : PlaceResolution := ⟨binder.id, [], boxType⟩
private theorem bareLayout : DataPlaceResolvedTarget.Layout checked signatures functions source Child scope barePlace
    barePrepared [] [] (SourceCoreLocalCell.coreContext scope ++ [.unit]) := by
  refine ⟨.nil, rfl, .ordinary nonMapping rfl, ?_, infer_sound (by decide)⟩
  intro mapping world sources values projections shaped related
  cases shaped
  exact ⟨0, .nil rfl⟩
private def rhs : Expr := LanguageResult.success (.construct ⟨⟨0⟩, 0⟩ (.bool true))
private def bareExpression : Expr := execute barePrepared (.var 0) (SourceCoreCalls.packArguments []) rhs
  (LanguageResult.success .unit) .unit none false Word.zero
private def finalStore : Store := [.inRight .unit (.constructed ⟨⟨0⟩, 0⟩ (.bool true)), .integer 900]
private theorem bareRan : runStateful 100 (.initial bareExpression environment store) = .done (.inRight .word .unit) finalStore := by cbv

/-- The resolved branch carries its actual empty snapshot and the remaining
RHS/write/continuation evaluation under three administrative slots. -/
example (program : SourceSemantics.Program) : ∃ target after, ∃ execution : DataPlaceResolvedTarget.Execution checked signatures functions barePrepared [] [] barePlace target
      environment store [0] world heap after,
    Dynamic.SourcePlaceResolves program sourceContext [] source sourceEnvironment heap barePlace target after ∧
    Evaluates (DataPlaceExecution.snapshotEnvironment barePrepared.route.rootType execution.target
      (DataPatternValues.packValues execution.values) execution.snapshot environment) execution.store
      (DataPlacePrefixReflection.remainder barePrepared .unit rhs (LanguageResult.success .unit) .unit none false Word.zero)
      (.inRight .word .unit) finalStore := by
  have result := DataPlacePrefixReflection.reflects (checked := checked) bareLayout
    (steps := []) (.nil rfl) (fuel := 5) (missing := fun _ => Word.zero) (.nil 0)
    (meaning program) functionTypes layouts observations faithful (fun _ => trivial) environments heapRelated locals rfl
    .head (.intro .head) rfl trivial (runStateful_evaluation_sound bareRan)
  cases result with
  | fault sourceFault resultEq => cases resultEq
  | resolved sourceTrace execution continuation => exact ⟨_, _, execution, sourceTrace, continuation⟩

end Tests.SourceCoreDataPlacePrefixReflection
