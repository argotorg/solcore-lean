import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleAssignmentReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_assignment_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_assignment_reflection.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool .bool
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], .bool⟩, []⟩
private def context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem unique : NodeOccurrencesUnique source := by simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem contains : ContainsExpression source key node := lookupExpression?_sound (by cbv)
private theorem selected {other : ExpressionNode} (member : ContainsExpression source key other) : other = node :=
  Option.some.inj ((lookupExpression?_complete unique member).symm.trans (show source.lookupExpression? key = some node by cbv))
private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ id code => id = key ∧ code = lowered

/-- The child reflection IH is proved uniformly, including every hidden-slot
renaming. Its source execution is constructed from the completed Core child. -/
private theorem childReflects (registry : SourceCoreRawMetadata.Registry) (faults : GenericExpressionMeaning.FaultRep) :
    GenericExpressionMeaning.Reflects (payloadModel checked registry (noFunctions checked.catalog))
      program context [] source Child faults := by
  intro scope id code certificate n found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨rfl, rfl⟩ := certificate
  have nodeEq : n = node := Option.some.inj (found.symm.trans (show source.lookupExpression? key = some node by cbv))
  subst n
  cases evaluated with
  | inRight inner =>
    cases inner
    exact ⟨.value (.bool true), before, mapping, world, .value (.intro contains (.builtinBoolean rfl) .nil),
      .value (.bool true), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private def scope (prepared : Prepared) : SourceCoreLocalCell.Scope := [(binder.id, prepared.route.rootType)]
private def getCode (prepared : Prepared) : Expr :=
  .apply (getter prepared .bool) (.pair (.loadCell (.var 1)) (.var 0))
private def putCode (prepared : Prepared) : Expr :=
  .apply (setter prepared .bool) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))
private def getContext (prepared : Prepared) : Core.Context :=
  [.bool, OptionalCell.referenceType prepared.route.rootType, OptionalCell.referenceType prepared.route.rootType]
private def putContext (prepared : Prepared) : Core.Context :=
  [prepared.route.leafType, prepared.route.leafType, prepared.optionalLeaf, .bool,
    OptionalCell.referenceType prepared.route.rootType, OptionalCell.referenceType prepared.route.rootType]

private theorem staticReceipt {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.zero) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions) :
    prepared.route.rootSourceType = rootType ∧ prepared.route.leafType = .bool ∧
    checked.catalog.project rootType = .ok prepared.route.rootType ∧
    ∃ leaf, SourceCoreRawMetadata.runtimeType leaf = .bool ∧
      CompatiblePlaceAssignmentSuccess.Layout compilation source Child (scope prepared) site assignment.target prepared [lowered] [.bool] leaf [] := by
  obtain ⟨actualBinder, leaf, receipt⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (receipt.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  obtain ⟨routeEq, _, path⟩ := receipt.prepared preparedBy
  have rootEq : prepared.route.rootSourceType = rootType := routeEq ▸ receipt.rootSource
  have leafEq : prepared.route.leafType = .bool := by
    rw [routeEq]
    exact Except.ok.inj receipt.leafProjected.symm
  have children : DataExpressionSequence.Tree source Child (scope prepared)
      (DataPlaceKeyOrder.sourceKeys assignment.target.projections) [.bool] [lowered] :=
    .single (node := node) (by cbv) ⟨rfl, rfl⟩
  have keyTyped : ExpressionHasType source context key .bool := by
    apply ExpressionHasType.ofOrdinary (node := node) (rawType := .bool) contains
      (.reference (.builtinBoolean true)) (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)) (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme))
    · intro id member; cases member
    · exact .nil _
    · rfl
  have projectionsTyped : SourceProjectionsHaveType source context rootType assignment.target.projections .bool := .index keyTyped (.nil _)
  have views := (CompatiblePlaceKeyTyping.of_typing unique rfl path rfl projectionsTyped children).1
  have actualPath : PreparedPath checked source site prepared.route.rootSourceType assignment.target.projections 0 prepared.steps prepared.keys leaf := by
    simpa only [rootEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using path
  refine ⟨rootEq, leafEq, by simpa only [routeEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using receipt.rootProjected, leaf, receipt.selectedType, ?_⟩
  refine ⟨actualPath, by simpa only [rootEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using views, children, keyTypes, ?_, ?_, nonempty, getterTyped, setterTyped⟩
  · change checked.catalog.project leaf = .ok prepared.route.leafType
    rw [← checked.catalog.project_runtimeType leaf, receipt.selectedType, leafEq]; rfl
  · intro key value declared
    rw [routeEq]
    apply receipt.virtual key value
    exact rootEq.symm.trans declared

private theorem functionViews : FunctionRuntimeViews (noFunctions checked.catalog) := fun impossible => False.elim impossible
private def before (initial : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨rootType, initial, none⟩]⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def world (prepared : Prepared) : StoreTyping := [OptionalCell.cellType prepared.route.rootType]
private def nativeEnvironment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 0]
private def body (prepared : Prepared) : Expr :=
  execute prepared (.var 0) (SourceCoreCalls.packArguments [lowered]) lowered.expression lowered.expression lowered.type none false Word.zero
private theorem localAgrees (initial : Option Dynamic.Value) : Dynamic.EnvironmentAgrees (before initial) context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme,
    .mapping (.builtin .bool) (.builtin .bool)⟩
private def diagnostics (registry : SourceCoreRawMetadata.Registry) (prepared : Prepared) : GenericExpressionMeaning.FaultRep :=
  fun reason token =>
    (∃ root resolved count, FaultToken checked registry root prepared.steps resolved reason token count) ∨
    ∃ location, reason = .uninitializedLocation location ∧ token = prepared.invalidProjection

/-- Actual describe/prepare/checker and authentic initial-cell receipts are
static inputs. The only execution premise is the completed emitted assignment;
its independent source target, RHS and update are outputs. -/
theorem whole {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.zero) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {registry : SourceCoreRawMetadata.Registry} (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native prepared.route.rootType)
    {result : Value} {after : Store}
    (completed : Evaluates (nativeEnvironment prepared) [native] (body prepared) result after) :
    CompatiblePlaceTailReflection.Result checked registry (noFunctions checked.catalog) program context [] source
      (diagnostics registry prepared) assignment.target .equal key environment (nativeEnvironment prepared)
      (before initial) [native] [0] (world prepared) lowered.expression .bool result after := by
  obtain ⟨rootEq, leafEq, rootProjection, leaf, leafView, layout⟩ := staticReceipt described preparedBy keyTypes nonempty getterTyped setterTyped
  obtain ⟨actualBinder, _, description⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  have routeEq := (description.prepared preparedBy).1
  have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
    intro nonmapping
    rw [routeEq]
    exact description.ordinary (fun k v same => nonmapping k v (rootEq.trans same))
  have empty : HeapRepresents checked registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate initialRep Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] (world prepared) [] (scope prepared)
      environment (nativeEnvironment prepared) := .cons reference (.nil .nil)
  exact CompatiblePlaceAssignmentReflection.reflects (node := node) (index := 0) layout ordinary registryExtension
    (childReflects registry _) functionViews faithful observations
    (fun receipt => .inl ⟨_, _, _, receipt⟩) (fun location => .inr ⟨location, rfl, rfl⟩)
    ⟨rfl, rfl⟩ (by cbv) leafView leafEq.symm (.inl rfl) environments heaps (localAgrees initial)
    (by simp [scope, SourceCoreLocalCell.lookup?, assignment]) (rootEq ▸ rootWritable) completed

/-- A successful whole run with this compiled literal continuation yields an
independent completed source assignment and the final common heap. -/
theorem successful_whole {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.zero) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {registry : SourceCoreRawMetadata.Registry} (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native prepared.route.rootType)
    {after : Store}
    (completed : Evaluates (nativeEnvironment prepared) [native] (body prepared) (.inRight .word (.bool true)) after) :
    ∃ updated sourceAfter finalMap finalWorld,
      Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
        environment (before initial) assignment.target key updated sourceAfter ∧
      HeapRepresents checked registry (noFunctions checked.catalog) finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends (world prepared) finalWorld ∧
      AdministrativePreserved [0] [native] finalMap after ∧ Dynamic.HeapMetadataExtend (before initial) sourceAfter := by
  have reflected := whole described preparedBy keyTypes nonempty getterTyped setterTyped registryExtension initialRep completed
  cases reflected with
  | fault _ resultEq => cases resultEq
  | committed trace heaps maps worlds frame metadata length continuation =>
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, lowered, LanguageResult.success] at continuation
    cases continuation with
    | inRight valueEvaluated =>
      cases valueEvaluated
      exact ⟨_, _, _, _, trace, heaps, maps, worlds, frame, metadata⟩

private theorem child_compiled {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (certified : Child scope id code) : SourceCoreBasic.lowerExpression 10 source scope id Word.zero = .ok code := by
  obtain ⟨rfl, rfl⟩ := certified
  cbv

private def exercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.zero) = .ok prepared)
    {registry : SourceCoreRawMetadata.Registry} (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initialSource : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initialSource, none⟩ native prepared.route.rootType)
    (expected : SourceCoreDataValues.Value) : IO Unit := do
  if keyTypes : prepared.keyTypes = [.bool] then
    if nonempty : prepared.steps ≠ [] then
      if getTyped : infer? (getContext prepared) (getCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
        if putTyped : infer? (putContext prepared) (putCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.route.rootType) then
          have _compiled := child_compiled (scope := scope prepared) (show Child (scope prepared) key lowered from ⟨rfl, rfl⟩)
          unless infer? [OptionalCell.referenceType prepared.route.rootType] (body prepared) checked.catalog.definitions == some (LanguageResult.resultType .bool) do
            throw (IO.userError "compatible assignment reflection checker failed")
          let initial := Core.State.initial (body prepared) (nativeEnvironment prepared) [native]
          match ran : runStateful 200000 initial with
          | .done result afterStore =>
            have _reflected := whole described preparedBy keyTypes nonempty (infer_sound getTyped) (infer_sound putTyped)
              registryExtension initialRep (runStateful_evaluation_sound ran)
            if success : result = .inRight .word (.bool true) then
              have _source := successful_whole described preparedBy keyTypes nonempty (infer_sound getTyped) (infer_sound putTyped)
                registryExtension initialRep (success ▸ runStateful_evaluation_sound ran)
              pure ()
            else throw (IO.userError "compatible assignment reflection did not succeed")
            unless result == .inRight .word (.bool true) && afterStore.length == 1 + 3 * (checked.catalog.entries.length + 1) do
              throw (IO.userError "compatible assignment reflection result/admin count changed")
            match afterStore.read? 0 with
            | some (.inRight .unit value) =>
              let outputContext : SourceCoreCompatibleValues.Context := ⟨checked, registry, registryExtension⟩
              match SourceCoreCompatibleValues.decode 100 outputContext rootType value with
              | .ok actual => unless actual == expected do
                  throw (IO.userError "compatible assignment reflection raw metadata/duplicate order changed")
              | .error error => throw (IO.userError s!"compatible assignment reflection decode failed {reprStr error}")
            | _ => throw (IO.userError "compatible assignment reflection root write missing")
            match runStateful 13 initial with
            | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done result afterStore do
                throw (IO.userError "compatible assignment reflection resume changed result/store")
            | _ => throw (IO.userError "compatible assignment reflection expected checkpoint")
          | other => throw (IO.userError s!"compatible assignment reflection run failed {reprStr other}")
        else throw (IO.userError "compatible assignment reflection setter checker failed")
      else throw (IO.userError "compatible assignment reflection getter checker failed")
    else throw (IO.userError "compatible assignment reflection missing steps")
  else throw (IO.userError "compatible assignment reflection key types changed")

private def carrier : SourceCoreDataValues.Value :=
  .mapping (.comptime .bool) (.comptime .bool) [(.bool true, .bool false), (.bool true, .bool false), (.bool false, .bool true)]
private def sourceRoot : Dynamic.Value :=
  .mapping (.comptime .bool) (.comptime .bool) [(.bool true, .bool false), (.bool true, .bool false), (.bool false, .bool true)]
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceRoot :=
  .mapping (.prepend (.bool true) (.bool false) (.prepend (.bool true) (.bool false) (.prepend (.bool false) (.bool true) .empty)))

private def casesFor {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.zero) = .ok prepared) : IO Unit := do
  have projected : checked.catalog.project rootType = .ok prepared.route.rootType := by
    obtain ⟨actualBinder, _, description⟩ := CompatiblePlaceDescription.of_describe described
    have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
    subst actualBinder
    have routeEq := (description.prepared preparedBy).1
    simpa only [routeEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using description.rootProjected
  exercise described preparedBy (.refl _) (.uninitialized projected) (.mapping .bool .bool [(.bool true, .bool true)])
  match accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
  | .error error => throw (IO.userError s!"compatible assignment reflection encode failed {reprStr error}")
  | .ok encoded =>
    have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [] []
    have same := Except.ok.inj (represented.projection.symm.trans projected)
    exercise described preparedBy encoded.preserves (.initialized (same ▸ represented))
      (.mapping (.comptime .bool) (.comptime .bool) [(.bool true, .bool true), (.bool true, .bool false), (.bool false, .bool true)])

def run : IO Unit := do
  match described : describe compilation checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"compatible assignment reflection describe failed {reprStr error}")
  | .ok route =>
    match preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.zero) with
    | .error error => throw (IO.userError s!"compatible assignment reflection prepare failed {reprStr error}")
    | .ok _ => casesFor described preparedBy
  IO.println "compatible whole assignment reflection derives source update and preserves raw duplicate order GREEN"

end Tests.SourceCoreCompatibleAssignmentReflection
