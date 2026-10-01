import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTargetFaults
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleTargetFaults
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_target_fault", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_target_fault.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def valueType : TypeSystem.Ty := .function .bool .bool
private def rootType : TypeSystem.Ty := .comptime (.mapping .bool valueType)
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], valueType⟩, []⟩
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

/-- The small child IH is independently proved for all heaps, environments
and renamings. It does not retain an execution as a certificate field. -/
private theorem childMeaning (registry : SourceCoreRawMetadata.Registry) : GenericExpressionMeaning.Preserves
    (payloadModel checked registry (noFunctions checked.catalog)) program context [] source Child (fun _ _ => False) := by
  intro scope id code certificate n found mapping world administrative environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨rfl, rfl⟩ := certificate
  have nodeEq : n = node := Option.some.inj (found.symm.trans (show source.lookupExpression? key = some node by cbv))
  subst n
  have outcomeEq : outcome = .value (.bool true) ∧ after = before := by
    cases trace with
    | value evaluated =>
      cases evaluated with
      | intro member form coercions =>
        have eq := selected member; subst_vars
        cases form
        cases coercions
        exact ⟨rfl, rfl⟩
      | generalizedLocal member form => have eq := selected member; subst_vars; cases form
    | fault fault =>
      cases fault with
      | missing absent => exact (Dynamic.ExpressionAbsentIn.excludes_contains (source := source) absent contains).elim
      | form member failed => have eq := selected member; subst_vars; cases failed
      | coercion member _ failed => have eq := selected member; subst_vars; cases failed
      | generalizedLocalRequirement member form => have eq := selected member; subst_vars; cases form
      | generalizedLocalCoercion member form => have eq := selected member; subst_vars; cases form
  obtain ⟨rfl, rfl⟩ := outcomeEq
  exact ⟨_, store, mapping, world, .inRight .bool, .value (.bool true), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private theorem keyEvaluates (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context [] source environment heap key (.bool true) heap :=
  .intro contains (.builtinBoolean rfl) .nil


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

private theorem pathViews {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
    (path : PreparedPath checked source site rootType assignment.target.projections 0 steps keySites leaf) : KeyViews path [.bool] := by
  cases path with
  | index certificate generated tail =>
    have same := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := same
    cases tail
    exact .index (certificate := certificate) (generated := generated) rfl .nil

private theorem staticReceipt {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions) :
    prepared.route.rootSourceType = rootType ∧ checked.catalog.project valueType = .ok prepared.route.leafType ∧
    checked.catalog.project rootType = .ok prepared.route.rootType ∧
    ∃ leaf, SourceCoreRawMetadata.runtimeType leaf = valueType ∧
      CompatiblePlaceAssignmentSuccess.Layout compilation source Child (scope prepared) site assignment.target prepared [lowered] [.bool] leaf [] := by
  obtain ⟨actualBinder, leaf, receipt⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (receipt.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  obtain ⟨routeEq, _, path⟩ := receipt.prepared preparedBy
  have rootEq : prepared.route.rootSourceType = rootType := routeEq ▸ receipt.rootSource
  have leafEq : checked.catalog.project valueType = .ok prepared.route.leafType := by
    rw [routeEq]
    exact receipt.leafProjected
  have children : DataExpressionSequence.Tree source Child (scope prepared)
      (DataPlaceKeyOrder.sourceKeys assignment.target.projections) [.bool] [lowered] :=
    .single (node := node) (by cbv) ⟨rfl, rfl⟩
  have views := pathViews path
  have actualPath : PreparedPath checked source site prepared.route.rootSourceType assignment.target.projections 0 prepared.steps prepared.keys leaf := by
    simpa only [rootEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using path
  refine ⟨rootEq, leafEq, by simpa only [routeEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using receipt.rootProjected, leaf, receipt.selectedType, ?_⟩
  refine ⟨actualPath, by simpa only [rootEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using views, children, keyTypes, ?_, ?_, nonempty, getterTyped, setterTyped⟩
  · change checked.catalog.project leaf = .ok prepared.route.leafType
    rw [← checked.catalog.project_runtimeType leaf, receipt.selectedType]; exact leafEq
  · intro key value declared
    rw [routeEq]
    apply receipt.virtual key value
    exact rootEq.symm.trans declared

private def carrier : SourceCoreDataValues.Value := .mapping .bool (.comptime valueType) []
private def sourceRoot : Dynamic.Value := .mapping .bool (.comptime valueType) []
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceRoot := .mapping .empty
private theorem unavailable : ¬ Dynamic.Defaultable (.comptime valueType) := by
  intro impossible; cases impossible with | comptime inner => cases inner
private theorem fault : Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault (.comptime valueType)) :=
  .indexDefaultUnavailable (.bool true) .nil unavailable
private def before : Dynamic.Heap := ⟨[⟨rootType, some sourceRoot, none⟩]⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def world (prepared : Prepared) : StoreTyping := [OptionalCell.cellType prepared.route.rootType]
private def nativeEnvironment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 0]
private def body (prepared : Prepared) : Expr :=
  execute prepared (.var 0) (SourceCoreCalls.packArguments [lowered])
    (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
    (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool none false Word.zero
private theorem localAgrees : Dynamic.EnvironmentAgrees before context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme,
    .comptime (.mapping (.builtin .bool) (.function (.builtin .bool) (.builtin .bool)))⟩

/-- The public target theorem consumes actual compiler and encoder receipts.
The proof uses a universal child theorem and authentic raw staged default. -/
theorem whole {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context [] source environment before assignment.target .equal key
        (.missingMappingDefault (.comptime valueType)) before ∧
      Evaluates (nativeEnvironment prepared) [.inRight .unit encoded.value] (body prepared) (.inLeft .bool (.word token)) finalStore ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) finalMap finalWorld before finalStore := by
  obtain ⟨rootEq, _, rootProjection, leaf, _, layout⟩ := staticReceipt described preparedBy keyTypes nonempty getterTyped setterTyped
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [] []
  have same := Except.ok.inj (represented.projection.symm.trans rootProjection)
  rw [same] at represented
  obtain ⟨heaps, reference⟩ := empty.allocate (.initialized represented) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] (world prepared) [] (scope prepared) environment (nativeEnvironment prepared) :=
    .cons reference (.nil .nil)
  have writable : WritableLocal context binder.id prepared.route.rootSourceType := rootEq ▸ rootWritable
  obtain ⟨token, _, _, finalStore, finalMap, finalWorld, failed, _, _, evaluated, heaps, _⟩ :=
    CompatiblePlaceTargetFaults.projection (compilation := compilation) (ambient := .original checked.catalog.definitions) (functions := noFunctions checked.catalog) (index := 0) layout (childMeaning encoded.context.registry) environments heaps localAgrees
      (by simp [scope, SourceCoreLocalCell.lookup?, assignment]) writable
      (Dynamic.Environment.LooksUp.head) (Dynamic.Heap.Reads.intro .head)
      (Dynamic.SourceProjectionsEvaluate.index (keyEvaluates environment before) .nil) (Dynamic.Heap.Reads.intro .head)
      encoded.preserves faithful observations Dynamic.RootInitialValue.initialized fault .equal key
      (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
      (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool Word.zero
  exact ⟨token, finalStore, finalMap, finalWorld, failed, evaluated, heaps⟩

private def absent : Dynamic.Heap := ⟨[⟨rootType, none, none⟩]⟩
private theorem absentAgrees : Dynamic.EnvironmentAgrees absent context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil

/-- An outer staged declaration remains a nonmapping raw root for the
independent uninitialized rule, although its structural route contains an
index. Actual describe supplies the absence of a virtual-empty initializer. -/
theorem uninitialized {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context [] source environment absent assignment.target .equal key
        (.uninitializedLocation ⟨0⟩) absent ∧
      Evaluates (nativeEnvironment prepared) [.inLeft prepared.route.rootType .unit] (body prepared)
        (.inLeft .bool (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents checked compilation.registry (noFunctions checked.catalog) finalMap finalWorld absent finalStore := by
  obtain ⟨rootEq, _, rootProjection, leaf, _, layout⟩ := staticReceipt described preparedBy keyTypes nonempty getterTyped setterTyped
  obtain ⟨actualBinder, _, description⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  have routeEq := (description.prepared preparedBy).1
  have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
    intro _
    rw [routeEq]
    exact description.ordinary (by intros; intro impossible; cases impossible)
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (.uninitialized rootProjection) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] (world prepared) [] (scope prepared) environment (nativeEnvironment prepared) :=
    .cons reference (.nil .nil)
  have writable : WritableLocal context binder.id prepared.route.rootSourceType := rootEq ▸ rootWritable
  obtain ⟨finalStore, finalMap, finalWorld, failed, evaluated, heaps, _⟩ :=
    CompatiblePlaceTargetFaults.uninitialized (compilation := compilation) (ambient := .original checked.catalog.definitions) (functions := noFunctions checked.catalog) (index := 0) layout (childMeaning compilation.registry) environments heaps absentAgrees
      (by simp [scope, SourceCoreLocalCell.lookup?, assignment]) writable
      (Dynamic.Environment.LooksUp.head) (Dynamic.Heap.Reads.intro .head)
      (Dynamic.SourceProjectionsEvaluate.index (keyEvaluates environment absent) .nil) (Dynamic.Heap.Reads.intro .head)
      ordinary rfl (by rintro ⟨k, v, impossible⟩; cases impossible) (by simp) .equal key
      (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
      (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool Word.zero
  exact ⟨finalStore, finalMap, finalWorld, failed, evaluated, heaps⟩

private def exercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) : IO Unit := do
  if keyTypes : prepared.keyTypes = [.bool] then
    match stepsEq : prepared.steps with
    | [] => throw (IO.userError "target fault omitted index")
    | _ :: _ =>
      have nonempty : prepared.steps ≠ [] := by rw [stepsEq]; simp
      if getTyped : infer? (getContext prepared) (getCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
        if putTyped : infer? (putContext prepared) (putCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.route.rootType) then
          have receipt := whole described preparedBy keyTypes nonempty (infer_sound getTyped) (infer_sound putTyped) accepted
          have _finite : ∃ fuel token after, runStateful fuel (.initial (body prepared) (nativeEnvironment prepared) [.inRight .unit encoded.value]) = .done (.inLeft .bool (.word token)) after := by
            obtain ⟨token, after, _, _, _, evaluated, _⟩ := receipt
            obtain ⟨fuel, completed⟩ := evaluation_runStateful_complete evaluated
            exact ⟨fuel, token, after, completed⟩
          have _absent := uninitialized described preparedBy keyTypes nonempty (infer_sound getTyped) (infer_sound putTyped)
          let absentStore := [Value.inLeft prepared.route.rootType .unit]
          unless runStateful 200000 (.initial (body prepared) (nativeEnvironment prepared) absentStore) ==
              .done (.inLeft .bool (.word prepared.invalidProjection)) absentStore do
            throw (IO.userError "ordinary absent root allocated helpers or ran RHS")
          let keyEffect := Expr.letE (.storeCell (.var 1) (.inRight .unit (.bool true))) (LanguageResult.success (.bool true))
          let effectBody := execute prepared (.var 0) ⟨.bool, keyEffect⟩
            (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
            (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool none false Word.zero
          let effectEnvironment := nativeEnvironment prepared ++ [.cellRef (OptionalCell.cellType .bool) 1]
          let effectStore := absentStore ++ [.inRight .unit (.bool false)]
          unless infer? [OptionalCell.referenceType prepared.route.rootType, OptionalCell.referenceType .bool]
              effectBody checked.catalog.definitions == some (LanguageResult.resultType .bool) do
            throw (IO.userError "target key effect body rejected")
          unless runStateful 200000 (.initial effectBody effectEnvironment effectStore) ==
              .done (.inLeft .bool (.word prepared.invalidProjection)) (absentStore ++ [.inRight .unit (.bool true)]) do
            throw (IO.userError "target fault lost successful key effects or ran RHS")
          let header ← match encoded.value with
            | .pair (.word word) _ => pure word
            | _ => throw (IO.userError "target fault missing raw mapping header")
          unless encoded.context.registry.lookup header == some (.mapping .bool (.comptime valueType)) do
            throw (IO.userError "target fault lost raw default metadata")
          unless infer? [OptionalCell.referenceType prepared.route.rootType] (body prepared) checked.catalog.definitions == some (LanguageResult.resultType .bool) do
            throw (IO.userError "target fault emitted body rejected")
          let initial := Core.State.initial (body prepared) (nativeEnvironment prepared) [.inRight .unit encoded.value]
          match runStateful 200000 initial with
          | .done (.inLeft .bool (.word token)) after =>
            unless token == (Word.ofNatModulo 100).add header && after.take 1 == [.inRight .unit encoded.value] &&
                after.length == 1 + checked.catalog.entries.length + 1 do
              throw (IO.userError "target fault lost root or evaluated RHS/continuation")
            match runStateful 11 initial with
            | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done (.inLeft .bool (.word token)) after do
                throw (IO.userError "target fault resumption changed observation")
            | _ => throw (IO.userError "target fault expected checkpoint")
          | other => throw (IO.userError s!"target fault unexpected result {reprStr other}")
        else throw (IO.userError "target fault setter checker failed")
      else throw (IO.userError "target fault getter checker failed")
  else throw (IO.userError "target fault key types changed")

def run : IO Unit := do
  match described : describe compilation checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"target fault describe failed {reprStr error}")
  | .ok route =>
    match preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) with
    | .error error => throw (IO.userError s!"target fault prepare failed {reprStr error}")
    | .ok _ =>
      match accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
      | .error error => throw (IO.userError s!"target fault encoding failed {reprStr error}")
      | .ok _ => exercise described preparedBy accepted
  IO.println "compatible target failure before RHS and exact raw default token GREEN"

end Tests.SourceCoreCompatibleTargetFaults
