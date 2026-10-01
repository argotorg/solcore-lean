import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceContinuation
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleAssignment
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_assignment", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_assignment.solc"⟩, 0, 1⟩
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

/-- The small child IH is independently proved for all heaps, environments
and renamings. It does not retain an execution as a certificate field. -/
private theorem childMeaning : GenericExpressionMeaning.Preserves
    (payloadModel checked compilation.registry (noFunctions checked.catalog)) program context [] source Child (fun _ _ => False) := by
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

private def before : Dynamic.Heap := ⟨[⟨rootType, none, none⟩]⟩
private def after : Dynamic.Heap := ⟨[⟨rootType, some (.mapping .bool .bool [(.bool true, .bool true)]), none⟩]⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def store (prepared : Prepared) : Store := [.inLeft prepared.route.rootType .unit]
private def world (prepared : Prepared) : StoreTyping := [OptionalCell.cellType prepared.route.rootType]
private def nativeEnvironment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 0]
private def body (prepared : Prepared) : Expr :=
  execute prepared (.var 0) (SourceCoreCalls.packArguments [lowered]) lowered.expression lowered.expression lowered.type none false Word.zero
private theorem localAgrees : Dynamic.EnvironmentAgrees before context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme, .mapping (.builtin .bool) (.builtin .bool)⟩
private theorem sourceAssignment : Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
    environment before assignment.target key (.mapping .bool .bool [(.bool true, .bool true)]) after := by
  have resolved : Dynamic.SourcePlaceResolves program context [] source environment before assignment.target
      ⟨⟨0⟩, rootType, .bool, [.index (.bool true)], some (.bool false)⟩ before :=
    .intro (place := assignment.target) (environment := environment) (before := before) (after := before) .head (.intro .head) (.index (keyEvaluates environment before) .nil) (.intro .head) (.emptyMapping .bool .bool)
      (.indexDefault .nil .bool .nil)
  refine .intro resolved (keyEvaluates environment before) ?_
  exact .intro (.intro .head) rfl (.emptyMapping .bool .bool)
    (.indexDefault .nil .bool (.leaf (.equal _ _)) (.append .nil)) (.intro (.intro .head) .head)

theorem whole {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.zero) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (nativeEnvironment prepared) (store prepared) (body prepared) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (payloadModel checked compilation.registry (noFunctions checked.catalog))
        finalMap finalWorld .bool .bool (fun _ _ => False) (.value (.bool true)) value ∧
      HeapRepresents checked compilation.registry (noFunctions checked.catalog) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends (world prepared) finalWorld ∧
      AdministrativePreserved [0] (store prepared) finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨rootEq, leafEq, rootProjection, leaf, leafView, layout⟩ := staticReceipt described preparedBy keyTypes nonempty getterTyped setterTyped
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (GenericHeap.CellRepresents.uninitialized rootProjection) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] (world prepared) [] (scope prepared) environment (nativeEnvironment prepared) :=
    .cons reference (.nil .nil)
  have writable : WritableLocal context binder.id prepared.route.rootSourceType := rootEq ▸ rootWritable
  exact CompatiblePlaceContinuation.preserves_from_source (compilation := compilation) (ambient := .original checked.catalog.definitions) (functions := noFunctions checked.catalog) (node := node) (nextNode := node) (index := 0) layout (.refl _) childMeaning faithful observations
    ⟨rfl, rfl⟩ (by cbv) leafView leafEq.symm (.inl rfl) environments heaps localAgrees (by simp [scope, SourceCoreLocalCell.lookup?, assignment])
    writable sourceAssignment Word.zero ⟨rfl, rfl⟩ (by cbv) (.value (keyEvaluates environment after))

/-- Staging changes the retained source type, while the actual modifier uses
the scalar payload. Zero divisors and negative Integer inputs remain total. -/
theorem staged_modifier (operator : Syntax.ValueAssignOp) (left right : Int) :
    ∃ result value, ValueRep checked compilation.registry (noFunctions checked.catalog) [] []
      (.comptime .integer) result value .integer ∧
      Dynamic.AssignmentValueApplies operator (some (.integer left)) (.integer right) result ∧
      Evaluates [.integer right, .inRight .unit (.integer left)] []
        (modified .integer (binaryOperator true operator) false (.var 1) (.var 0) Word.zero)
        (.inRight .word value) [] ∧
      ¬ Dynamic.AssignmentOperandsInvalid operator (some (.integer left)) (.integer right) :=
  CompatiblePlaceModifier.initialized_success (sourceType := .comptime .integer) (operator := operator)
    (environment := [.integer right, .inRight .unit (.integer left)]) observations (.inr (.inr rfl))
    (.compatible (actual := .integer) rfl (.integer left)) (.compatible (actual := .integer) rfl (.integer right))
    (.var rfl) (.var rfl) [] Word.zero

private theorem child_compiled {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (certified : Child scope id code) : SourceCoreBasic.lowerExpression 10 source scope id Word.zero = .ok code := by
  obtain ⟨rfl, rfl⟩ := certified
  cbv

private def exercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.zero) = .ok prepared) : IO Unit := do
  if keyTypes : prepared.keyTypes = [.bool] then
    match stepsEq : prepared.steps with
    | [] => throw (IO.userError "compatible assignment omitted index")
    | _ :: _ =>
      have nonempty : prepared.steps ≠ [] := by rw [stepsEq]; simp
      if getTyped : infer? (getContext prepared) (getCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
        if putTyped : infer? (putContext prepared) (putCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.route.rootType) then
          have receipt := whole described preparedBy keyTypes nonempty (infer_sound getTyped) (infer_sound putTyped)
          have _finite : ∃ fuel value finalStore, runStateful fuel (.initial (body prepared) (nativeEnvironment prepared) (store prepared)) = .done value finalStore := by
            obtain ⟨value, finalStore, _, _, evaluated, _⟩ := receipt
            obtain ⟨fuel, completed⟩ := evaluation_runStateful_complete evaluated
            exact ⟨fuel, value, finalStore, completed⟩
          have _actualChild := child_compiled (scope := scope prepared) (show Child (scope prepared) key lowered from ⟨rfl, rfl⟩)
          unless infer? [OptionalCell.referenceType prepared.route.rootType] (body prepared) checked.catalog.definitions == some (LanguageResult.resultType .bool) do
            throw (IO.userError "compatible assignment full checker failed")
          let initial := Core.State.initial (body prepared) (nativeEnvironment prepared) (store prepared)
          match runStateful 200000 initial with
          | .done (.inRight .word (.bool true)) afterStore =>
            unless afterStore.length == 1 + 3 * (checked.catalog.entries.length + 1) do
              throw (IO.userError "compatible assignment administrative allocation count changed")
            match afterStore.read? 0 with
            | some (.inRight .unit value) =>
              match SourceCoreCompatibleValues.decode 100 compilation rootType value with
              | .ok actual => unless actual == .mapping .bool .bool [(.bool true, .bool true)] do
                  throw (IO.userError "compatible assignment virtual-root write changed source payload")
              | .error error => throw (IO.userError s!"compatible assignment decode failed: {reprStr error}")
            | _ => throw (IO.userError "compatible assignment failed to initialize root")
            match runStateful 13 initial with
            | .outOfFuel checkpoint =>
              unless runStateful 200000 checkpoint == .done (.inRight .word (.bool true)) afterStore do
                throw (IO.userError "compatible assignment resume changed result/store")
            | _ => throw (IO.userError "compatible assignment expected a checkpoint")
          | other => throw (IO.userError s!"compatible assignment failed: {reprStr other}")
        else throw (IO.userError "compatible assignment setter checker failed")
      else throw (IO.userError "compatible assignment getter checker failed")
  else throw (IO.userError "compatible assignment key types changed")

def run : IO Unit := do
  match described : describe compilation checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"compatible assignment describe failed: {reprStr error}")
  | .ok route =>
    match preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.zero) with
    | .error error => throw (IO.userError s!"compatible assignment prepare failed: {reprStr error}")
    | .ok _ => exercise described preparedBy
  for (operator, left, right, expected) in
      [(Syntax.ValueAssignOp.divide, (-7 : Int), 3, -3), (.modulo, -7, 3, 2), (.divide, -7, 0, 0), (.modulo, -7, 0, 0), (.bitAnd, -7, 3, 1)] do
    have _meaning := staged_modifier operator left right
    let expression := modified .integer (binaryOperator true operator) false (.var 1) (.var 0) Word.zero
    unless runStateful 50 (.initial expression [.integer right, .inRight .unit (.integer left)] []) == .done (.inRight .word (.integer expected)) [] do
      throw (IO.userError "compatible staged Integer modifier changed independent primitive meaning")
  IO.println "compatible whole assignment, continuation and staged modifiers GREEN"

end Tests.SourceCoreCompatibleAssignment
