import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.Frontend.SourceCore.CompatibleFunctions
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.TypedPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive

/-!
# Compatible statement tests

Compatible assignments, renamed assignments, statements and typed compositions.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAssignment
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
the scalar payload. Zero divisors and negative Integer inputs remain total;
the shifts take Words only. -/
theorem staged_modifier (operator : Syntax.ValueAssignOp) (notWordOnly : operator.wordOnly = false) (left right : Int) :
    ∃ result value, ValueRep checked compilation.registry (noFunctions checked.catalog) [] []
      (.comptime .integer) result value .integer ∧
      Dynamic.AssignmentValueApplies operator (some (.integer left)) (.integer right) result ∧
      Evaluates [.integer right, .inRight .unit (.integer left)] []
        (modified .integer (binaryOperator true operator) false (.var 1) (.var 0) Word.zero)
        (.inRight .word value) [] ∧
      ¬ Dynamic.AssignmentOperandsInvalid operator (some (.integer left)) (.integer right) :=
  CompatiblePlaceModifier.initialized_success (sourceType := .comptime .integer) (operator := operator)
    (environment := [.integer right, .inRight .unit (.integer left)]) observations (.inr (.inr ⟨rfl, notWordOnly⟩))
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
    if notWordOnly : operator.wordOnly = false then
      have _meaning := staged_modifier operator notWordOnly left right
      let expression := modified .integer (binaryOperator true operator) false (.var 1) (.var 0) Word.zero
      unless runStateful 50 (.initial expression [.integer right, .inRight .unit (.integer left)] []) == .done (.inRight .word (.integer expected)) [] do
        throw (IO.userError "compatible staged Integer modifier changed independent primitive meaning")
    else
      throw (IO.userError "compatible staged Integer modifiers take no shift")
  IO.println "compatible whole assignment, continuation and staged modifiers GREEN"

end Tests.SourceCoreCompatibleAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAssignmentReflection
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAssignmentStatements
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Assignment spines consume actual compatible flow receipts and retain all
source effects before failure. Runtime fixtures combine projected and bare
writes with lexical tails, early return, a closure that keeps the value it
captured before a later write, and suspension. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCompatibleAssignmentStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleAssignmentStatements GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"assignment_statement", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "assignment_statement.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (n : Nat) : StatementId := ⟨⟨owner, n + 1⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "x", .mono .bool, [], false, none⟩
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .bool⟩, []⟩
private def literal : ExpressionNode := { id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def assigned : StatementNode := ⟨statement 0, span, .unit, .assignValue assignment .equal expression⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some expression)⟩
private def source : TypedSource := {
  owner := owner
  inputs := [binder]
  roots := [.statement (statement 0), .statement (statement 1)]
  nodes := [.expression literal, .statement assigned, .statement returned]
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[{type := .bool, value := none}]⟩
private def after : Dynamic.Heap := ⟨[{type := .bool, value := some (.bool true)}]⟩
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem booleanTyped : ExpressionHasType source context expression .bool := by
  have admissible : TypeAdmissible context .bool := .bool (by
    simp [TypeParameterBindersWellFormed, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
  apply ExpressionHasType.ofOrdinary (node := literal) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) admissible admissible
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem writable : WritableLocal context binder.id .bool := by
  apply WritableLocal.withLocal_mono_admissible
  exact .bool (by simp [TypeParameterBindersWellFormed, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
private theorem syntaxTree (mode : Bool) : CompatibleAssignmentStatements.Syntax source context mode [statement 0, statement 1] .bool := by
  apply CompatibleAssignmentStatements.Syntax.assign (node := assigned) rfl rfl
  · intro actual found
    have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
    have same := Except.ok.inj (this.symm.trans found)
    cases same
    exact .nil _
  · intro actual found
    have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
    have same := Except.ok.inj (this.symm.trans found)
    cases same
    exact writable
  · exact booleanTyped
  · exact .inl rfl
  · exact .tail (.body (.returnValue [] rfl rfl rfl rfl rfl booleanTyped (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal rfl (.bool "true" true))))))))))

private theorem sourceAssigned : Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
    environment before assignment.target expression (.bool true) after := by
  have read : Dynamic.Heap.Reads before ⟨0⟩ {type := .bool, value := none} := .intro .head
  have initial : Dynamic.RootInitialValue {type := .bool, value := none} none :=
    .uninitialized (by rintro ⟨key, value, impossible⟩; cases impossible)
  refine .intro (targetHeap := before) (rhsHeap := before) (rightValue := .bool true)
    (target := ⟨⟨0⟩, .bool, .bool, [], none⟩) ?_ ?_ ?_
  · exact Dynamic.SourcePlaceResolves.intro (place := assignment.target) (environment := environment) .head read .nil read initial .nil
  · exact .intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
  · exact .intro read rfl initial (.leaf (.equal none (.bool true))) (.intro read .head)

private theorem sourceTrace (mode : Bool) : TypedScopedStatements.Executes mode program context [] source environment before
    [statement 0, statement 1] context (.returned (.bool true)) after := by
  have first : Dynamic.StatementExecutes program context [] source environment before (statement 0) context (.fallthrough environment) after :=
    .assignValue (lookupStatement?_sound rfl) rfl sourceAssigned
  have last : Dynamic.StatementExecutes program context [] source environment after (statement 1) context (.returned (.bool true)) after :=
    .returnValue (lookupStatement?_sound rfl) rfl (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil)
  exact TypedScopedStatements.prepend (lookupStatement?_sound (show source.lookupStatement? (statement 0) = some assigned from rfl))
    (by intro _ _ _ impossible; cases impossible) first
    (TypedLexicalControl.terminal_outcome program [] (show source.lookupStatement? (statement 1) = some returned from rfl)
      (by intro expression impossible; cases impossible) (.control last) (.returned _))

section CompilerBridge
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {definitions : DataEnvironment}
  {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingReason : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (matched : AssignmentPolicy policy values invalidProjection invalidOperand missingReason)
  (sourceSignatures : context.signatures = values.checked.signatures)
  (expressions : ∀ fuel id lowered, policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
    source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope id lowered ∧
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  (sites : ∀ {fuel statements type mode selfReason code},
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code →
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code (LocalLoop.resultType type) definitions)
  (tails : ∀ {mode statements expected fuel type selfReason code},
    TypedLexicalControl.Syntax source context mode statements expected →
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code →
    TypedLexicalControl.Tree layouts specialization active frame globals onError readFuel values source solved reasonAt context scope mode statements expected type code)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [statement 0, statement 1] .bool reasonAt mode selfReason = .ok code)

include matched sourceSignatures expressions sites tails accepted in
theorem certified : Tree layouts specialization active frame globals onError readFuel values source solved reasonAt
    context scope administrative definitions mode [statement 0, statement 1] .bool .bool code :=
  tree_of_flow matched unique sourceSignatures expressions sites tails (syntaxTree mode) accepted

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (sameDefinitions : definitions = ambient.definitions)
  (layoutDefinitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (valid : CompatibleExpressionLiterals.ContextValid solved context []) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (errors : Tree.Errors registry faults (certified matched sourceSignatures expressions sites tails accepted))
  {mapping : LocationMap} {world : StoreTyping} {canonical actual : Environment} {actualContext : Core.Context}
  {store : Store} {ξ : Renaming} {location : Location} {native : CallableIndexedHistory.NativeFrame}
  (environments : DataHeap.EnvRepresents (storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type location))
  (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
  (unmapped : location ∉ mapping)

include matched sourceSignatures expressions sites tails sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_preserves :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedScopedStatements.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool (.returned (.bool true)) value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment context after := by
  subst definitions
  exact (certified matched sourceSignatures expressions sites tails accepted).preserves functions layoutDefinitions registered extension program [] valid
    uninitialized missing faithful observations errors unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include matched sourceSignatures expressions sites tails sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_reflects (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ finalContext outcome sourceHeap finalMap finalWorld,
      TypedScopedStatements.Executes mode program context [] source environment before [statement 0, statement 1] finalContext outcome sourceHeap ∧
      TypedScopedStatements.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld sourceHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before sourceHeap ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext sourceHeap := by
  subst definitions
  exact (certified matched sourceSignatures expressions sites tails accepted).reflects functions layoutDefinitions registered extension program [] valid
    uninitialized missing faithful observations runtimeViews errors unique environments heaps locals agrees typed reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Word) }",
    "function bare() returns (Word) { let x: Word; x = 3; x += 4; x *= 2; x -= 1; return x; }",
    "function mapping() returns (Word) { let m: mapping(Bool => Word); m[true] = 3; m[true] += 4; m[false] = m[true] * 2; { let answer = m[false]; return answer; } return 0; }",
    "function nested() returns (Word) { let m: mapping(Bool => mapping(Bool => Word)); let keys: mapping(Bool => Bool); m[keys[true]][keys[false]] = 5; m[false][false] += 2; return m[false][false]; }",
    "function captured() returns (Word) { let x = 1; let read = lam() { return x; }; x += 8; return read(); }",
    "function missing() returns (Word) { let x: Word; let rhs: mapping(Bool => Word); x += rhs[true] + 2; let never = true; return 0; }",
    "function rhsFault() returns (Word) { let m: mapping(Bool => Word); let keys: mapping(Bool => Bool); let rhs: mapping(Bool => Word); let missing: Word; m[keys[true]] = rhs[false] + missing; let never = true; return 0; }",
    "function targetFault() returns (Word) { let m: mapping(Bool => Box); let keys: mapping(Bool => Bool); let rhs: mapping(Bool => Word); m[keys[true]] = .Box(rhs[false]); let never = true; return 0; }",
    "function early() returns (Word) { let x: Word; x = 11; if (true) { return x; } x = 99; return x; }"
  ]}] }

private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "assignment fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "assignment failure lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "assignment suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "assignment resume changed fault or executed unreachable allocation"
    | _, _ => throw (IO.userError "assignment resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "assignment statement checker" (checkProgram workspace)
  -- `read` captures `x = 1` by value, so the later `x += 8` does not reach it.
  for (name, result) in [("bare", 13), ("mapping", 14), ("nested", 7), ("captured", 1), ("early", 11)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected : SourceCompilerFeatureSupport.Value := .word (Word.ofNatModulo result)
    SourceCompilerFeatureSupport.require ((← entry.run []) == expected) s!"{name}: assignment statement value changed"
    entry.checkResume [] expected
  let bare ← SourceCompilerFeatureSupport.compileNamed checked "bare"
  bare.checkCells [] [(.word, some (.word (Word.ofNatModulo 13)))]
  let missing ← SourceCompilerFeatureSupport.compileNamed checked "missing"
  failureResume missing
  missing.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word []))]
  let rhs ← SourceCompilerFeatureSupport.compileNamed checked "rhsFault"
  failureResume rhs
  rhs.checkCells [] [(.mapping .bool .word, none), (.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.mapping .bool .word, some (.mapping .bool .word [])), (.word, none)]
  let target ← SourceCompilerFeatureSupport.compileNamed checked "targetFault"
  failureResume target
  let cells := (SourceCompilerFeatureSupport.sourceState (← target.audit [])).heap
  SourceCompilerFeatureSupport.require ((match cells with | [first, _, third] => first.value.isNone && third.value.isNone | _ => false))
    "target fault executed RHS or continuation"
  IO.println "assignment statements: bare/projected spines, compound updates, lazy key/RHS fault order, lexical tails, capture and resume GREEN"
end Tests.SourceCoreCompatibleAssignmentStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleRenamedAssignment
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Concrete expression trees close every key/RHS premise for an arbitrary
related actual environment. Checked-source executions insert an unrelated
Integer at an interior lexical position; real getter/setter comparator closures
capture that environment. Completed and faulting stores are checked on resume. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleRenamedAssignment
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceAssignmentSuccess
theorem preserves_prefix {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (layout : Layout (definitions := ambient.definitions) compilation source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (CompatibleRenamedPlaceSuccess.writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        ∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ)) := by
  have preservation : TypedGenericExpressionMeaning.Preserves
      (payloadModel compilation.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions registryExtension program evidence contextValid unique uninitialized missing
  exact CompatibleRenamedPlaceSuccess.preserves_prefix layout ordinary registryExtension preservation faithful observations
    rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped slot rootTyped trace invalidOperand


theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) result finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after ∧
      result = .inLeft outputType (.word token) ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleRenamedPlaceSuccess.writtenContext prepared (SourceCoreCalls.packArguments codes).type
          actualContext) ambient.definitions ∧
      Evaluates (slots ++ coreEnvironment) written (shift 7 (next.rename ξ)) result finalStore) := by
  have preservation : TypedGenericExpressionMeaning.Preserves
      (payloadModel compilation.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions registryExtension program evidence contextValid unique uninitialized missing
  have reflection : TypedGenericExpressionMeaning.Reflects
      (payloadModel compilation.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.reflects functions registryExtension program evidence contextValid uninitialized missing
  exact CompatibleRenamedPlaceReflection.reflects layout ordinary registryExtension reflection preservation
    functionTypes faithful observations missingTokens invalidTokens rhsGenerated found rhsView rhsCoreType
    operatorProfile environments heaps agrees actualTyped locals slot rootTyped completed

theorem preserves_fault {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have meaning : TypedGenericExpressionMeaning.Preserves
      (payloadModel compilation.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions registryExtension program evidence valid unique uninitialized missing
  exact CompatibleRenamedPlaceFaults.preserves layout ordinary registryExtension meaning faithful observations
    missingTokens invalidTokens rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped
    slot rootTyped trace next outputType invalid


namespace Completed
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function success() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[keys[true]] = vals[false] + 2; return root[false] + nextMap[true]; }",
    "function repeated() returns (Word) { let root: mapping(Bool => mapping(Bool => Word)); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[keys[true]][keys[true]] = vals[false] + 2; return root[false][false] + nextMap[true]; }",
    "function keyFault() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Bool; root[missing || keys[true]] = vals[false] + 2; return root[false] + nextMap[true]; }",
    "function rhsFault() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Word; root[keys[true]] = vals[false] + missing; return root[false] + nextMap[true]; }",
    "function skipped() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[false && keys[true]] = vals[false] + 2; return true ? root[false] : nextMap[true]; }",
    "function nextFault() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Word; root[keys[true]] = vals[false] + 2; return nextMap[true] + missing; }"
  ]}] }

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (solved : List SolvedRequirement) (name : String) : IO Unit := do
  let (statement, assignment, operator, rhs) ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .assignValue assignment operator rhs => some (node, assignment, operator, rhs) | _ => none
    | _ => none with
    | some result => pure result | none => throw (IO.userError "renamed assignment assignment missing")
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "renamed assignment diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "renamed assignment owner missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for binder in SourceCoreCompatibleDataPlaces.declaredBinders source do
    let type ← get "renamed assignment binder type" (checked.catalog.project binder.scheme.body)
    let expected ← match binder.scheme.body with
      | .mapping key value => do
        let encoded ← get "renamed assignment mapping header" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key value []))
        values := encoded.context
        pure (some encoded.value)
      | .constructor (.builtin .bool) | .constructor (.builtin .word) => pure none
      | other => throw (IO.userError s!"renamed assignment unsupported fixture binder: {reprStr other}")
    bindings := bindings ++ [(binder, type, OptionalCell.allocate type, expected)]
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let representation := SourceCoreCompatibleFunctions.representation values 150
  let child : SourceCoreCompatibleDataPlaces.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation checked.signatures prepared.locals
      prepared.contexts own.assignments diagnostics context prepared.callableContext none none fuel source scope id reasonAt
  let reasonAt := diagnostics.reasonAt owner
  let invalid := Word.ofNatModulo 999
  let nextId ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
    | _ => none with
    | some id => pure id | none => throw (IO.userError "renamed assignment return expression missing")
  let next ← get "renamed assignment actual continuation" (child 150 source scope nextId reasonAt)
  match accepted : SourceCoreCompatibleDataPlaces.lower values checked.signatures child 150 source scope
      (.occurrence statement.id.occurrence) assignment operator (some rhs) next.type next.expression
      reasonAt invalid invalid (fun _ => invalid) with
  | .error error => throw (IO.userError s!"actual renamed assignment lowering failed: {reprStr error}")
  | .ok lowered =>
    have receipt := CompatiblePlaceCompilerCertificates.generated_of_lower accepted
    let _receipt := receipt
    let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
    let frameExpr := SourceCoreCallableIndexedFrames.empty frame
    let closureType := Ty.function .unit frame.type
    let closure := Expr.lambda .unit frame.type (.var 1)
    -- The extra binding is inside the source-local slots, before slot 2.
    let insertion := Renaming.insertion 2
    let renamed := lowered.rename insertion
    let body := bindings.zipIdx.foldl (fun body ((_, _, initial, _), index) =>
      let body := if index == 2 then Expr.letE (.integer 91) body else body
      Expr.letE initial body) renamed
    let native : Core.Program := ⟨LanguageResult.resultType next.type,
      .letE frameExpr (.letE (.newCell closureType closure) body), checked.catalog.definitions ++ [frame.definition]⟩
    assertTrue native.check s!"renamed assignment {name} ambient checker rejected"
    let completed ← match native.runStateful 200000 with
      | .done result store => pure (result, store)
      | other => throw (IO.userError s!"renamed assignment {name} did not complete: {reprStr other}")
    for fuel in [0, 5, 40, 1000] do
      let result := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 200000 checkpoint
        | other => other
      assertTrue (result == .done completed.1 completed.2) s!"renamed assignment {name} resume changed result/store"
    assertTrue (completed.2[0]? == some (.closure .unit frame.type (.var 1) [.constructed frame.empty .unit]))
      "renamed assignment changed captured ambient value"
    let prefixFailed := name == "keyFault" || name == "rhsFault"
    let failed := prefixFailed || name == "nextFault"
    if failed then
      let occurrence ← match source.nodes.findSome? fun
        | .expression node => match node.form with | .reference "missing" (.local _) => some node.id | _ => none
        | _ => none with
        | some id => pure id | none => throw (IO.userError "renamed assignment missing fault occurrence")
      assertTrue (completed.1 == .inLeft next.type (.word (reasonAt occurrence))) "renamed assignment changed source fault token"
    else assertTrue (completed.1 == .inRight .word (.word (Word.ofNatModulo 2))) "renamed assignment successful outcome changed"
    for ((binder, type, _, expected), position) in bindings.zipIdx do
      let cell ← match completed.2[bindings.length - position]? with
        | some cell => pure cell | none => throw (IO.userError "renamed assignment lost a source cell")
      if binder.name == "root" then
        if prefixFailed then assertTrue (cell == .inLeft type .unit) "renamed assignment wrote root after child fault"
        else
          let .inRight .unit payload := cell | throw (IO.userError "renamed assignment root was not initialized")
          let decoded ← get "renamed assignment root decode" (SourceCoreCompatibleValues.decode 100 values binder.scheme.body payload)
          let two := SourceCoreDataValues.Value.word (Word.ofNatModulo 2)
          let expected := if name == "repeated" then
              SourceCoreDataValues.Value.mapping .bool (.mapping .bool .word)
                [(.bool false, .mapping .bool .word [(.bool false, two)])]
            else .mapping .bool .word [(.bool false, two)]
          assertTrue (decoded == expected) "renamed assignment changed key order or RHS result"
      else if let some expected := expected then
        let skipped := name == "keyFault" || (name == "skipped" && (binder.name == "keys" || binder.name == "nextMap")) || (prefixFailed && binder.name == "nextMap")
        assertTrue (cell == if skipped then .inLeft type .unit else .inRight .unit expected)
          s!"renamed assignment {name} changed lazy child effects for {binder.name}"
      else assertTrue (cell == .inLeft type .unit) "renamed assignment initialized faulting local"

def run : IO Unit := do
  let program ← get "renamed assignment source checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"renamed assignment specialization: {reprStr other}")
  let automatic ← get "renamed assignment actual factory" (SourceCoreCompatibleFunctions.prepare program plan 400)
  for function in automatic.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared function.specialized.function.typedBody function.signature.key
      function.specialized.function.solvedRequirements name
  assertTrue (automatic.prepared.functions.length == 6) "renamed assignment fixture coverage missing"
  IO.println "renamed assignment: actual seven-slot continuations, nested index, key/RHS/next faults, lazy effects and resume GREEN"


end Completed

namespace Faults
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function missingDefault() returns (Word) { let root: mapping(Bool => Box<Word>); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[keys[true]] = .Box(vals[false] + 2); return nextMap[true]; }",
    "function nestedDefault() returns (Word) { let root: mapping(Bool => mapping(Bool => Box<Word>)); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[keys[true]][keys[true]] = .Box(vals[false] + 2); return nextMap[true]; }",
    "function keyFirst() returns (Word) { let root: mapping(Bool => Box<Word>); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Bool; root[missing || keys[true]] = .Box(vals[false] + 2); return nextMap[true]; }",
    "function rhsFault() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Word; root[keys[true]] += vals[false] + missing; return nextMap[true]; }"
  ]}] }

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (solved : List SolvedRequirement) (name : String) : IO Unit := do
  let (statement, assignment, operator, rhs) ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .assignValue assignment operator rhs => some (node, assignment, operator, rhs) | _ => none
    | _ => none with
    | some result => pure result | none => throw (IO.userError "renamed assignment fault assignment missing")
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "renamed assignment fault diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "renamed assignment fault owner missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for binder in SourceCoreCompatibleDataPlaces.declaredBinders source do
    let type ← get "renamed assignment fault binder type" (checked.catalog.project binder.scheme.body)
    let expected ← match binder.scheme.body with
      | .mapping key value => do
        let encoded ← get "renamed assignment fault mapping header" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key value []))
        values := encoded.context
        pure (some encoded.value)
      | .constructor (.builtin .bool) | .constructor (.builtin .word) => pure none
      | other => throw (IO.userError s!"renamed assignment fault unsupported fixture binder: {reprStr other}")
    bindings := bindings ++ [(binder, type, OptionalCell.allocate type, expected)]
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let representation := SourceCoreCompatibleFunctions.representation values 150
  let child : SourceCoreCompatibleDataPlaces.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation checked.signatures prepared.locals
      prepared.contexts own.assignments diagnostics context prepared.callableContext none none fuel source scope id reasonAt
  let reasonAt := diagnostics.reasonAt owner
  let invalid := Word.ofNatModulo 999
  let nextId ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
    | _ => none with
    | some id => pure id | none => throw (IO.userError "renamed assignment fault return expression missing")
  let next ← get "renamed assignment fault actual continuation" (child 150 source scope nextId reasonAt)
  match accepted : SourceCoreCompatibleDataPlaces.lower values checked.signatures child 150 source scope
      (.occurrence statement.id.occurrence) assignment operator (some rhs) next.type next.expression
      reasonAt invalid invalid (fun _ => invalid) with
  | .error error => throw (IO.userError s!"actual renamed assignment fault lowering failed: {reprStr error}")
  | .ok lowered =>
    have receipt := CompatiblePlaceCompilerCertificates.generated_of_lower accepted
    let _receipt := receipt
    let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
    let frameExpr := SourceCoreCallableIndexedFrames.empty frame
    let closureType := Ty.function .unit frame.type
    let closure := Expr.lambda .unit frame.type (.var 1)
    -- The extra binding is inside the source-local slots, before slot 2.
    let insertion := Renaming.insertion 2
    let renamed := lowered.rename insertion
    let body := bindings.zipIdx.foldl (fun body ((_, _, initial, _), index) =>
      let body := if index == 2 then Expr.letE (.integer 91) body else body
      Expr.letE initial body) renamed
    let native : Core.Program := ⟨LanguageResult.resultType next.type,
      .letE frameExpr (.letE (.newCell closureType closure) body), checked.catalog.definitions ++ [frame.definition]⟩
    assertTrue native.check s!"renamed assignment fault {name} ambient checker rejected"
    let completed ← match native.runStateful 200000 with
      | .done result store => pure (result, store)
      | other => throw (IO.userError s!"renamed assignment fault {name} did not complete: {reprStr other}")
    for fuel in [0, 5, 40, 1000] do
      let result := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 200000 checkpoint
        | other => other
      assertTrue (result == .done completed.1 completed.2) s!"renamed assignment fault {name} resume changed result/store"
    assertTrue (completed.2[0]? == some (.closure .unit frame.type (.var 1) [.constructed frame.empty .unit]))
      "renamed assignment fault changed captured ambient value"
    let expectedToken ← if name == "keyFirst" || name == "rhsFault" then do
      let occurrence ← match source.nodes.findSome? fun
        | .expression node => match node.form with | .reference "missing" (.local _) => some node.id | _ => none
        | _ => none with
        | some id => pure id | none => throw (IO.userError "renamed assignment fault missing occurrence")
      pure (reasonAt occurrence)
    else do
      let root ← match bindings.find? (fun entry => entry.1.name == "root") with
        | some entry => pure entry.1.scheme.body | none => throw (IO.userError "renamed assignment fault missing root")
      let mapping ← match root with
        | .mapping _ (.mapping key value) => pure (SourceCoreRawMetadata.Metadata.mapping key value)
        | .mapping key value => pure (.mapping key value)
        | _ => throw (IO.userError "renamed assignment fault invalid root metadata")
      let header ← match values.registry.id? mapping with
        | some header => pure header | none => throw (IO.userError "renamed assignment fault missing raw header")
      pure (invalid.add header)
    assertTrue (completed.1 == .inLeft next.type (.word expectedToken))
      s!"renamed assignment fault {name} changed failure precedence/token"
    for ((binder, type, _, expected), position) in bindings.zipIdx do
      let cell ← match completed.2[bindings.length - position]? with
        | some cell => pure cell | none => throw (IO.userError "renamed assignment fault lost source cell")
      let initialized := (binder.name == "keys" && name != "keyFirst") || (binder.name == "vals" && name == "rhsFault")
      if initialized then
        let some expected := expected | throw (IO.userError "renamed assignment fault wrong initialized fixture")
        assertTrue (cell == .inRight .unit expected) s!"renamed assignment fault {name} lost earlier effects at {binder.name}"
      else
        assertTrue (cell == .inLeft type .unit) s!"renamed assignment fault {name} ran a later phase or wrote {binder.name}"

def run : IO Unit := do
  let program ← get "renamed assignment fault source checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"renamed assignment fault specialization: {reprStr other}")
  let automatic ← get "renamed assignment fault actual factory" (SourceCoreCompatibleFunctions.prepare program plan 400)
  for function in automatic.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared function.specialized.function.typedBody function.signature.key
      function.specialized.function.solvedRequirements name
  assertTrue (automatic.prepared.functions.length == 4) "renamed assignment fault fixture coverage missing"
  IO.println "renamed assignment fault: raw missing-default precedence, nested target/key/RHS effects, captures and resume GREEN"


end Faults

def run : IO Unit := do
  Completed.run
  Faults.run

end Tests.SourceCoreCompatibleRenamedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleRenamedBareBitNot
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleRenamedBareBitNot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"renamed_bare_bitnot", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [.word, .integer]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [.word, .integer]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder (type : TypeSystem.Ty) : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono type, [], false, none⟩
private def source (type : TypeSystem.Ty) : TypedSource := { owner, inputs := [binder type], roots := [], nodes := [] }
private def assignment (type : TypeSystem.Ty) : AssignmentResolution := ⟨⟨(binder type).id, [], type⟩, []⟩
private def scope (type : Core.Ty) : SourceCoreLocalCell.Scope := [((binder .word).id, type)]
private def reference (type : Core.Ty) : Value := .cellRef (OptionalCell.cellType type) 0

-- This existing closure is captured before insertion. Its body reads the same
-- physical root after the unary write, without changing its captured environment.
private def reader (type : Core.Ty) : Value :=
  .closure .unit type (.caseE (.loadCell (.var 1)) (if type = .integer then .integer 0 else .word Word.zero) (.var 0)) [reference type]
private def canonical (type : Core.Ty) : Environment := [reference type, reader type]
private def actual (type : Core.Ty) : Environment := [.bool false, .unit, reference type, reader type]
private def nativeContext (type : Core.Ty) : Core.Context := [OptionalCell.referenceType type, .function .unit type]
private def actualContext (type : Core.Ty) : Core.Context := [.bool, .unit, OptionalCell.referenceType type, .function .unit type]
private def embedding : Renaming := fun index => index + 2
private theorem agrees (type : Core.Ty) : ReadOnly.EnvironmentsAgree embedding (canonical type) (actual type) := by
  intro index value found
  change (.bool false :: .unit :: canonical type)[index + 2]? = some value
  simpa using found

private def wordContext := (SourceSemantics.Context.ofSignatures signatures).withLocal (binder .word).id (binder .word).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def sourceEnvironment : Dynamic.Environment := [((binder .word).id, ⟨0⟩)]
private def sourceHeap (initial : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨.word, initial, none⟩]⟩
private def world : StoreTyping := [OptionalCell.cellType .word]
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem localAgrees (initial : Option Dynamic.Value) :
    Dynamic.EnvironmentAgrees (sourceHeap initial) wordContext.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal wordContext (binder .word).id .word :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder .word).id (binder .word).scheme,
    .builtin .word⟩
private theorem writable : ∀ found, rootBinder (source .word) (assignment .word).target.root = .ok found →
    WritableLocal wordContext (assignment .word).target.root found.scheme.body := by
  intro found selected
  have same := Except.ok.inj (selected.symm.trans
    (show rootBinder (source .word) (assignment .word).target.root = .ok (binder .word) by cbv))
  subst found
  exact rootWritable
private theorem readerTyped : RuntimeValueHasType world (reader .word) (.function .unit .word) checked.catalog.definitions :=
  .closure (.cons (.cellRef rfl) .nil) (.caseE (.loadCell (.var rfl)) .word (.var rfl))
private theorem actualTyped : RuntimeEnvironmentHasTypes world (actual .word) (actualContext .word) checked.catalog.definitions :=
  .cons .bool (.cons .unit (.cons (.cellRef rfl) (.cons readerTyped .nil)))

private def noChildren : ExpressionLowerer := fun _ _ _ id _ => .error (.missingExpression id)
private def invalid : Word := Word.ofNatModulo 41
private def projectionFault : Word := Word.ofNatModulo 73
private def next : Expr := LanguageResult.success (.apply (.var 1) .unit)
private def compile (raw : TypeSystem.Ty) (type : Core.Ty) (tail : Expr := next) :=
  lowerChecked compilation checked.signatures noChildren 100 (source raw) (scope type) site (assignment raw) .equal none type tail
    (fun _ => Word.zero) projectionFault invalid (fun _ => Word.zero) checked.catalog.definitions (nativeContext type)

/-- Actual compiler completion reconstructs an independent source fault or
write and seven typed continuation slots in a genuinely inserted environment. -/
theorem actual_reflects {certified : Certified checked.catalog.definitions (nativeContext .word) .word}
    (accepted : compile .word .word = .ok certified)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked compilation.registry (noFunctions checked.catalog)) [] []
      ⟨.word, initial, none⟩ native .word)
    {result : Value} {after : Store}
    (completed : Evaluates (actual .word) [native] (certified.expression.rename embedding) result after) :
    ∃ prepared, CompatibleRenamedBareBitNot.Result checked compilation.registry (noFunctions checked.catalog) program wordContext [] (source .word)
      (fun _ _ => True) prepared (assignment .word).target sourceEnvironment (sourceHeap initial) [native] [0] world
      (actual .word) (actualContext .word) embedding next .word result after := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, ref⟩ := empty.allocate initialRep Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [.function .unit .word]
      (scope .word) sourceEnvironment (canonical .word) := .cons ref (.nil (.cons readerTyped .nil))
  exact CompatibleRenamedBareBitNot.reflects_of_lower writable rfl (.inl rfl) environments heaps (localAgrees initial)
    (agrees .word) actualTyped (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) True.intro completed

private theorem absentFault : Dynamic.SourcePlaceBitNotFaults program wordContext [] (source .word) sourceEnvironment
    (sourceHeap none) (assignment .word).target (.invalidUnaryOperand .bitNot) (sourceHeap none) :=
  .uninitialized (CompatibleBareBitNotMeaning.resolves rfl .head (.intro .head)
    (.uninitialized (by rintro ⟨a, b, impossible⟩; cases impossible))) rfl

theorem actual_absent {certified : Certified checked.catalog.definitions (nativeContext .word) .word}
    (accepted : compile .word .word = .ok certified) :
    Evaluates (actual .word) [.inLeft .word .unit] (certified.expression.rename embedding)
      (.inLeft .word (.word invalid)) [.inLeft .word .unit] := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, ref⟩ := empty.allocate (GenericHeap.CellRepresents.uninitialized (show checked.catalog.project .word = .ok .word by rfl))
    Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [.function .unit .word]
      (scope .word) sourceEnvironment (canonical .word) := .cons ref (.nil (.cons readerTyped .nil))
  exact (CompatibleRenamedBareBitNot.preserves_fault_of_lower writable rfl (.inl rfl) environments heaps
    (localAgrees none) (agrees .word) (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) absentFault).2.2

private def seven : Word := Word.ofNatModulo 7
private theorem sourceUpdate : Dynamic.SourcePlaceSnapshotUpdate program wordContext [] (source .word) Dynamic.BitNotSnapshot
    sourceEnvironment (sourceHeap (some (.word seven))) (assignment .word).target (.word seven.bitNot)
    (sourceHeap (some (.word seven.bitNot))) :=
  .intro (CompatibleBareBitNotMeaning.resolves rfl .head (.intro .head) .initialized)
    (.intro (.intro .head) rfl .initialized (.leaf (.word seven)) (DataPlaceCommitReflection.source_writes (.intro .head) _))

/-- The independent source update supplies the exact native prefix and a
typed actual continuation. No source or Core continuation run is a premise. -/
theorem actual_preserves_prefix {certified : Certified checked.catalog.definitions (nativeContext .word) .word}
    (accepted : compile .word .word = .ok certified) :
    ∃ prepared replacement finalStore slots,
      ValueRep checked compilation.registry (noFunctions checked.catalog) [0] world prepared.route.rootSourceType (.word seven.bitNot) replacement prepared.route.rootType ∧
      HeapRepresents checked compilation.registry (noFunctions checked.catalog) [0] world (sourceHeap (some (.word seven.bitNot))) finalStore ∧
      AdministrativePreserved [0] [.inRight .unit (.word seven)] [0] finalStore ∧
      Dynamic.HeapMetadataExtend (sourceHeap (some (.word seven))) (sourceHeap (some (.word seven.bitNot))) ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual .word) (CompatibleRenamedBareBitNot.writtenContext prepared (actualContext .word)) checked.catalog.definitions ∧
      CoreProof.ContinuationAgreement (actual .word) [.inRight .unit (.word seven)] (certified.expression.rename embedding)
        (slots ++ actual .word) finalStore (shift 7 (next.rename embedding)) := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, ref⟩ := empty.allocate (GenericHeap.CellRepresents.initialized (ValueRep.word seven)) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [.function .unit .word]
      (scope .word) sourceEnvironment (canonical .word) := .cons ref (.nil (.cons readerTyped .nil))
  exact CompatibleRenamedBareBitNot.preserves_prefix_of_lower writable rfl (.inl rfl) environments heaps
    (localAgrees (some (.word seven))) (agrees .word) actualTyped
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) sourceUpdate

private def exercise (raw : TypeSystem.Ty) (type : Core.Ty) (initial expected : Value) (succeeds : Bool) : IO Unit := do
  match compile raw type with
  | .error error => throw (IO.userError s!"renamed bare bit-not compile: {reprStr error}")
  | .ok certified =>
    let code := certified.expression.rename embedding
    let start := State.initial code (actual type) [initial]
    let wanted := if succeeds then Value.inRight .word expected else .inLeft type (.word invalid)
    let after := [if succeeds then .inRight .unit expected else initial]
    unless runStateful 2000 start == .done wanted after do throw (IO.userError "renamed bare bit-not captured continuation mismatch")
    for budget in [0, 7, 43] do
      match runStateful budget start with
      | .outOfFuel checkpoint => unless runStateful 2000 checkpoint == .done wanted after do
          throw (IO.userError "renamed bare bit-not captured resume mismatch")
      | .done value store => unless value == wanted && store == after do throw (IO.userError "renamed bare bit-not early completion mismatch")
      | .fault _ _ => throw (IO.userError "renamed bare bit-not stuck")
  -- Absence must also skip a continuation which would write the captured root.
  let effect := Expr.letE (.storeCell (.var 0) (.inRight .unit (if type = .integer then .integer 99 else .word (Word.ofNatModulo 99)))) (shift 1 next)
  match compile raw type effect with
  | .error error => throw (IO.userError s!"renamed bare bit-not effect compile: {reprStr error}")
  | .ok certified =>
    let absent := Value.inLeft type .unit
    unless runStateful 2000 (State.initial (certified.expression.rename embedding) (actual type) [absent]) ==
        .done (.inLeft type (.word invalid)) [absent] do throw (IO.userError "renamed absent operand ran captured write")

def run : IO Unit := do
  match accepted : compile .word .word with
  | .error error => throw (IO.userError s!"renamed bare bit-not Word compile: {reprStr error}")
  | .ok certified =>
    have _absent := actual_absent accepted
    have _prefix := actual_preserves_prefix accepted
    match ran : runStateful 2000 (State.initial (certified.expression.rename embedding) (actual .word) [.inRight .unit (.word seven)]) with
    | .done result after =>
      have _source := actual_reflects accepted (.initialized (.word seven)) (runStateful_evaluation_sound ran)
      unless result == .inRight .word (.word seven.bitNot) && after == [.inRight .unit (.word seven.bitNot)] do
        throw (IO.userError "renamed bare bit-not proof consumer mismatch")
    | _ => throw (IO.userError "renamed bare bit-not proof consumer incomplete")
  exercise .word .word (.inLeft .word .unit) (.word Word.zero) false
  exercise .word .word (.inRight .unit (.word seven)) (.word seven.bitNot) true
  -- Integer is an existing retained IR profile; source admission is unchanged.
  exercise .integer .integer (.inLeft .integer .unit) (.integer 0) false
  for value in [0, 7, -7, -(2^300 : Int)] do
    exercise .integer .integer (.inRight .unit (.integer value)) (.integer (~~~value)) true
  IO.println "renamed bare bit-not: independent writes/faults, Unit RHS, seven typed slots, existing closure capture and resume GREEN"

end Tests.SourceCoreCompatibleRenamedBareBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleStatementBindings
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual marked compiler receipts supply a two-binding semantic certificate.
Runtime regressions use one cached artifact for public calls and source/native
heap audits, including uninitialized failure and continuation resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCompatibleStatementBindings
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleStatementBindings CompatiblePayload GeneralHeap ReadOnly CallableIndexedHistory

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_bindings", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "bindings.solc"⟩, 0, 1⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "local", .mono .word, [], false, none⟩
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 0) none⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 1) none⟩
private def returned : StatementNode := ⟨statement 2, span, .unit, .returnStmt none⟩
private def source : TypedSource := {
  owner, inputs := [], roots := [0, 1, 2].map (fun index => .statement (statement index)),
  nodes := [.statement first, .statement second, .statement returned] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial : SourceSemantics.Context := .ofSignatures signatures
private def firstContext := initial.withLocal (binder 0).id (binder 0).scheme
private def finalContext := firstContext.withLocal (binder 1).id (binder 1).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private theorem firstExtension : BinderExtends owner initial (binder 0) firstContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, initial, SourceSemantics.Context.ofSignatures, signatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures]
private theorem secondExtension : BinderExtends owner firstContext (binder 1) finalContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, firstContext, initial, SourceSemantics.Context.ofSignatures,
          SourceSemantics.Context.withLocal, signatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, firstContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal, binder]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem syntaxTree : Syntax source finalContext initial [statement 0, statement 1, statement 2] .unit :=
  .uninitialized (node := first) (by rfl) rfl (by rfl) rfl firstExtension rfl
    (.uninitialized (node := second) (by rfl) rfl (by rfl) rfl secondExtension rfl
      (.body (.returnUnit (node := returned) [] (by rfl) rfl rfl)))
private theorem valid : CompatibleExpressionLiterals.ContextValid [] finalContext [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, finalContext, firstContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member
    simp [finalContext, firstContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [finalContext, firstContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .unit]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def reason := Word.ofNatModulo 29
private def faults : FunctionCalls.FaultRep := fun _ token => token = reason
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun _ _ _ id _ => .error (.missingExpression id)
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

/-- Any actual successful compiler output for the two marked bindings supplies
its complete static tree, including both genuine allocation ledger receipts. -/
private theorem certified {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source []
      [statement 0, statement 1, statement 2] .unit (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = CompatibleStatements.finish .unit flow reason reason ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source finalContext [] (fun _ => reason)
        initial [] [statement 0, statement 1, statement 2] .unit .unit flow := by
  apply tree_of_body rfl (fun _ _ _ => rfl) rfl ?_ syntaxTree ?_ rfl accepted
  · intro scope budget id node lowered _ _ _ _ generated
    cases generated
  · intro id declared index type selected _
    cases selected

private theorem sourceTrace : Dynamic.FunctionStatementsExecuteOutcome program initial [] source [] ⟨[]⟩
    [statement 0, statement 1, statement 2] finalContext (.returned .unit)
    ⟨[⟨.word, none, none⟩, ⟨.word, none, none⟩]⟩ :=
  .control (.cons (.letUninitialized (lookupStatement?_sound (by rfl)) rfl rfl firstExtension .append)
    (.cons (.letUninitialized (lookupStatement?_sound (by rfl)) rfl rfl secondExtension .append)
      (.singleton (lookupStatement?_sound (by rfl)) (by intro expression; simp [returned])
        (.returnUnit (lookupStatement?_sound (by rfl)) rfl))))

/-- The concrete source allocation order entails finite evaluation of whatever
code the actual marked compiler emitted, in arbitrary typed ambient storage. -/
theorem compiled_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source []
      [statement 0, statement 1, statement 2] .unit (fun _ => reason) reason reason = .ok code)
    {world administrative actualContext canonical actual store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [] world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions [] world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native)) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
        .unit .unit (.returned .unit) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld
        ⟨[⟨.word, none, none⟩, ⟨.word, none, none⟩]⟩ finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [] store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ ⟨[⟨.word, none, none⟩, ⟨.word, none, none⟩]⟩ := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact (Tree.body_preserves (values := values) (ambient := ambient) (faults := faults) functions definitions registered (.refl _) program [] valid (fun _ _ => rfl) tree
    reason reason unique environments heaps .nil agrees typed reference read sourceTrace).2

/-- Conversely a completed generated body reconstructs source execution;
no supplied source trace or semantic body hypothesis is involved. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source []
      [statement 0, statement 1, statement 2] .unit (fun _ => reason) reason reason = .ok code)
    {world administrative actualContext canonical actual store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [] world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions [] world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program initial [] source [] ⟨[]⟩
        [statement 0, statement 1, statement 2] finalContext outcome after ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
        .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_reflects (values := values) (ambient := ambient) (faults := faults) functions definitions registered (.refl _) program [] valid (fun _ _ => rfl) tree
    reason reason environments heaps .nil agrees typed reference read completed

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function ordered() { let first: Word; let second: Bool; return; }",
    "function fail() returns (Bool) { let first: Word; let second: Bool; return second; }",
    "function lazy() returns (Word) { let first: Bool; let second: mapping(Word => Word); return second[8]; }",
    "function early() returns (Bool) { let first: Word; return true; let never: Bool; }"]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "binding checker" (checkProgram rawWorkspace)
  let ordered ← SourceCompilerFeatureSupport.compileNamed checked "ordered"
  SourceCompilerFeatureSupport.require ((← ordered.run []) == .unit) "uninitialized prefix Unit result changed"
  ordered.checkCells [] [(.word, none), (.bool, none)]
  ordered.checkResume [] .unit
  let fail ← SourceCompilerFeatureSupport.compileNamed checked "fail"
  let invocation ← fail.invoke []
  match invocation.outcome with
  | .failed token _ =>
    SourceCompilerFeatureSupport.require (← invocation.diagnostic token).isSome "new local read failure lost its diagnostic"
  | _ => throw (IO.userError "new uninitialized local did not fail")
  fail.checkCells [] [(.word, none), (.bool, none)]
  let lazyEntry ← SourceCompilerFeatureSupport.compileNamed checked "lazy"
  SourceCompilerFeatureSupport.require ((← lazyEntry.run []) == .word Word.zero) "new mapping default changed"
  lazyEntry.checkCells [] [(.bool, none), (.mapping .word .word, some (.mapping .word .word []))]
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == .bool true) "early return changed"
  early.checkCells [] [(.word, none)]
  IO.println "compatible marked bindings: actual receipts, source order, ambient heap, preservation/reflection, failure and resume GREEN"
end Tests.SourceCoreCompatibleStatementBindings
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleStatementInitialized
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! The initializer reads the old scope. Independent success/fault source
traces consume actual lowering receipts; a fault does not reach the binder's
allocation. Public cached runs also test a lazy-read effect before failure. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCompatibleStatementInitialized
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleStatementInitialized CompatiblePayload GeneralHeap ReadOnly CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"initialized_binding", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "initializer.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 1⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def node : ExpressionNode := {id := expression, span, type := .bool, form := .reference "value" (.local (binder 0).id)}
private def initialized : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 1) (some expression)⟩
private def returned : StatementNode := ⟨statement 1, span, .unit, .returnStmt none⟩
private def source : TypedSource := {
  owner, inputs := [binder 0], roots := [.statement (statement 0), .statement (statement 1)],
  nodes := [.expression node, .statement initialized, .statement returned] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal (binder 0).id (binder 0).scheme
private def finalContext := initial.withLocal (binder 1).id (binder 1).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def scope : SourceCoreLocalCell.Scope := [((binder 0).id, .bool)]
private def reason := Word.ofNatModulo 31
private def faults : FunctionCalls.FaultRep := fun fault token => fault = .uninitializedLocation ⟨0⟩ ∧ token = reason
private theorem extension : BinderExtends owner initial (binder 1) finalContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal, signatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .bool }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal, binder]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem boolAdmitted : TypeAdmissible initial .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder 0).id (binder 0).scheme)
private theorem localTyped : ExpressionHasType source initial expression .bool := by
  apply ExpressionHasType.ofOrdinary (node := node) (rawType := .bool) (lookupExpression?_sound (by rfl))
    (.reference (.local .head .head (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible boolAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem localSyntax : CompatibleExpressionConstructors.Syntax source expression :=
  .fragment (.primitive (.product (.read (node := node) (by rfl) rfl)))
private theorem syntaxTree : Syntax source initial finalContext finalContext (statement 0) [statement 1] .unit :=
  .initialized (node := initialized) (initializerNode := node) (by rfl) rfl (by rfl) rfl extension (by decide)
    (by rfl) rfl localTyped localSyntax (.body (.returnUnit (node := returned) [] (by rfl) rfl rfl))
private theorem valid (context : SourceSemantics.Context) (same : context = initial ∨ context = finalContext) :
    CompatibleExpressionLiterals.ContextValid [] context [] := by
  rcases same with rfl | rfl
  all_goals
    refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
    · simp [RequirementIdsUnique, finalContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
    · intro requirement member
      simp [finalContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
    · constructor
      · intro goal evidence found; cases found
      · intro predicate member
        simp [finalContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .unit]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 10 values
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope initial := by
  intro id declared index type selected authentic
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have found : SourceCoreDataPlaces.rootBinder source (binder 0).id = .ok (binder 0) := rfl
    rw [found] at authentic; cases authentic
    exact .head
  · simp at selected
private theorem metadata {id : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  subst node
  rfl

private theorem certified {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      [statement 0, statement 1] .unit (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = CompatibleStatements.finish .unit flow reason reason ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source initial finalContext finalContext [] (fun _ => reason)
        scope (statement 0) [statement 1] .unit .unit flow := by
  apply tree_of_body rfl (fun _ _ _ => rfl) rfl ?_ syntaxTree declarations rfl accepted
  intro current reachable currentScope budget id node lowered declared childSyntax found typed generated
  have closed : current.typeVariables = [] := by rcases reachable with rfl | rfl <;> rfl
  have residual : current.residualTypeVariables = false := by rcases reachable with rfl | rfl <;> rfl
  exact CompatibleExpressionConstructors.tree_of_functions unique declared closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => metadata found)
    childSyntax found typed generated

private def sourceEnvironment : Dynamic.Environment := [((binder 0).id, ⟨0⟩)]
private def sourceHeap (value : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨.bool, value, none⟩]⟩
private theorem sourceFailure : Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment (sourceHeap none)
    [statement 0, statement 1] initial (.fault (.uninitializedLocation ⟨0⟩)) (sourceHeap none) := by
  apply Dynamic.FunctionStatementsExecuteOutcome.fault
  apply Dynamic.FunctionStatementsFault.head
  apply Dynamic.StatementFaults.letInitializer (node := initialized) (lookupStatement?_sound (by rfl)) rfl rfl
  apply Dynamic.ExpressionFaults.form (node := node) (lookupExpression?_sound (by rfl))
  exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
    rfl .head (.intro .head) rfl rfl (by rintro ⟨key, value, impossible⟩; cases impossible)

/-- Failure before the marked allocation retains the original lexical context
and source heap; its finite generated execution follows from actual compilation. -/
theorem compiled_failure_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      [statement 0, statement 1] .unit (fun _ => reason) reason reason = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world (sourceHeap none) store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        (fun _ token => token = reason) .unit .unit (.fault (.uninitializedLocation ⟨0⟩)) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld (sourceHeap none) finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend (sourceHeap none) (sourceHeap none) := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact (Tree.body_preserves (values := values) (ambient := ambient) (faults := fun _ token => token = reason)
    functions definitions registered (.refl _) program [] (valid _ (.inl rfl)) (valid _ (.inr rfl)) (fun _ _ => rfl)
    tree reason reason unique environments heaps (.cons (.intro .head) rfl (.ordinary rfl rfl) .nil)
    agrees typed reference read unmapped sourceFailure).2

/-- Actual completed code reconstructs whether execution reached the binding's
context; the conclusion does not force that context on an early failure. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      [statement 0, statement 1] .unit (fun _ => reason) reason reason = .ok code)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap initial.locals sourceEnvironment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      (resultContext = initial ∨ resultContext = finalContext) ∧
      Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment heap
        [statement 0, statement 1] resultContext outcome after ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        (fun _ token => token = reason) .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_reflects (values := values) (ambient := ambient) (faults := fun _ token => token = reason)
    functions definitions registered (.refl _) program [] (valid _ (.inl rfl)) (valid _ (.inr rfl)) (fun _ _ => rfl)
    tree reason reason environments heaps locals agrees typed reference read unmapped completed

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "function ordered() returns (Bool) { let first = true; let second: Word; return first; }",
    "function fail() returns (Bool) { let missing: Bool; let bound = missing; let never: Word; return true; }",
    "function effectFailure() returns (Bool) { let m: mapping(Word => Word); let missing: Bool; let bound = (m, missing); let never: Word; return true; }",
    "function boxed() returns (Box) { let value: Box = .Box(true); return value; }"]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "initialized checker" (checkProgram rawWorkspace)
  let ordered ← SourceCompilerFeatureSupport.compileNamed checked "ordered"
  SourceCompilerFeatureSupport.require ((← ordered.run []) == .bool true) "initialized local result changed"
  ordered.checkCells [] [(.bool, some (.bool true)), (.word, none)]
  ordered.checkResume [] (.bool true)
  let fail ← SourceCompilerFeatureSupport.compileNamed checked "fail"
  let invocation ← fail.invoke []
  match invocation.outcome with
  | .failed token _ => SourceCompilerFeatureSupport.require (← invocation.diagnostic token).isSome "initializer fault diagnostic missing"
  | _ => throw (IO.userError "absent initializer did not fail")
  fail.checkCells [] [(.bool, none)]
  let partialEntry ← SourceCompilerFeatureSupport.compileNamed checked "effectFailure"
  match (← partialEntry.invoke []).outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "partial initializer did not fail")
  partialEntry.checkCells [] [(.mapping .word .word, some (.mapping .word .word [])), (.bool, none)]
  let boxed ← SourceCompilerFeatureSupport.compileNamed checked "boxed"
  match ← boxed.run [] with
  | .constructed _ [.bool true] => pure ()
  | _ => throw (IO.userError "initialized nominal payload changed")
  IO.println "compatible initialized statement: old-context failure, initializer effects before allocation, actual receipts, reflection and resume GREEN"
end Tests.SourceCoreCompatibleStatementInitialized
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleStatementMixed
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! A mixed prefix reaches three source allocations, then fails in its fourth
initializer. Static receipts and independent semantics agree on the exact
intermediate lexical context; real cached calls exercise longer prefixes. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCompatibleStatementMixed
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleStatementMixed CompatiblePayload GeneralHeap ReadOnly CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"mixed_binding", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "mixed.solc"⟩, 0, 1⟩
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def inputNode : ExpressionNode := {id := expression 0, span, type := .bool, form := .reference "input" (.local (binder 0).id)}
private def missingNode : ExpressionNode := {id := expression 1, span, type := .bool, form := .reference "missing" (.local (binder 2).id)}
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 1) (some (expression 0))⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 2) none⟩
private def third : StatementNode := ⟨statement 2, span, .unit, .letDecl (binder 3) (some (expression 0))⟩
private def fourth : StatementNode := ⟨statement 3, span, .unit, .letDecl (binder 4) (some (expression 1))⟩
private def returned : StatementNode := ⟨statement 4, span, .unit, .returnStmt none⟩
private def statements := [statement 0, statement 1, statement 2, statement 3, statement 4]
private def source : TypedSource := {
  owner, inputs := [binder 0], roots := statements.map .statement,
  nodes := [.expression inputNode, .expression missingNode, .statement first, .statement second,
    .statement third, .statement fourth, .statement returned] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal (binder 0).id (binder 0).scheme
private def context1 := initial.withLocal (binder 1).id (binder 1).scheme
private def context2 := context1.withLocal (binder 2).id (binder 2).scheme
private def context3 := context2.withLocal (binder 3).id (binder 3).scheme
private def context4 := context3.withLocal (binder 4).id (binder 4).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def scope : SourceCoreLocalCell.Scope := [((binder 0).id, .bool)]
private def reason := Word.ofNatModulo 37
private theorem extend {context : SourceSemantics.Context} (index : Nat)
    (binders : TypeParameterBindersWellFormed context) (fresh : LocalFresh context (binder index).id) :
    BinderExtends owner context (binder index) (context.withLocal (binder index).id (binder index).scheme) := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · exact fresh
private theorem extension1 : BinderExtends owner initial (binder 1) context1 := by
  apply extend 1
  · simp [TypeParameterBindersWellFormed, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem extension2 : BinderExtends owner context1 (binder 2) context2 := by
  apply extend 2
  · simp [TypeParameterBindersWellFormed, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem extension3 : BinderExtends owner context2 (binder 3) context3 := by
  apply extend 3
  · simp [TypeParameterBindersWellFormed, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem extension4 : BinderExtends owner context3 (binder 4) context4 := by
  apply extend 4
  · simp [TypeParameterBindersWellFormed, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem localTyped {context : SourceSemantics.Context} {node : ExpressionNode} {index : Nat}
    (found : source.lookupExpression? node.id = some node)
    (form : node.form = .reference "input" (.local (binder index).id) ∨ node.form = .reference "missing" (.local (binder index).id))
    (type : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = [])
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals (binder index).id (binder index).scheme)
    (schemes : context.LocalSchemeRequirementsLookup (binder index).id []) :
    ExpressionHasType source context node.id node.type := by
  have admitted : TypeAdmissible context .bool := .bool binders
  rcases form with form | form
  all_goals
    apply ExpressionHasType.ofOrdinary (rawType := .bool) (owned := []) (lookupExpression?_sound found)
    · rw [form]
      exact .reference (.local lookup schemes (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
        .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
        (by simp) (by intro _ member; cases member) .nil))
    · exact admitted
    · exact type ▸ admitted
    · intro requirement member; cases member
    · rw [coercions, type]; exact .nil _
    · simp [requirements, coercions, coercionRequirementIds]
private theorem inputInitial : ExpressionHasType source initial (expression 0) .bool := by
  apply localTyped (node := inputNode) (index := 0) rfl (.inl rfl) rfl rfl rfl
  · exact (TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _
  · exact .head
  · exact .head
private theorem inputSecond : ExpressionHasType source context2 (expression 0) .bool := by
  apply localTyped (node := inputNode) (index := 0) rfl (.inl rfl) rfl rfl rfl
  · exact (((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _
  · exact .tail (by decide) (.tail (by decide) .head)
  · exact .tail (by decide) (.tail (by decide) .head)
private theorem missingThird : ExpressionHasType source context3 (expression 1) .bool := by
  apply localTyped (node := missingNode) (index := 2) rfl (.inr rfl) rfl rfl rfl
  · exact ((((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _).withLocal _ _
  · exact .tail (by decide) .head
  · exact .tail (by decide) .head
private theorem inputSyntax : CompatibleExpressionConstructors.Syntax source (expression 0) :=
  .fragment (.primitive (.product (.read (node := inputNode) rfl rfl)))
private theorem missingSyntax : CompatibleExpressionConstructors.Syntax source (expression 1) :=
  .fragment (.primitive (.product (.read (node := missingNode) rfl rfl)))
private theorem syntaxTree : Syntax source initial statements .unit :=
  .initialized (node := first) (initializerNode := inputNode) rfl rfl rfl rfl extension1 (by decide)
    rfl rfl inputInitial inputSyntax
    (.uninitialized (node := second) rfl rfl rfl rfl extension2 (by decide)
      (.initialized (node := third) (initializerNode := inputNode) rfl rfl rfl rfl extension3 (by decide)
        rfl rfl inputSecond inputSyntax
        (.initialized (node := fourth) (initializerNode := missingNode) rfl rfl rfl rfl extension4 (by decide)
          rfl rfl missingThird missingSyntax (.body (.returnUnit (node := returned) [] rfl rfl rfl)))))
private theorem valid : CompatibleExpressionLiterals.ContextValid [] initial [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member
    simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .unit]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 10 values
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope initial := by
  intro id declared index type selected authentic
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have found : SourceCoreDataPlaces.rootBinder source (binder 0).id = .ok (binder 0) := rfl
    rw [found] at authentic; cases authentic
    exact .head
  · simp at selected
private theorem metadata {id : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl <;> rfl

private theorem certified {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = CompatibleStatements.finish .unit flow reason reason ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason)
        initial scope statements .unit .unit flow := by
  apply tree_of_body rfl (fun _ _ _ => rfl) rfl ?_ syntaxTree rfl rfl declarations rfl accepted
  intro current closed residual currentScope budget id node lowered declared childSyntax found typed generated
  exact CompatibleExpressionConstructors.tree_of_functions unique declared closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => metadata found)
    childSyntax found typed generated

private def sourceEnvironment : Dynamic.Environment := [((binder 0).id, ⟨0⟩)]
private def environment1 : Dynamic.Environment := ((binder 1).id, ⟨1⟩) :: sourceEnvironment
private def environment2 : Dynamic.Environment := ((binder 2).id, ⟨2⟩) :: environment1
private def environment3 : Dynamic.Environment := ((binder 3).id, ⟨3⟩) :: environment2
private def sourceHeap : Dynamic.Heap := ⟨[⟨.bool, some (.bool true), none⟩]⟩
private def heap1 : Dynamic.Heap := ⟨sourceHeap.cells ++ [⟨.bool, some (.bool true), none⟩]⟩
private def heap2 : Dynamic.Heap := ⟨heap1.cells ++ [⟨.bool, none, none⟩]⟩
private def heap3 : Dynamic.Heap := ⟨heap2.cells ++ [⟨.bool, some (.bool true), none⟩]⟩
private theorem sourceFailure : Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment sourceHeap
    statements context3 (.fault (.uninitializedLocation ⟨2⟩)) heap3 := by
  apply Dynamic.FunctionStatementsExecuteOutcome.fault
  apply Dynamic.FunctionStatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := first) (lookupStatement?_sound rfl) rfl
      (.intro (node := inputNode) (lookupExpression?_sound rfl) (.local rfl .head (.intro .head) rfl rfl) .nil)
      rfl extension1 .append)
  apply Dynamic.FunctionStatementsFault.tail
    (Dynamic.StatementExecutes.letUninitialized (node := second) (lookupStatement?_sound rfl) rfl rfl extension2 .append)
  apply Dynamic.FunctionStatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := third) (lookupStatement?_sound rfl) rfl
      (.intro (node := inputNode) (environment := environment2) (before := heap2) (lookupExpression?_sound rfl)
        (.local rfl (.tail (by decide) (.tail (by decide) .head)) (.intro .head) rfl rfl) .nil)
      rfl extension3 .append)
  apply Dynamic.FunctionStatementsFault.head
  apply Dynamic.StatementFaults.letInitializer (node := fourth) (lookupStatement?_sound rfl) rfl rfl
  apply Dynamic.ExpressionFaults.form (node := missingNode) (lookupExpression?_sound rfl)
  exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
    rfl (.tail (by decide) .head) (.intro (.tail (.tail .head))) rfl rfl
      (by rintro ⟨key, value, impossible⟩; cases impossible)

private theorem failureContext_ne_full : context3 ≠ context4 := by
  intro same
  have impossible : 4 = 5 := congrArg (fun context => context.locals.length) same
  omega

/-- Three successful bindings precede the fault. Reflection recovers that
intermediate context and represented lexical environment from actual code. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) reason reason = .ok code)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap initial.locals sourceEnvironment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment heap
        statements resultContext outcome after ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        (fun _ token => token = reason) .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment resultContext after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_reflects (values := values) (ambient := ambient) (faults := fun _ token => token = reason)
    functions definitions registered (.refl _) program [] (fun _ _ => rfl)
    tree valid reason reason environments heaps locals agrees typed reference read unmapped completed

theorem compiled_failure_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) reason reason = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world sourceHeap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        (fun _ token => token = reason) .unit .unit (.fault (.uninitializedLocation ⟨2⟩)) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld heap3 finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend sourceHeap heap3 ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment context3 heap3 := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_preserves (values := values) (ambient := ambient) (faults := fun _ token => token = reason)
    functions definitions registered (.refl _) program [] (fun _ _ => rfl)
    tree valid reason reason unique environments heaps (.cons (.intro .head) rfl (.ordinary rfl rfl) .nil)
    agrees typed reference read unmapped sourceFailure

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "function mixed() returns (Bool) { let a = true; let b: Word; let c = a; let d: Bool; let e = c; return e; }",
    "function fail() returns (Bool) { let a = true; let missing: Bool; let c = a; let d = missing; let never = false; return a; }",
    "function effectFailure() returns (Bool) { let a = true; let m: mapping(Word => Word); let c = a; let missing: Bool; let d = (m, missing); let never = false; return a; }",
    "function boxed() returns (Box) { let a: Box = .Box(true); let missing: Bool; let b = a; let c = b; return c; }"]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "mixed checker" (checkProgram rawWorkspace)
  let mixed ← SourceCompilerFeatureSupport.compileNamed checked "mixed"
  SourceCompilerFeatureSupport.require ((← mixed.run []) == .bool true) "mixed local result changed"
  mixed.checkCells [] [(.bool, some (.bool true)), (.word, none), (.bool, some (.bool true)), (.bool, none), (.bool, some (.bool true))]
  mixed.checkResume [] (.bool true)
  let fail ← SourceCompilerFeatureSupport.compileNamed checked "fail"
  let invocation ← fail.invoke []
  match invocation.outcome with
  | .failed token complete =>
      SourceCompilerFeatureSupport.require (← invocation.diagnostic token).isSome "mixed initializer fault diagnostic missing"
      let suspended ← SourceCompilerFeatureSupport.get "mixed fault suspension"
        (← invocation.initial.run invocation.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := 10})
      let checkpoint ← match suspended with
        | .outOfFuel checkpoint => pure checkpoint
        | _ => throw (IO.userError "mixed fault fixture did not suspend")
      match ← checkpoint.resume 300000 1024 with
      | .failed resumed finished =>
          SourceCompilerFeatureSupport.require (resumed == token && finished.heapSize == complete.heapSize)
            "resumption changed mixed failure or allocated an unreachable binding"
      | _ => throw (IO.userError "mixed fault checkpoint changed outcome")
  | _ => throw (IO.userError "absent mixed initializer did not fail")
  fail.checkCells [] [(.bool, some (.bool true)), (.bool, none), (.bool, some (.bool true))]
  let effect ← SourceCompilerFeatureSupport.compileNamed checked "effectFailure"
  match (← effect.invoke []).outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "mixed effectful initializer did not fail")
  effect.checkCells [] [(.bool, some (.bool true)), (.mapping .word .word, some (.mapping .word .word [])),
    (.bool, some (.bool true)), (.bool, none)]
  let boxed ← SourceCompilerFeatureSupport.compileNamed checked "boxed"
  match ← boxed.run [] with
  | .constructed _ [.bool true] => pure ()
  | _ => throw (IO.userError "mixed nominal payload changed")
  IO.println "compatible mixed statements: arbitrary binding induction, intermediate context failure, raw heap order, effects and resume GREEN"
end Tests.SourceCoreCompatibleStatementMixed
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleStatements
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Static production receipts plus full finite sequence proofs. An actual fresh
frame type remains in the ambient store; a discarded local read can fail before
a return. The checked-source integration cases separately audit lazy mapping
effects and early return through the cached public Core artifact. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleStatements CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_statements", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "statements.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 9⟩, "input", .mono .bool, [], false, none⟩
private def localNode : ExpressionNode := { id := id 0, span, type := .bool, form := .reference "input" (.local binder.id) }
private def boolean : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def paired : ExpressionNode := { id := id 2, span, type := .product .bool .bool, form := .tuple [id 0, id 1] }
private def discardNode : StatementNode := ⟨statement 10, span, .unit, .expression (id 0) true⟩
private def returnNode : StatementNode := ⟨statement 11, span, .product .bool .bool, .returnStmt (some (id 2))⟩
private def unreachable : StatementNode := ⟨statement 12, span, .unit, .breakStmt⟩
private def tailNode : StatementNode := ⟨statement 13, span, .bool, .expression (id 1) false⟩
private def unitNode : StatementNode := ⟨statement 14, span, .unit, .returnStmt none⟩
private def statements := [statement 10, statement 11, statement 12]
private def source : TypedSource := {
  owner, inputs := [binder], roots := statements.map .statement,
  nodes := [.expression localNode, .expression boolean, .expression paired,
    .statement discardNode, .statement returnNode, .statement unreachable, .statement tailNode, .statement unitNode] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun fault token => (∃ location, fault = .uninitializedLocation location) ∧ token = reason
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem localTyped : ExpressionHasType source context (id 0) .bool := by
  apply ExpressionHasType.ofOrdinary (node := localNode) (rawType := .bool) (lookupExpression?_sound (by rfl))
    (.reference (.local .head .head (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible boolAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem boolTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool) (lookupExpression?_sound (by cbv))
    (.reference (.builtinBoolean false)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairTyped : ExpressionHasType source context (id 2) (.product .bool .bool) := by
  apply ExpressionHasType.ofOrdinary (node := paired) (rawType := .product .bool .bool) (lookupExpression?_sound (by cbv))
    (.tuple (.cons localTyped (.cons boolTyped (.nil _)))) (.product boolAdmitted boolAdmitted) (.product boolAdmitted boolAdmitted)
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem localSyntax : CompatibleExpressionConstructors.Syntax source (id 0) :=
  .fragment (.primitive (.product (.read (node := localNode) (by rfl) rfl)))
private theorem boolSyntax : CompatibleExpressionConstructors.Syntax source (id 1) :=
  .fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ _))))
private theorem pairSyntax : CompatibleExpressionConstructors.Syntax source (id 2) :=
  .fragment (.primitive (.product (.pair (node := paired) (by cbv) rfl
    (.read (node := localNode) (by rfl) rfl) (.literal (node := boolean) (by cbv) (.bool _ _)))))
private theorem sourceSyntax : CompatibleStatements.Syntax source context statements (.product .bool .bool) :=
  .discard (node := discardNode) (expressionNode := localNode) (by cbv) rfl rfl rfl (by rfl) localTyped localSyntax
    (.returnValue (node := returnNode) (expressionNode := paired) [statement 12] (by cbv) rfl rfl (by cbv) rfl pairTyped pairSyntax)
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def scope : SourceCoreLocalCell.Scope := [(binder.id, .bool)]
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 20 values
private def policy : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope expression reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope expression reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked }
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro localId declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst localId
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted; cases accepted
    exact .head
  · simp at selected
private theorem certify {ids : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (syntaxTree : CompatibleStatements.Syntax source context ids expected)
    (projection : checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope ids type (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = finish type flow reason reason ∧ Tree 20 values source context [] (fun _ => reason) scope ids expected type flow := by
  apply tree_of_body rfl ?_ syntaxTree projection accepted
  intro budget expression node lowered childSyntax found typed generated
  exact CompatibleExpressionConstructors.tree_of_functions unique declarations rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => (metadata found).2)
    childSyntax found typed generated
private def readCode := OptionalCell.read .bool (.var 0) reason
private def pairCode := LocalSequence.pair .bool .bool readCode (LanguageResult.success (.bool false))
private def flow := LocalSequence.discard (LocalLoop.controlType (.product .bool .bool)) readCode
  (LocalLoop.returnValue (.product .bool .bool) pairCode)
private def code := finish (.product .bool .bool) flow reason reason
private theorem localAccepted (fuel : Nat) :
    policy.lowerExpression (fuel + 1) source scope (id 0) (fun _ => reason) = .ok ⟨.bool, readCode⟩ := by
  change SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody (fuel + 1) compilation source scope (id 0) (fun _ => reason) = _
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  rfl
private theorem boolAccepted (fuel : Nat) :
    policy.lowerExpression (fuel + 1) source scope (id 1) (fun _ => reason) = .ok ⟨.bool, LanguageResult.success (.bool false)⟩ := by
  change SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody (fuel + 1) compilation source scope (id 1) (fun _ => reason) = _
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  rfl
private theorem pairAccepted (fuel : Nat) :
    policy.lowerExpression (fuel + 2) source scope (id 2) (fun _ => reason) = .ok ⟨.product .bool .bool, pairCode⟩ := by
  change SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody (fuel + 2) compilation source scope (id 2) (fun _ => reason) = _
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 2).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 2) = some paired := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 2) = .ok (paired, .product .bool .bool) := rfl
  simp only [expressionPolicy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, paired]
  rw [read]
  simp only [bind, Except.bind, paired]
  have first := localAccepted fuel
  have second := boolAccepted fuel
  simp only [policy, expressionPolicy, SourceCoreCompatibleDataExpressions.functionPolicy, pure, Except.pure] at first second
  rw [first]
  simp only [bind, Except.bind]
  rw [second]
  rfl
private theorem accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope statements
    (.product .bool .bool) (fun _ => reason) reason reason = .ok code := by
  have readDiscard : policy.readStatement source (statement 10) = .ok (discardNode, .unit) := rfl
  have readReturn : policy.readStatement source (statement 11) = .ok (returnNode, .product .bool .bool) := rfl
  simp only [SourceCoreLoops.lowerStatementsWithPolicy, statements, SourceCoreLoops.lowerFlowStatementsWithPolicy,
    readDiscard, readReturn, bind, Except.bind, pure, Except.pure, discardNode, returnNode]
  rw [localAccepted 18]
  simp only [bind, Except.bind, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have ensureUnit : SourceCoreBasic.ensureType (.occurrence (statement 10).occurrence) .unit .unit = .ok () := rfl
  have ensurePair : SourceCoreBasic.ensureType (.occurrence (statement 11).occurrence) (.product .bool .bool) (.product .bool .bool) = .ok () := rfl
  rw [ensureUnit]
  simp only [bind, Except.bind]
  rw [ensurePair]
  simp only [bind, Except.bind]
  rw [pairAccepted 16]
  simp only [bind, Except.bind, ensurePair, pure, Except.pure]
  rfl
private theorem certified : Tree 20 values source context [] (fun _ => reason) scope statements (.product .bool .bool) (.product .bool .bool) flow := by
  obtain ⟨generatedFlow, same, tree⟩ := certify sourceSyntax rfl accepted
  have flowSame : generatedFlow = flow := by
    have structural := same
    simp only [code, finish, LocalControl.finish, LocalLoop.toControl, LanguageResult.bind, Expr.caseE.injEq] at structural
    exact structural.1.1.symm
  exact flowSame ▸ tree

/-- The whole source sequence is reconstructed from completed native code.
The actual compiler receipt supplied every child tree; no source execution or
universal body/child meaning is assumed. -/
theorem compiled_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source environment before statements context outcome after ∧
      BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
        (.product .bool .bool) (.product .bool .bool) outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  Tree.body_reflects (values := values) (ambient := ambient) functions (.refl _) program [] valid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
    certified reason reason environments heaps locals agrees completed

private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := by intros; contradiction
  runtime_hasType := by intros; contradiction
  source_function := by intros; contradiction
  extend := by intros; contradiction
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private theorem initialHeap : GenericHeap.HeapRepresents model [] [administrativeType] ⟨[]⟩ [administrativeValue] :=
  GenericHeap.HeapRepresents.empty.allocate_administrative administrativeTyped
private def boolHeap (value : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨.bool, value, none⟩]⟩
private def world : StoreTyping := [administrativeType, OptionalCell.cellType .bool]
private def environment : Environment := [.cellRef (OptionalCell.cellType .bool) 1]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private theorem locals (value : Option Dynamic.Value) : Dynamic.EnvironmentAgrees (boolHeap value) context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem visible {sourceValue : Option Dynamic.Value} {native : Value}
    (cell : GenericHeap.CellRepresents model [] [administrativeType] ⟨.bool, sourceValue, none⟩ native .bool) :
    GenericHeap.HeapRepresents model [1] world (boolHeap sourceValue) [administrativeValue, native] ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] world [] scope sourceEnvironment environment ambient.definitions := by
  obtain ⟨heap, reference⟩ := initialHeap.allocate cell Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩

/-- A failure in the discarded first expression bypasses the pair and return,
keeps the source cell absent, and preserves the fresh ambient closure. -/
theorem discarded_failure_reflects : ∃ outcome after finalMap finalWorld,
    Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment (boolHeap none) statements context outcome after ∧
    BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
      (.product .bool .bool) (.product .bool .bool) outcome (.inLeft (.product .bool .bool) (.word reason)) ∧
    CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after [administrativeValue, .inLeft .bool .unit] ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inLeft .bool .unit] finalMap [administrativeValue, .inLeft .bool .unit] ∧
    Dynamic.HeapMetadataExtend (boolHeap none) after := by
  obtain ⟨heaps, environments⟩ := visible (.uninitialized (show checked.catalog.project .bool = .ok .bool by rfl))
  have child : Evaluates environment [administrativeValue, .inLeft .bool .unit] readCode
      (.inLeft .bool (.word reason)) [administrativeValue, .inLeft .bool .unit] :=
    OptionalCell.read_failure reason (.var rfl) rfl
  have completed : Evaluates environment [administrativeValue, .inLeft .bool .unit] code
      (.inLeft (.product .bool .bool) (.word reason)) [administrativeValue, .inLeft .bool .unit] :=
    LocalControl.finish_failure _ (LocalLoop.toControl_failure _ reason (LocalSequence.discard_failure _ child))
  exact compiled_reflects functions environments heaps (locals none) (ξ := Renaming.id) (fun {_ _} found => found)
    (by simpa only [Expr.rename_id] using completed)

/-- Independent source execution supplies the forward direction, including the
same local read under both the discarded-payload and pair-payload slots. -/
theorem initialized_preserves : ∃ value finalStore finalMap finalWorld,
    Evaluates environment [administrativeValue, .inRight .unit (.bool true)] code value finalStore ∧
    BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
      (.product .bool .bool) (.product .bool .bool) (.returned (.product (.bool true) (.bool false))) value ∧
    CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld (boolHeap (some (.bool true))) finalStore ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inRight .unit (.bool true)] finalMap finalStore ∧
    Dynamic.HeapMetadataExtend (boolHeap (some (.bool true))) (boolHeap (some (.bool true))) := by
  obtain ⟨heaps, environments⟩ := visible (.initialized (.bool true))
  have localEvaluation : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (boolHeap (some (.bool true))) (id 0)
      (.bool true) (boolHeap (some (.bool true))) :=
    .intro (lookupExpression?_sound (show source.lookupExpression? (id 0) = some localNode by rfl))
      (.local rfl .head (.intro .head) rfl rfl) .nil
  have booleanEvaluation : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (boolHeap (some (.bool true))) (id 1)
      (.bool false) (boolHeap (some (.bool true))) :=
    .intro (lookupExpression?_sound (show source.lookupExpression? (id 1) = some boolean by cbv)) (.builtinBoolean rfl) .nil
  have pairEvaluation : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (boolHeap (some (.bool true))) (id 2)
      (.product (.bool true) (.bool false)) (boolHeap (some (.bool true))) :=
    .intro (lookupExpression?_sound (show source.lookupExpression? (id 2) = some paired by cbv))
      (.tuple rfl (.cons localEvaluation (.cons booleanEvaluation .nil)) (.cons (.singleton _))) .nil
  have sourceTrace : Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment
      (boolHeap (some (.bool true))) statements context (.returned (.product (.bool true) (.bool false))) (boolHeap (some (.bool true))) :=
    .control (.cons (.expression (lookupStatement?_sound (show source.lookupStatement? (statement 10) = some discardNode by cbv)) rfl localEvaluation)
      (.terminal (.returnValue (lookupStatement?_sound (show source.lookupStatement? (statement 11) = some returnNode by cbv)) rfl pairEvaluation) (.returned _)))
  have result := Tree.body_preserves (values := values) (ambient := ambient) functions (.refl _) program [] valid unique
    (faults := faults) (fun _ location => ⟨⟨location, rfl⟩, rfl⟩) certified reason reason
    environments heaps (locals _) (ξ := Renaming.id) (show EnvironmentsAgree Renaming.id environment environment from fun {_ _} found => found) sourceTrace
  simpa only [Expr.rename_id, code, values, SourceCoreCompatibleValues.Context.initial] using result.2

/-- Empty and explicit Unit exits and a semicolon-free tail use the very same
production traversal certificate factory. -/
theorem unit_and_tail_certificates :
    (∃ flow, Tree 20 values source context [] (fun _ => reason) scope [] .unit .unit flow) ∧
    (∃ flow, Tree 20 values source context [] (fun _ => reason) scope [statement 14, statement 12] .unit .unit flow) ∧
    (∃ flow, Tree 20 values source context [] (fun _ => reason) scope [statement 13] .bool .bool flow) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨flow, _, tree⟩ := certify .nil rfl (show SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope [] .unit (fun _ => reason) reason reason = .ok (finish .unit (LocalLoop.fallthrough .unit) reason reason) by rfl)
    exact ⟨flow, tree⟩
  · obtain ⟨flow, _, tree⟩ := certify (.returnUnit (node := unitNode) [statement 12] (by cbv) rfl rfl) rfl
      (show SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope [statement 14, statement 12] .unit (fun _ => reason) reason reason = .ok (finish .unit (LocalLoop.returned .unit) reason reason) by rfl)
    exact ⟨flow, tree⟩
  · obtain ⟨flow, _, tree⟩ := certify (.tail (node := tailNode) (expressionNode := boolean) (by cbv) rfl rfl (by cbv) rfl boolTyped boolSyntax) rfl
      (show SourceCoreLoops.lowerStatementsWithPolicy policy 20 source scope [statement 13] .bool (fun _ => reason) reason reason = .ok (finish .bool (LocalLoop.returnValue .bool (LanguageResult.success (.bool false))) reason reason) by
        have read : policy.readStatement source (statement 13) = .ok (tailNode, .bool) := rfl
        simp only [SourceCoreLoops.lowerStatementsWithPolicy, SourceCoreLoops.lowerFlowStatementsWithPolicy,
          read, bind, Except.bind, pure, Except.pure, tailNode]
        rw [boolAccepted 18]
        rfl)
    exact ⟨flow, tree⟩

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Word) }",
    "function success() returns (Bool, Bool) { true; return (false, true); }",
    "function lazy() returns (Bool) { let m: mapping(Word => Word); m; return true; }",
    "function stopped() returns (Bool) { let missing: Bool; let m: mapping(Word => Word); missing; m; return true; }",
    "function early() returns (Bool) { let missing: Bool; return true; missing; }",
    "function tail() returns (Bool, Bool) { true; (true, false) }",
    "function boxed() returns (Box) { true; return .Box(7); }",
    "function unit() { true; return; }"]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "statement checker" (checkProgram rawWorkspace)
  let success ← SourceCompilerFeatureSupport.compileNamed checked "success"
  SourceCompilerFeatureSupport.require ((← success.run []) == .product (.bool false) (.bool true)) "discard/return pair changed"
  success.checkResume [] (.product (.bool false) (.bool true))
  let lazyEntry ← SourceCompilerFeatureSupport.compileNamed checked "lazy"
  SourceCompilerFeatureSupport.require ((← lazyEntry.run []) == .bool true) "lazy read return changed"
  lazyEntry.checkCells [] [(.mapping .word .word, some (.mapping .word .word []))]
  let stopped ← SourceCompilerFeatureSupport.compileNamed checked "stopped"
  let invocation ← stopped.invoke []
  match invocation.outcome with
  | .failed token _ =>
    let diagnostic ← invocation.diagnostic token
    SourceCompilerFeatureSupport.require (diagnostic.isSome) "discarded failure diagnostic missing"
  | _ => throw (IO.userError "discarded absent read did not stop")
  stopped.checkCells [] [(.bool, none), (.mapping .word .word, none)]
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == .bool true) "unreachable read ran"
  early.checkCells [] [(.bool, none)]
  let tail ← SourceCompilerFeatureSupport.compileNamed checked "tail"
  SourceCompilerFeatureSupport.require ((← tail.run []) == .product (.bool true) (.bool false)) "tail pair changed"
  let dataEntry ← SourceCompilerFeatureSupport.compileNamed checked "boxed"
  match ← dataEntry.run [] with
  | .constructed _ [.word value] => SourceCompilerFeatureSupport.require (value == Word.ofNatModulo 7) "returned constructor payload changed"
  | _ => throw (IO.userError "returned constructor shape changed")
  let unitEntry ← SourceCompilerFeatureSupport.compileNamed checked "unit"
  SourceCompilerFeatureSupport.require ((← unitEntry.run []) == .unit) "explicit Unit return changed"
  IO.println "compatible statements: compiler certificates, full preservation/reflection, discard fault, lazy effects, early return, tail data and resume GREEN"
end Tests.SourceCoreCompatibleStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleTypedAssignment
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Concrete expression trees close every key/RHS premise of whole assignment
preservation and completed reflection. The actual post-write temporary values
are typed before a continuation is evaluated, including comparator captures. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleTypedAssignment
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceAssignmentSuccess
theorem preserves_prefix {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (layout : Layout (definitions := ambient.definitions) compilation source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope site place prepared codes sourceTypes leaf administrativeContext)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (CompatibleTypedPlaceAssignmentSuccess.writtenContext prepared (SourceCoreCalls.packArguments codes).type
            (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions ∧
        ∀ next outputType, ContinuationAgreement coreEnvironment store
          (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
          (slots ++ coreEnvironment) finalStore (shift 7 next) := by
  have preservation : TypedGenericExpressionMeaning.Preserves
      (payloadModel compilation.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions registryExtension program evidence contextValid unique uninitialized missing
  exact CompatibleTypedPlaceAssignmentSuccess.preserves_prefix layout registryExtension preservation faithful observations
    rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals slot rootTyped trace invalidOperand


theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid) result finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after ∧
      result = .inLeft outputType (.word token) ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleTypedPlaceAssignmentSuccess.writtenContext prepared (SourceCoreCalls.packArguments codes).type
          (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions ∧
      Evaluates (slots ++ coreEnvironment) written (shift 7 next) result finalStore) := by
  have preservation : TypedGenericExpressionMeaning.Preserves
      (payloadModel compilation.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions registryExtension program evidence contextValid unique uninitialized missing
  have reflection : TypedGenericExpressionMeaning.Reflects
      (payloadModel compilation.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.reflects functions registryExtension program evidence contextValid uninitialized missing
  exact CompatibleTypedPlaceAssignmentReflection.reflects layout ordinary registryExtension reflection preservation
    functionTypes faithful observations missingTokens invalidTokens rhsGenerated found rhsView rhsCoreType
    operatorProfile environments heaps locals slot rootTyped completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function success() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[keys[true]] = vals[false] + 2; return root[false] + nextMap[true]; }",
    "function repeated() returns (Word) { let root: mapping(Bool => mapping(Bool => Word)); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[keys[true]][keys[true]] = vals[false] + 2; return root[false][false] + nextMap[true]; }",
    "function keyFault() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Bool; root[missing || keys[true]] = vals[false] + 2; return root[false] + nextMap[true]; }",
    "function rhsFault() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Word; root[keys[true]] = vals[false] + missing; return root[false] + nextMap[true]; }",
    "function skipped() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[false && keys[true]] = vals[false] + 2; return true ? root[false] : nextMap[true]; }",
    "function nextFault() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Word; root[keys[true]] = vals[false] + 2; return nextMap[true] + missing; }"
  ]}] }

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (solved : List SolvedRequirement) (name : String) : IO Unit := do
  let (statement, assignment, operator, rhs) ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .assignValue assignment operator rhs => some (node, assignment, operator, rhs) | _ => none
    | _ => none with
    | some result => pure result | none => throw (IO.userError "typed assignment assignment missing")
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "typed assignment diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "typed assignment owner missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for binder in SourceCoreCompatibleDataPlaces.declaredBinders source do
    let type ← get "typed assignment binder type" (checked.catalog.project binder.scheme.body)
    let expected ← match binder.scheme.body with
      | .mapping key value => do
        let encoded ← get "typed assignment mapping header" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key value []))
        values := encoded.context
        pure (some encoded.value)
      | .constructor (.builtin .bool) | .constructor (.builtin .word) => pure none
      | other => throw (IO.userError s!"typed assignment unsupported fixture binder: {reprStr other}")
    bindings := bindings ++ [(binder, type, OptionalCell.allocate type, expected)]
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let representation := SourceCoreCompatibleFunctions.representation values 150
  let child : SourceCoreCompatibleDataPlaces.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation checked.signatures prepared.locals
      prepared.contexts own.assignments diagnostics context prepared.callableContext none none fuel source scope id reasonAt
  let reasonAt := diagnostics.reasonAt owner
  let invalid := Word.ofNatModulo 999
  let nextId ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
    | _ => none with
    | some id => pure id | none => throw (IO.userError "typed assignment return expression missing")
  let next ← get "typed assignment actual continuation" (child 150 source scope nextId reasonAt)
  match accepted : SourceCoreCompatibleDataPlaces.lower values checked.signatures child 150 source scope
      (.occurrence statement.id.occurrence) assignment operator (some rhs) next.type next.expression
      reasonAt invalid invalid (fun _ => invalid) with
  | .error error => throw (IO.userError s!"actual typed assignment lowering failed: {reprStr error}")
  | .ok lowered =>
    have receipt := CompatiblePlaceCompilerCertificates.generated_of_lower accepted
    let _receipt := receipt
    let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
    let frameExpr := SourceCoreCallableIndexedFrames.empty frame
    let closureType := Ty.function .unit frame.type
    let closure := Expr.lambda .unit frame.type (.var 1)
    let body := bindings.foldl (fun body (_, _, initial, _) => Expr.letE initial body)
      (.letE (.integer 91) (lowered.weakenAt 0))
    let native : Core.Program := ⟨LanguageResult.resultType next.type,
      .letE frameExpr (.letE (.newCell closureType closure) body), checked.catalog.definitions ++ [frame.definition]⟩
    assertTrue native.check s!"typed assignment {name} ambient checker rejected"
    let completed ← match native.runStateful 200000 with
      | .done result store => pure (result, store)
      | other => throw (IO.userError s!"typed assignment {name} did not complete: {reprStr other}")
    for fuel in [0, 5, 40, 1000] do
      let result := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 200000 checkpoint
        | other => other
      assertTrue (result == .done completed.1 completed.2) s!"typed assignment {name} resume changed result/store"
    assertTrue (completed.2[0]? == some (.closure .unit frame.type (.var 1) [.constructed frame.empty .unit]))
      "typed assignment changed captured ambient value"
    let prefixFailed := name == "keyFault" || name == "rhsFault"
    let failed := prefixFailed || name == "nextFault"
    if failed then
      let occurrence ← match source.nodes.findSome? fun
        | .expression node => match node.form with | .reference "missing" (.local _) => some node.id | _ => none
        | _ => none with
        | some id => pure id | none => throw (IO.userError "typed assignment missing fault occurrence")
      assertTrue (completed.1 == .inLeft next.type (.word (reasonAt occurrence))) "typed assignment changed source fault token"
    else assertTrue (completed.1 == .inRight .word (.word (Word.ofNatModulo 2))) "typed assignment successful outcome changed"
    for ((binder, type, _, expected), position) in bindings.zipIdx do
      let cell ← match completed.2[bindings.length - position]? with
        | some cell => pure cell | none => throw (IO.userError "typed assignment lost a source cell")
      if binder.name == "root" then
        if prefixFailed then assertTrue (cell == .inLeft type .unit) "typed assignment wrote root after child fault"
        else
          let .inRight .unit payload := cell | throw (IO.userError "typed assignment root was not initialized")
          let decoded ← get "typed assignment root decode" (SourceCoreCompatibleValues.decode 100 values binder.scheme.body payload)
          let two := SourceCoreDataValues.Value.word (Word.ofNatModulo 2)
          let expected := if name == "repeated" then
              SourceCoreDataValues.Value.mapping .bool (.mapping .bool .word)
                [(.bool false, .mapping .bool .word [(.bool false, two)])]
            else .mapping .bool .word [(.bool false, two)]
          assertTrue (decoded == expected) "typed assignment changed key order or RHS result"
      else if let some expected := expected then
        let skipped := name == "keyFault" || (name == "skipped" && (binder.name == "keys" || binder.name == "nextMap")) || (prefixFailed && binder.name == "nextMap")
        assertTrue (cell == if skipped then .inLeft type .unit else .inRight .unit expected)
          s!"typed assignment {name} changed lazy child effects for {binder.name}"
      else assertTrue (cell == .inLeft type .unit) "typed assignment initialized faulting local"

def run : IO Unit := do
  let program ← get "typed assignment source checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"typed assignment specialization: {reprStr other}")
  let automatic ← get "typed assignment actual factory" (SourceCoreCompatibleFunctions.prepare program plan 400)
  for function in automatic.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared function.specialized.function.typedBody function.signature.key
      function.specialized.function.solvedRequirements name
  assertTrue (automatic.prepared.functions.length == 6) "typed assignment fixture coverage missing"
  IO.println "typed assignment: actual seven-slot continuations, nested index, key/RHS/next faults, lazy effects and resume GREEN"

end Tests.SourceCoreCompatibleTypedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleTypedAssignmentFaults
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! A concrete typed-expression consumer closes the full source-fault dispatcher.
Checked-source regressions distinguish target missing defaults, key faults and
RHS faults and check exact preceding effects, captured values and resumed stores. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleTypedAssignmentFaults
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have meaning : TypedGenericExpressionMeaning.Preserves
      (payloadModel compilation.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions registryExtension program evidence valid unique uninitialized missing
  exact CompatibleTypedPlaceAssignmentFaults.preserves layout ordinary registryExtension meaning faithful observations
    missingTokens invalidTokens rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals
    slot rootTyped trace next outputType invalid

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function missingDefault() returns (Word) { let root: mapping(Bool => Box<Word>); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[keys[true]] = .Box(vals[false] + 2); return nextMap[true]; }",
    "function nestedDefault() returns (Word) { let root: mapping(Bool => mapping(Bool => Box<Word>)); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); root[keys[true]][keys[true]] = .Box(vals[false] + 2); return nextMap[true]; }",
    "function keyFirst() returns (Word) { let root: mapping(Bool => Box<Word>); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Bool; root[missing || keys[true]] = .Box(vals[false] + 2); return nextMap[true]; }",
    "function rhsFault() returns (Word) { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let nextMap: mapping(Bool => Word); let missing: Word; root[keys[true]] += vals[false] + missing; return nextMap[true]; }"
  ]}] }

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (solved : List SolvedRequirement) (name : String) : IO Unit := do
  let (statement, assignment, operator, rhs) ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .assignValue assignment operator rhs => some (node, assignment, operator, rhs) | _ => none
    | _ => none with
    | some result => pure result | none => throw (IO.userError "typed assignment fault assignment missing")
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "typed assignment fault diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "typed assignment fault owner missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for binder in SourceCoreCompatibleDataPlaces.declaredBinders source do
    let type ← get "typed assignment fault binder type" (checked.catalog.project binder.scheme.body)
    let expected ← match binder.scheme.body with
      | .mapping key value => do
        let encoded ← get "typed assignment fault mapping header" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key value []))
        values := encoded.context
        pure (some encoded.value)
      | .constructor (.builtin .bool) | .constructor (.builtin .word) => pure none
      | other => throw (IO.userError s!"typed assignment fault unsupported fixture binder: {reprStr other}")
    bindings := bindings ++ [(binder, type, OptionalCell.allocate type, expected)]
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let representation := SourceCoreCompatibleFunctions.representation values 150
  let child : SourceCoreCompatibleDataPlaces.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation checked.signatures prepared.locals
      prepared.contexts own.assignments diagnostics context prepared.callableContext none none fuel source scope id reasonAt
  let reasonAt := diagnostics.reasonAt owner
  let invalid := Word.ofNatModulo 999
  let nextId ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
    | _ => none with
    | some id => pure id | none => throw (IO.userError "typed assignment fault return expression missing")
  let next ← get "typed assignment fault actual continuation" (child 150 source scope nextId reasonAt)
  match accepted : SourceCoreCompatibleDataPlaces.lower values checked.signatures child 150 source scope
      (.occurrence statement.id.occurrence) assignment operator (some rhs) next.type next.expression
      reasonAt invalid invalid (fun _ => invalid) with
  | .error error => throw (IO.userError s!"actual typed assignment fault lowering failed: {reprStr error}")
  | .ok lowered =>
    have receipt := CompatiblePlaceCompilerCertificates.generated_of_lower accepted
    let _receipt := receipt
    let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
    let frameExpr := SourceCoreCallableIndexedFrames.empty frame
    let closureType := Ty.function .unit frame.type
    let closure := Expr.lambda .unit frame.type (.var 1)
    let body := bindings.foldl (fun body (_, _, initial, _) => Expr.letE initial body)
      (.letE (.integer 91) (lowered.weakenAt 0))
    let native : Core.Program := ⟨LanguageResult.resultType next.type,
      .letE frameExpr (.letE (.newCell closureType closure) body), checked.catalog.definitions ++ [frame.definition]⟩
    assertTrue native.check s!"typed assignment fault {name} ambient checker rejected"
    let completed ← match native.runStateful 200000 with
      | .done result store => pure (result, store)
      | other => throw (IO.userError s!"typed assignment fault {name} did not complete: {reprStr other}")
    for fuel in [0, 5, 40, 1000] do
      let result := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 200000 checkpoint
        | other => other
      assertTrue (result == .done completed.1 completed.2) s!"typed assignment fault {name} resume changed result/store"
    assertTrue (completed.2[0]? == some (.closure .unit frame.type (.var 1) [.constructed frame.empty .unit]))
      "typed assignment fault changed captured ambient value"
    let expectedToken ← if name == "keyFirst" || name == "rhsFault" then do
      let occurrence ← match source.nodes.findSome? fun
        | .expression node => match node.form with | .reference "missing" (.local _) => some node.id | _ => none
        | _ => none with
        | some id => pure id | none => throw (IO.userError "typed assignment fault missing occurrence")
      pure (reasonAt occurrence)
    else do
      let root ← match bindings.find? (fun entry => entry.1.name == "root") with
        | some entry => pure entry.1.scheme.body | none => throw (IO.userError "typed assignment fault missing root")
      let mapping ← match root with
        | .mapping _ (.mapping key value) => pure (SourceCoreRawMetadata.Metadata.mapping key value)
        | .mapping key value => pure (.mapping key value)
        | _ => throw (IO.userError "typed assignment fault invalid root metadata")
      let header ← match values.registry.id? mapping with
        | some header => pure header | none => throw (IO.userError "typed assignment fault missing raw header")
      pure (invalid.add header)
    assertTrue (completed.1 == .inLeft next.type (.word expectedToken))
      s!"typed assignment fault {name} changed failure precedence/token"
    for ((binder, type, _, expected), position) in bindings.zipIdx do
      let cell ← match completed.2[bindings.length - position]? with
        | some cell => pure cell | none => throw (IO.userError "typed assignment fault lost source cell")
      let initialized := (binder.name == "keys" && name != "keyFirst") || (binder.name == "vals" && name == "rhsFault")
      if initialized then
        let some expected := expected | throw (IO.userError "typed assignment fault wrong initialized fixture")
        assertTrue (cell == .inRight .unit expected) s!"typed assignment fault {name} lost earlier effects at {binder.name}"
      else
        assertTrue (cell == .inLeft type .unit) s!"typed assignment fault {name} ran a later phase or wrote {binder.name}"

def run : IO Unit := do
  let program ← get "typed assignment fault source checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"typed assignment fault specialization: {reprStr other}")
  let automatic ← get "typed assignment fault actual factory" (SourceCoreCompatibleFunctions.prepare program plan 400)
  for function in automatic.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared function.specialized.function.typedBody function.signature.key
      function.specialized.function.solvedRequirements name
  assertTrue (automatic.prepared.functions.length == 4) "typed assignment fault fixture coverage missing"
  IO.println "typed assignment fault: raw missing-default precedence, nested target/key/RHS effects, captures and resume GREEN"

end Tests.SourceCoreCompatibleTypedAssignmentFaults
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleTypedCompositions
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! One-level heads compose concrete, typed index children. The closed
consumers have no runtime child derivation or universal child meaning premise.
The runtime cases use real contextual compilation and full ambient definitions;
actual root-to-head extraction is supplied by the recursive compiler layer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleTypedCompositions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionTypedCompositions CompatibleExpressionIndices CompatiblePayload GeneralHeap ReadOnly

variable {values : ValuesContext} {readFuel : Nat} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension valid unique uninitialized missing in
/-- Arbitrary certified index children discharge the head's preservation
obligations, including native comparator allocation under the inserted slot. -/
theorem head_preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (CompatibleExpressionIndices.Tree readFuel values source context solved reasonAt)) faults :=
  Head.preserves functions program evidence unique
    (CompatibleExpressionIndices.preserves functions extension program evidence valid unique uninitialized missing)

include extension valid uninitialized missing in
/-- Completed native heads construct their independent source result without
being given source child traces in advance. -/
theorem head_reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (CompatibleExpressionIndices.Tree readFuel values source context solved reasonAt)) faults :=
  Head.reflects functions program evidence
    (CompatibleExpressionIndices.reflects functions extension program evidence valid uninitialized missing)

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function strict() returns (Word) { let m: mapping(Bool => Word); let n: mapping(Bool => Word); return m[true] + n[false]; }",
    "function left_fault() returns (Word) { let missing: Word; let other: mapping(Bool => Word); return missing + other[true]; }",
    "function right_fault() returns (Word) { let m: mapping(Bool => Word); let missing: Word; return m[true] + missing; }",
    "function and_skip() returns (Bool) { let other: mapping(Bool => Bool); return false && other[true]; }",
    "function or_skip() returns (Bool) { let other: mapping(Bool => Bool); return true || other[true]; }",
    "function and_evaluate() returns (Bool) { let m: mapping(Bool => Bool); return true && m[true]; }",
    "function or_evaluate() returns (Bool) { let m: mapping(Bool => Bool); return false || m[true]; }",
    "function true_branch() returns (Bool) { let m: mapping(Bool => Bool); let other: mapping(Bool => Bool); return true ? m[true] : other[true]; }",
    "function unary() returns (Bool) { let m: mapping(Bool => Bool); return !m[true]; }",
    "function conditional() returns (Bool) { let m: mapping(Bool => Bool); let other: mapping(Bool => Bool); let n: mapping(Bool => Bool); return m[true] ? other[true] : n[false]; }",
    "function branch_fault() returns (Bool) { let m: mapping(Bool => Bool); let other: mapping(Bool => Bool); let missing: Bool; return m[true] ? other[true] : missing; }",
    "function condition_fault() returns (Bool) { let missing: Bool; let other: mapping(Bool => Bool); return missing ? other[true] : other[false]; }",
    "function pair() returns ((Bool, Bool)) { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); return (m[true], n[false]); }",
    "function grouped() returns (Bool) { let m: mapping(Bool => Bool); return (m[true]); }"
  ]}] }
private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | budget + 1, source, id => match source.lookupExpression? id with
    | none => []
    | some node => node :: (match node.form with
      | .index base key => reached budget source base ++ reached budget source key
      | .group inner | .unary _ inner => reached budget source inner
      | .binary left _ right => reached budget source left ++ reached budget source right
      | .conditional condition first second => reached budget source condition ++ reached budget source first ++ reached budget source second
      | .tuple ids => ids.flatMap (reached budget source)
      | _ => [])

def run : IO Unit := do
  let program ← get "typed head checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"typed head specialization: {reprStr other}")
  let prepared ← get "typed head real compiler" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let checked := prepared.checked
  let mut count := 0
  for function in prepared.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    let source := function.specialized.function.typedBody
    let returnId : ExpressionId ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
      | _ => none with
      | some id => pure id | none => throw (IO.userError "typed head return missing")
    let nodes := reached 30 source returnId
    let binderIds := (nodes.filterMap fun node => match node.form with | .reference _ (.local id) => some id | _ => none).eraseDups
    let mut values := SourceCoreCompatibleValues.Context.initial checked
    let mut bindings : List (TypedBinder × Ty × Option Value) := []
    for id in binderIds do
      let binder ← get "typed head binder" (SourceCoreDataPlaces.rootBinder source id)
      let native ← get "typed head binder projection" (checked.catalog.project binder.scheme.body)
      let expected ← match binder.scheme.body with
        | .mapping key result => do
          let encoded ← get "typed head expected mapping" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key result []))
          values := encoded.context
          pure (some encoded.value)
        | _ => pure none
      bindings := bindings ++ [(binder, native, expected)]
    let diagnostics ← match prepared.prepared.diagnostics with
      | some diagnostics => pure diagnostics.program | none => throw (IO.userError "typed head diagnostics missing")
    let owner := function.signature.key
    let own ← match diagnostics.base.find? owner with
      | some own => pure own | none => throw (IO.userError "typed head owner missing")
    let compilation : SourceCoreFunctions.Context := {
      plan := prepared.prepared.plan, owner, globals := prepared.prepared.globals, administrativePrefix := 1,
      solvedRequirements := function.specialized.function.solvedRequirements, internalReason := Word.zero }
    let scope := bindings.map fun (binder, type, _) => (binder.id, type)
    let representation := SourceCoreCompatibleFunctions.representation values 150
    let lowered ← get "typed head actual contextual compiler" (
      SourceCoreGeneralFunctions.lowerContextualExpression program representation checked.signatures prepared.prepared.locals
        prepared.prepared.contexts own.assignments diagnostics compilation prepared.prepared.callableContext none none 150 source scope returnId (diagnostics.reasonAt owner))
    let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
    let adminType := Ty.function .unit frame.type
    let adminExpr := Expr.lambda .unit frame.type (SourceCoreCallableIndexedFrames.empty frame)
    let body := bindings.foldl (fun body (_, type, _) => Expr.letE (OptionalCell.allocate type) body)
      (.letE (.integer 99) (lowered.expression.weakenAt 0))
    let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
      .letE (.newCell adminType adminExpr) body, checked.catalog.definitions ++ [frame.definition]⟩
    assertTrue native.check s!"typed head {name} failed Core checker"
    for fuel in [0, 5, 50, 1000] do
      let completed := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
        | other => other
      match completed with
      | .done result store =>
        assertTrue (store[0]? == some (.closure .unit frame.type (SourceCoreCallableIndexedFrames.empty frame) []))
          "typed head changed administrative closure"
        let shouldAllocate := !(name == "left_fault" || name == "and_skip" || name == "or_skip" || name == "condition_fault")
        assertTrue ((store.length > bindings.length + 1) == shouldAllocate) "typed head evaluated a skipped helper or lost a reached helper"
        if name.endsWith "fault" then
          let missing ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
            | some node => pure node | none => throw (IO.userError "typed head failure node missing")
          assertTrue (result == .inLeft lowered.type (.word (diagnostics.reasonAt owner missing.id))) "typed head changed first fault"
        else
          let expected : Value := if name == "strict" then .word Word.zero
            else if name == "pair" then .pair (.bool false) (.bool false)
            else .bool (name == "unary" || name == "or_skip")
          assertTrue (result == .inRight .word expected) "typed head returned the wrong primitive/selected branch result"
        for ((binder, type, expected), position) in bindings.zipIdx do
          let expectedCell := if binder.name == "other" || binder.name == "missing" then Value.inLeft type .unit
            else match expected with | some value => .inRight .unit value | none => .inLeft type .unit
          assertTrue (store[bindings.length - position]? == some expectedCell) "typed head lost prefix or evaluated skipped tail"
      | other => throw (IO.userError s!"typed head {name} failed: {reprStr other}")
    count := count + 1
  assertTrue (count == 14) "typed head cases missing"
  IO.println "typed heads: real contextual index operands, group/pair, strict and short-circuit operators, lazy conditional branches, typed temporary slots, first faults and resume GREEN"

end Tests.SourceCoreCompatibleTypedCompositions
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleTypedExpressions
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual production contextual receipts close every semantic child obligation
in the typed recursive grammar. Runtime cases combine index, constructor,
member, proxy, primitive, conditional and product syntax under captured hidden slots. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleTypedExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionTyped CompatiblePayload GeneralHeap ReadOnly

variable {values : ValuesContext} {readFuel : Nat} {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {compilation : SourceCoreFunctions.Context} {native : Option SourceCoreGeneralFunctions.CallableContext}
  {parent : Option SourceCoreLocalEvidence.Prepared} {skip : Option ExpressionId}
  {fuel : Nat} {reasonAt : ExpressionId → Word}
  (ordinary : Ordinary source locals compilation.owner) (unique : NodeOccurrencesUnique source)
  (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
  (signatures : sourceContext.signatures = values.checked.signatures)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)

/-- The complete static receipt is extracted from real contextual compilation.
No child lowering result or child execution is supplied by the caller. -/
def Accepted : GenericExpressionMeaning.Certificate := fun scope id code => ∃ node,
  CompatibleExpressionReads.ScopeDeclarations source scope sourceContext ∧
  Syntax source id ∧ source.lookupExpression? id = some node ∧
  ExpressionHasType source sourceContext id node.type ∧
  SourceCoreGeneralFunctions.lowerContextualExpression program representation values.checked.signatures locals parents
    assignments diagnostics compilation native parent skip fuel source scope id reasonAt = .ok code

include ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy in
theorem actual_tree {scope id code}
    (accepted : Accepted (sourceContext := sourceContext) (values := values)
      (source := source) (program := program) (representation := representation) (locals := locals) (parents := parents)
      (assignments := assignments) (diagnostics := diagnostics) (compilation := compilation) (native := native)
      (parent := parent) (skip := skip) (fuel := fuel) (reasonAt := reasonAt) scope id code) :
    Tree readFuel values source sourceContext compilation.solvedRequirements reasonAt scope id code := by
  obtain ⟨node, declarations, syntaxTree, found, typed, generated⟩ := accepted
  exact tree_of_contextual ordinary unique closed residual declarations signatures syntaxTree found typed
    readPolicy lowerPolicy leafPolicy generated

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (semantics : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements sourceContext evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy extension valid uninitialized missing in
theorem accepted_preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      semantics sourceContext evidence source
      (Accepted (sourceContext := sourceContext) (values := values)
        (source := source) (program := program) (representation := representation) (locals := locals) (parents := parents)
        (assignments := assignments) (diagnostics := diagnostics) (compilation := compilation) (native := native)
        (parent := parent) (skip := skip) (fuel := fuel) (reasonAt := reasonAt)) faults := by
  intro scope id code accepted node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps lexical agrees actualTyped trace
  have tree := actual_tree ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy accepted
  exact preserves functions extension semantics evidence valid unique uninitialized missing tree
    found environments heaps lexical agrees actualTyped trace

include ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy extension valid uninitialized missing in
theorem accepted_reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      semantics sourceContext evidence source
      (Accepted (sourceContext := sourceContext) (values := values)
        (source := source) (program := program) (representation := representation) (locals := locals) (parents := parents)
        (assignments := assignments) (diagnostics := diagnostics) (compilation := compilation) (native := native)
        (parent := parent) (skip := skip) (fuel := fuel) (reasonAt := reasonAt)) faults := by
  intro scope id code accepted node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps lexical agrees actualTyped completed
  have tree := actual_tree ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy accepted
  exact reflects functions extension semantics evidence valid uninitialized missing tree
    found environments heaps lexical agrees actualTyped completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function build_box() returns (Box<Bool>) { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); return .Box(!m[true] || n[false]); }",
    "function conditional() returns (Box<Bool>) { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); return m[true] ? .Box(n[true]) : .Box(!m[false]); }",
    "function paired() returns ((Box<Bool>, Bool)) { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); let box: Box<Bool> = .Box(!m[true]); return (box, n[m[false]]); }",
    "function member_base() returns (Box<mapping(Bool => Bool)>) { let m: mapping(Bool => Bool); return .Box(m); }",
    "function child_fault() returns (Box<Bool>) { let m: mapping(Bool => Bool); let missing: Bool; let n: mapping(Bool => Bool); return .Box(m[true] || missing || n[true]); }",
    "function skipped() returns (Box<Bool>) { let m: mapping(Bool => Bool); return .Box(false && m[true]); }",
    "function proxy_box() returns (Box<@Word>) { return .Box(@Word); }",
    "function proxy_choice(flag: Bool) returns (@Word) { return flag ? @Word : @Word; }",
    "function proxy_pair() returns ((@Word, @Bool)) { return (@Word, @Bool); }",
    "function proxy_nested() returns ((Box<@Word>, @Bool)) { let boxed: Box<@Word> = .Box(@Word); return (boxed, @Bool); }",
    "function proxy_parent() returns (Box<@Word>) { let make = lam(value) -> Box<@Word> { return .Box(@Word); }; return make(true); }",
    "function parent(seed: Bool) returns (Box<Bool>) { let f = lam(item) -> Box<Bool> { let m: mapping(Bool => Bool); return .Box(m[seed] ? m[false] : !m[true]); }; return f(true); }"]}] }
private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | budget + 1, source, id => match source.lookupExpression? id with
    | none => []
    | some node => node :: (match node.form with
      | .index base key => reached budget source base ++ reached budget source key
      | .group inner | .unary _ inner | .member inner _ _ => reached budget source inner
      | .binary left _ right => reached budget source left ++ reached budget source right
      | .conditional condition first second => reached budget source condition ++ reached budget source first ++ reached budget source second
      | .tuple ids | .constructor _ ids => ids.flatMap (reached budget source)
      | _ => [])

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (original : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let originalNode ← match original.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "typed recursive original expression missing")
  let original ← if name == "paired" || name == "proxy_nested" then do
      let constructor ← match original.nodes.findSome? fun
        | .expression node => match node.form with | .constructor _ _ => some node.id | _ => none
        | _ => none with
        | some id => pure id | none => throw (IO.userError "typed recursive paired constructor missing")
      let .tuple [_, right] := originalNode.form | throw (IO.userError "typed recursive pair shape changed")
      -- The checked initializer is used as the tuple child in retained typed IR.
      pure { original with nodes := original.nodes.map fun
        | .expression node => if node.id == expression then .expression {node with form := .tuple [constructor, right]} else .expression node
        | other => other }
    else pure original
  let (source, expression) := if name == "member_base" then
      let nextId := fun index => (⟨⟨original.owner, 100000 + index⟩⟩ : ExpressionId)
      let selected : ExpressionNode := { id := nextId 0, span := originalNode.span, type := .mapping .bool .bool, form := .member expression "0" 0 }
      let key : ExpressionNode := { id := nextId 1, span := originalNode.span, type := .bool, form := .reference "true" (.builtinBoolean true) }
      let indexed : ExpressionNode := { id := nextId 2, span := originalNode.span, type := .bool, form := .index selected.id key.id }
      ({ original with roots := [.expression indexed.id], nodes := original.nodes ++
        [.expression selected, .expression key, .expression indexed] }, indexed.id)
    else if name == "proxy_raw" then
      -- Retained typed IR changes only raw proxy metadata; the native identity
      -- is deliberately shared with canonical @Word. This is not new source admission.
      let raw := TypeSystem.Ty.comptime .word
      ({ original with nodes := original.nodes.map fun
        | .expression node => match node.form with
          | .proxy .word => .expression {node with type := .proxy raw, form := .proxy raw}
          | .tuple _ => if node.id == expression then
              .expression {node with type := .product (.proxy raw) (.proxy .bool)} else .expression node
          | _ => .expression node
        | other => other }, expression)
    else (original, expression)
  let nodes := reached 100 source expression
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  if name == "proxy_raw" then
    let raw := TypeSystem.Ty.comptime .word
    let encoded ← get "typed raw proxy registry" (SourceCoreCompatibleValues.encode 100 values (.proxy raw) (.proxy raw))
    values := encoded.context
    assertTrue ((checked.catalog.project (.proxy raw)).toOption == (checked.catalog.project (.proxy .word)).toOption)
      "raw proxy fixture no longer shares native type"
    assertTrue (values.registry.id? (.proxy raw) != values.registry.id? (.proxy .word))
      "raw proxy inner metadata collapsed to canonical header"
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for id in ids do
    let binder ← get "typed recursive binder" (SourceCoreDataPlaces.rootBinder source id)
    let native ← get "typed recursive binder projection" (checked.catalog.project binder.scheme.body)
    let (initializer, expected) ← match binder.scheme.body with
      | .mapping key result => do
        let encoded ← get "typed recursive expected mapping" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key result []))
        values := encoded.context
        pure (OptionalCell.allocate native, some encoded.value)
      | .bool => pure (if binder.name == "missing" then (OptionalCell.allocate native, none)
          else (OptionalCell.allocateInitialized native (.bool true), some (.bool true)))
      | other => throw (IO.userError s!"typed recursive unexpected binder {reprStr other}")
    bindings := bindings ++ [(binder, native, initializer, expected)]
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "typed recursive diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "typed recursive owner diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let representation := SourceCoreCompatibleFunctions.representation values 150
  let lowered ← get "typed recursive actual contextual compiler" (
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation checked.signatures prepared.locals
      prepared.contexts own.assignments diagnostics compilation prepared.callableContext parent none 150 source scope expression (diagnostics.reasonAt owner))
  let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
  let adminType := Ty.function .unit frame.type
  let adminExpr := Expr.lambda .unit frame.type (SourceCoreCallableIndexedFrames.empty frame)
  let body := bindings.foldl (fun body (_, _, initializer, _) => Expr.letE initializer body)
    (.letE (.integer 99) (lowered.expression.weakenAt 0))
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
    .letE (.newCell adminType adminExpr) body, checked.catalog.definitions ++ [frame.definition]⟩
  assertTrue native.check s!"typed recursive {name} failed Core checker"
  for fuel in [0, 5, 50, 1000] do
    let completed := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
      | other => other
    match completed with
    | .done result store =>
      assertTrue (store[0]? == some (.closure .unit frame.type (SourceCoreCallableIndexedFrames.empty frame) []))
        "typed recursive comparator changed ambient closure"
      if name == "child_fault" then
        let failed ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "typed recursive first fault absent")
        assertTrue (result == .inLeft lowered.type (.word (diagnostics.reasonAt owner failed.id))) "typed recursive fault changed"
      else
        let payload ← match result with
          | .inRight .word value => pure value
          | other => throw (IO.userError s!"typed recursive failed: {reprStr other}")
        let node ← match source.lookupExpression? expression with
          | some node => pure node | none => throw (IO.userError "typed recursive root metadata missing")
        let decoded ← get "typed recursive decode" (SourceCoreCompatibleValues.decode 150 values node.type payload)
        match name, decoded with
        | "build_box", .constructed _ [.bool true] | "conditional", .constructed _ [.bool true]
        | "parent", .constructed _ [.bool true] | "skipped", .constructed _ [.bool false]
        | "member_base", .bool false | "paired", .product (.constructed _ [.bool true]) (.bool false)
        | "proxy_box", .constructed _ [.proxy .word] | "proxy_parent", .constructed _ [.proxy .word]
        | "proxy_choice", .proxy .word | "proxy_pair", .product (.proxy .word) (.proxy .bool)
        | "proxy_raw", .product (.proxy (.comptime .word)) (.proxy .bool)
        | "proxy_nested", .product (.constructed _ [.proxy .word]) (.proxy .bool) => pure ()
        | _, other => throw (IO.userError s!"typed recursive {name} unexpected result: {reprStr other}")
      for ((binder, type, _, expected), position) in bindings.zipIdx do
        if let some expected := expected then
          let skipped := name == "skipped" || (name == "build_box" && binder.name == "n") ||
            (name == "conditional" && binder.name == "n") || (name == "child_fault" && binder.name == "n")
          let expectedCell := if skipped then Value.inLeft type .unit else Value.inRight .unit expected
          assertTrue (store[bindings.length - position]? == some expectedCell)
            s!"typed recursive {name} changed lazy initialization/skip at {binder.name}"
    | other => throw (IO.userError s!"typed recursive {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let program ← get "typed recursive checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"typed recursive specialization: {reprStr other}")
  let prepared ← get "typed recursive actual factory" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let mut count := 0
  for function in prepared.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" && name != "proxy_parent" then
      let source := function.specialized.function.typedBody
      let returnId ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some id => pure id | none => throw (IO.userError "typed recursive return missing")
      inspect prepared.prepared source function.signature.key none function.specialized.function.solvedRequirements name returnId
      if name == "proxy_pair" then
        inspect prepared.prepared source function.signature.key none function.specialized.function.solvedRequirements "proxy_raw" returnId
      count := count + 1
  let mut parentsSeen := 0
  let mut proxyParentsSeen := 0
  for parent in prepared.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .constructor _ _ =>
            let name := (program.signatures.functions.find? (·.id == parent.caller.key.declaration)).map (·.name) |>.getD ""
            let fixture := if name == "proxy_parent" then "proxy_parent" else "parent"
            inspect prepared.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements fixture node.id
            if fixture == "proxy_parent" then proxyParentsSeen := proxyParentsSeen + 1
            else parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (count == 10) s!"typed recursive cases missing: {count}"
  assertTrue (parentsSeen > 0) "typed recursive specialized parent case missing"
  assertTrue (proxyParentsSeen > 0) "typed recursive specialized proxy parent missing"
  IO.println "typed recursive expressions: proxy raw headers, nested proxies, constructor/control/index/key/member/product, typed captures, lazy effects, skipped/failing child, parent and resume GREEN"

end Tests.SourceCoreCompatibleTypedExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleTypedPlaceExpressions
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Concrete typed expression trees close all key and RHS child meanings.
Runtime cases use actual contextual child compilation and actual place lowering,
including comparator allocation under a nominal captured administrative value. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleTypedPlaceExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces GeneralHeap DataPatternValues

section Concrete
variable {compilationValues : SourceCoreCompatibleValues.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions compilationValues.checked.catalog.definitions}
  (functions : FunctionModel compilationValues.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends compilationValues.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension valid unique uninitialized missing in
theorem keys_preserves {scope : Scope}
    {site : SourceCoreElaboration.ErrorSite} {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath compilationValues.checked source site root projections 0 steps keySites leaf}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (views : KeyViews path types)
    (tree : DataExpressionSequence.Tree source (CompatibleExpressionTyped.Tree fuel compilationValues source context solved reasonAt) scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {resolved : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilationValues.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilationValues.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections resolved after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues values)) finalStore ∧
      Arguments compilationValues.checked registry functions finalMap finalWorld source site values path resolved ∧
      HeapRepresents compilationValues.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have meaning : TypedGenericExpressionMeaning.Preserves
      (payloadModel compilationValues.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilationValues source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing
  exact CompatibleTypedPlaceKeys.preserves views tree meaning environments heaps locals layout actualTyped trace

include extension valid uninitialized missing in
/-- Every completed packed-key computation reconstructs either the ordered
source key trace and authenticated path arguments, or its exact source fault. -/
theorem keys_reflects {scope : Scope}
    {site : SourceCoreElaboration.ErrorSite} {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath compilationValues.checked source site root projections 0 steps keySites leaf}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (views : KeyViews path types)
    (tree : DataExpressionSequence.Tree source (CompatibleExpressionTyped.Tree fuel compilationValues source context solved reasonAt) scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store after : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilationValues.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilationValues.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (completed : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value after) :
    ∃ sourceAfter finalMap finalWorld,
      ((∃ values resolved,
        Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections resolved sourceAfter ∧
        Arguments compilationValues.checked registry functions finalMap finalWorld source site values path resolved ∧
        value = .inRight .word (DataPatternValues.packValues values)) ∨
       (∃ reason token,
        Dynamic.SourceProjectionsFault program context evidence source environment before projections reason sourceAfter ∧
        faults reason token ∧ value = .inLeft (SourceCoreCalls.packArguments codes).type (.word token))) ∧
      HeapRepresents compilationValues.checked registry functions finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap after ∧ Dynamic.HeapMetadataExtend before sourceAfter := by
  have meaning : TypedGenericExpressionMeaning.Reflects
      (payloadModel compilationValues.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree fuel compilationValues source context solved reasonAt) faults :=
    CompatibleExpressionTyped.reflects functions extension program evidence valid uninitialized missing
  exact CompatibleTypedPlaceKeys.reflects views tree meaning environments heaps locals layout actualTyped completed

open CompatiblePlaceRhs DataPlaceExecution
variable {scope : Scope} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}
  (resolution : CompatiblePlaceResolution.Execution compilationValues.checked registry functions prepared codes sourceTypes place leaf sourceTarget
    coreEnvironment initialStore initialMap initialWorld before targetHeap)
variable {administrativeContext : Core.Context} {environment : Dynamic.Environment}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

include extension valid unique uninitialized missing in
/-- Every source RHS outcome executes under the actual saved snapshot slots.
The returned live-root receipt is derived from the IH's new heap. -/
theorem rhs_preserves
    (generated : CompatibleExpressionTyped.Tree fuel compilationValues source context solved reasonAt scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilationValues.checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world := by
  exact CompatibleTypedPlaceRhs.preserves resolution
    (CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing)
    generated found environments locals trace

include extension valid uninitialized missing in
/-- Completed RHS code reconstructs the independent source outcome and the
post-RHS live root, without supplying a source execution or child evaluation IH
at one preselected runtime environment. -/
theorem rhs_reflects
    (generated : CompatibleExpressionTyped.Tree fuel compilationValues source context solved reasonAt scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilationValues.checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {value : Value} {store : Store}
    (evaluated : Evaluates
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 lowered.expression) value store) :
    ∃ outcome after mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world := by
  exact CompatibleTypedPlaceRhs.reflects resolution
    (CompatibleExpressionTyped.reflects functions extension program evidence valid uninitialized missing)
    generated found environments locals evaluated

end Concrete

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function success() { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); root[keys[true]] = vals[false] + 2; }",
    "function repeated() { let root: mapping(Bool => mapping(Bool => Word)); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); root[keys[true]][keys[true]] = vals[false] + 2; }",
    "function keyFault() { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let missing: Bool; root[missing || keys[true]] = vals[false] + 2; }",
    "function rhsFault() { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); let missing: Word; root[keys[true]] = vals[false] + missing; }",
    "function skipped() { let root: mapping(Bool => Word); let keys: mapping(Bool => Bool); let vals: mapping(Bool => Word); root[false && keys[true]] = vals[false] + 2; }"
  ]}] }

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (solved : List SolvedRequirement) (name : String) : IO Unit := do
  let (statement, assignment, operator, rhs) ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .assignValue assignment operator rhs => some (node, assignment, operator, rhs) | _ => none
    | _ => none with
    | some result => pure result | none => throw (IO.userError "typed place assignment missing")
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "typed place diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "typed place owner missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for binder in SourceCoreCompatibleDataPlaces.declaredBinders source do
    let type ← get "typed place binder type" (checked.catalog.project binder.scheme.body)
    let expected ← match binder.scheme.body with
      | .mapping key value => do
        let encoded ← get "typed place mapping header" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key value []))
        values := encoded.context
        pure (some encoded.value)
      | .constructor (.builtin .bool) | .constructor (.builtin .word) => pure none
      | other => throw (IO.userError s!"typed place unsupported fixture binder: {reprStr other}")
    bindings := bindings ++ [(binder, type, OptionalCell.allocate type, expected)]
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let representation := SourceCoreCompatibleFunctions.representation values 150
  let child : SourceCoreCompatibleDataPlaces.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation checked.signatures prepared.locals
      prepared.contexts own.assignments diagnostics context prepared.callableContext none none fuel source scope id reasonAt
  let reasonAt := diagnostics.reasonAt owner
  let invalid := Word.ofNatModulo 999
  match accepted : SourceCoreCompatibleDataPlaces.lower values checked.signatures child 150 source scope
      (.occurrence statement.id.occurrence) assignment operator (some rhs) .unit (LanguageResult.success .unit)
      reasonAt invalid invalid (fun _ => invalid) with
  | .error error => throw (IO.userError s!"actual typed place lowering failed: {reprStr error}")
  | .ok lowered =>
    have receipt := CompatiblePlaceCompilerCertificates.generated_of_lower accepted
    let _receipt := receipt
    let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
    let frameExpr := SourceCoreCallableIndexedFrames.empty frame
    let closureType := Ty.function .unit frame.type
    let closure := Expr.lambda .unit frame.type (.var 1)
    let body := bindings.foldl (fun body (_, _, initial, _) => Expr.letE initial body)
      (.letE (.integer 91) (lowered.weakenAt 0))
    let native : Core.Program := ⟨LanguageResult.resultType .unit,
      .letE frameExpr (.letE (.newCell closureType closure) body), checked.catalog.definitions ++ [frame.definition]⟩
    assertTrue native.check s!"typed place {name} ambient checker rejected"
    let completed ← match native.runStateful 200000 with
      | .done result store => pure (result, store)
      | other => throw (IO.userError s!"typed place {name} did not complete: {reprStr other}")
    for fuel in [0, 5, 40, 1000] do
      let result := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 200000 checkpoint
        | other => other
      assertTrue (result == .done completed.1 completed.2) s!"typed place {name} resume changed result/store"
    assertTrue (completed.2[0]? == some (.closure .unit frame.type (.var 1) [.constructed frame.empty .unit]))
      "typed place changed captured ambient value"
    let failed := name == "keyFault" || name == "rhsFault"
    if failed then
      let occurrence ← match source.nodes.findSome? fun
        | .expression node => match node.form with | .reference "missing" (.local _) => some node.id | _ => none
        | _ => none with
        | some id => pure id | none => throw (IO.userError "typed place missing fault occurrence")
      assertTrue (completed.1 == .inLeft .unit (.word (reasonAt occurrence))) "typed place changed source fault token"
    else assertTrue (completed.1 == .inRight .word .unit) "typed place successful outcome changed"
    for ((binder, type, _, expected), position) in bindings.zipIdx do
      let cell ← match completed.2[bindings.length - position]? with
        | some cell => pure cell | none => throw (IO.userError "typed place lost a source cell")
      if binder.name == "root" then
        if failed then assertTrue (cell == .inLeft type .unit) "typed place wrote root after child fault"
        else
          let .inRight .unit payload := cell | throw (IO.userError "typed place root was not initialized")
          let decoded ← get "typed place root decode" (SourceCoreCompatibleValues.decode 100 values binder.scheme.body payload)
          let two := SourceCoreDataValues.Value.word (Word.ofNatModulo 2)
          let expected := if name == "repeated" then
              SourceCoreDataValues.Value.mapping .bool (.mapping .bool .word)
                [(.bool false, .mapping .bool .word [(.bool false, two)])]
            else .mapping .bool .word [(.bool false, two)]
          assertTrue (decoded == expected) "typed place changed key order or RHS result"
      else if let some expected := expected then
        let skipped := name == "keyFault" || (name == "skipped" && binder.name == "keys")
        assertTrue (cell == if skipped then .inLeft type .unit else .inRight .unit expected)
          s!"typed place {name} changed lazy child effects for {binder.name}"
      else assertTrue (cell == .inLeft type .unit) "typed place initialized faulting local"

def run : IO Unit := do
  let program ← get "typed place source checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"typed place specialization: {reprStr other}")
  let automatic ← get "typed place actual factory" (SourceCoreCompatibleFunctions.prepare program plan 400)
  for function in automatic.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared function.specialized.function.typedBody function.signature.key
      function.specialized.function.solvedRequirements name
  assertTrue (automatic.prepared.functions.length == 5) "typed place fixture coverage missing"
  IO.println "typed place keys/RHS: actual contextual lowering, repeated index, lazy/fault order, typed hidden captures and resume GREEN"

end Tests.SourceCoreCompatibleTypedPlaceExpressions
end
