import Solcore.SourceSemantics.CoreLowering.CompatiblePlacePrefixReflection
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleGetterReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces CompatiblePlaceKeys
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_getter_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_getter_reflection.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def valueType : TypeSystem.Ty := .function .bool .bool
private def rootType : TypeSystem.Ty := .mapping .bool valueType
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
private theorem functionViews : FunctionRuntimeViews (noFunctions checked.catalog) := fun impossible => False.elim impossible
private def carrier : SourceCoreDataValues.Value := .mapping (.comptime .bool) (.comptime valueType) []
private def sourceRoot : Dynamic.Value := .mapping (.comptime .bool) (.comptime valueType) []
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceRoot := .mapping .empty
private def before : Dynamic.Heap := ⟨[⟨rootType, some sourceRoot, none⟩]⟩
private def world (prepared : Prepared) : StoreTyping := [OptionalCell.cellType prepared.route.rootType]
private def environment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 0, .bool true]
private def coreContext (prepared : Prepared) : Core.Context := [OptionalCell.referenceType prepared.route.rootType, .bool]
private def code (prepared : Prepared) : Expr := .apply (getter prepared .bool) (.pair (.loadCell (.var 0)) (.var 1))

private theorem pathArguments {registry : SourceCoreRawMetadata.Registry} {prepared : Prepared}
    {steps : List PreparedStep} {sites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
    (path : PreparedPath checked source site rootType assignment.target.projections 0 steps sites leaf) :
    Arguments checked registry (noFunctions checked.catalog) [0] (world prepared) source site [.bool true] path [.index (.bool true)] ∧
      steps ≠ [] ∧ sites.length = 1 := by
  cases path with
  | index certificate generated tail =>
    have shape := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := shape
    have nativeKey := Except.ok.inj certificate.keyProjection
    cases tail
    refine ⟨?_, (by simp), rfl⟩
    apply Arguments.index (certificate := certificate) (generated := generated) rfl
    · rw [← nativeKey]; exact .bool true
    · exact .nil

/-- Actual compiler/encoder/checker receipts and a completed native getter
suffice to reconstruct the source classification. No source path outcome is an
input. In particular the raw staged key guard is derived from payloads. -/
theorem actual_reflection {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    {result : Value} {after : Store}
    (completed : Evaluates (environment prepared) [.inRight .unit encoded.value] (code prepared) result after) :
    ∃ futureWorld,
      (∃ leaf, CompatiblePlaceGetterReflection.ResultRep checked encoded.context.registry (noFunctions checked.catalog)
        [0] futureWorld prepared ⟨rootType, some sourceRoot, none⟩ [.index (.bool true)] leaf result) ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [0] futureWorld before after := by
  obtain ⟨actualBinder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
  have projected : checked.catalog.project rootType = .ok prepared.route.rootType := routeEq ▸ description.rootProjected
  have leafProjected : checked.catalog.project leaf = .ok prepared.route.leafType := by
    rw [← checked.catalog.project_runtimeType leaf, description.selectedType, routeEq]
    exact description.leafProjected
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [] []
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  rw [same] at represented
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (.initialized represented) Dynamic.Heap.Allocates.append
  obtain ⟨arguments, nonempty, length⟩ := pathArguments (registry := encoded.context.registry) (prepared := prepared) path
  have keyLength : prepared.keyTypes.length = ([Value.bool true] : List Value).length := by simpa [Prepared.keyTypes] using length
  have typedEnvironment : RuntimeEnvironmentHasTypes (world prepared) (environment prepared) (coreContext prepared) checked.catalog.definitions :=
    .cons (.cellRef rfl) (.cons .bool .nil)
  obtain ⟨futureWorld, _, resultRep, finalHeaps, _⟩ := CompatiblePlaceGetterReflection.reflects
    arguments leafProjected (fun key value declared => routeEq ▸ description.virtual key value declared)
    (fun ordinary => routeEq ▸ description.ordinary ordinary) encoded.preserves nonempty functionViews faithful observations keyLength
    heaps reference (Dynamic.Heap.Reads.intro .head) typedEnvironment typed (.var rfl) (.var rfl) completed
  exact ⟨futureWorld, ⟨leaf, resultRep⟩, finalHeaps⟩

/-- This fixture cannot succeed: its actual empty raw mapping has no
function default. The reflected fault and token are outputs of the theorem. -/
theorem actual_missing {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    {result : Value} {after : Store}
    (completed : Evaluates (environment prepared) [.inRight .unit encoded.value] (code prepared) result after) :
    ∃ token count futureWorld,
      result = .inLeft prepared.optionalLeaf (.word token) ∧
      Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault (.comptime valueType)) ∧
      FaultToken checked encoded.context.registry sourceRoot prepared.steps [.index (.bool true)]
        (.missingMappingDefault (.comptime valueType)) token count ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [0] futureWorld before after := by
  have unavailable : ¬ Dynamic.Defaultable (.comptime valueType) := by
    intro impossible; cases impossible with | comptime inner => cases inner
  obtain ⟨futureWorld, ⟨leaf, resultRep⟩, heaps⟩ := actual_reflection described preparedBy accepted typed completed
  cases resultRep with
  | read initial selection represented =>
    cases initial with
    | initialized =>
      cases selection with
      | indexFound located => cases located
      | indexDefault _ defaulted => exact (unavailable defaulted.defaultable).elim
  | @missing root reason token count initial fault receipt =>
    cases initial with
    | initialized =>
      cases fault with
      | indexDefaultUnavailable matched absent missing =>
        exact ⟨token, count, futureWorld, rfl, .indexDefaultUnavailable matched absent missing, receipt, heaps⟩
      | indexFound _ located => cases located
      | indexDefault _ _ defaulted => exact (unavailable defaulted.defaultable).elim
  | uninitialized empty => cases empty

private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ id code => id = key ∧ code = lowered
private theorem contains : ContainsExpression source key node := lookupExpression?_sound (by cbv)

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

private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def nativeEnvironment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 0]
private def body (prepared : Prepared) : Expr :=
  execute prepared (.var 0) (SourceCoreCalls.packArguments [lowered])
    (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
    (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool none false Word.zero
private theorem localAgrees : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme,
    .mapping (.builtin .bool) (.function (.builtin .bool) (.builtin .bool))⟩
private def diagnostics (registry : SourceCoreRawMetadata.Registry) (prepared : Prepared) : GenericExpressionMeaning.FaultRep :=
  fun reason token =>
    (∃ root resolved count, FaultToken checked registry root prepared.steps resolved reason token count) ∨
    ∃ location, reason = .uninitializedLocation location ∧ token = prepared.invalidProjection

/-- A real completed emitted assignment reconstructs its source target prefix.
There is no source key, source read or native helper execution premise. -/
theorem whole_reflection {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded)
    {result : Value} {after : Store}
    (completed : Evaluates (nativeEnvironment prepared) [.inRight .unit encoded.value] (body prepared) result after) :
    ∃ leaf, CompatiblePlacePrefixReflection.Result checked encoded.context.registry (noFunctions checked.catalog) program context [] source
      (diagnostics encoded.context.registry prepared) prepared [lowered] [.bool] assignment.target leaf sourceEnvironment
      (nativeEnvironment prepared) before [.inRight .unit encoded.value] [0] (world prepared)
      (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
      (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool none false Word.zero result after := by
  obtain ⟨rootEq, _, rootProjection, leaf, _, layout⟩ := staticReceipt described preparedBy keyTypes nonempty getterTyped setterTyped
  obtain ⟨actualBinder, _, description⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  have routeEq := (description.prepared preparedBy).1
  have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
    intro nonmapping
    rw [routeEq]
    exact description.ordinary (fun k v same => nonmapping k v (rootEq.trans same))
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [] []
  have same := Except.ok.inj (represented.projection.symm.trans rootProjection)
  rw [same] at represented
  obtain ⟨heaps, reference⟩ := empty.allocate (.initialized represented) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] (world prepared) [] (scope prepared)
      sourceEnvironment (nativeEnvironment prepared) := .cons reference (.nil .nil)
  refine ⟨leaf, CompatiblePlacePrefixReflection.reflects (index := 0) layout ordinary encoded.preserves
    (childReflects encoded.context.registry _) functionViews faithful observations ?_ ?_ environments heaps localAgrees
    (by simp [scope, SourceCoreLocalCell.lookup?, assignment]) (rootEq ▸ rootWritable) completed⟩
  · intro root resolved reason token count receipt
    exact .inl ⟨root, resolved, count, receipt⟩
  · intro location
    exact .inr ⟨location, rfl, rfl⟩

private def wholeExercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) : IO Unit := do
  if keyTypes : prepared.keyTypes = [.bool] then
    if nonempty : prepared.steps ≠ [] then
      if getTyped : infer? (getContext prepared) (getCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
        if putTyped : infer? (putContext prepared) (putCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.route.rootType) then
          unless infer? (SourceCoreLocalCell.coreContext (scope prepared)) (body prepared) checked.catalog.definitions == some (LanguageResult.resultType .bool) do
            throw (IO.userError "prefix reflection actual checker rejected")
          let initial := Core.State.initial (body prepared) (nativeEnvironment prepared) [.inRight .unit encoded.value]
          match ran : runStateful 200000 initial with
          | .done result after =>
            have _reflected := whole_reflection described preparedBy keyTypes nonempty (infer_sound getTyped) (infer_sound putTyped)
              accepted (runStateful_evaluation_sound ran)
            let header ← match encoded.value with
              | .pair (.word header) _ => pure header
              | _ => throw (IO.userError "prefix reflection header missing")
            unless result == .inLeft .bool (.word ((Word.ofNatModulo 100).add header)) &&
                after.take 1 == [.inRight .unit encoded.value] && after.length == checked.catalog.entries.length + 2 do
              throw (IO.userError "prefix reflection fault order or heap changed")
            match runStateful 11 initial with
            | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done result after do
                throw (IO.userError "prefix reflection resume changed result")
            | _ => throw (IO.userError "prefix reflection expected checkpoint")
          | other => throw (IO.userError s!"prefix reflection failed {reprStr other}")
        else throw (IO.userError "prefix reflection setter checker rejected")
      else throw (IO.userError "prefix reflection getter checker rejected")
    else throw (IO.userError "prefix reflection missing steps")
  else throw (IO.userError "prefix reflection key types changed")

private def exercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) : IO Unit := do
  if typed : infer? (coreContext prepared) (code prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
    let initial := Core.State.initial (code prepared) (environment prepared) [.inRight .unit encoded.value]
    match ran : runStateful 200000 initial with
    | .done result after =>
      have _reflected := actual_missing described preparedBy accepted (infer_sound typed) (runStateful_evaluation_sound ran)
      let header ← match encoded.value with
        | .pair (.word header) _ => pure header
        | _ => throw (IO.userError "getter reflection header missing")
      unless result == .inLeft prepared.optionalLeaf (.word ((Word.ofNatModulo 100).add header)) &&
          after.take 1 == [.inRight .unit encoded.value] && after.length == checked.catalog.entries.length + 2 do
        throw (IO.userError "getter reflection raw key/default or heap changed")
      match runStateful 11 initial with
      | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done result after do
          throw (IO.userError "getter reflection resume changed result")
      | _ => throw (IO.userError "getter reflection expected checkpoint")
    | other => throw (IO.userError s!"getter reflection failed {reprStr other}")
  else throw (IO.userError "getter reflection actual checker rejected")

def run : IO Unit := do
  match described : describe compilation checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"getter reflection describe failed {reprStr error}")
  | .ok route =>
    match preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) with
    | .error error => throw (IO.userError s!"getter reflection prepare failed {reprStr error}")
    | .ok _ =>
      match accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
      | .error error => throw (IO.userError s!"getter reflection encode failed {reprStr error}")
      | .ok _ =>
        exercise described preparedBy accepted
        wholeExercise described preparedBy accepted
  IO.println "compatible live getter reflection derives staged key fault from actual run GREEN"

end Tests.SourceCoreCompatibleGetterReflection
