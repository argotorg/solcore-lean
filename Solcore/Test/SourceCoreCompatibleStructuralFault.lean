import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceStructuralFault
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCompatibleStructuralFault
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_structural", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_structural.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal owner []
private def rootType : TypeSystem.Ty := .mapping .bool boxType
private def signature : ProgramDataSignature := {
  id := owner, name := "Box", parameters := []
  constructors := [⟨⟨owner, 0⟩, "Box", [], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def metadata : DataConstructorInstantiation := ⟨⟨owner, 0⟩, [], [], boxType⟩
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def catalog : SourceCoreCompatibleCatalog.Catalog := { entries := [
  { sourceType := rootType, definition := some (OrderedMapping.Layout.definition ⟨.bool, .namedData ⟨1⟩, ⟨0⟩⟩) },
  { sourceType := boxType, constructors := [⟨owner, 0⟩], definition := some ⟨[.product .word .unit]⟩ }] }
private theorem registryExists : (SourceCoreRawMetadata.prepare signatures [.mapping .bool boxType]).toOption.isSome = true := by decide
private def registry := (SourceCoreRawMetadata.prepare signatures [.mapping .bool boxType]).toOption.get registryExists
private def checked : SourceCoreCompatibleCatalog.Checked :=
  ⟨catalog, DataEnvironment.isWellFormed_sound (by decide), signatures, registry,
    SourceCoreRawMetadata.prepare_signatures (except_get _ registryExists)⟩
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], boxType⟩, []⟩
private def missing : Word := Word.ofNatModulo 100
private def carrier : SourceCoreDataValues.Value := .mapping .bool (.comptime boxType) []
private def sourceRoot : Dynamic.Value := .mapping .bool (.comptime boxType) []
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceRoot := .mapping .empty
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private theorem unavailable : ¬ Dynamic.Defaultable (.comptime boxType) := by
  intro impossible; cases impossible with | comptime inner => cases inner
private theorem fault : Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault (.comptime boxType)) :=
  .indexDefaultUnavailable (.bool true) .nil unavailable

private def coreContext (prepared : Prepared) : Core.Context :=
  [OptionalCell.referenceType prepared.route.rootType, .bool, prepared.route.leafType]
private def code (prepared : Prepared) : Expr :=
  .apply (setter prepared .bool) (.pair (.loadCell (.var 0)) (.pair (.var 1) (.var 2)))
private def environment (prepared : Prepared) (replacement : Value) : Environment :=
  [.cellRef (OptionalCell.cellType prepared.route.rootType) 1, .bool true, replacement]
private def world (prepared : Prepared) : StoreTyping := [.integer, OptionalCell.cellType prepared.route.rootType]

private theorem pathArguments {registry : SourceCoreRawMetadata.Registry} {prepared : Prepared}
    {steps : List PreparedStep} {sites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
    (path : PreparedPath checked source site rootType assignment.target.projections 0 steps sites leaf) :
    Arguments checked registry (noFunctions checked.catalog) [1] (world prepared) source site [.bool true] path [.index (.bool true)] ∧
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

/-- The actual route and encoder suffice to construct a live setter fault.
The raw staged nominal default is unavailable, even though its native carrier
uses the same type as the unstaged declaration. -/
theorem certified {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => missing) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded)
    {replacement : Value}
    (replacementTyped : RuntimeValueHasType (world prepared) replacement prepared.route.leafType checked.catalog.definitions)
    (setterTyped : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions) :
    ∃ token count finalStore futureWorld,
      FaultToken checked encoded.context.registry sourceRoot prepared.steps [.index (.bool true)]
        (.missingMappingDefault (.comptime boxType)) token count ∧
      Evaluates (environment prepared replacement) [.integer (-123), .inRight .unit encoded.value] (code prepared)
        (.inLeft prepared.route.rootType (.word token)) finalStore ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [1] futureWorld
        ⟨[⟨rootType, some sourceRoot, none⟩]⟩ finalStore ∧
      finalStore.read? 0 = some (.integer (-123)) ∧ finalStore.read? 1 = some (.inRight .unit encoded.value) := by
  obtain ⟨actualBinder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
  have projected : checked.catalog.project rootType = .ok prepared.route.rootType := routeEq ▸ description.rootProjected
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [1] (world prepared)
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  rw [same] at represented
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  have before := empty.allocate_administrative (RuntimeValueHasType.integer (value := -123))
  have firstRep := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [] [.integer]
  rw [same] at firstRep
  obtain ⟨heaps, reference⟩ := before.allocate (.initialized firstRep) Dynamic.Heap.Allocates.append
  have heaps : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [1] (world prepared)
      ⟨[⟨rootType, some sourceRoot, none⟩]⟩ [.integer (-123), .inRight .unit encoded.value] := heaps
  have root : RootRead checked encoded.context.registry (noFunctions checked.catalog) [1] (world prepared) prepared
      ⟨[⟨rootType, some sourceRoot, none⟩]⟩ [.integer (-123), .inRight .unit encoded.value] ⟨0⟩ 1
      ⟨rootType, some sourceRoot, none⟩ (.inRight .unit encoded.value) sourceRoot encoded.value :=
    .initialized (.intro .head) ⟨rfl, rfl⟩ rfl represented
  obtain ⟨arguments, nonempty, length⟩ := pathArguments (registry := encoded.context.registry) (prepared := prepared) path
  have keyLength : prepared.keyTypes.length = ([Value.bool true] : List Value).length := by
    simpa [Prepared.keyTypes] using length
  have typed : RuntimeEnvironmentHasTypes (world prepared) (environment prepared replacement) (coreContext prepared) checked.catalog.definitions :=
    .cons (.cellRef rfl) (.cons .bool (.cons replacementTyped .nil))
  obtain ⟨token, count, after, administrative, futureWorld, receipt, evaluated, finalHeaps, _, _, finalRoot, appended, _⟩ :=
    CompatiblePlaceSetterFault.preserves root heaps arguments fault nonempty faithful observations keyLength typed setterTyped
      (.var rfl) (.var rfl) (.var rfl)
  exact ⟨token, count, after, futureWorld, receipt, evaluated, finalHeaps, by rw [appended]; rfl, finalRoot.nativeRead⟩

private def executeAfterRhs (prepared : Prepared) : Expr :=
  execute prepared (.var 0) ⟨.bool, LanguageResult.success (.bool true)⟩
    (.letE (.storeCell (.var 0) (.inRight .unit (.var 4))) (LanguageResult.success (.var 3)))
    (LanguageResult.failure .bool (.word (Word.ofNatModulo 777))) .bool none false Word.zero

private def exercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => missing) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) : IO Unit := do
  let replacement ← match SourceCoreCompatibleValues.encode 100 encoded.context boxType (.constructed metadata []) with
    | .ok result => pure result
    | .error error => throw (IO.userError s!"structural-fault replacement encoding failed: {reprStr error}")
  if same : replacement.type = prepared.route.leafType then
    if typed : infer? (coreContext prepared) (code prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.route.rootType) then
      have replacementTyped : RuntimeValueHasType (world prepared) replacement.value prepared.route.leafType checked.catalog.definitions :=
        same ▸ replacement.typed (world prepared)
      have receipt := certified described preparedBy accepted replacementTyped (infer_sound typed)
      have _finite : ∃ fuel token after,
          runStateful fuel (.initial (code prepared) (environment prepared replacement.value) [.integer (-123), .inRight .unit encoded.value]) =
            .done (.inLeft prepared.route.rootType (.word token)) after := by
        obtain ⟨token, _, after, _, _, evaluated, _⟩ := receipt
        obtain ⟨fuel, completed⟩ := evaluation_runStateful_complete evaluated
        exact ⟨fuel, token, after, completed⟩
      let header ← match encoded.value with
        | .pair (.word header) _ => pure header
        | _ => throw (IO.userError "structural-fault raw header missing")
      unless encoded.context.registry.lookup header == some (.mapping .bool (.comptime boxType)) do
        throw (IO.userError "structural-fault raw staged metadata erased")
      let before := [Value.integer (-123), Value.inRight .unit encoded.value]
      match runStateful 200000 (.initial (code prepared) (environment prepared replacement.value) before) with
      | .done (.inLeft _ (.word token)) after =>
        unless token == missing.add header && after.take 2 == before &&
            after.length == 2 + checked.catalog.entries.length + 1 do
          throw (IO.userError "structural-fault setter changed token, root or allocation order")
      | other => throw (IO.userError s!"structural-fault setter failed: {reprStr other}")
      let initialRoot ← match SourceCoreCompatibleValues.encode 100 replacement.context rootType
          (.mapping .bool (.comptime boxType) [(.bool true, .constructed metadata [])]) with
        | .ok value => pure value
        | .error error => throw (IO.userError s!"structural-fault initial root failed: {reprStr error}")
      let fullContext := [OptionalCell.referenceType prepared.route.rootType, Ty.bool, prepared.route.leafType,
        prepared.route.rootType, prepared.route.rootType]
      let fullEnvironment := [Value.cellRef (OptionalCell.cellType prepared.route.rootType) 1, .bool true,
        replacement.value, initialRoot.value, encoded.value]
      unless infer? fullContext (executeAfterRhs prepared) checked.catalog.definitions == some (LanguageResult.resultType .bool) do
        throw (IO.userError "structural-fault whole execute checker failed")
      let initial := Core.State.initial (executeAfterRhs prepared) fullEnvironment [.integer (-123), .inRight .unit initialRoot.value]
      match runStateful 200000 initial with
      | .done (.inLeft .bool (.word token)) after =>
        unless token == missing.add header && after.take 2 == before && after.length == 2 + 2 * (checked.catalog.entries.length + 1) do
          throw (IO.userError "RHS/latest-root fault did not preserve prefix effects or suppress writeback")
        match runStateful 19 initial with
        | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done (.inLeft .bool (.word token)) after do
            throw (IO.userError "structural-fault resume changed observation")
        | _ => throw (IO.userError "structural-fault expected a checkpoint")
      | other => throw (IO.userError s!"RHS/latest-root structural fault failed: {reprStr other}")
    else throw (IO.userError "structural-fault setter checker failed")
  else throw (IO.userError "structural-fault replacement type changed")

def run : IO Unit := do
  match described : describe compilation checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"structural-fault describe failed: {reprStr error}")
  | .ok route =>
    match preparedBy : prepare compilation 100 route Word.zero (fun _ => missing) with
    | .error error => throw (IO.userError s!"structural-fault prepare failed: {reprStr error}")
    | .ok _ =>
      match accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
      | .error error => throw (IO.userError s!"structural-fault carrier encode failed: {reprStr error}")
      | .ok _ => exercise described preparedBy accepted
  IO.println "compatible latest-root structural fault and raw default token GREEN"

end Tests.SourceCoreCompatibleStructuralFault
