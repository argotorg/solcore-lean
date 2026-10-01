import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSnapshot

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual describe/prepare receipts feed live-cell snapshots. The Core store
has an administrative prefix, so source location zero maps to Core location
one. Both initialized and virtual roots keep that slot unchanged. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCompatiblePlaceSnapshot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreCompatibleDataPlaces CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute
open CompatiblePlaceLiveRoot

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_live", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_live.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool .word
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index key]
private def assignment : AssignmentResolution := ⟨⟨binder.id, projections, .word⟩, []⟩
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

private def world (prepared : Prepared) : StoreTyping := [.integer, OptionalCell.cellType prepared.route.rootType]
private def environment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 1, .bool true]
private def coreContext (prepared : Prepared) : Core.Context := [OptionalCell.referenceType prepared.route.rootType, .bool]
private def code (prepared : Prepared) : Expr := .apply (getter prepared .bool) (.pair (.loadCell (.var 0)) (.var 1))
private def keys : List Value := [.bool true]
private def resolved : List Dynamic.EvaluatedProjection := [.index (.bool true)]
private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful noIdentities := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem noFunctionObservations : FunctionObservations checked.catalog (noFunctions checked.catalog) noIdentities := fun impossible => False.elim impossible

private theorem leaf_word {steps : List PreparedStep} {sites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
    (path : PreparedPath checked source site rootType projections 0 steps sites leaf) : leaf = .word := by
  cases path with
  | index certificate generated tail =>
    have shape := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := shape
    cases tail
    rfl

private theorem actualPath {route : Route} {prepared : Prepared}
    (described : describe context checked.signatures source site assignment = .ok route)
    (preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared) :
    PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys .word ∧
    checked.catalog.project rootType = .ok prepared.route.rootType ∧
    checked.catalog.project .word = .ok prepared.route.leafType ∧
    VirtualRoot.Generated context prepared.route .bool .word := by
  obtain ⟨actualBinder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have binding : rootBinder source assignment.target.root = .ok binder := by cbv
  have same := Except.ok.inj (description.binding.symm.trans binding)
  subst actualBinder
  obtain ⟨sameRoute, _, path⟩ := description.prepared preparedBy
  have selectedEq := leaf_word path
  subst selected
  exact ⟨path, sameRoute ▸ description.rootProjected, sameRoute ▸ description.leafProjected,
    sameRoute ▸ description.virtual .bool .word rfl⟩

private theorem arguments {registry : SourceCoreRawMetadata.Registry} {prepared : Prepared}
    {steps : List PreparedStep} {sites : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site rootType projections 0 steps sites .word) :
    Arguments checked registry (noFunctions checked.catalog) [1] (world prepared) source site keys path resolved ∧
      steps ≠ [] ∧ sites.length = keys.length := by
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

private theorem store_typed {prepared : Prepared} {optional : Value}
    (typed : RuntimeValueHasType (world prepared) optional (OptionalCell.cellType prepared.route.rootType) checked.catalog.definitions) :
    RuntimeStoreHasTypes (world prepared) [.integer (-123), optional] checked.catalog.definitions := by
  refine ⟨rfl, ?_⟩
  intro index type found
  cases index with
  | zero => cases found; exact ⟨_, rfl, .integer⟩
  | succ index => cases index with
    | zero => cases found; exact ⟨_, rfl, typed⟩
    | succ index => simp [world] at found
private theorem environment_typed (prepared : Prepared) :
    RuntimeEnvironmentHasTypes (world prepared) (environment prepared) (coreContext prepared) checked.catalog.definitions :=
  .cons (.cellRef rfl) (.cons .bool .nil)

private theorem snapshot {prepared : Prepared} {registry : SourceCoreRawMetadata.Registry}
    {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot selected : Dynamic.Value}
    (root : RootRead checked registry (noFunctions checked.catalog) [1] (world prepared) prepared
      ⟨[cell]⟩ [.integer (-123), optional] ⟨0⟩ 1 cell optional sourceRoot rootValue)
    (path : PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys .word)
    (cellType : cell.type = rootType) (leaf : checked.catalog.project .word = .ok prepared.route.leafType)
    (read : Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected))
    (optionalTyped : RuntimeValueHasType (world prepared) optional (OptionalCell.cellType prepared.route.rootType) checked.catalog.definitions)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions) :
    ∃ native after,
      FiniteRun (environment prepared) [.integer (-123), optional] (code prepared) (.inRight .word (.inRight .unit native)) after ∧
      after.read? 1 = some optional ∧ after.read? 0 = some (.integer (-123)) := by
  obtain ⟨keysRelated, nonempty, keyLength⟩ := arguments (registry := registry) (prepared := prepared) path
  have keyLength : prepared.keyTypes.length = keys.length := by simpa [Prepared.keyTypes] using keyLength
  have root' : RootRead checked registry (noFunctions checked.catalog) [1] (world prepared) prepared
      ⟨[cell]⟩ [.integer (-123), optional] ⟨0⟩ 1 cell optional sourceRoot rootValue := root
  have path' : PreparedPath checked source site cell.type projections 0 prepared.steps prepared.keys .word := cellType.symm ▸ path
  have keysRelated' : Arguments checked registry (noFunctions checked.catalog) [1] (world prepared) source site keys path' resolved := by
    simpa only [cellType] using keysRelated
  obtain ⟨native, after, suffix, future, _, _, ran, _, _, _, finalRoot, _, appended, _⟩ := read_at root' keysRelated' leaf read
    nonempty faithful noFunctionObservations keyLength (store_typed optionalTyped) (environment_typed prepared) typed (.var rfl) (.var rfl)
  refine ⟨native, after, ran, finalRoot.nativeRead, ?_⟩
  rw [appended]
  rfl

private def w (n : Nat) : Word := Word.ofNatModulo n
private def carrier : SourceCoreDataValues.Value := .mapping .bool .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private def sourceRoot : Dynamic.Value := .mapping .bool .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private theorem meaning : CompatibleEncoding.Means carrier sourceRoot :=
  .mapping (.prepend (.bool _) (.word _) (.prepend (.bool _) (.word _) .empty))

private theorem initialized_snapshot {route : Route} {prepared : Prepared}
    (described : describe context checked.signatures source site assignment = .ok route)
    (preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions) :
    ∃ native after,
      FiniteRun (environment prepared) [.integer (-123), .inRight .unit encoded.value] (code prepared) (.inRight .word (.inRight .unit native)) after ∧
      after.read? 1 = some (.inRight .unit encoded.value) ∧ after.read? 0 = some (.integer (-123)) := by
  obtain ⟨path, projected, leaf, _⟩ := actualPath described preparedBy
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted meaning [1] (world prepared)
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  rw [same] at represented
  have root := RootRead.initialized (prepared := prepared) (heap := ⟨[⟨rootType, some sourceRoot, none⟩]⟩)
    (store := [.integer (-123), .inRight .unit encoded.value]) (location := ⟨0⟩) (target := 1) (.intro .head) ⟨rfl, rfl⟩ rfl represented
  exact snapshot root path rfl leaf (.indexFound (.head ⟨rfl, .bool _⟩) .nil) (.inRight represented.runtime_hasType) typed

private theorem virtual_snapshot {route : Route} {prepared : Prepared}
    (described : describe context checked.signatures source site assignment = .ok route)
    (preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions) :
    ∃ native after,
      FiniteRun (environment prepared) [.integer (-123), .inLeft prepared.route.rootType .unit] (code prepared) (.inRight .word (.inRight .unit native)) after ∧
      after.read? 1 = some (.inLeft prepared.route.rootType .unit) ∧ after.read? 0 = some (.integer (-123)) := by
  obtain ⟨path, projected, leaf, generated⟩ := actualPath described preparedBy
  obtain ⟨value, root⟩ := RootRead.virtual (functions := noFunctions checked.catalog) (mapping := [1]) (world := world prepared)
    (heap := ⟨[⟨rootType, none, none⟩]⟩) (store := [.integer (-123), .inLeft prepared.route.rootType .unit])
    (location := ⟨0⟩) (target := 1) generated (.refl _) projected (.intro .head) ⟨rfl, rfl⟩ rfl
  exact snapshot root path rfl leaf (.indexDefault .nil .word .nil) (.inLeft .unit) typed

private def completed (prepared : Prepared) (optional : Value) (expected : Word) : IO Unit := do
  let before := [.integer (-123), optional]
  let initial := State.initial (code prepared) (environment prepared) before
  match runStateful 100000 initial with
  | .done value after =>
    unless value == .inRight .word (.inRight .unit (.word expected)) do throw (IO.userError "live snapshot value changed")
    unless after.take 2 == before do throw (IO.userError "snapshot changed root or prior admin cell")
    unless after.length == 2 + checked.catalog.entries.length + 1 do throw (IO.userError "snapshot helper allocation count changed")
    match runStateful 1 initial with
    | .outOfFuel checkpoint =>
      unless runStateful 100000 checkpoint == .done value after do throw (IO.userError "live snapshot resumption changed observation")
    | _ => throw (IO.userError "live snapshot expected a checkpoint")
  | other => throw (IO.userError s!"live snapshot did not finish: {reprStr other}")

def run : IO Unit := do
  match described : describe context checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"live describe failed: {reprStr error}")
  | .ok route => match preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) with
    | .error error => throw (IO.userError s!"live prepare failed: {reprStr error}")
    | .ok prepared =>
      if inferred : infer? (coreContext prepared) (code prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
        have typed := infer_sound inferred
        have _virtual := virtual_snapshot described preparedBy typed
        completed prepared (.inLeft prepared.route.rootType .unit) Word.zero
        match accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier with
        | .error error => throw (IO.userError s!"live encode failed: {reprStr error}")
        | .ok encoded =>
          have _initialized := initialized_snapshot described preparedBy accepted typed
          completed prepared (.inRight .unit encoded.value) (w 7)
      else throw (IO.userError "live generated helper was rejected by Core checker")
  IO.println "compatible live-root snapshot proofs GREEN"

end Tests.SourceCoreCompatiblePlaceSnapshot
