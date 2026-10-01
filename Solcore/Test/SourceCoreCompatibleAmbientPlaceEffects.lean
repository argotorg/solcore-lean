import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceFailures
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceGetterReflection
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyReflection
import Solcore.Frontend.SourceCoreCallableIndexedLedger
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Effectful key/RHS composition under real indexed definitions. The semantic
consumer keeps the universal expression IH explicit; its source resolution and
RHS traces construct native runs, snapshot preservation and latest-root facts.
The IO fixture separately exercises actual compiler hooks and source effects. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientPlaceEffects
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap GenericExpressionMeaning CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open CompatiblePlaceKeys SourceCoreCompatibleDataPlaces

/-- Source key effects finish before the snapshot; the RHS executes under the
actual three hidden slots and retains both the old snapshot and new live root.
No particular child execution is assumed instead of the universal IH. -/
theorem resolve_then_rhs {compilation : SourceCoreCompatibleDataPlaces.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared compilation.checked)
    {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel compilation.checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) artifact.layouts.definitions)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := artifact.layouts.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment coreEnvironment)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {outcome : Dynamic.ExpressionOutcome}
    (rhsGenerated : certificate scope rhs lowered) (rhsFound : source.lookupExpression? rhs = some node)
    (rhsTrace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap rhs outcome after) :
    ∃ resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared codes sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before targetHeap,
      ∃ native finalStore finalMap finalWorld,
        CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := evidence)
          (source := source) (faults := faults) resolution rhs node lowered environment outcome after native finalStore finalMap finalWorld ∧
        ValueRep compilation.checked registry functions finalMap finalWorld leaf resolution.selected resolution.snapshot prepared.route.leafType ∧
        Nonempty (CompatiblePlaceRhs.Latest compilation.checked registry functions finalMap finalWorld prepared sourceTarget
          resolution.target after finalStore) := by
  obtain ⟨resolution, _⟩ := CompatiblePlaceResolution.preserves path views children keyTypes leafProjected virtual registryExtension
    nonempty getterTyped meaning faithful observations environments heaps locals slot rootTyped resolve
  obtain ⟨native, finalStore, finalMap, finalWorld, result⟩ :=
    CompatiblePlaceRhs.preserves resolution meaning rhsGenerated rhsFound environments locals rhsTrace
  exact ⟨resolution, native, finalStore, finalMap, finalWorld, result, result.saved_snapshot, result.latest⟩

/-- An actual completed RHS yields its independent source outcome in the full
ambient model. Resolution is a prior semantic output, not a static certificate. -/
theorem rhs_reflects_under_indexed {checked : Checked}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared checked) {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : Certificate} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {store afterStore : Store}
    {mapping : LocationMap} {world : StoreTyping} {before resolvedHeap : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
      coreEnvironment store mapping world before resolvedHeap)
    (meaning : Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {administrativeContext : Core.Context} {rhs : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {value : Value}
    (generated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (environments : DataHeap.EnvRepresents (definitions := artifact.layouts.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (completed : Evaluates
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType resolution.target
        (DataPatternValues.packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (SourceCoreCompatibleDataPlaces.shift 3 lowered.expression) value afterStore) :
    ∃ outcome after finalMap finalWorld,
      CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := evidence)
        (source := source) (faults := faults) resolution rhs node lowered environment outcome after value afterStore finalMap finalWorld :=
  CompatiblePlaceRhs.reflects resolution meaning generated found environments locals completed

private def w (n : Nat) : Word := Word.ofNatModulo n
private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function effects(root: mapping(Word => Word)) returns (Word) {",
    " let key = lam(x: Word) { root[1] = 20; return x; };",
    " let rhs = lam(x: Word) { root[1] = 30; root[2] = 40; return x; };",
    " root[key(1)] += rhs(3); return root[1] + root[2]; }",
    "function keyFault(root: mapping(Word => Word)) returns (Word) {",
    " let key = lam(x: Word) { root[1] = 20; let absent: Word; return absent; };",
    " let rhs = lam(x: Word) { root[2] = 40; return x; };",
    " root[key(1)] += rhs(3); root[3] = 50; return 0; }",
    "function rhsFault(root: mapping(Word => Word)) returns (Word) {",
    " let key = lam(x: Word) { root[1] = 20; return x; };",
    " let rhs = lam(x: Word) { root[2] = 40; let absent: Word; return absent; };",
    " root[key(1)] += rhs(3); root[3] = 50; return 0; }"
  ]}] }

private def exercise {checked : Checked} (artifact : SourceCoreCallableIndexedPrograms.Prepared checked)
    (program : CheckedProgram) (name : String) (expected : Option Word)
    (entries : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)) : IO Unit := do
  let signature ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature | none => throw (IO.userError "effectful function absent")
  let key : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let sourceCell ← match artifact.base.functions.find? (·.specialized.key == key) with
    | some function => match function.specialized.function.typedBody.inputs with
      | [input] => pure input | _ => throw (IO.userError "effectful root input changed")
    | none => throw (IO.userError "effectful prepared function absent")
  let initial : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word) []
  let suspended ← get "effectful start" (artifact.runSource key [initial] 1 500)
  require suspended.result.native.checkpoint?.isSome "effectful run did not checkpoint"
  let completed := suspended.resume 300000
  let direct ← get "effectful direct" (artifact.runSource key [initial] 300000 500)
  require (completed.result.native.observation == direct.result.native.observation) "effectful resume changed final observation"
  match expected, completed.result.native.observation with
  | some expected, .succeeded (.word value) _ => require (value == expected) "snapshot used RHS-mutated root value"
  | none, .failed token _ => require ((completed.result.diagnostics.diagnostic? token).isSome) "effectful fault lost source diagnostic"
  | _, other => throw (IO.userError s!"effectful outcome: {reprStr other}")
  let ledger ← get "effectful source ledger" (SourceCoreCallableIndexedLedger.scan completed)
  let row ← match ledger.ledger.rows.filter (·.entry.key.binder.id == sourceCell.id) with
    | [row] => pure row | _ => throw (IO.userError "effectful root ledger is not unique")
  let native ← match row.payload with
    | some native => pure native | none => throw (IO.userError "effectful root became uninitialized")
  let actual ← get "effectful raw root" (SourceCoreCompatibleValues.decode 500 completed.result.context sourceCell.scheme.body native)
  require (actual == .mapping (.comptime .word) (.comptime .word) entries) "effect order, write suppression or raw mapping metadata changed"
  require (artifact.layouts.definitions.length > checked.catalog.definitions.length) "effectful fixture lacks actual ambient definitions"

def run : IO Unit := do
  let program ← get "effectful source check" (checkProgram workspace)
  let requests := program.signatures.functions.map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"effectful plan: {reprStr other}")
  let automatic ← get "effectful base compiler" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let artifact ← get "effectful indexed compiler" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  exercise artifact program "effects" (some (w 63)) [(.word (w 1), .word (w 23)), (.word (w 2), .word (w 40))]
  exercise artifact program "keyFault" none [(.word (w 1), .word (w 20))]
  exercise artifact program "rhsFault" none [(.word (w 1), .word (w 20)), (.word (w 2), .word (w 40))]
  IO.println "compatible ambient place key/RHS effects GREEN"

end Tests.SourceCoreCompatibleAmbientPlaceEffects
