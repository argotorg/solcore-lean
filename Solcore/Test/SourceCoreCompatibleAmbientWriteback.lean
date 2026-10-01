import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentSuccess
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterReflection
import Solcore.Frontend.SourceCoreCallableIndexedOutputs
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Successful whole assignment now shares the real indexed definition table
with its function model and native checker receipts. The universal expression
IH and actual static layout remain explicit intermediate obligations. Runtime
regressions store fresh capturing closures and preserve source mapping order;
this does not infer source closure authenticity from native typing alone. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientWriteback
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap GenericExpressionMeaning CompatiblePayload CompatibleEquality CompatibleHeap
open SourceCoreCompatibleDataPlaces CompatibleMapping.MixedPaths

/-- The static native helper types use the artifact's full definitions, while
all source path, metadata and projection receipts retain their base catalog. -/
theorem whole_success_under_indexed {compilation : SourceCoreCompatibleDataPlaces.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared compilation.checked)
    {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel compilation.checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout compilation source certificate scope site place prepared codes sourceTypes leaf
      administrativeContext (definitions := artifact.layouts.definitions))
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := artifact.layouts.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment coreEnvironment)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      FiniteRun coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression (LanguageResult.success .unit) .unit
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inRight .word .unit) finalStore ∧
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    CompatiblePlaceAssignmentSuccess.preserves layout registryExtension meaning faithful observations rhsGenerated found rhsView
      rhsCoreType profile environments heaps locals slot rootTyped trace invalid
  exact ⟨value, finalStore, finalMap, finalWorld, .of_evaluates evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

private def w (n : Nat) : Word := Word.ofNatModulo n
private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function inc(x: Word) returns (Word) { return x + 1; }",
    "function replace(root: mapping(Word => F), seed: Word) returns (mapping(Word => F)) {",
    " root[1] = lam(x: Word) { return x + seed; }; return root; }",
    "function invoke(root: mapping(Word => F), seed: Word) returns (Word) {",
    " root[1] = lam(x: Word) { return x + seed; }; return root[1](8) + root[2](8); }",
    "function removed(root: mapping(Word => F), seed: Word) returns (Word) {",
    " let rhs = lam() -> F { let empty: mapping(Word => F); root = empty; return lam(x: Word) { return x + seed; }; };",
    " root[1] = rhs(); return 999; }"
  ]}] }
private structure Projection (checked : SourceCoreCompatibleCatalog.Checked) (source : TypeSystem.Ty) (native : Ty) : Type where
  equation : checked.catalog.project source = .ok native
private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩ | none => throw (IO.userError s!"writeback fixture missing {name}")

def run : IO Unit := do
  let program ← get "writeback source" (checkProgram workspace)
  let requests := program.signatures.functions.map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"writeback plan: {reprStr other}")
  let automatic ← get "writeback base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let artifact ← get "writeback indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let outputs ← get "writeback output cache" (SourceCoreCallableIndexedOutputs.prepare artifact)
  let inc ← key program "inc"
  let functionType := TypeSystem.Ty.function .word .word
  let rootType := TypeSystem.Ty.mapping .word functionType
  let initial : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime functionType)
    [(.word (w 1), .global inc []), (.word (w 1), .global inc []), (.word (w 2), .global inc [])]
  require (artifact.layouts.definitions.length > automatic.checked.catalog.definitions.length) "writeback lacks real ambient suffix"
  for name in ["replace", "invoke", "removed"] do
    let owner ← key program name
    let first ← get "writeback start" (artifact.runSource owner [initial, .word (w 5)] 1 500)
    require first.result.native.checkpoint?.isSome "writeback did not checkpoint"
    let completed := first.resume 300000
    let direct ← get "writeback direct" (artifact.runSource owner [initial, .word (w 5)] 300000 500)
    require (completed.result.native.observation == direct.result.native.observation) "writeback resume differs"
    if name == "replace" then
      let projected ← match accepted : automatic.checked.catalog.project rootType with
        | .error error => throw (IO.userError s!"writeback projection: {reprStr error}")
        | .ok type =>
          if same : type = completed.entry.native.resultType then
            pure (show Projection automatic.checked rootType completed.entry.native.resultType from ⟨by simpa only [same] using accepted⟩)
          else throw (IO.userError "writeback result projection changed")
      let exported ← get "writeback mapping output" (SourceCoreCallableIndexedOutputs.decodeSuccess outputs completed rootType projected.equation [] 1024)
      match exported.decoded.source with
      | .mapping rawKey rawValue [(.word first, .closure _ _ _ _ _ captures _), (.word second, .global duplicate _), (.word third, .global other _)] =>
        require (rawKey == .comptime .word && rawValue == .comptime functionType) "writeback changed raw header"
        require (first == w 1 && second == w 1 && third == w 2 && duplicate == inc && other == inc) "writeback changed ordered duplicates or sibling"
        require (!captures.isEmpty) "writeback lost fresh closure captures"
      | other => throw (IO.userError s!"writeback lost returned function mapping: {reprStr other}")
    else if name == "invoke" then
      match completed.result.native.observation with
      | .succeeded (.word value) _ => require (value == w 22) "writeback fresh closure or named sibling changed"
      | other => throw (IO.userError s!"writeback invocation failed: {reprStr other}")
    else
      match completed.result.native.observation with
      | .failed token _ =>
        match completed.result.diagnostics.diagnostic? token with
        | some diagnostic =>
          require (decide (diagnostic.error = .typeMismatch functionType none)) "setter fault used the old raw default type"
          require diagnostic.span.isSome "setter fault lost its assignment span"
        | none => throw (IO.userError "writeback missing-default diagnostic absent")
      | other => throw (IO.userError s!"latest-root removal did not fault: {reprStr other}")
      let rootBinder ← match artifact.base.functions.find? (·.specialized.key == owner) with
        | some function => match function.specialized.function.typedBody.inputs with
          | root :: _ => pure root | _ => throw (IO.userError "removed root binder absent")
        | none => throw (IO.userError "removed function absent")
      let ledger ← get "writeback failure ledger" (SourceCoreCallableIndexedLedger.scan completed)
      let row ← match ledger.ledger.rows.filter (·.entry.key.binder.id == rootBinder.id) with
        | [row] => pure row | _ => throw (IO.userError "removed root ledger not unique")
      let native ← match row.payload with
        | some native => pure native | none => throw (IO.userError "removed root became absent")
      let after ← get "writeback remaining root" (SourceCoreCompatibleValues.decode 500 completed.result.context rootType native)
      require (after == .mapping .word functionType []) "setter fault overwrote the RHS's latest empty root"
  IO.println "compatible ambient writeback and fresh function payloads GREEN"

end Tests.SourceCoreCompatibleAmbientWriteback
