import Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentFaults
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualTyped
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

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
      SourceCoreRawMetadata.runtimeType leaf = .integer)
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
