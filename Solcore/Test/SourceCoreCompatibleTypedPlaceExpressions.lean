import Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceKeys
import Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceRhs
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualTyped
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

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
