import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBodyMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! The real compiler equations feed the function-body factory and concrete
finite call consumers. Core-only fixtures cover Unit fallthrough, loop control,
match returns and retained faults under suspension and resumption. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBody.Certificate.mk
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreBuiltinImperativeMatchBody
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open BuiltinImperativeMatchBody GeneralHeap ReadOnly CompatiblePayload CoreProof

section CompilerConsumers
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (program : SourceSemantics.Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_preserves
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated tree
  exact certificate.preserves functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_reflects
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated tree
  exact certificate.reflects functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped evaluated
end CompilerConsumers

/-- Escaped control uses its escaped token for every native result type. -/
theorem break_finish {type : Ty} {environment : Environment} {store : Store}
    (fellThrough escaped : Word) :
    Evaluates environment store
      (CompatibleStatements.finish type (LocalLoop.breaking type) fellThrough escaped)
      (.inLeft type (.word escaped)) store :=
  LocalControl.finish_failure type
    (LocalLoop.toControl_transfer type escaped
      (LocalLoop.breaking_evaluates type environment store))

theorem continue_finish {type : Ty} {environment : Environment} {store : Store}
    (fellThrough escaped : Word) :
    Evaluates environment store
      (CompatibleStatements.finish type (LocalLoop.continuing type) fellThrough escaped)
      (.inLeft type (.word escaped)) store :=
  LocalControl.finish_failure type
    (LocalLoop.toControl_transfer type escaped
      (LocalLoop.continuing_evaluates type environment store))

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "enum Box<T> { Box(T) }",
      "function unitComposite(seed: Word) { let cursor = seed; for (let i = 0; i < 2; i += 1) { match (i) { case 0 { continue; } default { cursor += 1; } } } while (cursor < 2) { cursor += 1; match (cursor) { case 2 { break; } default {} } } match (cursor) { case 0 {} default { let shadow = cursor; shadow; } } }",
      "function returnedComposite(seed: Word) returns (integer) { for (let i = 0; true; i += 1) { match (Box((seed, i))) { case .Box((0, x)) { return integerSub(wordToInteger(x), 3); } case .Box((x, y)) { while (integerLt(wordToInteger(y), 2)) { y += 1; } return integerAdd(wordToInteger(x), wordToInteger(y)); } } } return 99; }",
      "function failedComposite(seed: Word) returns (integer) { let seen: mapping(Bool => Word); let gap: Word; for (let i = 0; true; i += 1) { match (seed) { case 0 { seen[false] = seed + 5; return wordToInteger(gap); } default { seen[true] = seed; return integerSub(wordToInteger(gap), 1); } } } return 0; }"
    ]}] }

private def fault_resume (entry : SourceCompilerFeatureSupport.Entry)
    (arguments : List SourceCompilerFeatureSupport.Value) : IO Unit := do
  let complete ← entry.invoke arguments
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "imperative body fault unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome
    "imperative body fault lost its diagnostic"
  for fuel in [0, 11, 89] do
    let started ← SourceCompilerFeatureSupport.get "imperative body suspension"
      (← complete.initial.run complete.key arguments
        {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual _ =>
      SourceCompilerFeatureSupport.require (actual == token)
        "resumed imperative body fault changed its token"
    | _ => throw (IO.userError "resumed imperative body fault ran its continuation")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "imperative body checker"
    (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let unitBody ← SourceCompilerFeatureSupport.compileNamed checked "unitComposite"
  for n in [0, 3] do
    SourceCompilerFeatureSupport.require ((← unitBody.run [w n]) == .unit)
      "imperative Unit body changed fallthrough"
    for fuel in [0, 11, 89] do unitBody.checkResume [w n] .unit fuel
  let returned ← SourceCompilerFeatureSupport.compileNamed checked "returnedComposite"
  for (n, expected) in [(0, -3), (3, 5)] do
    SourceCompilerFeatureSupport.require ((← returned.run [w n]) == .integer expected)
      "imperative body return changed its value"
    for fuel in [0, 11, 89] do returned.checkResume [w n] (.integer expected) fuel
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "failedComposite"
  for n in [0, 3] do fault_resume failed [w n]
  failed.checkCells [w 0]
    [(.word, some (w 0)), (.mapping .bool .word, some (.mapping .bool .word [(.bool false, w 5)])),
      (.word, none), (.word, some (w 0)), (.word, some (w 0))]
  IO.println "builtin imperative function body: actual compiler consumers, Unit fallthrough, returned values, escaped Core control, retained fault writes and resume GREEN"
end Tests.SourceCoreBuiltinImperativeMatchBody
