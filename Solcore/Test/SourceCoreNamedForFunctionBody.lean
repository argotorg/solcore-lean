import Solcore.SourceSemantics.CoreLowering.NamedForFunctionBodyMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual compiler equations and concrete nested named-for trees feed finite
function-body consumers. Checked fixtures retain returns and fault writes through
nested for/while calls and suspended execution. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.NamedForFunctionBody.Certificate.mk
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreNamedForFunctionBody
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup
open NamedForFunctionBody GeneralHeap ReadOnly CompatiblePayload CoreProof

section CompilerConsumers
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {function : Dynamic.Closure} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem actual_compiler_body_preserves
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source expressionSyntax solved reasonAt administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree)
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
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  let certificate := of_extracted accepted projection generated tree errors
  exact certificate.preserves functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem actual_compiler_body_reflects
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source expressionSyntax solved reasonAt administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree)
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
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  let certificate := of_extracted accepted projection generated tree errors
  exact certificate.reflects functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem actual_compiler_body_finite_iff
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source expressionSyntax solved reasonAt administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
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
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  let certificate := of_extracted accepted projection generated tree errors
  exact certificate.finite_iff functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed
end CompilerConsumers


private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "function next(value: Word) returns (Word) { return value + 1; }",
      "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
      "function bad() returns (Word) { let gap: Word; return gap; }",
      "function unitBody(seed: Word) { for (let outer = seed; less(outer, 3); outer += next(0)) { for (let inner = 0; less(inner, 4); inner += next(0)) { if (less(inner, 1)) { continue; } if (less(1, inner)) { break; } } } }",
      "function returnedBody(seed: Word) returns (Word) { for (let outer = seed; less(outer, 3); outer += next(0)) { let inner = 0; while (less(inner, 4)) { inner += next(0); if (less(inner, 2)) { continue; } return next(outer + inner); } } return next(seed); }",
      "function failedBody(seed: Word) returns (Word) { let seen: mapping(Bool => Word); for (let outer = seed; less(outer, 3); outer += next(0)) { let inner = 0; while (less(inner, 4)) { inner += next(0); seen[false] += next(0); if (less(inner, 2)) { continue; } seen[true] = next(outer); return bad(); } } return next(seed); }",
      "function bitNotBody(seed: Word) returns (Word) { let result = seed; for (let count = 0; less(count, 3); count += next(0)) { result ~=; } return result; }",
      "function postFaultBody(seed: Word) returns (Word) { let result = seed; for (let count = 0; less(count, 3); count += bad()) { result += next(0); } return result; }",
      "function initializerFaultBody(seed: Word) returns (Word) { let result = seed; for (let count = bad(); less(count, 3); count += next(0)) { result += next(0); } return result; }"
    ]}] }

private def fault_resume (entry : SourceCompilerFeatureSupport.Entry)
    (arguments : List SourceCompilerFeatureSupport.Value) : IO Unit := do
  let complete ← entry.invoke arguments
  let (token, finalSession) ← match complete.outcome with
    | .failed token session => pure (token, session)
    | _ => throw (IO.userError "named for function fault unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome
    "named for function fault lost its diagnostic"
  let baseline ← SourceCompilerFeatureSupport.get "named for fault snapshot" (← finalSession.snapshot 2048)
  for fuel in [0, 7, 61, 199] do
    let started ← SourceCompilerFeatureSupport.get "named for function suspension"
      (← complete.initial.run complete.key arguments
        {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
      | .failed actual session =>
        let snapshot ← SourceCompilerFeatureSupport.get "named for resumed fault snapshot" (← session.snapshot 2048)
        SourceCompilerFeatureSupport.require (reprStr snapshot.cells == reprStr baseline.cells)
          "named for function resume changed fault writes or source allocation"
        SourceCompilerFeatureSupport.require (actual == token)
          "named for function resume changed the stopping fault"
      | _ => throw (IO.userError "named for function resume ran its continuation")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "named for function checker" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let unitBody ← SourceCompilerFeatureSupport.compileNamed checked "unitBody"
  let returned ← SourceCompilerFeatureSupport.compileNamed checked "returnedBody"
  for (seed, result) in [(0, 3), (2, 5), (4, 5)] do
    SourceCompilerFeatureSupport.require ((← unitBody.run [w seed]) == .unit)
      "named for function Unit fallthrough changed"
    SourceCompilerFeatureSupport.require ((← returned.run [w seed]) == w result)
      "named for function nested return changed"
    for fuel in [0, 7, 61, 199] do
      unitBody.checkResume [w seed] .unit fuel
      returned.checkResume [w seed] (w result) fuel
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "failedBody"
  for seed in [0, 2] do fault_resume failed [w seed]
  let fault ← failed.audit [w 0]
  let heap := (SourceCompilerFeatureSupport.sourceState fault).heap
  let expectedPrefix : List (TypeSystem.Ty × SourceCompilerFeatureSupport.Value) :=
    [(.word, w 0), (.mapping .bool .word, .mapping .bool .word [(.bool false, w 2), (.bool true, w 1)]), (.word, w 0)]
  let expectedCells ← expectedPrefix.mapM fun (type, value) => do
    let raw ← SourceCompilerFeatureSupport.get "named for expected fault prefix" (SourceCompilerFeatureSupport.rawData 128 value)
    pure (SourceTypedRuntime.Cell.mk type (some raw))
  SourceCompilerFeatureSupport.require (reprStr (heap.take expectedCells.length) == reprStr expectedCells)
    "named for function lost writes before the first fault"
  SourceCompilerFeatureSupport.require (reprStr heap.getLast? == reprStr (some (SourceTypedRuntime.Cell.mk .word none)))
    "named for function changed the uninitialized stopping cell"
  SourceCompilerFeatureSupport.require ((← failed.run [w 4]) == w 5)
    "named for function zero-iteration path changed"
  let bitNot ← SourceCompilerFeatureSupport.compileNamed checked "bitNotBody"
  let allOnes := w (2 ^ 256 - 1)
  SourceCompilerFeatureSupport.require ((← bitNot.run [w 0]) == allOnes)
    "named for function bare bit-not changed"
  for fuel in [0, 7, 61, 199] do bitNot.checkResume [w 0] allOnes fuel
  let postFault ← SourceCompilerFeatureSupport.compileNamed checked "postFaultBody"
  let initializerFault ← SourceCompilerFeatureSupport.compileNamed checked "initializerFaultBody"
  fault_resume postFault [w 0]
  fault_resume initializerFault [w 0]
  let postAudit ← postFault.audit [w 0]
  let initialAudit ← initializerFault.audit [w 0]
  let one ← SourceCompilerFeatureSupport.get "named for expected post write" (SourceCompilerFeatureSupport.rawData 128 (w 1))
  let zero ← SourceCompilerFeatureSupport.get "named for expected initial write" (SourceCompilerFeatureSupport.rawData 128 (w 0))
  SourceCompilerFeatureSupport.require
    (reprStr ((SourceCompilerFeatureSupport.sourceState postAudit).heap[1]?) ==
      reprStr (some (SourceTypedRuntime.Cell.mk .word (some one))))
    "named for post fault lost the completed body write"
  SourceCompilerFeatureSupport.require
    (reprStr ((SourceCompilerFeatureSupport.sourceState initialAudit).heap[1]?) ==
      reprStr (some (SourceTypedRuntime.Cell.mk .word (some zero))))
    "named for initializer fault ran the body"
  IO.println "named for function body: actual body passes/finish, finite equivalence, nested for/while, Unit/return, initializer/body/post faults, bare bit-not and resume GREEN"
end Tests.SourceCoreNamedForFunctionBody
