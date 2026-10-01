import Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionBodyMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual compiler equations and concrete nested named-loop trees feed finite
function-body consumers. Checked fixtures retain returns and fault writes through
nested calls and suspended execution. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionBody.Certificate.mk
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreNamedLoopFunctionBody
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup
open NamedLoopFunctionBody GeneralHeap ReadOnly CompatiblePayload CoreProof

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
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
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
    (tree : NamedLoopStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source solved reasonAt administrative registry faults
      context scope true function.body function.resultType type flow)
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
  let certificate := of_extracted accepted projection generated tree
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
    (tree : NamedLoopStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source solved reasonAt administrative registry faults
      context scope true function.body function.resultType type flow)
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
  let certificate := of_extracted accepted projection generated tree
  exact certificate.reflects functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
end CompilerConsumers


private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "function next(value: Word) returns (Word) { return value + 1; }",
      "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
      "function bad() returns (Word) { let gap: Word; return gap; }",
      "function unitBody(seed: Word) { let outer = seed; while (less(outer, 3)) { outer += next(0); let inner = 0; while (less(inner, 4)) { inner += next(0); if (less(inner, 2)) { continue; } if (less(2, inner)) { break; } } } }",
      "function returnedBody(seed: Word) returns (Word) { let outer = seed; while (less(outer, 3)) { outer += next(0); let inner = 0; while (less(inner, 4)) { inner += next(0); if (less(inner, 2)) { continue; } return next(outer + inner); } } return next(outer); }",
      "function failedBody(seed: Word) returns (Word) { let seen: mapping(Bool => Word); let outer = seed; while (less(outer, 3)) { outer += next(0); let inner = 0; while (less(inner, 4)) { inner += next(0); seen[false] += next(0); if (less(inner, 2)) { continue; } seen[true] = next(outer); return bad(); } } return next(outer); }"
    ]}] }

private def fault_resume (entry : SourceCompilerFeatureSupport.Entry)
    (arguments : List SourceCompilerFeatureSupport.Value) : IO Unit := do
  let complete ← entry.invoke arguments
  let (token, finalSession) ← match complete.outcome with
    | .failed token session => pure (token, session)
    | _ => throw (IO.userError "named loop function fault unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome
    "named loop function fault lost its diagnostic"
  let baseline ← SourceCompilerFeatureSupport.get "named loop fault snapshot" (← finalSession.snapshot 2048)
  for fuel in [0, 7, 61, 199] do
    let started ← SourceCompilerFeatureSupport.get "named loop function suspension"
      (← complete.initial.run complete.key arguments
        {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
      | .failed actual session =>
        let snapshot ← SourceCompilerFeatureSupport.get "named loop resumed fault snapshot" (← session.snapshot 2048)
        SourceCompilerFeatureSupport.require (reprStr snapshot.cells == reprStr baseline.cells)
          "named loop function resume changed fault writes or source allocation"
        SourceCompilerFeatureSupport.require (actual == token)
          "named loop function resume changed the stopping fault"
      | _ => throw (IO.userError "named loop function resume ran its continuation")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "named loop function checker" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let unitBody ← SourceCompilerFeatureSupport.compileNamed checked "unitBody"
  let returned ← SourceCompilerFeatureSupport.compileNamed checked "returnedBody"
  for (seed, result) in [(0, 4), (2, 6), (4, 5)] do
    SourceCompilerFeatureSupport.require ((← unitBody.run [w seed]) == .unit)
      "named loop function Unit fallthrough changed"
    SourceCompilerFeatureSupport.require ((← returned.run [w seed]) == w result)
      "named loop function nested return changed"
    for fuel in [0, 7, 61, 199] do
      unitBody.checkResume [w seed] .unit fuel
      returned.checkResume [w seed] (w result) fuel
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "failedBody"
  for seed in [0, 2] do fault_resume failed [w seed]
  let fault ← failed.audit [w 0]
  let heap := (SourceCompilerFeatureSupport.sourceState fault).heap
  let expectedPrefix : List (TypeSystem.Ty × SourceCompilerFeatureSupport.Value) :=
    [(.word, w 0), (.mapping .bool .word, .mapping .bool .word [(.bool false, w 2), (.bool true, w 2)]), (.word, w 1)]
  let expectedCells ← expectedPrefix.mapM fun (type, value) => do
    let raw ← SourceCompilerFeatureSupport.get "named loop expected fault prefix" (SourceCompilerFeatureSupport.rawData 128 value)
    pure (SourceTypedRuntime.Cell.mk type (some raw))
  SourceCompilerFeatureSupport.require (reprStr (heap.take expectedCells.length) == reprStr expectedCells)
    "named loop function lost writes before the first fault"
  SourceCompilerFeatureSupport.require (reprStr heap.getLast? == reprStr (some (SourceTypedRuntime.Cell.mk .word none)))
    "named loop function changed the uninitialized stopping cell"
  SourceCompilerFeatureSupport.require ((← failed.run [w 4]) == w 5)
    "named loop function zero-iteration path changed"
  IO.println "named loop function body: actual compiler consumers, nested control, Unit/return, first fault writes and resume GREEN"
end Tests.SourceCoreNamedLoopFunctionBody
