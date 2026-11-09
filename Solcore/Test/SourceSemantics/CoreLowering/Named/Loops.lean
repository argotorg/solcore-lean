import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedFunctionLoops
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinarySequenceCallers
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories

/-!
# Named loop tests

Named functions with `for` and `while` loops.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForFunctionBody
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
theorem actual_compiler_body_preserves [FunctionCalls.FaultTokens faults]
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
theorem actual_compiler_body_reflects [FunctionCalls.FaultTokens faults]
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
theorem actual_compiler_body_finite_iff [FunctionCalls.FaultTokens faults]
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedLoopFunctionBody
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
theorem actual_compiler_body_preserves [FunctionCalls.FaultTokens faults]
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
theorem actual_compiler_body_reflects [FunctionCalls.FaultTokens faults]
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileSource
/-! Independent Source typing for a named function with a mutable while condition and an outer return. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics

structure Read (source : TypedSource) (binder : TypedBinder) (expected : TypeSystem.Ty) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .reference binder.name (.local binder.id)
  raw : node.rawType = expected
  type : node.type = expected
  requirements : node.requirements = []
  coercions : node.coercions = []

theorem Read.typed {source : TypedSource} {binder : TypedBinder} {expected : TypeSystem.Ty}
    (read : Read source binder expected) {context : SourceSemantics.Context}
    (scheme : binder.scheme = .mono expected) (requirements : binder.schemeRequirements = [])
    (word : TypeAdmissible context expected)
    (lookup : context.LocalLookup binder.id binder.scheme)
    (localRequirements : context.LocalSchemeRequirementsLookup binder.id binder.schemeRequirements) :
    ExpressionHasType source context read.node.id expected := by
  have instantiated : LocalSchemeInstantiationValid context binder expected [] := by
    refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ requirements)
      (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
    · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
    · intro metavariable replacement member; cases member
    · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply expected
    · intro id member; cases member
    · rw [instantiateLocalSchemePredicates, requirements]
      exact .nil
  have typed : ExpressionHasType source context read.node.id read.node.type := by
    refine .intro (lookupExpression?_sound read.found)
      (read.form ▸ ExpressionFormHasRawType.reference (.local lookup localRequirements instantiated))
      read.raw word (Eq.mp (congrArg (TypeAdmissible context) read.type.symm) word) ?_
    rw [read.requirements, read.coercions, read.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context read.node.id type) read.type) typed

abbrev WordRead (source : TypedSource) (binder : TypedBinder) := Read source binder .word
abbrev BoolRead (source : TypedSource) (binder : TypedBinder) := Read source binder .bool

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  flag : TypedBinder
  argument : TypedBinder
  stop : TypedBinder
  conditionRead : BoolRead function.typedBody flag
  stopRead : BoolRead function.typedBody stop
  finalRead : WordRead function.typedBody argument
  assignment : StatementNode
  resolution : AssignmentResolution
  loop : StatementNode
  statement : StatementNode
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOrdinary : flag.comptime = false
  flagOwner : flag.id.owner = function.typedBody.owner
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOrdinary : argument.comptime = false
  argumentFlag : argument.id ≠ flag.id
  stopScheme : stop.scheme = .mono .bool
  stopRequirements : stop.schemeRequirements = []
  stopOrdinary : stop.comptime = false
  stopFlag : stop.id ≠ flag.id
  stopArgument : stop.id ≠ argument.id
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.bool, .word, .bool]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [flag, argument, stop]
  roots : function.typedBody.roots = [.statement loop.id, .statement statement.id]
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal stopRead.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = flag.id
  targetType : resolution.target.type = .bool
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .whileLoop conditionRead.node.id [assignment.id]
  loopType : loop.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.loop.id, shape.statement.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.conditionRead.node, .expression shape.stopRead.node,
    .statement shape.assignment, .statement shape.loop, .expression shape.finalRead.node, .statement shape.statement]

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

theorem FactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.loop.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons flagScheme flagExtended tail =>
    cases tail with
    | cons argumentScheme argumentExtended tail =>
      cases tail with
      | cons stopScheme stopExtended tail =>
        cases tail
        have binders : TypeParameterBindersWellFormed lexical := by
          rw [TypeParameterBindersWellFormed, stopExtended.context_fields.2.2.1,
            argumentExtended.context_fields.2.2.1, flagExtended.context_fields.2.2.1]
          simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
            Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
        have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
        have bool : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
        have flagLookup : lexical.LocalLookup shape.flag.id shape.flag.scheme := by
          cases stopExtended
          cases argumentExtended
          exact .tail shape.stopFlag (.tail shape.argumentFlag flagExtended.local_self)
        have flagRequirements : lexical.LocalSchemeRequirementsLookup shape.flag.id shape.flag.schemeRequirements := by
          cases stopExtended
          cases argumentExtended
          exact .tail shape.stopFlag (.tail shape.argumentFlag flagExtended.local_scheme_requirements_self)
        have conditionTyped := shape.conditionRead.typed flagScheme shape.flagRequirements bool flagLookup flagRequirements
        have rhsTyped := shape.stopRead.typed stopScheme shape.stopRequirements bool
          stopExtended.local_self stopExtended.local_scheme_requirements_self
        have finalTyped := shape.finalRead.typed argumentScheme shape.argumentRequirements word
          (by cases stopExtended; exact .tail shape.stopArgument argumentExtended.local_self)
          (by cases stopExtended; exact .tail shape.stopArgument argumentExtended.local_scheme_requirements_self)
        have writable : WritableLocal lexical shape.resolution.target.root .bool := by
          rw [shape.targetRoot]
          exact .intro flagLookup (flagScheme.symm ▸ SchemeWellFormed.monoAdmissible bool)
            (by rw [flagScheme]; rfl) (by rw [flagScheme]; rfl)
        have assignmentTyped : SourceAssignmentHasType function.typedBody lexical shape.resolution .equal shape.stopRead.node.id :=
          .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) rhsTyped shape.assignmentRequirements
        have assigned : StatementHasType function.typedBody ⟨.word, 1⟩ lexical shape.assignment.id lexical ordinary :=
          .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
        have loopTyped := StatementHasType.whileLoop (control := ⟨.word, 0⟩)
          (lookupStatement?_sound shape.loopFound) shape.loopForm conditionTyped (.singleton assigned) shape.loopType
        have returned := StatementHasType.returnValue (control := ⟨.word, 0⟩)
          (lookupStatement?_sound shape.statementFound) shape.statementForm finalTyped shape.statementType
        exact ⟨lexical, .cons loopTyped (.singleton returned)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function choose(flag: Bool, value: Word, stop: Bool) returns (Word) { while (flag) { flag = stop; } return value; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeRead (source : TypedSource) (binder : TypedBinder) (node : ExpressionNode) (expected : TypeSystem.Ty) : IO (Read source binder expected) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "read lookup"
  let ⟨form⟩ ← observed (node.form = .reference binder.name (.local binder.id)) "read binder"
  let ⟨raw⟩ ← observed (node.rawType = expected) "read raw Word"
  let ⟨type⟩ ← observed (node.type = expected) "read Word"
  let ⟨requirements⟩ ← observed (node.requirements = []) "read requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "read coercions"
  return { node, found, form, raw, type, requirements, coercions }

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FactoryShape function signature) := do
  let [flag, argument, stop] := function.typedBody.inputs | throw (IO.userError "named while inputs")
  let [.expression condition, .expression next, .statement assignment,
      .statement loop, .expression result, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "named while graph")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "bare flag assignment")
  let conditionRead ← observeRead function.typedBody flag condition .bool
  let stopRead ← observeRead function.typedBody stop next .bool
  let finalRead ← observeRead function.typedBody argument result .word
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "named while flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "named while flagRequirements"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "named while flagOrdinary"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "named while flagOwner"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "named while argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "named while argumentRequirements"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "named while argumentOrdinary"
  let ⟨argumentFlag⟩ ← observed (argument.id ≠ flag.id) "named while argumentFlag"
  let ⟨stopScheme⟩ ← observed (stop.scheme = .mono .bool) "named while stopScheme"
  let ⟨stopRequirements⟩ ← observed (stop.schemeRequirements = []) "named while stopRequirements"
  let ⟨stopOrdinary⟩ ← observed (stop.comptime = false) "named while stopOrdinary"
  let ⟨stopFlag⟩ ← observed (stop.id ≠ flag.id) "named while stopFlag"
  let ⟨stopArgument⟩ ← observed (stop.id ≠ argument.id) "named while stopArgument"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "named while parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.bool, .word, .bool]) "named while inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "named while returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [flag, argument, stop]) "named while inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement loop.id, .statement statement.id]) "named while roots"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "named while assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal stopRead.node.id) "named while assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "named while assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = flag.id) "named while targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .bool) "named while targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "named while targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "named while assignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "named while loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop conditionRead.node.id [assignment.id]) "named while loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "named while loopType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "named while statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "named while statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "named while statementType"
  return { flag, argument, stop, conditionRead, stopRead, finalRead, assignment, resolution, loop, statement, flagScheme, flagRequirements, flagOrdinary, flagOwner, argumentScheme, argumentRequirements, argumentOrdinary, argumentFlag, stopScheme, stopRequirements, stopOrdinary, stopFlag, stopArgument, parameters, inputTypes, returns, inputs, roots, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : program.functions = [function]
  signatures : program.signatures.functions = [signature]
  methods : program.methods = []
  sourceShape : FactoryShape function signature
  nodes : function.typedBody.nodes = sourceShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [function], [signature] =>
      let sourceShape ← observeShape function signature
      if methods : program.methods = [] then
        let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
          functions := by
            intro actual member candidate candidateMember _accepted
            have sameFunction : actual = function := by simpa only [functions, List.mem_singleton] using member
            have sameSignature : candidate = signature := by simpa only [signatures, List.mem_singleton] using candidateMember
            subst actual candidate
            exact sourceShape.statementTyping program.signatures
          methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete named while graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected named while methods")
    | _, _ => throw (IO.userError "named while declaration count")

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForSource
/-! Independent Source typing for a scoped for-header local, body mutation,
post update and restored outer return. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedWhile.Read

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  value : TypedBinder
  argument : TypedBinder
  running : TypedBinder
  stop : TypedBinder
  flag : TypedBinder
  initialRead : Read function.typedBody running .bool
  conditionRead : Read function.typedBody flag .bool
  argumentRead : Read function.typedBody argument .word
  stopRead : Read function.typedBody stop .bool
  finalRead : Read function.typedBody value .word
  assignment : StatementNode
  resolution : AssignmentResolution
  postResolution : AssignmentResolution
  loop : StatementNode
  statement : StatementNode
  valueScheme : value.scheme = .mono .word
  valueRequirements : value.schemeRequirements = []
  valueOrdinary : value.comptime = false
  valueOwner : value.id.owner = function.typedBody.owner
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOrdinary : argument.comptime = false
  argumentOwner : argument.id.owner = function.typedBody.owner
  runningScheme : running.scheme = .mono .bool
  runningRequirements : running.schemeRequirements = []
  runningOrdinary : running.comptime = false
  runningOwner : running.id.owner = function.typedBody.owner
  stopScheme : stop.scheme = .mono .bool
  stopRequirements : stop.schemeRequirements = []
  stopOrdinary : stop.comptime = false
  stopOwner : stop.id.owner = function.typedBody.owner
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOrdinary : flag.comptime = false
  flagOwner : flag.id.owner = function.typedBody.owner
  argumentValue : argument.id ≠ value.id
  runningValue : running.id ≠ value.id
  runningArgument : running.id ≠ argument.id
  stopValue : stop.id ≠ value.id
  stopArgument : stop.id ≠ argument.id
  stopRunning : stop.id ≠ running.id
  flagValue : flag.id ≠ value.id
  flagArgument : flag.id ≠ argument.id
  flagRunning : flag.id ≠ running.id
  flagStop : flag.id ≠ stop.id
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word, .word, .bool, .bool]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [value, argument, running, stop]
  roots : function.typedBody.roots = [.statement loop.id, .statement statement.id]
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal argumentRead.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = value.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  postRoot : postResolution.target.root = flag.id
  postType : postResolution.target.type = .bool
  postBare : postResolution.target.projections = []
  postRequirements : postResolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .forLoop [.letDecl flag (some initialRead.node.id)] conditionRead.node.id [.assignValue postResolution .equal stopRead.node.id] [assignment.id]
  loopType : loop.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.loop.id, shape.statement.id]
def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.conditionRead.node, .expression shape.argumentRead.node,
    .statement shape.assignment, .expression shape.stopRead.node, .statement shape.loop,
    .expression shape.finalRead.node, .statement shape.statement]

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

theorem FactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.loop.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons valueScheme valueExtended tail =>
    cases tail with
    | cons argumentScheme argumentExtended tail =>
      cases tail with
      | cons runningScheme runningExtended tail =>
        cases tail with
        | cons stopScheme stopExtended tail =>
          cases tail
          have binders : TypeParameterBindersWellFormed lexical := by
            rw [TypeParameterBindersWellFormed, stopExtended.context_fields.2.2.1,
              runningExtended.context_fields.2.2.1, argumentExtended.context_fields.2.2.1,
              valueExtended.context_fields.2.2.1]
            simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
              Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
          have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
          have bool : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
          let loopContext := lexical.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
          have flagExtended : BinderExtends function.typedBody.owner lexical shape.flag loopContext := by
            apply BinderExtends.intro
            · exact {owned := shape.flagOwner
                     scheme := shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible bool
                     quantified_fresh := by rw [shape.flagScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
                     monomorphic_requirements_empty := fun _ => shape.flagRequirements}
            · cases stopExtended; cases runningExtended; cases argumentExtended; cases valueExtended
              simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
                Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
                Context.withSolvedRequirements, Context.withResidualTypeVariables,
                shape.flagValue, shape.flagArgument, shape.flagRunning, shape.flagStop]
          have loopWord : TypeAdmissible loopContext .word := ⟨binders, .builtin .word⟩
          have loopBool : TypeAdmissible loopContext .bool := ⟨binders, .builtin .bool⟩
          have initialTyped := shape.initialRead.typed runningScheme shape.runningRequirements bool
            (by cases stopExtended; exact .tail shape.stopRunning runningExtended.local_self)
            (by cases stopExtended; exact .tail shape.stopRunning runningExtended.local_scheme_requirements_self)
          have initialized : ForItemsHaveType function.typedBody ⟨.word, 0⟩ lexical
              [.letDecl shape.flag (some shape.initialRead.node.id)] loopContext := by
            refine .cons (.letInitialized ?_ ?_ ?_ flagExtended) (.nil _ _)
            · simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using initialTyped
            · rw [shape.flagScheme]; rfl
            · rw [shape.flagScheme]; rfl
          have conditionTyped := shape.conditionRead.typed shape.flagScheme shape.flagRequirements loopBool
            flagExtended.local_self flagExtended.local_scheme_requirements_self
          have argumentTyped := shape.argumentRead.typed argumentScheme shape.argumentRequirements loopWord
            (by cases stopExtended; cases runningExtended
                exact .tail shape.flagArgument (.tail shape.stopArgument (.tail shape.runningArgument argumentExtended.local_self)))
            (by cases stopExtended; cases runningExtended
                exact .tail shape.flagArgument (.tail shape.stopArgument (.tail shape.runningArgument argumentExtended.local_scheme_requirements_self)))
          have stopTyped := shape.stopRead.typed stopScheme shape.stopRequirements loopBool
            (.tail shape.flagStop stopExtended.local_self) (.tail shape.flagStop stopExtended.local_scheme_requirements_self)
          have valueLookup : lexical.LocalLookup shape.value.id shape.value.scheme := by
            cases stopExtended; cases runningExtended; cases argumentExtended
            exact .tail shape.stopValue (.tail shape.runningValue (.tail shape.argumentValue valueExtended.local_self))
          have valueRequirements : lexical.LocalSchemeRequirementsLookup shape.value.id shape.value.schemeRequirements := by
            cases stopExtended; cases runningExtended; cases argumentExtended
            exact .tail shape.stopValue (.tail shape.runningValue (.tail shape.argumentValue valueExtended.local_scheme_requirements_self))
          have finalTyped := shape.finalRead.typed valueScheme shape.valueRequirements word valueLookup valueRequirements
          have valueWritable : WritableLocal loopContext shape.resolution.target.root .word := by
            rw [shape.targetRoot]
            exact .intro (.tail shape.flagValue valueLookup)
              (valueScheme.symm ▸ SchemeWellFormed.monoAdmissible loopWord)
              (by rw [valueScheme]; rfl) (by rw [valueScheme]; rfl)
          have assignmentTyped : SourceAssignmentHasType function.typedBody loopContext shape.resolution .equal shape.argumentRead.node.id :=
            .equal (.intro valueWritable (by rw [shape.targetBare]; exact .nil _) shape.targetType)
              argumentTyped shape.assignmentRequirements
          have assigned : StatementHasType function.typedBody ⟨.word, 1⟩ loopContext shape.assignment.id loopContext ordinary :=
            .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
          have flagWritable : WritableLocal loopContext shape.postResolution.target.root .bool := by
            rw [shape.postRoot]
            exact .intro flagExtended.local_self (shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible loopBool)
              (by rw [shape.flagScheme]; rfl) (by rw [shape.flagScheme]; rfl)
          have postTyped : ForItemsHaveType function.typedBody ⟨.word, 1⟩ loopContext
              [.assignValue shape.postResolution .equal shape.stopRead.node.id] loopContext :=
            .cons (.assignValue (.equal (.intro flagWritable (by rw [shape.postBare]; exact .nil _) shape.postType)
              stopTyped shape.postRequirements)) (.nil _ _)
          have loopTyped := StatementHasType.forLoop (control := ⟨.word, 0⟩)
            (lookupStatement?_sound shape.loopFound) shape.loopForm initialized conditionTyped (.singleton assigned) postTyped shape.loopType
          have returned := StatementHasType.returnValue (control := ⟨.word, 0⟩)
            (lookupStatement?_sound shape.statementFound) shape.statementForm finalTyped shape.statementType
          exact ⟨lexical, .cons loopTyped (.singleton returned)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function update(value: Word, next: Word, running: Bool, done: Bool) returns (Word) { for (let flag: Bool = running; flag; flag = done) { value = next; } return value; }"}] }
private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)
abbrev observeRead := Tests.SourceCoreNamedWhile.observeRead

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FactoryShape function signature) := do
  let [value, argument, running, stop] := function.typedBody.inputs | throw (IO.userError "named for inputs")
  let [.expression initial, .expression condition, .expression rhs, .statement assignment,
       .expression post, .statement loop, .expression finalNode, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "named for nodes")
  let .forLoop [.letDecl flag _] _ [.assignValue postResolution .equal _] _ := loop.form
    | throw (IO.userError "named for header")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "named for assignment")
  let initialRead ← observeRead function.typedBody running initial .bool
  let conditionRead ← observeRead function.typedBody flag condition .bool
  let argumentRead ← observeRead function.typedBody argument rhs .word
  let stopRead ← observeRead function.typedBody stop post .bool
  let finalRead ← observeRead function.typedBody value finalNode .word
  let ⟨valueScheme⟩ ← observed (value.scheme = .mono .word) "named for valueScheme"
  let ⟨valueRequirements⟩ ← observed (value.schemeRequirements = []) "named for valueRequirements"
  let ⟨valueOrdinary⟩ ← observed (value.comptime = false) "named for valueOrdinary"
  let ⟨valueOwner⟩ ← observed (value.id.owner = function.typedBody.owner) "named for valueOwner"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "named for argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "named for argumentRequirements"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "named for argumentOrdinary"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "named for argumentOwner"
  let ⟨runningScheme⟩ ← observed (running.scheme = .mono .bool) "named for runningScheme"
  let ⟨runningRequirements⟩ ← observed (running.schemeRequirements = []) "named for runningRequirements"
  let ⟨runningOrdinary⟩ ← observed (running.comptime = false) "named for runningOrdinary"
  let ⟨runningOwner⟩ ← observed (running.id.owner = function.typedBody.owner) "named for runningOwner"
  let ⟨stopScheme⟩ ← observed (stop.scheme = .mono .bool) "named for stopScheme"
  let ⟨stopRequirements⟩ ← observed (stop.schemeRequirements = []) "named for stopRequirements"
  let ⟨stopOrdinary⟩ ← observed (stop.comptime = false) "named for stopOrdinary"
  let ⟨stopOwner⟩ ← observed (stop.id.owner = function.typedBody.owner) "named for stopOwner"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "named for flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "named for flagRequirements"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "named for flagOrdinary"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "named for flagOwner"
  let ⟨argumentValue⟩ ← observed (argument.id ≠ value.id) "named for argumentValue"
  let ⟨runningValue⟩ ← observed (running.id ≠ value.id) "named for runningValue"
  let ⟨runningArgument⟩ ← observed (running.id ≠ argument.id) "named for runningArgument"
  let ⟨stopValue⟩ ← observed (stop.id ≠ value.id) "named for stopValue"
  let ⟨stopArgument⟩ ← observed (stop.id ≠ argument.id) "named for stopArgument"
  let ⟨stopRunning⟩ ← observed (stop.id ≠ running.id) "named for stopRunning"
  let ⟨flagValue⟩ ← observed (flag.id ≠ value.id) "named for flagValue"
  let ⟨flagArgument⟩ ← observed (flag.id ≠ argument.id) "named for flagArgument"
  let ⟨flagRunning⟩ ← observed (flag.id ≠ running.id) "named for flagRunning"
  let ⟨flagStop⟩ ← observed (flag.id ≠ stop.id) "named for flagStop"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "named for parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word, .word, .bool, .bool]) "named for inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "named for returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [value, argument, running, stop]) "named for inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement loop.id, .statement statement.id]) "named for roots"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "named for assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal argumentRead.node.id) "named for assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "named for assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = value.id) "named for targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "named for targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "named for targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "named for assignmentRequirements"
  let ⟨postRoot⟩ ← observed (postResolution.target.root = flag.id) "named for postRoot"
  let ⟨postType⟩ ← observed (postResolution.target.type = .bool) "named for postType"
  let ⟨postBare⟩ ← observed (postResolution.target.projections = []) "named for postBare"
  let ⟨postRequirements⟩ ← observed (postResolution.requirements = []) "named for postRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "named for loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .forLoop [.letDecl flag (some initialRead.node.id)] conditionRead.node.id [.assignValue postResolution .equal stopRead.node.id] [assignment.id]) "named for loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "named for loopType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "named for statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "named for statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "named for statementType"
  return { value, argument, running, stop, flag, initialRead, conditionRead, argumentRead, stopRead, finalRead, assignment, resolution, postResolution, loop, statement, valueScheme, valueRequirements, valueOrdinary, valueOwner, argumentScheme, argumentRequirements, argumentOrdinary, argumentOwner, runningScheme, runningRequirements, runningOrdinary, runningOwner, stopScheme, stopRequirements, stopOrdinary, stopOwner, flagScheme, flagRequirements, flagOrdinary, flagOwner, argumentValue, runningValue, runningArgument, stopValue, stopArgument, stopRunning, flagValue, flagArgument, flagRunning, flagStop, parameters, inputTypes, returns, inputs, roots, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, postRoot, postType, postBare, postRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : program.functions = [function]
  signatures : program.signatures.functions = [signature]
  methods : program.methods = []
  sourceShape : FactoryShape function signature
  nodes : function.typedBody.nodes = sourceShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [function], [signature] =>
      let sourceShape ← observeShape function signature
      if methods : program.methods = [] then
        let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
          functions := by
            intro actual member candidate candidateMember _accepted
            have sameFunction : actual = function := by simpa only [functions, List.mem_singleton] using member
            have sameSignature : candidate = signature := by simpa only [signatures, List.mem_singleton] using candidateMember
            subst actual candidate
            exact sourceShape.statementTyping program.signatures
          methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete named for graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected named for methods")
    | _, _ => throw (IO.userError "named for declaration count")

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForFixture
/-! Actual compilation, selected inventory and static loop observations for
one named Bool/Word function with a mutable loop condition and an outer return. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics

private def observeFact (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program
  recipePrepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe

def compiledFixture : IO CompiledFixture := do
  let checked ← checkedFixture
  let signature :: _ := checked.program.signatures.functions
    | throw (IO.userError "factory signature missing")
  let seeds := [SourceCompiler.Seed.declaration signature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
  match generated : SourceCoreCompiler.compileChecked checked.program seeds options with
  | .error error => throw (IO.userError (reprStr error))
  | .ok source =>
    match selected : source.artifact? with
    | none => throw (IO.userError "factory cached artifact missing")
    | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (IO.userError (reprStr error))
      | .ok recipe =>
        match facade : SourceCoreExecution.prepare source with
        | .error error => throw (IO.userError (reprStr error))
        | .ok facadeCompiled =>
          have accepted : SourceCompiler.compileChecked checked.program seeds options = .ok facadeCompiled := by
            simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError,
              bind, Except.bind] using facade
          have sameProgram : recipe.compiled.sourceProgram = checked.program :=
            (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
              ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))
          return {
            toCheckedFixture := checked
            seeds := seeds
            options := options
            facadeCompiled := facadeCompiled
            accepted := accepted
            recipe := recipe
            issued := CoreLowering.RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade
            sameProgram := sameProgram
            recipePrepared := by rw [SourceCoreIndexedSession.Recipe.prepare_compiled prepared]; exact prepared }

theorem CompiledFixture.prepared (fixture : CompiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ fixture.recipe.compiled.validationPlan.specializations) :
    Nonempty (CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row) :=
  CoreLowering.RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued member

theorem CompiledFixture.source_wellFormed (fixture : CompiledFixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  rw [fixture.sameProgram]
  exact fixture.wellFormed

structure ActualHeader (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) where
  prepared : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row
  header : CoreLowering.CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
    (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  aligned : CoreLowering.RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
    (CoreLowering.CallableNamedMetadata.instantiation row) header
  diagnostic : CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared



open CoreLowering

structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  shape : FactoryShape row.function fixture.signature
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = fixture.signature.id
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .word
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  nodes : row.function.typedBody.nodes = shape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries

abbrev ObservedFactory.inputs {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.inputs
abbrev ObservedFactory.roots {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.roots
abbrev ObservedFactory.flag {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.flag
abbrev ObservedFactory.argument {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argument
abbrev ObservedFactory.binderScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argumentScheme

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observeFact (key = row.key) "captured factory exact key"
    return ⟨by rw [accepted, same]⟩

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    let shape ← observeShape row.function fixture.signature
    match entries : fixture.recipe.compiled.indexed.entries with
    | [entry] =>
      let ⟨sourceOwner⟩ ← observeFact (row.function.typedBody.owner = fixture.signature.id) "named while source owner"
      let ⟨parameters⟩ ← observeFact (row.parameterSubstitution = []) "named while substitution"
      let ⟨closed⟩ ← observeFact (row.assumptions = []) "named while assumptions"
      let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .word) "named while result type"
      let ⟨ordinary⟩ ← observeFact (row.function.returnComptime = false) "named while ordinary result"
      let ⟨target⟩ ← observeTarget fixture row
      let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = shape.nodeList) "named while nodes"
      let ⟨noLocals⟩ ← observeFact (fixture.recipe.compiled.indexed.base.locals.bindings = []) "named while local catalog"
      let ⟨profile⟩ ← observeFact (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "named while profile"
      return {
        row, shape, sourceOwner, parameters, closed, ordinary, resultType, target, nodes, noLocals, profile, entry
        member := by rw [rows]; exact .head []
        entryMember := by rw [entries]; exact .head [] }
    | _ => throw (IO.userError "named while entry count")
  | _ => throw (IO.userError "named while specialization count")

/-- The staged selection is obtained from the retained callable table and
original sidecar of the concrete compiler result. -/
structure ObservedStages (fixture : CompiledFixture)
    (observed : ObservedFactory fixture) where
  singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      if singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1 then
        match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
            (.named observed.row.key) with
        | .error error => throw (IO.userError (reprStr error))
        | .ok descriptor => return ⟨singletonGlobal, descriptor, native, present, sidecar, issued⟩
      else throw (IO.userError "factory global count")

def ObservedStages.registry {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem ActualHeader.complete {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [actual.header] := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled actual.prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : actual.prepared.index = 0 := by omega
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [stages.singletonGlobal] at bound
  have indexZero : index = 0 := by omega
  refine ⟨actual.header, .head [], actual.aligned.slot.trans (zero.trans indexZero.symm), ?_⟩
  rw [actual.aligned.named]
  rw [zero] at selected
  rw [indexZero] at found
  exact Option.some.inj (selected.symm.trans found)

theorem bootstrap_zero (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)) :
    owner.key.capturePrefix = 0 := by
  have bound := owner.position.isLt
  change owner.position.val < 1 at bound
  have zero : owner.position.val = 0 := by omega
  simp only [CallableIndexedOwnedFunctionValues.OwnedKey.key,
    CallableIndexedOwnedPreparedBootstrapRootState.keys,
    CallableIndexedOwnedPreparedBootstrapRootState.key, zero, List.getElem_cons_zero]


theorem ObservedStages.inventory {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row, actual.header = packet.header := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  have target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok prepared.named.signature.key := by
    rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
    exact observed.target
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : prepared.index = 0 := by omega
  have globals : fixture.recipe.compiled.indexed.base.globals = [prepared.named.signature] := by
    obtain ⟨first, single⟩ := List.length_eq_one_iff.mp stages.singletonGlobal
    rw [single, zero] at selected
    have same : first = prepared.named.signature := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
    exact single.trans (congrArg (fun value => [value]) same)
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := by
      intro binder member
      rw [observed.inputs] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact observed.shape.valueOrdinary
      · exact observed.shape.argumentOrdinary
      · exact observed.shape.runningOrdinary
      · exact observed.shape.stopOrdinary
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl⟩



theorem ObservedStages.source_of_cached {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 1 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using stages.singletonGlobal
  have before := (List.getElem?_eq_some_iff.mp actual.prepared.selected).1
  have after := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at before after
  have same : index = actual.prepared.index := by omega
  rw [same, actual.prepared.selected] at selected
  cases Option.some.inj selected
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem CompiledFixture.signature_member (fixture : CompiledFixture) :
    fixture.signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
  rw [fixture.sameProgram, fixture.signatures]
  exact .head []

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same


theorem ActualHeader.body {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.body = observed.shape.body := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = [observed.shape.loop.id, observed.shape.statement.id]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForFacts
/-! Finite observations identify all original reads and exclude anonymous code.
They establish compiler coverage without an execution or body-meaning premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word, .word, .bool, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.shape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.shape.valueScheme, observed.shape.argumentScheme, observed.shape.runningScheme, observed.shape.stopScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem ActualHeader.output {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.result_type] at projected
  exact (Except.ok.inj projected).symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

theorem ObservedFactory.read_cases {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node) :
    node = observed.shape.initialRead.node ∨ node = observed.shape.conditionRead.node ∨ node = observed.shape.argumentRead.node ∨ node = observed.shape.stopRead.node ∨ node = observed.shape.finalRead.node := by
  have member := found.1
  rw [observed.nodes] at member
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton, Node.expression.injEq,
    reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedFactory.metadata {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.row.function.typedBody := by
  apply CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named _ observed.noLocals
  intro id node found
  rcases observed.read_cases (lookupExpression?_sound found) with same | same | same | same | same
  all_goals subst node
  · exact .inl ⟨_, _, observed.shape.initialRead.form, observed.shape.initialRead.requirements, observed.shape.initialRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.conditionRead.form, observed.shape.conditionRead.requirements, observed.shape.conditionRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.argumentRead.form, observed.shape.argumentRead.requirements, observed.shape.argumentRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.stopRead.form, observed.shape.stopRead.requirements, observed.shape.stopRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.finalRead.form, observed.shape.finalRead.requirements, observed.shape.finalRead.coercions⟩

theorem ObservedFactory.no_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.read_cases found with same | same | same | same | same
  all_goals subst node
  · rw [observed.shape.initialRead.form] at form; cases form
  · rw [observed.shape.conditionRead.form] at form; cases form
  · rw [observed.shape.argumentRead.form] at form; cases form
  · rw [observed.shape.stopRead.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form

theorem ObservedFactory.flag_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.flag.id = .ok observed.shape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form, observed.shape.conditionRead.form,
    observed.shape.argumentRead.form, observed.shape.stopRead.form, observed.shape.finalRead.form,
    observed.shape.assignmentForm, observed.shape.loopForm, observed.shape.statementForm, observed.shape.flagOwner,
    observed.shape.flagScheme, TypeSystem.Scheme.mono, observed.shape.flagRequirements,
    Ne.symm observed.shape.flagValue, Ne.symm observed.shape.flagArgument,
    Ne.symm observed.shape.flagRunning, Ne.symm observed.shape.flagStop]

theorem ObservedFactory.value_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.value.id = .ok observed.shape.value := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form, observed.shape.conditionRead.form,
    observed.shape.argumentRead.form, observed.shape.stopRead.form, observed.shape.finalRead.form,
    observed.shape.assignmentForm, observed.shape.loopForm, observed.shape.statementForm, observed.shape.valueOwner,
    observed.shape.valueScheme, TypeSystem.Scheme.mono, observed.shape.valueRequirements,
    observed.shape.argumentValue, observed.shape.runningValue, observed.shape.stopValue, observed.shape.flagValue]

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.loop.id, observed.shape.statement.id] := actual.body

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForRuntime
/-! Actual public calls execute one iteration and then zero iterations of the accepted named for.
The second call consumes the exact session returned by the first. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def firstInput : Core.Word := Core.Word.ofNatModulo 11
def firstValue : Core.Word := Core.Word.ofNatModulo 12
def secondInput : Core.Word := Core.Word.ofNatModulo 22
def secondValue : Core.Word := Core.Word.ofNatModulo 23

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

structure ObservedCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (flag : Bool) (input value : Core.Word) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word input, .word value, .bool flag, .bool false] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word input, .word value, .bool flag, .bool false] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word (if flag then value else input)

def observeCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (flag : Bool) (input value : Core.Word) : IO (ObservedCall observed session flag input value) := do
  match started : session.start observed.row.key [.word input, .word value, .bool flag, .bool false] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt observed.row.key [.word input, .word value, .bool flag, .bool false] runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "named for failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "named for exhausted its execution budget")
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word (if flag then value else input) then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "named for returned an unexpected Word")

structure ObservedInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedCall observed session true firstInput firstValue

def observeInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedInitial fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "named for bootstrap exhausted")
  | .ready session =>
    let call ← observeCall observed session true firstInput firstValue
    return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready, call⟩

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  initial : ObservedInitial fixture observed
  next : ObservedCall observed initial.call.completion.session false secondInput secondValue

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let initial ← observeInitial fixture observed
  let next ← observeCall observed initial.call.completion.session false secondInput secondValue
  return ⟨initial, next⟩

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedInitial.start_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.call.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word firstInput, .word firstValue, .bool true, .bool false]
        runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.call.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩

theorem ObservedInitial.metadata_at_start {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word firstInput, .word firstValue, .bool true, .bool false]
      runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .word firstInput
  · exact .word firstValue
  · exact .bool true
  · exact .bool false

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForSyntax
/-! The original typed for loop supplies its initialized flag, condition, body write,
post write and restored suffix. Every expression is an actual local read. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original

private theorem returning {source : TypedSource} {context final : SourceSemantics.Context}
    {binder : TypedBinder} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (read : Read source binder .word)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some read.node.id))
    (annotation : node.type = .word) (leaf : approved read.node.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation read.found read.type
        (by simpa only [read.type] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder rhsBinder : TypedBinder} {payload : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (read : Read source rhsBinder payload) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal read.node.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved read.node.id)
    (typed : SourceAssignmentHasType source context assignment .equal read.node.id)
    (remaining : GenericImperativeMatch.Syntax source approved context (.statements mode rest) .word) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal target rhs _requirements =>
      cases target with
      | intro writable projections target =>
          apply GenericImperativeMatch.Syntax.assign found form
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [scheme, bare, targetType]
            exact .nil _
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [bare] at projections
            cases projections
            have word := target.symm.trans targetType
            simpa only [word, scheme, TypeSystem.Scheme.mono] using writable
          · simpa only [target] using rhs
          · exact .inl rfl
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨leaf, read.node, read.found, by simpa only [← target, targetType, read.type] using rhs⟩
          · exact remaining

private theorem header_assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder rhsBinder : TypedBinder} {payload : TypeSystem.Ty}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {rest : List ForItemForm}
    (read : Read source rhsBinder payload)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved read.node.id)
    (typed : SourceAssignmentHasType source context assignment .equal read.node.id)
    (remaining : GenericForHeader.Syntax source approved context rest) :
    GenericForHeader.Syntax source approved context (.assignValue assignment .equal read.node.id :: rest) := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal target rhs _requirements =>
      cases target with
      | intro writable projections target =>
          apply GenericForHeader.Syntax.assign
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [scheme, bare, targetType]
            exact .nil _
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [bare] at projections
            cases projections
            have word := target.symm.trans targetType
            simpa only [word, scheme, TypeSystem.Scheme.mono] using writable
          · simpa only [target] using rhs
          · exact .inl rfl
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨leaf, read.node, read.found, by simpa only [← target, targetType, read.type] using rhs⟩
          · exact remaining

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.row.function.typedBody true observed.shape.body :=
  .forLoop observed.shape.loopFound observed.shape.loopForm (.initialized .nil)
    (.assign (.inl rfl) observed.shape.postBare .nil)
    (.assign observed.shape.assignmentFound observed.shape.assignmentForm (.inl rfl) observed.shape.targetBare .nil)
    (.returnValue [] observed.shape.statementFound observed.shape.statementForm)

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.initialRead.node.id, observed.shape.conditionRead.node.id,
    observed.shape.argumentRead.node.id, observed.shape.stopRead.node.id, observed.shape.finalRead.node.id]

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context observed.shape.body final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true observed.shape.body) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.loopFound first
  rw [observed.shape.loopForm] at firstForm
  cases firstForm with
  | forLoop initializerTyped conditionTyped bodyTyped postTyped =>
    apply GenericImperativeMatch.Syntax.forLoop observed.shape.loopFound observed.shape.loopForm observed.shape.loopType
    · cases initializerTyped with
      | cons initial rest =>
        cases rest
        cases initial with
        | letInitialized initializer mono generalized extended =>
          apply GenericImperativeMatch.Syntax.initializerInitialized observed.flag_declaration mono extended
            (by simp [observed.inputs, Ne.symm observed.shape.flagValue, Ne.symm observed.shape.flagArgument,
              Ne.symm observed.shape.flagRunning, Ne.symm observed.shape.flagStop])
            observed.shape.initialRead.found
            (by rw [observed.shape.initialRead.type, observed.shape.flagScheme]; rfl)
            (by simpa only [observed.shape.initialRead.type, observed.shape.flagScheme, TypeSystem.Scheme.mono] using initializer)
            (leaf _ (by simp [readIds]))
          apply GenericImperativeMatch.Syntax.initializersDone observed.shape.conditionRead.found observed.shape.conditionRead.type
            (by simpa only [observed.shape.conditionRead.type] using conditionTyped) (leaf _ (by simp [readIds]))
          · obtain ⟨_, _, _, assignedHead, _⟩ := head_tail bodyTyped
            have assignment := form_at unique observed.shape.assignmentFound assignedHead
            rw [observed.shape.assignmentForm] at assignment
            cases assignment with
            | assignValue assignmentTyped =>
              exact assigned observed.shape.argumentRead observed.shape.assignmentFound observed.shape.assignmentForm
                (by rw [observed.shape.targetRoot]; exact observed.value_declaration)
                observed.shape.valueScheme observed.shape.targetBare observed.shape.targetType
                (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
          · cases postTyped with
            | cons post tail =>
              cases post with
              | assignValue assignmentTyped =>
                exact header_assigned observed.shape.stopRead
                  (by rw [observed.shape.postRoot]; exact observed.flag_declaration)
                  observed.shape.flagScheme observed.shape.postBare observed.shape.postType
                  (leaf _ (by simp [readIds])) assignmentTyped .nil
        | letInitializedGeneralized polymorphic _ _ _ _ =>
          exact False.elim (polymorphic (by rw [observed.shape.flagScheme]; rfl))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.finalRead observed.shape.statementFound observed.shape.statementForm
        observed.shape.statementType (leaf _ (by simp [readIds])) returningHead

theorem ActualHeader.syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericImperativeMatch.Syntax actual.header.function.source (fun id => ∃ node name binderId,
      actual.header.function.source.lookupExpression? id = some node ∧ node.form = .reference name (.local binderId))
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.shape.roots, actual.result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.body, actual.result_type]
  apply observed.body_syntax (actual.source ▸ actual.header.unique) _ typed
  intro id member
  simp only [ObservedFactory.readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
  · exact ⟨_, _, _, observed.shape.conditionRead.found, observed.shape.conditionRead.form⟩
  · exact ⟨_, _, _, observed.shape.argumentRead.found, observed.shape.argumentRead.form⟩
  · exact ⟨_, _, _, observed.shape.stopRead.found, observed.shape.stopRead.form⟩
  · exact ⟨_, _, _, observed.shape.finalRead.found, observed.shape.finalRead.form⟩

theorem ActualHeader.branching_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.body]
  exact observed.body_shape

def ActualHeader.branching_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .branching receipt }

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForSupports
/-! The complete authentic singleton catalog selects the named branching
compiler packet and derives all static children from actual local-read lowering. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  input : Input fixture.recipe.compiled
  packet : Issued input
  actual : ActualHeader fixture observed.row
  headerEq : actual.header = packet.header
  rows : Inventory [input]
  rowsEq : rows = .cons packet .nil
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl


theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header)
    (rootHeaders : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) rootHeaders)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingSupport.Support rootHeaders
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedBranchingCollectors.of_imperative_compiler actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.entryMember receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver) _ actual.syntax.prepared
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  obtain ⟨original, name, localId, lookup, form⟩ := approved
  have same := Option.some.inj (found.symm.trans lookup)
  subst original
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    form
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

theorem static_supports (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : Inventory [input] := .cons packet .nil
  have headerList : headers rows = [actual.header] := by simp only [rows, headers, sameHeader]
  have complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows) := by
    rw [headerList]; exact actual.complete stages
  obtain ⟨receipt⟩ := actual.branching_receipt
  let body := actual.branching_body receipt
  obtain ⟨supported⟩ := actual.support receipt (headers rows) complete (registry := registry) receiver
  let terminals : ∀ header, header ∈ headers rows → Body header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ body
  have supports : ∀ header (member : header ∈ headers rows),
      Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
        (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [terminals, body, ActualHeader.branching_body, Support] using supported
  have family : ∀ {mapping world function native bindings parameter result}
      (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        mapping world function native bindings parameter result),
      CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association := by
    intro mapping world function native bindings parameter result association
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      have found := code.sourceFound
      rw [support.source.trans (stages.source_of_cached actual support.caller.selected)] at found
      exact False.elim (observed.no_lambda (lookupExpression?_sound found) code.sourceForm)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input
    packet := packet
    actual := actual
    headerEq := sameHeader
    rows := rows
    rowsEq := rfl
    complete := complete
    terminals := terminals
    supports := supports
    family := family
    descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForCommon
/-! Retained callers connect the exact sessions and Source heaps of both named calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.actual.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.actual.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForSeed
/-! The initial nonempty-loop call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed)
    (first : ObservedInitial fixture observed) :
    ∃ state : RetainedState support first.call.completion.session [],
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word firstInput, .word firstValue, .bool true, .bool false] (.value (.word firstValue)) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word firstInput, .word firstValue, .bool true, .bool false] [.word firstInput, .word firstValue, .bool true, .bool false] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩)) (.cons (.leaf (.data ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) (.cons (.leaf (.data ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩)) (.cons (.leaf (.data ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩
      ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩)) (.nil))))
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.call.started first.call.executed .skip support.descriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.call.returned) support.actual.output result
  let state : RetainedState support first.call.completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  exact ⟨state, support.input.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForStep
/-! The zero-iteration loop starts from the exact session and heap reached by the nonempty loop. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.update {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {flag : Bool} {input value : Core.Word}
    (call : ObservedCall observed session flag input value) (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session [],
      SourceCall support support.actual.header invocation state.heap [.word input, .word value, .bool flag, .bool false]
        (.value (.word (if flag then value else input))) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word input, .word value, .bool flag, .bool false] [.word input, .word value, .bool flag, .bool false] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.word input, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word input⟩
      ⟨.word input, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word input⟩) (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) (.cons (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩) (.cons (.data ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩
      ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩) (.nil))))
  have registry := request.started.simple_registry state.registry (by
    intro publicValue member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact .word input
    · exact .word value
    · exact .bool flag
    · exact .bool false)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]; exact support.descriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (extension := state.receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned) (by rw [selectedHeader]; exact support.actual.output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := retained }
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForInitialForward
/-! The independent nonempty-loop trace determines both public fuel bounds at its
original checkpoint. Every sufficient resume returns Word11 and the same heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.value = .word firstValue ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation ⟨[]⟩ [.word firstInput, .word firstValue, .bool true, .bool false] (.value (.word firstValue)) after) :
    InitialForwardAt support first after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.word firstInput, .word firstValue, .bool true, .bool false] [.word firstInput, .word firstValue, .bool true, .bool false] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩
      ⟨.word firstInput, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstInput⟩)) (.cons (.leaf (.data ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) (.cons (.leaf (.data ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩)) (.cons (.leaf (.data ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩
      ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩)) (.nil))))
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult, support.actual.result_type] at requested
  have nativeWord : _payload = .word firstValue := by
    have represented := _fullResult.2.1
    rw [support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl⟩


end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {flag : Bool} {input value : Core.Word} (call : ObservedCall observed session flag input value)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word (if flag then value else input) ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_update {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {flag : Bool} {input value : Core.Word}
    (call : ObservedCall observed session flag input value) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation state.heap
      [.word input, .word value, .bool flag, .bool false] (.value (.word (if flag then value else input))) after) :
    ForwardAt support call after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word input, .word value, .bool flag, .bool false] [.word input, .word value, .bool flag, .bool false] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.word input, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word input⟩
      ⟨.word input, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word input⟩) (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) (.cons (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩) (.cons (.data ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩
      ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩) (.nil))))
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have nativeWord : payload = .word (if flag then value else input) := by
    have represented := fullResult.2.1
    rw [selectedHeader, support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedForPublicExecution
/-! An independently checked and compiled named for executes one iteration
and then zero iterations through two public calls. Its real returned session carries the first
heap into the second call; each Source trace also entails sufficient public
execution and output fuel at that call's original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (first : RetainedState support sequence.initial.call.completion.session [])
      (second : RetainedState support sequence.next.completion.session []),
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word firstInput, .word firstValue, .bool true, .bool false] (.value (.word firstValue)) first.heap ∧
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        first.heap [.word secondInput, .word secondValue, .bool false, .bool false] (.value (.word secondInput)) second.heap ∧
      InitialForwardAt support sequence.initial first.heap ∧
      ForwardAt support sequence.next second.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  obtain ⟨first, initialTrace⟩ := first_meaning support stages sequence.initial
  obtain ⟨second, nextTrace⟩ := first.update sequence.next
    (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
  have initialReady : sequence.initial.session.ExportsReady :=
    (show sequence.initial.bootstrap.ReadyAt 100000 sequence.initial.session from .single sequence.initial.ready).exportsReady
      sequence.initial.authority
  have firstReady := sequence.initial.call.executed.exportsReady initialReady
  exact ⟨receiver, support, first, second, initialTrace, nextTrace,
    forward_initial support sequence.initial initialTrace,
    forward_update first sequence.next firstReady nextTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual named for: (11,12,true,false)->12 then (22,23,false,false)->22, exact Source histories and sufficient public fuel for both calls proved"

end Tests.SourceCoreNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileFixture
/-! Actual compilation, selected inventory and static loop observations for
one named Bool/Word function with a mutable loop condition and an outer return. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics

private def observeFact (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program
  recipePrepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe

def compiledFixture : IO CompiledFixture := do
  let checked ← checkedFixture
  let signature :: _ := checked.program.signatures.functions
    | throw (IO.userError "factory signature missing")
  let seeds := [SourceCompiler.Seed.declaration signature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
  match generated : SourceCoreCompiler.compileChecked checked.program seeds options with
  | .error error => throw (IO.userError (reprStr error))
  | .ok source =>
    match selected : source.artifact? with
    | none => throw (IO.userError "factory cached artifact missing")
    | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (IO.userError (reprStr error))
      | .ok recipe =>
        match facade : SourceCoreExecution.prepare source with
        | .error error => throw (IO.userError (reprStr error))
        | .ok facadeCompiled =>
          have accepted : SourceCompiler.compileChecked checked.program seeds options = .ok facadeCompiled := by
            simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError,
              bind, Except.bind] using facade
          have sameProgram : recipe.compiled.sourceProgram = checked.program :=
            (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
              ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))
          return {
            toCheckedFixture := checked
            seeds := seeds
            options := options
            facadeCompiled := facadeCompiled
            accepted := accepted
            recipe := recipe
            issued := CoreLowering.RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade
            sameProgram := sameProgram
            recipePrepared := by rw [SourceCoreIndexedSession.Recipe.prepare_compiled prepared]; exact prepared }

theorem CompiledFixture.prepared (fixture : CompiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ fixture.recipe.compiled.validationPlan.specializations) :
    Nonempty (CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row) :=
  CoreLowering.RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued member

theorem CompiledFixture.source_wellFormed (fixture : CompiledFixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  rw [fixture.sameProgram]
  exact fixture.wellFormed

structure ActualHeader (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) where
  prepared : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row
  header : CoreLowering.CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
    (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  aligned : CoreLowering.RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
    (CoreLowering.CallableNamedMetadata.instantiation row) header
  diagnostic : CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared



open CoreLowering

structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  shape : FactoryShape row.function fixture.signature
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = fixture.signature.id
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .word
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  nodes : row.function.typedBody.nodes = shape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries

abbrev ObservedFactory.inputs {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.inputs
abbrev ObservedFactory.roots {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.roots
abbrev ObservedFactory.flag {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.flag
abbrev ObservedFactory.argument {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argument
abbrev ObservedFactory.binderScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argumentScheme

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observeFact (key = row.key) "captured factory exact key"
    return ⟨by rw [accepted, same]⟩

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    let shape ← observeShape row.function fixture.signature
    match entries : fixture.recipe.compiled.indexed.entries with
    | [entry] =>
      let ⟨sourceOwner⟩ ← observeFact (row.function.typedBody.owner = fixture.signature.id) "named while source owner"
      let ⟨parameters⟩ ← observeFact (row.parameterSubstitution = []) "named while substitution"
      let ⟨closed⟩ ← observeFact (row.assumptions = []) "named while assumptions"
      let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .word) "named while result type"
      let ⟨ordinary⟩ ← observeFact (row.function.returnComptime = false) "named while ordinary result"
      let ⟨target⟩ ← observeTarget fixture row
      let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = shape.nodeList) "named while nodes"
      let ⟨noLocals⟩ ← observeFact (fixture.recipe.compiled.indexed.base.locals.bindings = []) "named while local catalog"
      let ⟨profile⟩ ← observeFact (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "named while profile"
      return {
        row, shape, sourceOwner, parameters, closed, ordinary, resultType, target, nodes, noLocals, profile, entry
        member := by rw [rows]; exact .head []
        entryMember := by rw [entries]; exact .head [] }
    | _ => throw (IO.userError "named while entry count")
  | _ => throw (IO.userError "named while specialization count")

/-- The staged selection is obtained from the retained callable table and
original sidecar of the concrete compiler result. -/
structure ObservedStages (fixture : CompiledFixture)
    (observed : ObservedFactory fixture) where
  singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      if singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1 then
        match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
            (.named observed.row.key) with
        | .error error => throw (IO.userError (reprStr error))
        | .ok descriptor => return ⟨singletonGlobal, descriptor, native, present, sidecar, issued⟩
      else throw (IO.userError "factory global count")

def ObservedStages.registry {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem ActualHeader.complete {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [actual.header] := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled actual.prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : actual.prepared.index = 0 := by omega
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [stages.singletonGlobal] at bound
  have indexZero : index = 0 := by omega
  refine ⟨actual.header, .head [], actual.aligned.slot.trans (zero.trans indexZero.symm), ?_⟩
  rw [actual.aligned.named]
  rw [zero] at selected
  rw [indexZero] at found
  exact Option.some.inj (selected.symm.trans found)

theorem bootstrap_zero (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)) :
    owner.key.capturePrefix = 0 := by
  have bound := owner.position.isLt
  change owner.position.val < 1 at bound
  have zero : owner.position.val = 0 := by omega
  simp only [CallableIndexedOwnedFunctionValues.OwnedKey.key,
    CallableIndexedOwnedPreparedBootstrapRootState.keys,
    CallableIndexedOwnedPreparedBootstrapRootState.key, zero, List.getElem_cons_zero]


theorem ObservedStages.inventory {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row, actual.header = packet.header := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  have target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok prepared.named.signature.key := by
    rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
    exact observed.target
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : prepared.index = 0 := by omega
  have globals : fixture.recipe.compiled.indexed.base.globals = [prepared.named.signature] := by
    obtain ⟨first, single⟩ := List.length_eq_one_iff.mp stages.singletonGlobal
    rw [single, zero] at selected
    have same : first = prepared.named.signature := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
    exact single.trans (congrArg (fun value => [value]) same)
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := by
      intro binder member
      rw [observed.inputs] at member
      rcases List.mem_cons.mp member with same | rest
      · exact same ▸ observed.shape.flagOrdinary
      · rcases List.mem_cons.mp rest with same | last
        · exact same ▸ observed.shape.argumentOrdinary
        · have same := List.mem_singleton.mp last
          exact same ▸ observed.shape.stopOrdinary
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl⟩



theorem ObservedStages.source_of_cached {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 1 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using stages.singletonGlobal
  have before := (List.getElem?_eq_some_iff.mp actual.prepared.selected).1
  have after := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at before after
  have same : index = actual.prepared.index := by omega
  rw [same, actual.prepared.selected] at selected
  cases Option.some.inj selected
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem CompiledFixture.signature_member (fixture : CompiledFixture) :
    fixture.signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
  rw [fixture.sameProgram, fixture.signatures]
  exact .head []

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same


theorem ActualHeader.body {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.body = observed.shape.body := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = [observed.shape.loop.id, observed.shape.statement.id]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileFacts
/-! Finite observations identify all original reads and exclude anonymous code.
They establish compiler coverage without an execution or body-meaning premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool, .word, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.shape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.shape.flagScheme, observed.shape.argumentScheme, observed.shape.stopScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem ActualHeader.output {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.result_type] at projected
  exact (Except.ok.inj projected).symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

theorem ObservedFactory.read_cases {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node) :
    node = observed.shape.conditionRead.node ∨ node = observed.shape.stopRead.node ∨ node = observed.shape.finalRead.node := by
  have member := found.1
  rw [observed.nodes] at member
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton, Node.expression.injEq,
    reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedFactory.metadata {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.row.function.typedBody := by
  apply CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named _ observed.noLocals
  intro id node found
  rcases observed.read_cases (lookupExpression?_sound found) with same | same | same
  all_goals subst node
  · exact .inl ⟨_, _, observed.shape.conditionRead.form, observed.shape.conditionRead.requirements, observed.shape.conditionRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.stopRead.form, observed.shape.stopRead.requirements, observed.shape.stopRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.finalRead.form, observed.shape.finalRead.requirements, observed.shape.finalRead.coercions⟩

theorem ObservedFactory.no_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.read_cases found with same | same | same
  all_goals subst node
  · rw [observed.shape.conditionRead.form] at form; cases form
  · rw [observed.shape.stopRead.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form

theorem ObservedFactory.flag_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.flag.id = .ok observed.shape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.conditionRead.form,
    observed.shape.stopRead.form, observed.shape.finalRead.form, observed.shape.assignmentForm,
    observed.shape.loopForm, observed.shape.statementForm, observed.shape.flagOwner,
    observed.shape.flagScheme, TypeSystem.Scheme.mono, observed.shape.argumentFlag,
    observed.shape.stopFlag, observed.shape.flagRequirements]

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.loop.id, observed.shape.statement.id] := actual.body

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileRuntime
/-! Actual public calls execute one iteration and then zero iterations of the accepted named while.
The second call consumes the exact session returned by the first. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def firstValue : Core.Word := Core.Word.ofNatModulo 11
def secondValue : Core.Word := Core.Word.ofNatModulo 22

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

structure ObservedCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (flag : Bool) (value : Core.Word) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.bool flag, .word value, .bool false] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.bool flag, .word value, .bool false] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word value

def observeCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (flag : Bool) (value : Core.Word) : IO (ObservedCall observed session flag value) := do
  match started : session.start observed.row.key [.bool flag, .word value, .bool false] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt observed.row.key [.bool flag, .word value, .bool false] runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "named while failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "named while exhausted its execution budget")
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word value then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "named while returned an unexpected Word")

structure ObservedInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedCall observed session true firstValue

def observeInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedInitial fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "named while bootstrap exhausted")
  | .ready session =>
    let call ← observeCall observed session true firstValue
    return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready, call⟩

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  initial : ObservedInitial fixture observed
  next : ObservedCall observed initial.call.completion.session false secondValue

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let initial ← observeInitial fixture observed
  let next ← observeCall observed initial.call.completion.session false secondValue
  return ⟨initial, next⟩

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedInitial.start_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.call.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.bool true, .word firstValue, .bool false]
        runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.call.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩

theorem ObservedInitial.metadata_at_start {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.bool true, .word firstValue, .bool false]
      runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  rcases List.mem_cons.mp member with same | member
  · exact same ▸ SourceCoreIndexedSession.SimplePublic.bool true
  · rcases List.mem_cons.mp member with same | member
    · exact same ▸ SourceCoreIndexedSession.SimplePublic.word firstValue
    · have same := List.mem_singleton.mp member
      exact same ▸ SourceCoreIndexedSession.SimplePublic.bool false

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileSyntax
/-! The original typed loop body supplies its condition, two writes and restored
suffix. Every expression is an actual local read. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original

private theorem returning {source : TypedSource} {context final : SourceSemantics.Context}
    {binder : TypedBinder} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (read : WordRead source binder)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some read.node.id))
    (annotation : node.type = .word) (leaf : approved read.node.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation read.found read.type
        (by simpa only [read.type] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder rhsBinder : TypedBinder} {payload : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (read : Read source rhsBinder payload) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal read.node.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved read.node.id)
    (typed : SourceAssignmentHasType source context assignment .equal read.node.id)
    (remaining : GenericImperativeMatch.Syntax source approved context (.statements mode rest) .word) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal target rhs _requirements =>
      cases target with
      | intro writable projections target =>
          apply GenericImperativeMatch.Syntax.assign found form
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [scheme, bare, targetType]
            exact .nil _
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [bare] at projections
            cases projections
            have word := target.symm.trans targetType
            simpa only [word, scheme, TypeSystem.Scheme.mono] using writable
          · simpa only [target] using rhs
          · exact .inl rfl
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨leaf, read.node, read.found, by simpa only [← target, targetType, read.type] using rhs⟩
          · exact remaining

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.row.function.typedBody true observed.shape.body :=
  .whileLoop observed.shape.loopFound observed.shape.loopForm
    (.assign observed.shape.assignmentFound observed.shape.assignmentForm (.inl rfl) observed.shape.targetBare .nil)
    (.returnValue [] observed.shape.statementFound observed.shape.statementForm)

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.conditionRead.node.id, observed.shape.stopRead.node.id, observed.shape.finalRead.node.id]

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context observed.shape.body final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true observed.shape.body) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.loopFound first
  rw [observed.shape.loopForm] at firstForm
  cases firstForm with
  | whileLoop conditionTyped bodyTyped =>
    apply GenericImperativeMatch.Syntax.whileLoop observed.shape.loopFound observed.shape.loopForm
      observed.shape.conditionRead.found observed.shape.conditionRead.type
      (by simpa only [observed.shape.conditionRead.type] using conditionTyped) (leaf _ (by simp [readIds]))
    · obtain ⟨_, _, _, assignedHead, _⟩ := head_tail bodyTyped
      have assignment := form_at unique observed.shape.assignmentFound assignedHead
      rw [observed.shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        exact assigned observed.shape.stopRead observed.shape.assignmentFound observed.shape.assignmentForm
          (by rw [observed.shape.targetRoot]; exact observed.flag_declaration)
          observed.shape.flagScheme observed.shape.targetBare observed.shape.targetType
          (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.finalRead observed.shape.statementFound observed.shape.statementForm
        observed.shape.statementType (leaf _ (by simp [readIds])) returningHead

theorem ActualHeader.syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericImperativeMatch.Syntax actual.header.function.source (fun id => ∃ node name binderId,
      actual.header.function.source.lookupExpression? id = some node ∧ node.form = .reference name (.local binderId))
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.shape.roots, actual.result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.body, actual.result_type]
  apply observed.body_syntax (actual.source ▸ actual.header.unique) _ typed
  intro id member
  simp only [ObservedFactory.readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.conditionRead.found, observed.shape.conditionRead.form⟩
  · exact ⟨_, _, _, observed.shape.stopRead.found, observed.shape.stopRead.form⟩
  · exact ⟨_, _, _, observed.shape.finalRead.found, observed.shape.finalRead.form⟩

theorem ActualHeader.branching_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.body]
  exact observed.body_shape

def ActualHeader.branching_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .branching receipt }

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileSupports
/-! The complete authentic singleton catalog selects the named branching
compiler packet and derives all static children from actual local-read lowering. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  input : Input fixture.recipe.compiled
  packet : Issued input
  actual : ActualHeader fixture observed.row
  headerEq : actual.header = packet.header
  rows : Inventory [input]
  rowsEq : rows = .cons packet .nil
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl


theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header)
    (rootHeaders : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) rootHeaders)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingSupport.Support rootHeaders
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedBranchingCollectors.of_imperative_compiler actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.entryMember receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver) _ actual.syntax.prepared
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  obtain ⟨original, name, localId, lookup, form⟩ := approved
  have same := Option.some.inj (found.symm.trans lookup)
  subst original
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    form
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

theorem static_supports (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : Inventory [input] := .cons packet .nil
  have headerList : headers rows = [actual.header] := by simp only [rows, headers, sameHeader]
  have complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows) := by
    rw [headerList]; exact actual.complete stages
  obtain ⟨receipt⟩ := actual.branching_receipt
  let body := actual.branching_body receipt
  obtain ⟨supported⟩ := actual.support receipt (headers rows) complete (registry := registry) receiver
  let terminals : ∀ header, header ∈ headers rows → Body header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ body
  have supports : ∀ header (member : header ∈ headers rows),
      Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
        (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [terminals, body, ActualHeader.branching_body, Support] using supported
  have family : ∀ {mapping world function native bindings parameter result}
      (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        mapping world function native bindings parameter result),
      CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association := by
    intro mapping world function native bindings parameter result association
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      have found := code.sourceFound
      rw [support.source.trans (stages.source_of_cached actual support.caller.selected)] at found
      exact False.elim (observed.no_lambda (lookupExpression?_sound found) code.sourceForm)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input
    packet := packet
    actual := actual
    headerEq := sameHeader
    rows := rows
    rowsEq := rfl
    complete := complete
    terminals := terminals
    supports := supports
    family := family
    descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileCommon
/-! Retained callers connect the exact sessions and Source heaps of both named calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.actual.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.actual.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileSeed
/-! The initial nonempty-loop call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed)
    (first : ObservedInitial fixture observed) :
    ∃ state : RetainedState support first.call.completion.session [],
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.bool true, .word firstValue, .bool false] (.value (.word firstValue)) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool true, .word firstValue, .bool false] [.bool true, .word firstValue, .bool false] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩))
      (.cons (.leaf (.data
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
        ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩))
      (.cons (.leaf (.data
        ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩
        ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩)) .nil))
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.call.started first.call.executed .skip support.descriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.call.returned) support.actual.output result
  let state : RetainedState support first.call.completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  exact ⟨state, support.input.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileStep
/-! The zero-iteration loop starts from the exact session and heap reached by the nonempty loop. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.choose {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {flag : Bool} {value : Core.Word}
    (call : ObservedCall observed session flag value) (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session [],
      SourceCall support support.actual.header invocation state.heap [.bool flag, .word value, .bool false]
        (.value (.word value)) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool flag, .word value, .bool false] [.bool flag, .word value, .bool false] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩)
      (.cons (.data ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩
        ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩) .nil))
  have registry := request.started.simple_registry state.registry (by
    intro publicValue member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .bool flag
    · exact .word value
    · exact .bool false)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]; exact support.descriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (extension := state.receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned) (by rw [selectedHeader]; exact support.actual.output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := retained }
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileInitialForward
/-! The independent nonempty-loop trace determines both public fuel bounds at its
original checkpoint. Every sufficient resume returns Word11 and the same heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.value = .word firstValue ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation ⟨[]⟩ [.bool true, .word firstValue, .bool false] (.value (.word firstValue)) after) :
    InitialForwardAt support first after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool true, .word firstValue, .bool false] [.bool true, .word firstValue, .bool false] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
      ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩))
      (.cons (.leaf (.data
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩))
      (.cons (.leaf (.data
        ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩
        ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩)) .nil))
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult, support.actual.result_type] at requested
  have nativeWord : _payload = .word firstValue := by
    have represented := _fullResult.2.1
    rw [support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl⟩


end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhileForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {flag : Bool} {value : Core.Word} (call : ObservedCall observed session flag value)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word value ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_choose {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {flag : Bool} {value : Core.Word}
    (call : ObservedCall observed session flag value) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation state.heap
      [.bool flag, .word value, .bool false] (.value (.word value)) after) :
    ForwardAt support call after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool flag, .word value, .bool false] [.bool flag, .word value, .bool false] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩)
      (.cons (.data ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩
        ⟨.bool false, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool false⟩) .nil))
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have nativeWord : payload = .word value := by
    have represented := fullResult.2.1
    rw [selectedHeader, support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreNamedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedWhilePublicExecution
/-! An independently checked and compiled named while executes one iteration
and then zero iterations through two public calls. Its real returned session carries the first
heap into the second call; each Source trace also entails sufficient public
execution and output fuel at that call's original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedWhile
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (first : RetainedState support sequence.initial.call.completion.session [])
      (second : RetainedState support sequence.next.completion.session []),
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.bool true, .word firstValue, .bool false] (.value (.word firstValue)) first.heap ∧
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        first.heap [.bool false, .word secondValue, .bool false] (.value (.word secondValue)) second.heap ∧
      InitialForwardAt support sequence.initial first.heap ∧
      ForwardAt support sequence.next second.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  obtain ⟨first, initialTrace⟩ := first_meaning support stages sequence.initial
  obtain ⟨second, nextTrace⟩ := first.choose sequence.next
    (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
  have initialReady : sequence.initial.session.ExportsReady :=
    (show sequence.initial.bootstrap.ReadyAt 100000 sequence.initial.session from .single sequence.initial.ready).exportsReady
      sequence.initial.authority
  have firstReady := sequence.initial.call.executed.exportsReady initialReady
  exact ⟨receiver, support, first, second, initialTrace, nextTrace,
    forward_initial support sequence.initial initialTrace,
    forward_choose first sequence.next firstReady nextTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual named while: true11 then false22, exact Source histories and sufficient public fuel for both calls proved"

end Tests.SourceCoreNamedWhile
end
