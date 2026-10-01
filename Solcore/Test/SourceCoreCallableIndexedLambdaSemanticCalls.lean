import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticCalls
import Solcore.Test.SourceCoreCallableIndexedLambdaCalls
import Solcore.Test.SourceCoreCallableLambdaViewBuiltinBodyTree

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation.ViewBody.mk
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaSemanticCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaSemanticInvocation CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
section Proof
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} (profile : values.checked.catalog.callableContracts = true)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code)
  (sourceFrame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
  (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy policy)
  {changed : List ExpressionId}
  (edited : CallableLambdaViewEdits.LocalView function.source code.view changed)
  (avoids : CallableLambdaBodyReachability.Avoids function.source (function.body.map NodeId.statement) changed)
  (unique : NodeOccurrencesUnique function.source)
  (valid : CompatibleExpressionLiterals.ContextValid code.compilation.solvedRequirements inputs.context function.evidence)
  (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
  (syntaxTree : BuiltinLexicalStatements.Syntax code.view inputs.context true function.body function.resultType)
  {flow : Expr}
  (emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason)
  (tree : BuiltinLexicalStatements.Tree prepared.layouts code.compilation.owner code.active prepared.ancestry.layout.frame
    prepared.base.globals.length code.allocationError readFuel values code.view code.compilation.solvedRequirements code.reasonAt
    inputs.context (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    true function.body function.resultType code.receipt.resultCore flow)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem completed_call {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Core.Value} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaSemanticCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inRight .word result) finalStore) :
    ∃ sourceResult after finalMap finalWorld,
      Dynamic.CallableApplies program callerContext callerEvidence function.evidence before (.closure function) arguments sourceResult after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile)).Represents
        finalMap finalWorld function.resultType sourceResult result code.receipt.resultCore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨viewBody⟩ := ViewBody.of_tree code inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaSemanticCalls.reflects captured code history viewBody.body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | value payload =>
    cases execution with
    | value called => exact ⟨_, after, finalMap, finalWorld, called, payload, finalHeap, caller.read⟩

include inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem failed_call {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {token : Word} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaSemanticCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inLeft code.receipt.resultCore (.word token)) finalStore) :
    ∃ reason after finalMap finalWorld,
      Dynamic.CallableFaults program callerContext callerEvidence function.evidence before (.closure function) arguments reason after ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨viewBody⟩ := ViewBody.of_tree code inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaSemanticCalls.reflects captured code history viewBody.body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | fault represented =>
    cases execution with
    | fault failed => exact ⟨_, after, finalMap, finalWorld, failed, represented, finalHeap, caller.read⟩
/- Independent source success or fault runs the same actual closure code.
Every body semantic input is constructed from static evidence at the compiler
view and its actual callback equation. -/
include inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem source_call {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaSemanticCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨viewBody⟩ := ViewBody.of_tree code inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, heaps, _, _, _, _, restored⟩ :=
    CallableIndexedLambdaSemanticCalls.preserves captured code history viewBody.body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing executed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, heaps, restored.read⟩

/- The body action retained by the lambda compiler uses the exact ordered
parameter scope; acceptance is at the actual view, never the canonical source. -/
include callback in
theorem actual_body_receipt :
    code.receipt.bodyScope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope ∧
    SourceCoreLoops.lowerStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body :=
  ⟨body_scope code, loops_accepted code policy callback⟩

end Proof


def run : IO Unit := do
  Tests.SourceCoreCallableIndexedLambdaCalls.run
  Tests.SourceCoreCallableLambdaViewBuiltinBodyTree.run
  IO.println "indexed semantic lambda calls: actual view callback/parameter receipt, canonical source call/fault, caller restore and resumed heap GREEN"

end Tests.SourceCoreCallableIndexedLambdaSemanticCalls
