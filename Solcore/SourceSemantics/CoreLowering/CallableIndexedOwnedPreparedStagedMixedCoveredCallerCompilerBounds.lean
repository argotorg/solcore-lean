import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveCallerCompilerBounds

/-! Static coverage supplies a dependent packet and support at each actual
Association. Each proof chooses that pair locally and uses the accepted caller
compiler theorem. The production recipe and supported body shape remain genuine
coverage obligations. Classical.choice is confined to the theorem proofs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {reasonAt : ExpressionId → Word}

variable {readFuel : Nat}

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closureCoverage : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    Nonempty (Σ packet : PacketFor association stages, SupportFor association stages packet))
  (namedTerminals : ∀ header, header ∈ headers → Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closureCoverage namedTerminals namedSupport
  sameLedger runtimeLedger uninitialized in
/-- Static Association coverage suffices for the same accepted caller preservation theorem. -/
theorem preserves_compiled
    {rootScope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source rootScope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy
      compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source rootScope reasonAt)
    (coercions : ∀ id node,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [])
    {rootId : ExpressionId}
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source rootId)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
    (typed : ExpressionHasType invocation.source context rootId node.type)
    {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation
      invocation.source rootScope rootId reasonAt = .ok rootCode)
    (ports : CallsReady (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted))
    (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
    classical
    let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore),
        Σ packet : PacketFor association stages, SupportFor association stages packet :=
      fun association => Classical.choice (closureCoverage association)
    let packets : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore), PacketFor association stages :=
      fun association => (chosen association).1
    let supported : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore), SupportFor association stages (packets association) :=
      fun association => (chosen association).2
    intro current id child point
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerCompilerBounds.preserves_compiled
      (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
      (profile := profile) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      (unique := unique) (actualFunctionType := actualFunctionType) (observations := observations)
      (extension := extension) (semantic := semantic)
      (closurePackets := packets) (closureSupport := supported)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (sameLedger := sameLedger) (runtimeLedger := runtimeLedger) (uninitialized := uninitialized)
      declarations policyFor coercions syntaxTree found typed accepted ports size point

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closureCoverage namedTerminals namedSupport
  sameLedger runtimeLedger uninitialized in
/-- The same local dependent choice retains the independent Source reflection grade. -/
theorem reflects_compiled
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {rootScope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source rootScope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy
      compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source rootScope reasonAt)
    (coercions : ∀ id node,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [])
    {rootId : ExpressionId}
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source rootId)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
    (typed : ExpressionHasType invocation.source context rootId node.type)
    {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation
      invocation.source rootScope rootId reasonAt = .ok rootCode)
    (ports : CallsReady (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted))
    (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
    classical
    let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore),
        Σ packet : PacketFor association stages, SupportFor association stages packet :=
      fun association => Classical.choice (closureCoverage association)
    let packets : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore), PacketFor association stages :=
      fun association => (chosen association).1
    let supported : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore), SupportFor association stages (packets association) :=
      fun association => (chosen association).2
    intro current id child point
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerCompilerBounds.reflects_compiled
      (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
      (profile := profile) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      (unique := unique) (actualFunctionType := actualFunctionType) (observations := observations)
      (extension := extension) (semantic := semantic)
      (closurePackets := packets) (closureSupport := supported)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (sameLedger := sameLedger) (runtimeLedger := runtimeLedger) (uninitialized := uninitialized)
      stageEq declarations policyFor coercions syntaxTree found typed accepted ports size point

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds
