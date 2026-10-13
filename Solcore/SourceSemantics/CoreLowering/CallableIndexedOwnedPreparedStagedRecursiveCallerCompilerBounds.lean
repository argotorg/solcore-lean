import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLegacyCallerMethodExclusion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerBounds

/-! Successful compilation supplies the finite caller certificate internally.
These public entry ports compose the actual raw typing/compiler issuer with
the structural semantic fold. Static call authority is indexed by that exact
issued proof; no child or body execution law is supplied. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCompilerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds (FiniteFor)
open CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

open CallableIndexedOwnedPreparedStagedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
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
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    Nonempty (FiniteFor (registry := completion.result.context.registry) (stages := stages) association))
  (namedTerminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
  (namedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
    stages.Closure header.function child → child.evidence.Covers header.context)

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
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
  sameLedger runtimeLedger uninitialized in
/-- The accepted compiler action issues the actual tree used for Source preservation. -/
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
    let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted
    intro scope id lowered certified
    exact CallableIndexedOwnedPreparedStagedRecursiveCallerBounds.preserves
      bridge receiver stagePrepared profile wellFormed runtime covers unique
      actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
      sameLedger runtimeLedger uninitialized root (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy root syntaxTree policyFor)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax root syntaxTree)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax root syntaxTree) ports size certified

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
  sameLedger runtimeLedger uninitialized in
/-- The same issued tree reflects native completion to its independent Source grade. -/
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
    let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted
    intro scope id lowered certified
    exact CallableIndexedOwnedPreparedStagedRecursiveCallerBounds.reflects
      bridge receiver stagePrepared profile wellFormed runtime covers unique
      actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
      sameLedger runtimeLedger uninitialized stageEq root (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy root syntaxTree policyFor)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax root syntaxTree)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax root syntaxTree) ports size certified

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCompilerBounds
