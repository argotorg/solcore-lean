import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority

/-! Static support for the pool-zero numeric family. The certificate belongs
  to the actual original Source and parameter context. The chosen terminal
  point retains its genuine receipt and selected scope. These structures store
  no execution, child meaning, Below law or desired body/application result.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState

/-- The eventual body carrier uses the concrete owned pool at universe zero. -/
def poolZero {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ProtectedStateTransition.Protocol.{0, 0} (Records keys) :=
  protocol headers keys

/-- Exact static authority at one original expression occurrence. Runtime
  validity and evidence coverage are propositions, not completed executions. -/
structure RootData (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) where
  compilerFuel : Nat
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
    compilation invocation.source scope expression reasonAt = .ok lowered
  certificate : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
    policy lowerBody compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source context reasonAt scope expression lowered
  node : ExpressionNode
  found : invocation.source.lookupExpression? expression = some node
  rawResult : node.type = rawType
  typed : ExpressionHasType invocation.source context expression node.type
  sameLedger : context.solvedRequirements = compilation.solvedRequirements
  runtimeLedger : RuntimeRequirementLedgerValid context
  unique : NodeOccurrencesUnique invocation.source
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    context invocation.source
  covers : invocation.evidence.Covers context
  actualFunctionType : policy.callables.functionType = CallableContract.functionType
  uninitialized : ∀ current id code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current id code →
    CallableLambdaBodyReachability.Reaches invocation.source [.expression expression] (.expression id) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)
  callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
    (compiled := compiled) (invocation := invocation) certificate

/-- A pool-only law covers precisely the legacy finite certificates. Its
absence of direct calls is derived from actual supported syntax. -/
structure Root (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) extends
    RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults where
  noDirect : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoDirect toRootData.certificate
  noIndexes : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoIndexes toRootData.certificate

/-- Direct-enabled roots retain selected static authority in the same ordered
finite Header inventory. Actual canonical slot values remain runtime inputs. -/
structure CanonicalRoot (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))) extends
    RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults where
  directReady : ∀ {fuel callScope callId callee ids instantiation callCode}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId callee ids instantiation reasonAt callCode),
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler toRootData.certificate →
    Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.Port compiler headers)
  indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady toRootData.certificate

/-- Existential packaging for the numeric IH. All compiler indices belong to
  the stored authentic Root; the ambient Source/context/scope/child stay fixed. -/
structure RootAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (semanticFaults : FunctionCalls.FaultRep) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  readFuel : Nat
  reasonAt : ExpressionId → Word
  rawType : TypeSystem.Ty
  support : Root compiled policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults

/-- Packaging does not change any Source, compiler or validity index. -/
def RootAt.ofRoot {compiled : SourceCoreUnifiedCompilation.Compiled}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}
    (root : Root compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    RootAt compiled context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, root⟩

section RootConstruction
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}

/-- Legacy syntax proves the pool-only restriction for this exact extracted
certificate, including all recursively evaluated callee and argument entries. -/
def RootData.legacy
    (root : RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults)
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source expression) :
    Root compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults :=
  ⟨root, CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax root.certificate syntaxTree,
    CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax root.certificate syntaxTree⟩

/-- All reached direct sites use the original finite inventory and authentic
compiler context; no semantic call law or runtime globals are manufactured. -/
def RootData.canonical
    (root : RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    (indexes : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady root.certificate) :
    CanonicalRoot compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) :=
  ⟨root, fun compiler _path =>
    CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory compiler rows complete plan globals, indexes⟩
end RootConstruction

/-- The direct-enabled numeric family keeps the same authentic static indices
and a finite inventory; the actual caller supplies its physical slot values. -/
structure CanonicalRootAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (semanticFaults : FunctionCalls.FaultRep) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  readFuel : Nat
  reasonAt : ExpressionId → Word
  rawType : TypeSystem.Ty
  support : CanonicalRoot compiled policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults headers

def CanonicalRootAt.ofRoot {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}
    (root : CanonicalRoot compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults headers) :
    CanonicalRootAt compiled headers context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, root⟩

/-- The context is the actual retained EntryPrefix.Context. P receives static
  roots for every real Source-selected scope; R uses packet.child/selected.
  Guards and call authority are supplied at each such scope, rather than
  recovered from its Source equality alone. -/
structure SelectedBody {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function localScope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages)
    (semanticFaults : FunctionCalls.FaultRep) where
  point : packet.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
    packet.expression packet.receipt.child
  readFuel : Nat
  roots : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    Root compiled code.policy code.lowerBody code.compilation readFuel inputs.context child
      code.reasonAt
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child function.resultType semanticFaults

/-- Restriction uses the existing accepted-action singleton constructor.
  The original packet's policy, childFuel, reasonAt and selected scope remain. -/
abbrev selectedPoint {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {stages : Staging.Recursive.Registry}
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) :=
  CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow packet

/-- Every actual selected closure scope packages its original parameter Root.
  Preservation uses this projection for each Source-selected scope; reflection
  can use packet.child together with packet.selected. -/
def SelectedBody.rootAt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    {code : Code compiled.indexed function localScope administrative}
    {inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
    {stages : Staging.Recursive.Registry}
    {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
    {semanticFaults : FunctionCalls.FaultRep}
    (support : SelectedBody code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    RootAt compiled inputs.context child
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child semanticFaults :=
  RootAt.ofRoot (support.roots child selected)

/-- Named support retains the real Header context and literal physical binding
  scope. Its expression compiler indices remain bundled, rather than guessed
  from the Header's statement policy. Original raw result and reasonAt remain
  tied to this actual Header; all genuine selected Source scopes are covered. -/
structure NamedSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry)
    (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header)
    (semanticFaults : FunctionCalls.FaultRep) where
  point : packet.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    packet.expression packet.receipt.child
  roots : ∀ (child : Staging.Recursive.Scope), stages.Closure header.function child →
    { root : RootAt compiled header.context child
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        packet.expression packet.receipt.child semanticFaults //
      root.rawType = header.function.resultType ∧ root.reasonAt = header.reasonAt }

/-- Each contextual Association chooses its own actual BodyWith context.
  Neither the ordinary nor the principal branch invents context equality or
  converts that Support's arbitrary expression certificate family. -/
def ClosureSupportFor {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (stages : Staging.Recursive.Registry)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Type :=
  match association, packet with
  | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
      SelectedBody code support.body.toContext stages packet semanticFaults
  | .principal _ _ code _ support _ _ _ _ _ _, packet =>
      SelectedBody code support.body.toContext stages packet semanticFaults

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
