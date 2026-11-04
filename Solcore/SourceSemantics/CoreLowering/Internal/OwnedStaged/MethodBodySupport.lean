import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndexDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.Frontend.SourceInference.TypedIRProperties
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerPolicies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LexicalBodyFaults
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedMethods
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOperators
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState

/-!
# Staged bounds: method and selected body support

Static and compiler support of method and selected bodies, canonical call readiness, and method argument rows and invocation bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
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
  noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods toRootData.certificate
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
  noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods toRootData.certificate
  directReady : ∀ {fuel callScope callId callee ids instantiation callCode}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId callee ids instantiation reasonAt callCode),
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler toRootData.certificate →
    Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler headers context invocation.evidence)
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
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source expression)
    (noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods root.certificate) :
    Root compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults :=
  ⟨root, noMethods, CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax root.certificate syntaxTree,
    CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax root.certificate syntaxTree⟩

/-- Shared roots receive full evidence authority derived at their actual
caller context, for each reached compiler occurrence. -/
def RootData.canonical_with
    (root : RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    (ready : ∀ {fuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        policy lowerBody fuel compilation (.initial compiled.compatible.checked)
        invocation.source callScope callId callee ids instantiation reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler root.certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence
        compiler headers context invocation.evidence))
    (indexes : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady root.certificate)
    (noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods root.certificate) :
    CanonicalRoot compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults headers :=
  ⟨root, noMethods, ready, indexes⟩

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
    (ordinarySites : ∀ {fuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        policy lowerBody fuel compilation (.initial compiled.compatible.checked)
        invocation.source callScope callId callee ids instantiation reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler root.certificate →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Ordinary compilation.plan instantiation ∧
        compiler.node.requirements = [])
    (indexes : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady root.certificate)
    (noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods root.certificate) :
    CanonicalRoot compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) :=
  ⟨root, noMethods, fun compiler path => by
    obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory compiler rows complete plan globals
    obtain ⟨ordinary, requirements⟩ := ordinarySites compiler path
    exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
      compiler port ordinary requirements context invocation.evidence⟩⟩, indexes⟩
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodRootStaticSupport
/-! Static roots for expressions whose ordinary and trait calls use the actual
physical cache. Ports retain source selection and compilation evidence; the
numeric proof supplies every called-body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodRootStaticSupport
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootData)

/-- This first physical method family covers statically selected call sites. -/
def NoIndirect {compiled : SourceCoreUnifiedCompilation.Compiled}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy lowerBody compilation readFuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression lowered) : Prop :=
  ∀ {fuel callScope callId callee ids metadata callCode}
    (compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation
      invocation.source callScope callId callee ids metadata reasonAt callCode),
    Calls compiler root → False

structure Root (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) extends
    RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults where
  directReady : ∀ {fuel callScope callId callee ids instantiation callCode}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId callee ids instantiation reasonAt callCode),
    DirectCalls compiler toRootData.certificate →
    Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence
      compiler headers context invocation.evidence)
  indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady toRootData.certificate
  methodReady : ∀ {fuel callScope callId callCode}
    (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId reasonAt callCode),
    MethodCalls compiler toRootData.certificate →
    Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port
      (compiled := compiled) compiler context invocation.evidence stages)
  noIndirect : NoIndirect (compiled := compiled) (invocation := invocation) toRootData.certificate

structure RootAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (semanticFaults : FunctionCalls.FaultRep) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  readFuel : Nat
  reasonAt : ExpressionId → Word
  rawType : TypeSystem.Ty
  support : Root compiled headers stages policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}

def RootAt.ofRoot
    (root : Root compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    RootAt compiled headers stages context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, root⟩

/-- Original syntax can exclude indirect calls independently of compiler certificates. -/
def NoIndirectSource (source : TypedSource) : Prop :=
  ∀ id node callee ids metadata, source.lookupExpression? id = some node →
    node.form = .call callee ids (.indirect metadata) → False

theorem NoIndirect.of_source
    (root : Certificate policy lowerBody compilation readFuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression lowered)
    (syntaxOnly : NoIndirectSource invocation.source) :
    NoIndirect (compiled := compiled) (invocation := invocation) root := by
  intro fuel callScope callId callee ids metadata callCode compiler _path
  exact syntaxOnly callId compiler.original callee ids metadata compiler.found compiler.originalForm

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodRootStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport
/-! Selection formation and full raw replacement typing do not require an
empty method dictionary. Actual caller coverage is retained separately from
the method's own evidence assumptions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation)
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

structure Catalog (program : CheckedProgram) : Prop where
  formed : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → Formation implementation method

/-- Existing generic catalogs retain their original APIs. -/
theorem Catalog.of_generic {program : CheckedProgram}
    (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog program) :
    Catalog program := ⟨catalog.formed⟩

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy lowerBody fuel compilation values source scope id reasonAt lowered)

/-- Source instantiation retains the selected declaration's complete body and
the same checked replacement range. -/
theorem support_of_range     (checked : CallableMethodBodyCoherence.Checked receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures receipt.program.signatures)
      receipt.method.specialized.parameterSubstitution) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionCore receipt selected := by
  let chosen := selected.certificate.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  obtain ⟨definition, _member, _id, instantiated⟩ := chosen.instantiates checked formed.parameters range
  obtain ⟨types, lexical, facts, typing⟩ := instantiated.certificate wellFormed
  exact ⟨formed, range, covered, typing.graph_closed.wellFormed.nodeOccurrencesUnique⟩

/-- Genuine original parent typing and current requirement identities establish
the range before the selected method Source body is instantiated. -/
theorem selection_support     (checked : CallableMethodBodyCoherence.Checked receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method)
    {context : SourceSemantics.Context}
    (signatures : context.signatures = receipt.program.signatures)
    (ledger : context.solvedRequirements = receipt.caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ receipt.caller.assumptions → goal ∈ context.assumptions)
    (unique : NodeOccurrencesUnique source)
    (idsUnique : RequirementIdsUnique context)
    (typed : ExpressionHasType source context id receipt.node.type) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionCore receipt selected := by
  have goalAdmitted := CallableIndexedOwnedPreparedStagedMethodSelectionGoal.admissible
    receipt selected signatures ledger assumptions unique idsUnique typed
  have formed := catalog.formed _ selected.certificate.selected.implementationMember
    _ selected.certificate.selected.methodMember
  have range := CallableIndexedOwnedPreparedStagedMethodSelectionRanges.of_selected
    selected.certificate.selected wellFormed formed signatures goalAdmitted
  exact support_of_range receipt checked wellFormed catalog selected covered range

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerSupport
/-! Original Source compilation issues the recursive static Root internally.
  CallsReady belongs to the exact certificate returned by the existing issuer.
  Policy, raw typing, declarations, coercions and diagnostic interpretation
  remain genuine static inputs. This producer does not transport Code.view,
  choose a body packet, or supply any expression/body execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel compilerFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode} {rawType : TypeSystem.Ty}
  {semanticFaults : FunctionCalls.FaultRep}

/-- The certificate is issued from this original Source's actual accepted
  action. Reachable call authority stays indexed by that exact issued proof. -/
def Root.of_compiled
    (unique : NodeOccurrencesUnique invocation.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor
      policy compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source scope reasonAt)
    (coercions : ∀ id actualNode,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [])
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      invocation.source expression)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
      compilation invocation.source scope expression reasonAt = .ok lowered)
    (callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        unique declarations policyFor coercions syntaxTree found typed accepted))
    (rawResult : node.type = rawType)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context invocation.source)
    (covers : invocation.evidence.Covers context)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (uninitialized : ∀ current id code,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source context reasonAt current id code →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) :
    Root compiled policy lowerBody compilation readFuel context invocation reasonAt scope
      expression lowered rawType semanticFaults :=
  { compilerFuel := compilerFuel
    accepted := accepted
    certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
      unique declarations policyFor coercions syntaxTree found typed accepted
    node := node
    found := found
    rawResult := rawResult
    typed := typed
    sameLedger := sameLedger
    runtimeLedger := runtimeLedger
    unique := unique
    wellFormed := wellFormed
    runtime := runtime
    covers := covers
    actualFunctionType := actualFunctionType
    uninitialized := fun current id code receipt _reached => uninitialized current id code receipt
    callsReady := callsReady
    noMethods := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy _ syntaxTree policyFor
    noDirect := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax _ syntaxTree
    noIndexes := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax _ syntaxTree }

/-- Packaging retains all actual compiler indices while fixing the original
  Source invocation, parameter context, physical occurrence and lowered child. -/
def RootAt.of_compiled
    (unique : NodeOccurrencesUnique invocation.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor
      policy compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source scope reasonAt)
    (coercions : ∀ id actualNode,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [])
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      invocation.source expression)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
      compilation invocation.source scope expression reasonAt = .ok lowered)
    (callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        unique declarations policyFor coercions syntaxTree found typed accepted))
    (rawResult : node.type = rawType)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context invocation.source)
    (covers : invocation.evidence.Covers context)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (uninitialized : ∀ current id code,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source context reasonAt current id code →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) :
    RootAt compiled context invocation scope expression lowered semanticFaults :=
  RootAt.ofRoot (Root.of_compiled
    (compiled := compiled) (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (compilerFuel := compilerFuel) (context := context) (invocation := invocation)
    (reasonAt := reasonAt) (scope := scope) (expression := expression) (lowered := lowered)
    (node := node) (rawType := rawType) (semanticFaults := semanticFaults)
    unique declarations policyFor coercions syntaxTree found typed accepted callsReady rawResult
    sameLedger runtimeLedger wellFormed runtime covers actualFunctionType uninitialized)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopeCallPorts
/-! Static call authority at the canonical scope of the same actual Code.
The sidecar is recovered from its genuine descriptor/source receipt. Original
parent typing supplies the callee lookup. This does not assert authority at
all other scopes selected by an arbitrary registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopeCallPorts
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (PolicyFor Syntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function localScope administrative)
  {readFuel callFuel : Nat} {context : SourceSemantics.Context}
  {callScope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {lowered : SourceCoreBasic.LoweredExpr}
  (profile : PolicyFor code.policy code.compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    function.source callScope code.reasonAt)
  (syntaxTree : Syntax function.source id)
  (compiler : CallableIndirectCallCertificates.Receipt code.policy code.lowerBody callFuel
    code.compilation function.source callScope id callee ids metadata code.reasonAt lowered)
  (typed : ExpressionHasType function.source context id compiler.original.type)

include profile syntaxTree typed in
/-- Recover the actual full owner, original Source view and guard frame from
one Code's authentic stage producer. No invocation or sidecar is chosen by
an execution premise, and the emitted compiler receipt stays unchanged. -/
theorem canonical_scope_port
    (source : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram
      compiled.indexed.base.plan code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
        code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
        (compiled := compiled)
        (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler) := by
  obtain ⟨sidecar, issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code source unique
  have readPolicy := profile.read id syntaxTree
  have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent
    compiler readPolicy
  obtain ⟨prepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
    compiler readPolicy code.active code.callables
  obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, bundle, resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler parent unique typed
  obtain ⟨calleeNode, contains, stored⟩ := calleeTyped.stored_type
  have calleeFound := lookupExpression?_complete unique contains
  have sourceEq := source.source issued
  have originalUnique : NodeOccurrencesUnique sidecar.source := by
    have substituted : NodeOccurrencesUnique (sidecar.source.applySubstitution code.active) :=
      sourceEq ▸ unique
    change ((sidecar.source.applySubstitution code.active).nodes.map Node.occurrenceId).Nodup
      at substituted
    change (sidecar.source.nodes.map Node.occurrenceId).Nodup
    simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using substituted
  let port : CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
      (compiled := compiled)
      (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler := {
    prepared := prepared
    sidecar := sidecar
    caller := by rw [prepared.caller]; exact issued
    view := Or.inr ⟨code.active, sourceEq⟩
    guardFrame := rfl
    originalUnique := originalUnique
    sourceParent := parent
    calleeNode := calleeNode
    calleeFound := calleeFound }
  exact ⟨sidecar, issued, selected, ⟨port⟩⟩

include profile syntaxTree typed in
/-- Ordinary support supplies its own complete cached Header/source receipt.
The produced sidecar belongs to the same Code, including after recapture. -/
theorem ordinary_scope_port
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
        code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
        (compiled := compiled)
        (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler) := by
  exact canonical_scope_port code profile syntaxTree compiler typed
    support.source_receipt support.unique

include profile syntaxTree typed in
/-- Principal support supplies its genuine method Source record. No ordinary
Header, erased signature or independent policy witness replaces that record. -/
theorem principal_scope_port
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
        code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
        (compiled := compiled)
        (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler) := by
  exact canonical_scope_port code profile syntaxTree compiler typed
    support.source_receipt support.unique

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopeCallPorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalCallsReady
/-! Static call authority for one genuine root at the canonical invocation of
the same actual Code. The certificate retains every callee and argument row,
including duplicate occurrences. Original typing supplies each reached raw
parent type; the retained policy supplies its exact compiler callbacks. Global
metadata and original source attribution remain genuine static inputs.
This endpoint covers the canonical invocation. Other selected guard frames
require their own actual coherence proof. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalCallsReady
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax (syntax_child syntax_not_direct)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls Syntax)

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

/-- The shared certificate admits the complete supported grammar, including
actual direct declaration calls. -/
theorem certificate_syntax {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Certificate policy body compilation readFuel values source context reasonAt scope id lowered) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.SupportedSyntax compilation.plan source id :=
  CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.certificate_syntax tree

/-- The legacy grammar at a reached call follows its exact original child
path from authentic legacy syntax at the root. Shared certificates alone also
include direct calls, so they do not imply this restricted grammar. -/
theorem calls_syntax {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {lowered : SourceCoreBasic.LoweredExpr}
    {compiler : CallableIndirectCallCertificates.Receipt policy body callFuel compilation
      source callScope callId callee ids metadata reasonAt lowered}
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel values source context
      reasonAt rootScope rootId rootCode}
    (path : Calls compiler root) (tree : Syntax source rootId) : Syntax source callId := by
  induction path with
  | here sequence children => exact tree
  | @method_child scope id otherFuel code types outer sequence children child childCode member inside ih =>
    exact ih (syntax_child tree outer.metadata.found (outer.argument_references (List.of_mem_zip member).1))
  | @group scope id node inner innerNode code actual form found sourceType child inside ih =>
    exact ih (syntax_child tree actual.found (by simp [form, ExpressionForm.references]))
  | @tuple_child scope id node tupleIds types codes header sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @constructor_child scope id node instantiation constructorIds tag headerWord codes header form admissible ranges count nodes sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @builtin_child scope id otherCallee otherIds function otherFuel code outer calleeTyped sourceType nativeTypes sequence children child childCode member inside ih =>
    exact ih (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.syntax_child tree outer.metadata.found (by
      simp [outer.form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @direct_child scope id otherCallee otherIds instantiation otherFuel code types outer calleeTyped application sequence children child childCode member inside ih =>
    exact False.elim (syntax_not_direct tree outer.metadata.found outer.form)
  | @call_child scope id otherCallee otherIds metadata otherFuel code types outer sequence children child childCode member inside ih =>
    apply ih
    apply syntax_child tree outer.found
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      simp [outer.originalForm, ExpressionForm.references]
    · simp [outer.originalForm, ExpressionForm.references, (List.of_mem_zip remaining).1]
  | @unary_child scope id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType profile child inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @binary_left scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @binary_right scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_condition scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_then scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_else scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))

  | @index_base scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree inside ih
  | @index_key scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree inside ih =>
    exact False.elim (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.syntax_not_index tree header.metadata.found form)

/-- One actual sidecar is chosen outside the universal static call proof.
Each Port comes from the same successful prepareSidecar action, so its sidecar
is identified by constructor injectivity. No execution or body law is used. -/
theorem canonical_calls_ready
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function parameterScope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr} {rootType : TypeSystem.Ty}
    (typed : ExpressionHasType function.source context rootId rootType)
    (root : Certificate code.policy code.lowerBody code.compilation compiled.indexed.fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      function.source context code.reasonAt rootScope rootId rootCode)
    (tree : Syntax function.source rootId) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) ∧
      CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
        (compiled := compiled) (invocation := RecursiveStageRegistry.scope sidecar code.active function) root := by
  obtain ⟨sidecar, issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code sourceReceipt unique
  refine ⟨sidecar, issued, selected, ?_⟩
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  have syntaxTree := calls_syntax path tree
  have profile := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_for
    retained metadata callScope code.reasonAt
  have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
    compiler unique typed path
  obtain ⟨actualSidecar, actualIssued, _actualSelected, port⟩ :=
    CallableIndexedOwnedPreparedStagedCanonicalScopeCallPorts.canonical_scope_port
      code profile syntaxTree compiler parentTyped sourceReceipt unique
  have same : actualSidecar = sidecar := Except.ok.inj (actualIssued.symm.trans issued)
  cases same
  exact port

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalCallsReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
/-! Canonical roots retain compiler-selected Headers. Their laws quantify over
an actual caller carrying those global slots. Named terminals obtain this
receipt from the existing parameter packet, without changing the reached pool. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (CanonicalRootAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
  (faults : RecursiveStageMeaning.FaultRep)

/-- Physical global values are retained by the actual caller protocol. -/
def PreservesRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : CanonicalRootAt compiled headers context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys)
    {caller : ProtectedStateTransition.Protocol.{0, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
        owner root.compilation.administrativePrefix index.scope index.canonical) caller),
    PreservesAt bridge.forgetSlots context model stages invocation (Point scope expression lowered) faults size

def ReflectsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : CanonicalRootAt compiled headers context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys)
    {caller : ProtectedStateTransition.Protocol.{0, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
        owner root.compilation.administrativePrefix index.scope index.canonical) caller),
    ReflectsAt bridge.forgetSlots context model stages invocation (Point scope expression lowered) faults size

/-- Every selected scope uses one actual named compiler root; the prefix and
zero-capture facts identify the existing named parameter packet. -/
structure NamedSupport (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (terminal : Terminal header) where
  point : terminal.certificate = Point
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    terminal.expression terminal.receipt.child
  zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0
  roots : ∀ child, stages.Closure header.function child →
    { root : CanonicalRootAt compiled headers header.context child
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        terminal.expression terminal.receipt.child semanticFaults //
      root.rawType = header.function.resultType ∧ root.reasonAt = header.reasonAt ∧
      root.compilation.administrativePrefix = 1 }

variable {model stages semanticFaults faults}

/-- The stronger bridge projects the actual packet's global observations.
Its pool and restoration operation are definitionally the existing bridge. -/
def nestedCaller (owner : OwnedKey keys)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (callerPrefix : Nat) (samePrefix : callerPrefix = 1) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
        owner callerPrefix index.scope index.canonical)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header) where
  pool := (CallableIndexedOwnedOrdinaryLambdaEntries.bridge owner header).pool
  records_eq := (CallableIndexedOwnedOrdinaryLambdaEntries.bridge owner header).records_eq
  related := (CallableIndexedOwnedOrdinaryLambdaEntries.bridge owner header).related
  slots := fun state => samePrefix.symm ▸ state.property.globals
  restore := (CallableIndexedOwnedOrdinaryLambdaEntries.bridge owner header).restore

theorem NamedSupport.preserves
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {terminal : Terminal header}
    (static : NamedSupport (headers := headers) (keys := keys) stages semanticFaults header terminal)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
    {budget : Nat}
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
      header model stages child terminal.certificate faults budget := by
  refine .nested terminal.aligned.globals static.zero ?_
  intro owner size smaller current id lowered point
  rw [static.point] at point
  let root := (static.roots child selected).val
  intro node
  exact children size smaller root owner
    (nestedCaller owner header root.compilation.administrativePrefix (static.roots child selected).property.2.2) point (node := node)

theorem NamedSupport.reflects
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {terminal : Terminal header}
    (static : NamedSupport (headers := headers) (keys := keys) stages semanticFaults header terminal)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
    {budget : Nat}
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
      header model stages child terminal.certificate faults budget := by
  refine .nested terminal.aligned.globals static.zero ?_
  intro owner size smaller current id lowered point
  rw [static.point] at point
  let root := (static.roots child selected).val
  intro node
  exact children size smaller root owner
    (nestedCaller owner header root.compilation.administrativePrefix (static.roots child selected).property.2.2) point (node := node)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentRows
/-! Actual operator typing fixes the raw method argument vector before native
packing. The selected method carries the same result and reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context caller stages)

/-- Empty output coercions identify the complete owned requirement row. -/
theorem requirements : receipt.operator.requirements = receipt.node.requirements := by
  have layout := CallableCallRequirementLayouts.ordinary_owned receipt.operator.ordinary
  simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm

/-- The independent parent judgment supplies the real trait profile and its
ordered operand types. This uses no equality of native packed types. -/
theorem source_facts (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ∃ operand parameterTypes returnTypes predicates,
      ExpressionsHaveTypes source context receipt.arguments parameterTypes ∧
      OperatorProfileInstantiates context port.principal.traitName port.principal.methodName
        operand parameterTypes returnTypes predicates ∧
      RequirementSequenceProves context receipt.node.requirements predicates ∧
      receipt.node.type = TypeSystem.Ty.productMany returnTypes := by
  obtain ⟨selected⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted receipt.operator
  have names : selected.traitName = port.principal.traitName ∧
      selected.methodName = port.principal.methodName := by
    rcases port.dispatch with ⟨operator, operand, form, dispatch⟩ |
      ⟨operator, left, right, form, dispatch⟩
    · have actual := selected.dispatch
      rw [form] at actual
      exact CallablePreparedOperatorSourceBounds.unary_dispatch_unique actual dispatch
    · have actual := selected.dispatch
      rw [form] at actual
      exact CallablePreparedOperatorSourceBounds.binary_dispatch_unique actual dispatch
  obtain ⟨operand, parameterTypes, returnTypes, predicates, children, profile, proves, result⟩ :=
    CallableIndexedOwnedOperatorSourceAdmission.source_facts selected unique receipt.metadata.coercions typed
  exact ⟨operand, parameterTypes, returnTypes, predicates, children,
    names.1 ▸ names.2 ▸ profile, requirements receipt ▸ proves, result⟩

/-- Full Source typing identifies raw parameters and the result of the same
selected method, including the one-Unit versus no-argument distinction. -/
theorem raw_types
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ExpressionsHaveTypes source context receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) ∧
      port.principal.sourceBody.resultType = receipt.node.type := by
  obtain ⟨operand, parameterTypes, returnTypes, predicates, children, profile, proves, result⟩ :=
    source_facts receipt port unique typed
  obtain ⟨lexical, facts, certificate, bodyResult⟩ := port.selected.certificateOfProfile wellFormed
    runtime.signatures runtime.requirements.idsUnique profile proves
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend
  rw [port.sourceAt.parameters, List.map_map] at types
  exact ⟨types ▸ children, bodyResult.trans result.symm⟩

/-- The genuinely reached operand heap is transported to the selected method's
Source context. The full dictionary remains the one retained by the port. -/
theorem at_values
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    {heap : Dynamic.Heap} {arguments : List Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body))) :
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap ∧
      Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types ∧
      port.principal.sourceBody.resultType = receipt.node.type := by
  obtain ⟨operand, parameterTypes, returnTypes, predicates, _, profile, proves, result⟩ :=
    source_facts receipt port unique typed
  obtain ⟨lexical, facts, certificate, bodyResult⟩ := port.selected.certificateOfProfile wellFormed
    runtime.signatures runtime.requirements.idsUnique profile proves
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := argumentsTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq port.sourceAt.extended
  rw [port.sourceAt.parameters, List.map_map] at types
  exact ⟨port.principal.source_frame.context.symm ▸ bodyHeap,
    port.principal.source_frame.context.symm ▸ (types ▸ bodyArguments), bodyResult.trans result.symm⟩

/-- Native bundles are aligned only after the raw row has fixed the arity. -/
theorem represented_arguments
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body))
      (receipt.codes.map (·.type)) arguments payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads := by
  have binderCount : arguments.length = port.principal.named.inputs.length := by
    simpa only [List.length_map] using
      (CallableIndexedOwnedStoredArgumentAlignment.source_length represented).symm
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (port.principal.named.inputs.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type receipt.codes).symm.trans
      (receipt.parameter.symm.trans
        ((congrArg SourceCoreCalls.Signature.parameterType port.signature).symm.trans port.sourceAt.parameterType))
  exact CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    port.principal.named.inputs represented binderCount rfl nativePacked

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalRootBounds
/-! The numeric family quantifies over roots with actual complete cache state.
Every invocation produces this same carrier through its parameter allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalRootBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedMethodRootStaticSupport (RootAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
  (faults : RecursiveStageMeaning.FaultRep)

def PreservesRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    PreservesAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model stages invocation (Point scope expression lowered) faults size

def ReflectsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    ReflectsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model stages invocation (Point scope expression lowered) faults size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalRootBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyCompilerSupport
/-! Original Source compilation issues the recursive static Root internally.
  CallsReady belongs to the exact certificate returned by the existing issuer.
  Policy, raw typing, declarations, coercions and diagnostic interpretation
  remain genuine static inputs. This producer does not transport Code.view,
  choose a body packet, or supply any expression/body execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel compilerFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode} {rawType : TypeSystem.Ty}
  {semanticFaults : FunctionCalls.FaultRep}

/-- The certificate is issued from this original Source's actual accepted
  action. Reachable call authority stays indexed by that exact issued proof. -/
def RootData.of_steps_compiled {directSites : DeclarationInstantiation → Prop}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (unique : NodeOccurrencesUnique invocation.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.StepPolicyFor
      policy compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source scope reasonAt directSites)
    (coercions : ∀ id actualNode,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax invocation.source id directSites →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [])
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      invocation.source expression directSites)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
      compilation invocation.source scope expression reasonAt = .ok lowered)
    (callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_steps_functions
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted))
    (rawResult : node.type = rawType)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context invocation.source)
    (covers : invocation.evidence.Covers context)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (uninitialized : ∀ current id code,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source context reasonAt current id code →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) :
    RootData compiled policy lowerBody compilation readFuel context invocation reasonAt scope
      expression lowered rawType semanticFaults :=
  { compilerFuel := compilerFuel
    accepted := accepted
    certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_steps_functions
      (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
      native active callables unique declarations policyFor coercions syntaxTree found typed accepted
    node := node
    found := found
    rawResult := rawResult
    typed := typed
    sameLedger := sameLedger
    runtimeLedger := runtimeLedger
    unique := unique
    wellFormed := wellFormed
    runtime := runtime
    covers := covers
    actualFunctionType := actualFunctionType
    uninitialized := fun current id code receipt _reached => uninitialized current id code receipt
    callsReady := callsReady }

def RootData.of_sites_compiled {directSites : DeclarationInstantiation → Prop}
    (ordinary : ∀ i, directSites i → CallableIndexedOwnedPreparedStagedDirectCallCertificates.Ordinary compilation.plan i)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (unique : NodeOccurrencesUnique invocation.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
      policy compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source scope reasonAt directSites)
    (coercions : ∀ id actualNode,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax invocation.source id directSites →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [])
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      invocation.source expression directSites)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
      compilation invocation.source scope expression reasonAt = .ok lowered)
    (callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_sites_functions ordinary
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted))
    (rawResult : node.type = rawType)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context invocation.source)
    (covers : invocation.evidence.Covers context)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (uninitialized : ∀ current id code,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source context reasonAt current id code →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) :
    RootData compiled policy lowerBody compilation readFuel context invocation reasonAt scope
      expression lowered rawType semanticFaults :=
  { compilerFuel := compilerFuel
    accepted := accepted
    certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_sites_functions ordinary
      (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
      native active callables unique declarations policyFor coercions syntaxTree found typed accepted
    node := node
    found := found
    rawResult := rawResult
    typed := typed
    sameLedger := sameLedger
    runtimeLedger := runtimeLedger
    unique := unique
    wellFormed := wellFormed
    runtime := runtime
    covers := covers
    actualFunctionType := actualFunctionType
    uninitialized := fun current id code receipt _reached => uninitialized current id code receipt
    callsReady := callsReady }

/-- Packaging retains all actual compiler indices while fixing the original
  Source invocation, parameter context, physical occurrence and lowered child. -/
def CanonicalRootAt.of_steps_compiled {directSites : DeclarationInstantiation → Prop}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (unique : NodeOccurrencesUnique invocation.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.StepPolicyFor
      policy compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source scope reasonAt directSites)
    (coercions : ∀ id actualNode,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax invocation.source id directSites →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [])
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      invocation.source expression directSites)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
      compilation invocation.source scope expression reasonAt = .ok lowered)
    (callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_steps_functions
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted))
    (rawResult : node.type = rawType)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context invocation.source)
    (covers : invocation.evidence.Covers context)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (uninitialized : ∀ current id code,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source context reasonAt current id code →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (directReady : ∀ {callFuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        policy lowerBody callFuel compilation (.initial compiled.compatible.checked)
        invocation.source callScope callId callee ids instantiation reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_steps_functions
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted) →
      Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence
        compiler (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) context invocation.evidence))
    (indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_steps_functions
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted)) :
    CanonicalRootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      context invocation scope expression lowered semanticFaults :=
  CanonicalRootAt.ofRoot ((RootData.of_steps_compiled
    (compiled := compiled) (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (compilerFuel := compilerFuel) (context := context) (invocation := invocation)
    (reasonAt := reasonAt) (scope := scope) (expression := expression) (lowered := lowered)
    (node := node) (rawType := rawType) (semanticFaults := semanticFaults)
    native active callables unique declarations policyFor coercions syntaxTree found typed accepted callsReady rawResult
    sameLedger runtimeLedger wellFormed runtime covers actualFunctionType uninitialized).canonical_with directReady indexReady
    (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_steps _ syntaxTree policyFor))

def CanonicalRootAt.of_sites_compiled {directSites : DeclarationInstantiation → Prop}
    (ordinary : ∀ i, directSites i → CallableIndexedOwnedPreparedStagedDirectCallCertificates.Ordinary compilation.plan i)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (unique : NodeOccurrencesUnique invocation.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
      policy compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source scope reasonAt directSites)
    (coercions : ∀ id actualNode,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax invocation.source id directSites →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [])
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      invocation.source expression directSites)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
      compilation invocation.source scope expression reasonAt = .ok lowered)
    (callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_sites_functions ordinary
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted))
    (rawResult : node.type = rawType)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context invocation.source)
    (covers : invocation.evidence.Covers context)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (uninitialized : ∀ current id code,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source context reasonAt current id code →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    (indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_sites_functions ordinary
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted)) :
    CanonicalRootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      context invocation scope expression lowered semanticFaults :=
  CanonicalRootAt.ofRoot ((RootData.of_sites_compiled ordinary
    (compiled := compiled) (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (compilerFuel := compilerFuel) (context := context) (invocation := invocation)
    (reasonAt := reasonAt) (scope := scope) (expression := expression) (lowered := lowered)
    (node := node) (rawType := rawType) (semanticFaults := semanticFaults)
    native active callables unique declarations policyFor coercions syntaxTree found typed accepted callsReady rawResult
    sameLedger runtimeLedger wellFormed runtime covers actualFunctionType uninitialized).canonical rows complete plan globals (fun compiler path => by
      have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path syntaxTree
      refine ⟨ordinary _ (actualTree.direct_site compiler.metadata.found compiler.form), ?_⟩
      have sameScope := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_scope path
      exact compiler.ordinary_requirements
        (sameScope.symm ▸ policyFor.special _ actualTree) (policyFor.read _ actualTree)) indexReady
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_steps _ syntaxTree (policyFor.steps ordinary)))

def RootData.of_general_compiled
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (unique : NodeOccurrencesUnique invocation.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
      policy compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source scope reasonAt)
    (coercions : ∀ id actualNode,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax invocation.source id →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [])
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      invocation.source expression)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
      compilation invocation.source scope expression reasonAt = .ok lowered)
    (callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_general_functions
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted))
    (rawResult : node.type = rawType)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context invocation.source)
    (covers : invocation.evidence.Covers context)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (uninitialized : ∀ current id code,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source context reasonAt current id code →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) :
    RootData compiled policy lowerBody compilation readFuel context invocation reasonAt scope
      expression lowered rawType semanticFaults :=
  RootData.of_sites_compiled (fun _ mono => mono.ordinary compilation.plan)
    native active callables unique declarations policyFor coercions syntaxTree found typed accepted callsReady rawResult
    sameLedger runtimeLedger wellFormed runtime covers actualFunctionType uninitialized

def CanonicalRootAt.of_general_compiled
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (unique : NodeOccurrencesUnique invocation.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
      policy compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source scope reasonAt)
    (coercions : ∀ id actualNode,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax invocation.source id →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [])
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      invocation.source expression)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
      compilation invocation.source scope expression reasonAt = .ok lowered)
    (callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_general_functions
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted))
    (rawResult : node.type = rawType)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context invocation.source)
    (covers : invocation.evidence.Covers context)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (uninitialized : ∀ current id code,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source context reasonAt current id code →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    (indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_general_functions
        (policy := policy) (body := lowerBody) (compilation := compilation) (readFuel := readFuel)
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (source := invocation.source) (context := context) (reasonAt := reasonAt) (scope := scope)
        native active callables unique declarations policyFor coercions syntaxTree found typed accepted)) :
    CanonicalRootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      context invocation scope expression lowered semanticFaults :=
  CanonicalRootAt.of_sites_compiled (fun _ mono => mono.ordinary compilation.plan)
    native active callables unique declarations policyFor coercions syntaxTree found typed accepted callsReady rawResult
    sameLedger runtimeLedger wellFormed runtime covers actualFunctionType uninitialized rows complete plan globals indexReady

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCanonicalBodyStaticSupport
/-! Canonical terminal closure roots retain the same compiler, original Source
and parameter context. Actual captured global values are supplied later by the
real parameter entry, and are not a static support premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues

structure SelectedCanonicalBody {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
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
  «prefix» : code.compilation.administrativePrefix = 1
  roots : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CanonicalRoot compiled code.policy code.lowerBody code.compilation readFuel inputs.context child
      code.reasonAt
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child function.resultType semanticFaults headers

def SelectedCanonicalBody.rootAt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    {code : Code compiled.indexed function localScope administrative}
    {inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
    {stages : Staging.Recursive.Registry}
    {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
    {semanticFaults : FunctionCalls.FaultRep}
    (support : SelectedCanonicalBody (headers := headers) code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    CanonicalRootAt compiled headers inputs.context child
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child semanticFaults :=
  CanonicalRootAt.ofRoot (support.roots child selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots
/-! Original compiler roots are issued from the actual accepted view action.
The view transport and recursive extractor run internally. Original raw typing,
declarations, policy profiles, reached call authority and runtime admission
remain authentic static inputs. The terminal bridge identifies the literal
expression callback and clips its budget by the real Code fuel. No expression
execution, Below law, body result or original-action equality is an input.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (Root RootAt)

/-- Original admission has no compiler output or expression meaning field.
Call authority is supplied separately for the exact internally issued tree. -/
structure OriginalAuthority (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (rawType : TypeSystem.Ty)
    (semanticFaults : FunctionCalls.FaultRep) where
  node : ExpressionNode
  found : invocation.source.lookupExpression? expression = some node
  rawResult : node.type = rawType
  typed : ExpressionHasType invocation.source context expression node.type
  declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context
  coercions : ∀ id node, Syntax invocation.source id →
    invocation.source.lookupExpression? id = some node → node.coercions = []
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
    Reaches invocation.source [.expression expression] (.expression id) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)

section ViewActionOn
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel fuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}

variable
  (edited : LocalView invocation.source view changed)
  (avoids : Avoids invocation.source roots changed)
  (sourceProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source scope reasonAt (fun id => Reaches invocation.source roots (.expression id)))
  (viewProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    view scope reasonAt (fun id => Reaches view roots (.expression id)))
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
  (tree : Syntax view expression)
  (reached : Reaches invocation.source roots (.expression expression))
  (authority : OriginalAuthority compiled policy compilation readFuel context invocation
    reasonAt scope expression rawType semanticFaults)
  (acceptedView : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
    compilation view scope expression reasonAt = .ok lowered)

include edited avoids sourceProfile viewProfile callables tree reached authority acceptedView

/-- The genuine original acceptance is constructed before recursive extraction.
Only original lookup/type/declaration authority feeds that extractor. -/
theorem issued_certificate_on :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
      policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression lowered := by
  have acceptedOriginal :=
    CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.accepted_original_on
      edited avoids sourceProfile viewProfile callables fuel tree reached acceptedView
  exact CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions_on
    authority.unique authority.declarations sourceProfile
    (fun parent found edge => Reaches.expression parent found edge)
    (fun id node _ tree found => authority.coercions id node tree found)
    (CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.syntax_original
      edited avoids tree reached) reached authority.found authority.typed acceptedOriginal

/-- Ready is static Port authority for calls inside this exact issued proof.
It cannot stand for execution or a certificate family on unrelated terminals. -/
def of_view_action_on
    (ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (issued_certificate_on edited avoids sourceProfile viewProfile callables
        tree reached authority acceptedView)) :
    Root compiled policy body compilation readFuel context invocation reasonAt
      scope expression lowered rawType semanticFaults where
  compilerFuel := fuel
  accepted := CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.accepted_original_on
    edited avoids sourceProfile viewProfile callables fuel tree reached acceptedView
  certificate := issued_certificate_on edited avoids sourceProfile viewProfile callables
    tree reached authority acceptedView
  node := authority.node
  found := authority.found
  rawResult := authority.rawResult
  typed := authority.typed
  sameLedger := authority.sameLedger
  runtimeLedger := authority.runtimeLedger
  unique := authority.unique
  wellFormed := authority.wellFormed
  runtime := authority.runtime
  covers := authority.covers
  actualFunctionType := authority.actualFunctionType
  uninitialized := authority.uninitialized
  callsReady := ready
  noMethods := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy_on _
    (CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.syntax_original edited avoids tree reached) reached sourceProfile
  noDirect := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax _
    (CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.syntax_original edited avoids tree reached)
  noIndexes := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax _
    (CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.syntax_original edited avoids tree reached)

/-- Existential compiler packaging retains the same original indices. -/
def rootAt_of_view_action_on
    (ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (issued_certificate_on edited avoids sourceProfile viewProfile callables
        tree reached authority acceptedView)) :
    RootAt compiled context invocation scope expression lowered semanticFaults :=
  RootAt.ofRoot (of_view_action_on edited avoids sourceProfile viewProfile callables
    tree reached authority acceptedView ready)
end ViewActionOn

section ViewAction
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel fuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}

variable
  (edited : LocalView invocation.source view changed)
  (avoids : Avoids invocation.source roots changed)
  (sourceProfile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source scope reasonAt)
  (viewProfile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    view scope reasonAt)
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
  (tree : Syntax view expression)
  (reached : Reaches invocation.source roots (.expression expression))
  (authority : OriginalAuthority compiled policy compilation readFuel context invocation
    reasonAt scope expression rawType semanticFaults)
  (acceptedView : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
    compilation view scope expression reasonAt = .ok lowered)

include edited avoids sourceProfile viewProfile callables tree reached authority acceptedView

theorem issued_certificate :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
      policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression lowered :=
  issued_certificate_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables
    tree reached authority acceptedView

def of_view_action
    (ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (issued_certificate edited avoids sourceProfile viewProfile callables
        tree reached authority acceptedView)) :
    Root compiled policy body compilation readFuel context invocation reasonAt
      scope expression lowered rawType semanticFaults :=
  of_view_action_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables
    tree reached authority acceptedView ready

def rootAt_of_view_action
    (ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation)
      (issued_certificate edited avoids sourceProfile viewProfile callables
        tree reached authority acceptedView)) :
    RootAt compiled context invocation scope expression lowered semanticFaults :=
  RootAt.ofRoot (of_view_action edited avoids sourceProfile viewProfile callables
    tree reached authority acceptedView ready)
end ViewAction

section Terminal
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {stages : Staging.Recursive.Registry}
  (code : Code compiled.indexed function localScope administrative)
  (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages)

private abbrev parameterScope
    {compiled : SourceCoreUnifiedCompilation.Compiled} {function : Dynamic.Closure}
    {localScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function localScope administrative) : SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope

/-- Invert a standalone statement list before instantiating a dependent Code. -/
private theorem head_of_terminal
    {source view : TypedSource} {expression : ExpressionId} {statements : List StatementId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      view expression statements)
    (child : Staging.Recursive.Scope) (sameSource : child.source = source) :
    CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression statements := by
  cases terminal with
  | @returning id node rest found form =>
      have childFound : child.source.lookupStatement? id = some node := by
        rw [sameSource]
        exact metadata.statement found
      exact .returning rest (lookupStatement?_sound childFound) form
  | @tail id node found form =>
      have childFound : child.source.lookupStatement? id = some node := by
        rw [sameSource]
        exact metadata.statement found
      exact .tail (lookupStatement?_sound childFound) form

private theorem reached_of_terminal
    {source view : TypedSource} {expression : ExpressionId} {statements : List StatementId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      view expression statements) :
    Reaches source (statements.map NodeId.statement) (.expression expression) := by
  cases terminal with
  | returning rest found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
  | tail found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])

/-- Metadata transports only the actual full statement node. Registry source
then selects the original child Source; no expression type transport is used. -/
theorem original_head (child : Staging.Recursive.Scope)
    (selected : stages.Closure function child) :
    CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child
      packet.expression function.body :=
  head_of_terminal code.viewOfSource packet.receipt.terminal child (stages.source selected)

/-- The original terminal statement itself supplies expression reachability. -/
theorem terminal_reached :
    Reaches function.source (function.body.map NodeId.statement)
      (.expression packet.expression) :=
  reached_of_terminal code.viewOfSource packet.receipt.terminal

/-- Real original frame typing at the retained parameter entry supplies the
child node/type, independently of its projected native result. -/
theorem terminal_raw_type (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (prepared := compiled.indexed) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ node, child.source.lookupExpression? packet.expression = some node ∧
      node.type = function.resultType ∧
      ExpressionHasType child.source inputs.context packet.expression node.type := by
  exact CallableIndexedOwnedPreparedStagedTerminalBodyTyping.at_parameters
    frame inputs.extended (stages.source selected) (original_head code packet child selected)

/-- This callback link is a genuine factory obligation. A BodyWith equality
for the statement lowerer alone does not supply it for an arbitrary packet. -/
theorem accepted_view_action
    (callback : packet.policy.lowerExpression =
      FunctionCode.children code.policy code.lowerBody code.fuel code.compilation)
    (reason : packet.reasonAt = code.reasonAt) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody
      (min packet.receipt.childFuel code.fuel) code.compilation code.view
      (parameterScope code) packet.expression code.reasonAt = .ok packet.receipt.child := by
  have callbackAt := congrArg
    (fun lower : SourceCoreFunctions.ExpressionLowerer =>
      lower packet.receipt.childFuel code.view (parameterScope code)
        packet.expression packet.reasonAt) callback
  have reasonAt := congrArg
    (fun currentReason : ExpressionId → Word =>
      FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
        packet.receipt.childFuel code.view (parameterScope code)
        packet.expression currentReason) reason
  have generated := reasonAt.symm.trans (callbackAt.symm.trans packet.receipt.generated)
  simpa only [FunctionCode.children] using generated

/-- Clipped fuel belongs to the actual child callback. The original Source
action is an output, not an assumed action equality. -/
theorem accepted_terminal_original
    {readFuel : Nat} {changed : List ExpressionId}
    (edited : LocalView function.source code.view changed)
    (avoids : Avoids function.source (function.body.map NodeId.statement) changed)
    (sourceProfile : PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      function.source (parameterScope code) code.reasonAt)
    (viewProfile : PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      code.view (parameterScope code) code.reasonAt)
    (tree : Syntax code.view packet.expression)
    (callback : packet.policy.lowerExpression =
      FunctionCode.children code.policy code.lowerBody code.fuel code.compilation)
    (reason : packet.reasonAt = code.reasonAt)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody
      (min packet.receipt.childFuel code.fuel) code.compilation child.source
      (parameterScope code) packet.expression code.reasonAt = .ok packet.receipt.child := by
  have original :=
    CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.accepted_original
      edited avoids sourceProfile viewProfile code.callables
      (min packet.receipt.childFuel code.fuel) tree (terminal_reached code packet)
      (accepted_view_action code packet callback reason)
  simpa only [stages.source selected] using original


/-- The terminal packet, rather than a supplied accepted-view equation,
feeds this Root. The exact original raw authority remains an issuer input. -/
def of_terminal
    {readFuel : Nat} {changed : List ExpressionId} {semanticFaults : FunctionCalls.FaultRep}
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (prepared := compiled.indexed) code)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (edited : LocalView child.source code.view changed)
    (avoids : Avoids child.source (function.body.map NodeId.statement) changed)
    (sourceProfile : PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      child.source (parameterScope code) code.reasonAt)
    (viewProfile : PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      code.view (parameterScope code) code.reasonAt)
    (tree : Syntax code.view packet.expression)
    (callback : packet.policy.lowerExpression =
      FunctionCode.children code.policy code.lowerBody code.fuel code.compilation)
    (reason : packet.reasonAt = code.reasonAt)
    (authority : OriginalAuthority compiled code.policy code.compilation readFuel
      inputs.context child code.reasonAt (parameterScope code) packet.expression
      function.resultType semanticFaults)
    (ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child)
      (issued_certificate edited avoids sourceProfile viewProfile code.callables tree
        (by simpa only [stages.source selected] using terminal_reached code packet)
        authority (accepted_view_action code packet callback reason))) :
    Root compiled code.policy code.lowerBody code.compilation readFuel inputs.context child
      code.reasonAt (parameterScope code) packet.expression packet.receipt.child
      function.resultType semanticFaults :=
  of_view_action edited avoids sourceProfile viewProfile code.callables tree
    (by simpa only [stages.source selected] using terminal_reached code packet)
    authority (accepted_view_action code packet callback reason) ready

/-- The numeric family can consume this literal terminal RootAt. No compiler
indices or parameter context are inferred from an erased native type. -/
def rootAt_of_terminal
    {readFuel : Nat} {changed : List ExpressionId} {semanticFaults : FunctionCalls.FaultRep}
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (prepared := compiled.indexed) code)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (edited : LocalView child.source code.view changed)
    (avoids : Avoids child.source (function.body.map NodeId.statement) changed)
    (sourceProfile : PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      child.source (parameterScope code) code.reasonAt)
    (viewProfile : PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      code.view (parameterScope code) code.reasonAt)
    (tree : Syntax code.view packet.expression)
    (callback : packet.policy.lowerExpression =
      FunctionCode.children code.policy code.lowerBody code.fuel code.compilation)
    (reason : packet.reasonAt = code.reasonAt)
    (authority : OriginalAuthority compiled code.policy code.compilation readFuel
      inputs.context child code.reasonAt (parameterScope code) packet.expression
      function.resultType semanticFaults)
    (ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child)
      (issued_certificate edited avoids sourceProfile viewProfile code.callables tree
        (by simpa only [stages.source selected] using terminal_reached code packet)
        authority (accepted_view_action code packet callback reason))) :
    RootAt compiled inputs.context child (parameterScope code) packet.expression
      packet.receipt.child semanticFaults :=
  RootAt.ofRoot (of_terminal code packet inputs child selected edited avoids
    sourceProfile viewProfile tree callback reason authority ready)

end Terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalIndirectGlobalPrefixes
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalIndirectGlobalPrefixes
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


/-- The uncompleted named branch retains the actual global value, all three
Source prefixes and application suffix, and every native prefix witness. -/
def GlobalAppliedPrefix (calleeSize argumentsSize applicationSize : Nat)
    (sourceValue : Dynamic.Value) (calleeHeap argumentsHeap : Dynamic.Heap)
    (sources : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ function : Dynamic.GlobalFunction,
    sourceValue = .global function ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after ∧
    CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.ValuesPrefix (functionModel := functions)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources

/-- This remaining branch retains the actual global value and complete
original user prefix. It supplies no named application or body meaning. -/
def GlobalApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ function : Dynamic.GlobalFunction,
    ∃ rawParameter rawResult,
      calleeNode.type = .function rawParameter rawResult ∧
      TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
    ∃ calleeSize argumentsSize calleeHeap calleeStore calleeMap calleeWorld sources values carrier
        argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
      CallableIndexedOwnedPreparedStagedIndirectNativePrefix.CalleePost
        (registry := completion.result.context.registry) (context := context) (actual := actual)
        (ξ := ξ) (calleeNode := calleeNode) bridge functions compiler initial
        (.global function) calleeHeap carrier calleeStore calleeMap calleeWorld ∧
      Dynamic.ValueHasType context calleeHeap (.global function) calleeNode.type ∧
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
        invocation context environment before callee (.value (.global function)) calleeHeap ∧
      Staging.CallBoundary.GuardAccepts invocation.guards id ids (.global function) ∧
      Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
        invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
      DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
      GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
        (.global function) carrier compiler.calleeCode.type ∧
      CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.CallView originalNode compiler.original originalMetadata metadata ∧
      CallableIndexedOwnedContextualCalleeStageReceipts.BoundaryAt
        sidecar prepared.site callee ids originalMetadata originalNode (.global function) carrier ∧
      GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∃ suffixSize, EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
        argumentsStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ suffixSize < budget

/-- The remaining named branch carries the same original parent size and a
strict actual Source application child, alongside all original prefix receipts. -/
def GlobalAt (budget size : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources,
    size = Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize] ∧
    applicationSize < budget ∧
    GlobalAppliedPrefix (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial calleeSize argumentsSize applicationSize sourceValue
      calleeHeap argumentsHeap sources outcome after


end CallableIndexedOwnedPreparedStagedPhysicalIndirectGlobalPrefixes
end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationEntries
/-! Actual method hook and marked parameter entry, using only the original
Source frame and compiler prefix. The body has no execution contract here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationEntries
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds (ParameterEntry parameter_entry_with_state parameter_prefix_with_state)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
  (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt generation
    (.initial compiled.compatible.checked) sourceBody dictionary)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)

theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

theorem next_evaluates (index : Int) (actual : Environment) (initialStore : Store) (saved : Value) :
    Evaluates (saved :: actual) initialStore
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) initialStore := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

include sourceAt in
theorem accepted_parameters : SourceCoreSourceCells.bindParameters
    (CallableIndexedNamedGeneration.allocator compiled.indexed named) sourceBody.source [] named.inputs
    named.signature.resultType SourceCoreFunctions.argumentProjection generation.body = .ok generation.parameterCode := by
  rw [sourceAt.sameSource]
  exact generation.parametersCompiled

include sameFrame in
/-- Both original reads refer to the same physical cell. Its saved native
frame therefore agrees with the actual selected pool row; no ghost-history
substitution or equality of record lists is assumed. -/
theorem installed_current_eq : installed.current = (caller.rows owner.position).authority.current := by
  have physical : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have poolRead : store.read? owner.key.frameLocation = some
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) := by
    simpa only [physical] using (caller.rows owner.position).authority.frame.read
  have originalRead : store.read? owner.key.frameLocation = some
      (encode compiled.indexed.ancestry.layout.frame installed.current) := by
    simpa only [sameFrame] using installed.caller.read
  have encoded := Option.some.inj (originalRead.symm.trans poolRead)
  have decoded := congrArg (decode compiled.indexed.ancestry.layout.frame) encoded
  rw [decode_encode, decode_encode] at decoded
  exact Option.some.inj decoded

include sourceAt installed represented sameFrame heaps in
/-- The actual pool is installed at the method's real physical frame before
shared marked parameters allocate every snapshot. Complete method captures and
ordered canonical spines accompany the actual parameter post witness. -/
theorem parameters_with_state :
    ∃ originId index metadata,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named originId) (some metadata) ∧
      generation.output = withFrame (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) generation.parameterCode ∧
    ∃ entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body,
    ∃ added : Environment, added.length = named.inputs.length ∧
      entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  obtain ⟨originId, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry generation.hook
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have typed : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [physical] using authority.typed
  let installedPool := install caller owner.position (.stable history)
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), installed.canonical⟩ := installedPool
  obtain ⟨installedHeaps, nextCell⟩ := CallableIndexedBodyFrames.install (CallableIndexedAmbient.frame_registered compiled.indexed) heaps unmapped typed
    (show CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame owner.key.frameLocation authority.current authority.ghost store from
      by simpa only [physical] using authority.frame) (.stable history)
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation (.state index) :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position history
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads) named.signature.parameterType
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    sourceAt.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world (CallableIndexedAmbient.frame_registered compiled.indexed) authority.current) (.cons packTyped installed.captureTyped))
  have actualLayout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      (DataPatternValues.packValues payloads :: installed.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: installed.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  obtain ⟨entry, added, length, spine, reached, related⟩ := parameter_entry_with_state
    (compiled := compiled) (program := program) (headers := headers) (keys := keys)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (layouts := compiled.indexed.layouts) (owner := named.signature.key) (active := [])
    (layout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (function := methodFunction generation sourceBody dictionary) functions
    (fun error => .sourceAllocation (reprStr error)) (accepted_parameters generation sourceAt)
    sourceAt.parameters sourceAt.parameters sourceAt.extended rfl (CallableIndexedAmbient.frame_registered compiled.indexed) represented
    installed.environments installedHeaps installed.locals actualLayout actualTyped
    (by simpa only [sameFrame] using installed.canonicalReference) nextCell.read unmapped producer initial readyAt
  exact ⟨originId, index, metadata, owned, history, emitted, entry, added, length, spine, reached,
    (install_related caller owner.position (.stable history)).trans related⟩

include sourceAt installed represented sameFrame heaps in
/-- Original native hook inversion selects its strict parameter child; the
shared parameter fold produces the actual body pool and keeps the exact final
saved-frame write from that same completion. -/
theorem body_prefix_with_state {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) :
    ∃ originId index metadata prefixSize bodyStore,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named originId) (some metadata) ∧
      prefixSize < size ∧
      finalStore = bodyStore.set owner.key.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) ∧
    ∃ entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body prefixSize value bodyStore,
    ∃ added : Environment, added.length = named.inputs.length ∧
      entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have typed : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [physical] using authority.typed
  have reference : (DataPatternValues.packValues payloads :: installed.captured)[installed.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [sameFrame, Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using installed.capturedReference
  obtain ⟨originId, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry generation.hook
  have renamed : generation.output.rename installed.embedding.lift = withFrame
      (.var (installed.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (generation.parameterCode.rename installed.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  rw [renamed] at completed
  obtain ⟨nextSize, prefixSize, nextValue, nextStore, bodyStore, nextCompletion, prefixCompletion,
    _sizeBound, smaller, restored⟩ := RecursiveNamedCallBounds.with_frame (.var reference) read completed
  obtain ⟨nextEq, nextStoreEq⟩ := evaluation_deterministic nextCompletion.sound
    (next_evaluates index (DataPatternValues.packValues payloads :: installed.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current))
  rw [nextEq, nextStoreEq, ← rename_prefix] at prefixCompletion
  let installedPool := install caller owner.position (.stable history)
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), installed.canonical⟩ := installedPool
  obtain ⟨installedHeaps, nextCell⟩ := CallableIndexedBodyFrames.install (CallableIndexedAmbient.frame_registered compiled.indexed) heaps unmapped typed
    (show CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame owner.key.frameLocation authority.current authority.ghost store from
      by simpa only [physical] using authority.frame) (.stable history)
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation (.state index) :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position history
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads) named.signature.parameterType
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    sourceAt.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world (CallableIndexedAmbient.frame_registered compiled.indexed) authority.current) (.cons packTyped installed.captureTyped))
  have actualLayout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      (DataPatternValues.packValues payloads :: installed.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: installed.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  obtain ⟨entry, added, length, spine, reached, related⟩ := parameter_prefix_with_state
    (compiled := compiled) (program := program) (headers := headers) (keys := keys)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (layouts := compiled.indexed.layouts) (owner := named.signature.key) (active := [])
    (layout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (function := methodFunction generation sourceBody dictionary) functions
    (fun error => .sourceAllocation (reprStr error)) (accepted_parameters generation sourceAt)
    sourceAt.parameters sourceAt.parameters sourceAt.extended rfl (CallableIndexedAmbient.frame_registered compiled.indexed) represented
    installed.environments installedHeaps installed.locals actualLayout actualTyped
    (by simpa only [sameFrame] using installed.canonicalReference) nextCell.read unmapped producer initial readyAt prefixCompletion
  exact ⟨originId, index, metadata, prefixSize, bodyStore, owned, history, smaller, restored,
    entry, added, length, spine, reached, (install_related caller owner.position (.stable history)).trans related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationBounds
/-! Staged method invocation enters the actual marked parameter prefix and
restores the caller from the body's reached pool. Both callbacks receive the
real complete cache and slot layout, and preserve semantic and stage faults. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationBounds
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds (ParameterEntry)
open CallableIndexedOwnedPreparedStagedMethodInvocationEntries

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
  (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt generation
    (.initial compiled.compatible.checked) sourceBody dictionary)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)


variable {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] installed.canonical)

/-- The Source body callback starts at the exact parameter-produced state. -/
def SourceBodyAt (budget : Nat)
    {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) : Prop :=
  ∀ {size finalContext bodyOutcome outcome after},
    Staging.Recursive.Size.StatementsIn program stages true size child sourceAt.context entry.environment
      entry.heap generation.statements finalContext bodyOutcome after →
    Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome → size < budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (generation.body.rename entry.embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- Reflection uses the native body's independent strict grade. -/
def NativeBodyAt (budget : Nat)
    {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body prefixSize value finalStore)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) : Prop :=
  entry.childSize < budget →
    ∃ sourceSize finalContext bodyOutcome outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages true sourceSize child sourceAt.context entry.environment
        entry.heap generation.statements finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), finalMap, finalWorld, after, finalStore, entry.canonical⟩

def SourceContinuation (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (_history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_emitted : generation.output = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) generation.parameterCode)
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled entry.mapping entry.store →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical →
    SourceBodyAt (stages := stages) (child := child) (faults := faults)
      generation sourceAt functions budget entry reached

def NativeContinuation (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState) (prefixSize : Nat) (bodyStore : Store)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (_history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_prefixWithin : prefixSize < budget)
    {value : Value} {finalStore : Store}
    (_restored : finalStore = bodyStore.set owner.key.frameLocation
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body prefixSize value bodyStore)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled entry.mapping entry.store →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical →
    NativeBodyAt (stages := stages) (child := child) (faults := faults)
      generation sourceAt functions budget entry reached

include sourceAt installed represented sameFrame heaps physical slots in
theorem preserves (budget : Nat)
    (bodyMeaning : SourceContinuation (registry := registry) (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults) generation sourceAt functions installed budget)
    {bodySize : Nat} {environment : Dynamic.Environment} {bound after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome}
    (allocated : Dynamic.BindersAllocate [] before (methodFunction generation sourceBody dictionary).parameters
      arguments environment bound)
    (bodyTrace : Staging.Recursive.Size.StatementsIn program stages true bodySize child sourceAt.context environment
      bound generation.statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome)
    (within : bodySize < budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (generation.output.rename installed.embedding.lift) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨originId, index, metadata, owned, history, emitted, entry, added, length, spine, parameterState, parameterRelated⟩ :=
    parameters_with_state generation sourceAt functions installed represented owner caller sameFrame heaps
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  let physicalEntry := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine physical
    (by
      have same : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
        (caller.rows owner.position).frame_eq
      simpa only [same] using (caller.rows owner.position).authority.frame.read)
    (.state index) entry.frame parameterState slots (DataPatternValues.packValues payloads)
    (by simpa only [List.length_map, List.length_reverse] using length) spine
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated⟩ :=
    bodyMeaning originId index metadata owned history emitted entry added length spine parameterState parameterRelated
      physicalEntry.physical physicalEntry.base.property bodyTrace matched within
  have prefixEvaluation := entry.agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have reference : (DataPatternValues.packValues payloads :: installed.captured)[installed.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [sameFrame, Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using installed.capturedReference
  have evaluated := CallableContextFrames.withFrame_evaluates (.var reference) read
    (next_evaluates index (DataPatternValues.packValues payloads :: installed.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : generation.output.rename installed.embedding.lift = withFrame
      (.var (installed.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (generation.parameterCode.rename installed.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position (CallableIndexedAmbient.frame_registered compiled.indexed)
      finalHeaps worlds frame related
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩
  exact renamed.symm ▸ evaluated

include sourceAt installed represented sameFrame heaps physical slots in
theorem reflects (budget : Nat)
    (bodyMeaning : NativeContinuation (registry := registry) (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults) generation sourceAt functions installed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize environment bound finalContext bodyOutcome outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before (methodFunction generation sourceBody dictionary).parameters arguments environment bound ∧
      Staging.Recursive.Size.StatementsIn program stages true sourceSize child sourceAt.context environment
        bound generation.statements finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨originId, index, metadata, prefixSize, bodyStore, owned, history, strict, restored,
    entry, added, length, spine, parameterState, parameterRelated⟩ :=
    body_prefix_with_state generation sourceAt functions installed represented owner caller sameFrame heaps completed
  let physicalEntry := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine physical
    (by
      have same : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
        (caller.rows owner.position).frame_eq
      simpa only [same] using (caller.rows owner.position).authority.frame.read)
    (.state index) entry.frame parameterState slots (DataPatternValues.packValues payloads)
    (by simpa only [List.length_map, List.length_reverse] using length) spine
  obtain ⟨sourceSize, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld, bodyTrace, matched, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated⟩ :=
    bodyMeaning originId index metadata prefixSize bodyStore owned history
      (Nat.lt_of_lt_of_le strict within) restored entry added length spine parameterState parameterRelated
      physicalEntry.physical physicalEntry.base.property
      (Nat.lt_of_le_of_lt entry.bounded (Nat.lt_of_lt_of_le strict within))
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position (CallableIndexedAmbient.frame_registered compiled.indexed)
      finalHeaps worlds frame related
  subst finalStore
  exact ⟨sourceSize, entry.environment, entry.heap, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
    entry.allocation, bodyTrace, matched, result, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentBounds
/-! Ordered staged arguments are constructed from the actual compiler Tree
and strictly smaller expression results. Each successful child passes its
actual reached caller state to the next child. Both failure tags retain the
same originating scope, token and final state. Native reflection reconstructs
an independent Source grade from the original packed-helper computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

open CallableIndexedOwnedAdmittedStagedExpressionSequence (PostAdmission)

/-- Ordered operands retain their individual strict parent bounds. The list
has no extra grade: only the actual expression executions consume the budget. -/
inductive Trace (budget : Nat) (program : Program) (registry : Staging.Recursive.Registry)
    (scope : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) : Dynamic.Heap → List ExpressionId →
    Staging.Recursive.ValuesOutcome → Dynamic.Heap → Prop where
  | nil {heap} : Trace budget program registry scope context environment heap [] (.values []) heap
  | cons {headSize before middle after id ids value values}
      (head : Staging.Recursive.Size.Expression program registry headSize scope context environment before id (.value value) middle)
      (strict : headSize < budget)
      (tail : Trace budget program registry scope context environment middle ids (.values values) after) :
      Trace budget program registry scope context environment before (id :: ids) (.values (value :: values)) after
  | headFault {headSize before after id ids failure}
      (head : Staging.Recursive.Size.Expression program registry headSize scope context environment before id (.fault failure) after)
      (strict : headSize < budget) : Trace budget program registry scope context environment before (id :: ids) (.fault failure) after
  | tailFault {headSize before middle after id ids value failure}
      (head : Staging.Recursive.Size.Expression program registry headSize scope context environment before id (.value value) middle)
      (strict : headSize < budget)
      (tail : Trace budget program registry scope context environment middle ids (.fault failure) after) :
      Trace budget program registry scope context environment before (id :: ids) (.fault failure) after

theorem Trace.sized {budget : Nat} {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {ids : List ExpressionId} {outcome : Staging.Recursive.ValuesOutcome}
    (trace : Trace budget program registry scope context environment before ids outcome after) :
    ∃ size, Staging.Recursive.Size.Expressions program registry size scope context environment before ids outcome after := by
  induction trace with
  | nil => exact ⟨_, .nil⟩
  | cons head _strict _tail ih => obtain ⟨size, tail⟩ := ih; exact ⟨_, .cons head tail⟩
  | headFault head _strict => exact ⟨_, .headFault head⟩
  | tailFault head _strict _tail ih => obtain ⟨size, tail⟩ := ih; exact ⟨_, .tailFault head tail⟩

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem member_typing {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids types) :
    MemberTyping (context := context) (invocation := invocation) ids := by
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member found

variable {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}

private theorem preserves_values_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : Trace budget program registry invocation context environment
      before ids (.values sources) after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached := by
  induction tree generalizing mapping world actual actualContext before store ξ sources after with
  | nil =>
      cases execution
      exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial,
        admitted.rows, fun _ _ => admitted⟩
  | single found generated =>
      cases execution with
      | cons head strict tail =>
          cases tail
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | value payload =>
              exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
                finalHeaps, maps, worlds, frame, metadata, reached, related, post.rows,
                fun _ _ => post.at_value.2⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | cons head strict rest =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 rest
              have nonempty : values ≠ [] := by
                intro absent
                have lengths := restRep.length.2
                simp [absent] at lengths
              refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
                .cons (model.extend payload maps worlds) restRep, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
              rw [rename_prefix] at second
              have combined := LocalSequence.pair_success lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
              simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

private theorem preserves_fault_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : Trace budget program registry invocation context environment
      before ids (.fault failure) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.fault failure) reached := by
  induction tree generalizing mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
      cases execution with
      | headFault failed strict =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
      | tailFault _ _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | headFault failed strict =>
          obtain ⟨value, finalStore, finalMap, finalWorld, first, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first
      | tailFault head strict failed =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 failed
              refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post⟩
              rw [rename_prefix] at second
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

/-- Actual list typing supplies each used child's stored type. The successful
prefix retains the same cumulative caller records at every reached state. -/
theorem preserves_values (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ sources},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    Trace budget program registry invocation context environment before ids (.values sources) after →
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached :=
  preserves_values_with_members bridge budget tree (member_typing unique typing)

/-- A failing argument stops the original helper at the same reached caller
pool; no later argument runs and neither failure tag is relabeled. -/
theorem preserves_fault (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ failure},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    Trace budget program registry invocation context environment before ids (.fault failure) after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.fault failure) reached :=
  preserves_fault_with_members bridge budget tree (member_typing unique typing)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceArguments
/-! The independent unary/binary trace supplies actual ordered operand grades,
selected body and dictionary. Authentic roots and binder extensions identify
the compiler body's exact Source context without an execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open Staging.Recursive
open Solcore.SourceSemantics.Dynamic
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
open CallableIndexedOwnedPreparedStagedMethodArgumentBounds (Trace)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id reasonAt lowered)
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context invocation.evidence stages)

private theorem roots_unique {nodes : List NodeId} {left right : List StatementId}
    (first : StatementRoots nodes left) (second : StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons first ih => cases second with | cons second => exact congrArg (List.cons _) (ih second)

theorem unary_dispatch {operator : Syntax.UnaryOp} {operand : ExpressionId}
    (form : receipt.node.form = .unary operator operand) :
    UnaryTraitDispatch operator port.principal.traitName port.principal.methodName := by
  rcases port.dispatch with ⟨actual, child, actualForm, dispatch⟩ | ⟨actual, left, right, actualForm, _⟩
  · obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actualForm.symm.trans form)
    exact dispatch
  · simp [form] at actualForm

theorem binary_dispatch {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (form : receipt.node.form = .binary left operator right) :
    BinaryTraitDispatch operator port.principal.traitName port.principal.methodName := by
  rcases port.dispatch with ⟨actual, child, actualForm, _⟩ | ⟨actual, first, second, actualForm, dispatch⟩
  · simp [form] at actualForm
  · obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actualForm.symm.trans form)
    exact dispatch

private theorem dispatch_continues {operator : Syntax.BinaryOp} {traitName methodName : String}
    (dispatch : BinaryTraitDispatch operator traitName methodName) (value : Dynamic.Value) :
    EvaluatesRightOperand operator value := by
  cases dispatch <;> exact .strict (by constructor)

include port in
theorem binary_continues {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (form : receipt.node.form = .binary left operator right) (value : Dynamic.Value) :
    EvaluatesRightOperand operator value :=
  dispatch_continues (binary_dispatch receipt port form) value

/-- The selected method body starts only after the actual ordered operands. -/
def Success (budget : Nat) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ argumentsHeap arguments,
    Trace budget (Program.ofChecked compiled.sourceProgram) stages invocation context environment
      before receipt.arguments (.values arguments) argumentsHeap ∧
    ∃ bodySize bodyEnvironment bound finalContext bodyOutcome child,
      stages.Closure port.principal.sourceFunction child ∧
      BindersAllocate [] argumentsHeap port.principal.sourceBody.source.inputs arguments bodyEnvironment bound ∧
      Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
        bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after ∧
      BodyResult port.principal.sourceBody.resultType bodyOutcome outcome ∧ bodySize < budget

private theorem align_body {bodyInstance : BodyInstance} {dictionary : EvidenceEnvironment}
    {roots : List StatementId} {child : Staging.Recursive.Scope}
    {parameterTypes : List TypeSystem.Ty} {bodyContext : SourceSemantics.Context}
    {bodyEnvironment : Dynamic.Environment} {bound after : Dynamic.Heap} {bodySize : Nat}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    (selection : OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context invocation.evidence
      port.principal.traitName port.principal.methodName receipt.node.requirements bodyInstance dictionary)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : stages.Closure (methodView bodyInstance dictionary roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
    (trace : Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child bodyContext
      bodyEnvironment bound roots finalContext bodyOutcome after) :
    bodyInstance = port.principal.sourceBody ∧ dictionary = port.principal.dictionary ∧
    stages.Closure port.principal.sourceFunction child ∧
    Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
      bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after := by
  obtain ⟨rfl, rfl⟩ := port.agrees bodyInstance dictionary selection
  have rootsSame : roots = port.principal.cached.compilation.statements := roots_unique rootsEq port.sourceAt.frame.roots
  cases rootsSame
  have typesSame := parameters.bodyTypes_eq.symm.trans port.sourceAt.extended.bodyTypes_eq
  cases typesSame
  have contextSame := parameters.functional port.sourceAt.extended
  cases contextSame
  exact ⟨rfl, rfl, selected, trace⟩

theorem children {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (trace : Size.Expression (Program.ofChecked compiled.sourceProgram) stages size invocation context environment before id outcome after) :
    Success receipt port size environment before outcome after ∨
      ∃ failure, outcome = .fault failure ∧ Trace size (Program.ofChecked compiled.sourceProgram) stages
        invocation context environment before receipt.arguments (.fault failure) after := by
  have nonempty := CallableIndexedOwnedPreparedStagedMethodSourceInversion.requirements_nonempty port.selected
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · have dispatch := unary_dispatch receipt port form
    have original := CallableIndexedOwnedPreparedStagedMethodSourceInversion.unary unique receipt.metadata.found form nonempty trace
    cases original with
    | operandFault operandTrace =>
      refine .inr ⟨_, rfl, ?_⟩
      rw [Receipt.arguments, arguments]
      exact .headFault operandTrace (Size.child_lt_stepSize (by simp))
    | method selectedDispatch selection operandTrace rootsEq selected parameters allocate bodyTrace resultRule =>
      obtain ⟨rfl, rfl⟩ := CallablePreparedOperatorSourceBounds.unary_dispatch_unique selectedDispatch dispatch
      obtain ⟨bodyEq, dictionaryEq, selectedAligned, aligned⟩ := align_body receipt port selection rootsEq selected parameters bodyTrace
      cases bodyEq
      cases dictionaryEq
      refine .inl ⟨_, _, ?_, _, _, _, _, _, _, selectedAligned, allocate, aligned, resultRule, Size.child_lt_stepSize (by simp)⟩
      rw [Receipt.arguments, arguments]
      exact .cons operandTrace (Size.child_lt_stepSize (by simp)) .nil
  · have dispatch := binary_dispatch receipt port form
    have original := CallableIndexedOwnedPreparedStagedMethodSourceInversion.binary unique receipt.metadata.found form nonempty trace
    cases original with
    | leftFault first =>
      refine .inr ⟨_, rfl, ?_⟩
      rw [Receipt.arguments, arguments]
      exact .headFault first (Size.child_lt_stepSize (by simp))
    | rightFault first _continues second =>
      refine .inr ⟨_, rfl, ?_⟩
      rw [Receipt.arguments, arguments]
      exact .tailFault first (Size.child_lt_stepSize (by simp)) (.headFault second (Size.child_lt_stepSize (by simp)))
    | method selectedDispatch selection first _continues second rootsEq selected parameters allocate bodyTrace resultRule =>
      obtain ⟨rfl, rfl⟩ := CallablePreparedOperatorSourceBounds.binary_dispatch_unique selectedDispatch dispatch
      obtain ⟨bodyEq, dictionaryEq, selectedAligned, aligned⟩ := align_body receipt port selection rootsEq selected parameters bodyTrace
      cases bodyEq
      cases dictionaryEq
      refine .inl ⟨_, _, ?_, _, _, _, _, _, _, selectedAligned, allocate, aligned, resultRule, Size.child_lt_stepSize (by simp)⟩
      rw [Receipt.arguments, arguments]
      exact .cons first (Size.child_lt_stepSize (by simp)) (.cons second (Size.child_lt_stepSize (by simp)) .nil)

include port in
/-- An actual operand-list fault reconstructs the original operator fault. -/
theorem arguments_fault {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {failure : Staging.Recursive.Failure}
    (trace : Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size invocation context environment
      before receipt.arguments (.fault failure) after) :
    ∃ sourceSize, Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize invocation context
      environment before id (.fault failure) after := by
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · have occurrence : Occurrence invocation id (.unary operator operand) receipt.node.requirements :=
      ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, form, rfl, receipt.metadata.coercions⟩
    rw [Receipt.arguments, arguments] at trace
    cases trace with
    | headFault head => exact ⟨_, .unaryOperandFault occurrence head⟩
    | tailFault _ tail => cases tail
  · have occurrence : Occurrence invocation id (.binary left operator right) receipt.node.requirements :=
      ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, form, rfl, receipt.metadata.coercions⟩
    rw [Receipt.arguments, arguments] at trace
    cases trace with
    | headFault head => exact ⟨_, .binaryLeftFault occurrence head⟩
    | tailFault first tail =>
      cases tail with
      | headFault second => exact ⟨_, .binaryRightFault occurrence first (binary_continues receipt port form _) second⟩
      | tailFault _ tail => cases tail

/-- Real parameter entry and the selected body reconstruct the independent
operator call; ordered operands determine its exact arity. -/
theorem applied {environment bodyEnvironment : Dynamic.Environment}
    {before argumentsHeap bound after : Dynamic.Heap} {size bodySize : Nat}
    {arguments : List Dynamic.Value} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {outcome : Staging.Recursive.Outcome}
    {child : Staging.Recursive.Scope}
    (trace : Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size invocation context environment
      before receipt.arguments (.values arguments) argumentsHeap)
    (selected : stages.Closure port.principal.sourceFunction child)
    (allocated : BindersAllocate [] argumentsHeap port.principal.sourceBody.source.inputs arguments bodyEnvironment bound)
    (bodyTrace : Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
      bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after)
    (matched : BodyResult port.principal.sourceBody.resultType bodyOutcome outcome) :
    ∃ sourceSize, Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize invocation context
      environment before id outcome after := by
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · have occurrence : Occurrence invocation id (.unary operator operand) receipt.node.requirements :=
      ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, form, rfl, receipt.metadata.coercions⟩
    rw [Receipt.arguments, arguments] at trace
    cases trace with
    | cons operand tail =>
      cases tail
      exact ⟨_, .unaryMethod occurrence (unary_dispatch receipt port form) port.selected operand
        port.sourceAt.frame.roots selected port.sourceAt.extended allocated bodyTrace matched⟩
  · have occurrence : Occurrence invocation id (.binary left operator right) receipt.node.requirements :=
      ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, form, rfl, receipt.metadata.coercions⟩
    rw [Receipt.arguments, arguments] at trace
    cases trace with
    | cons first tail =>
      cases tail with
      | cons second tail =>
        cases tail
        exact ⟨_, .binaryMethod occurrence (binary_dispatch receipt port form) port.selected first
          (binary_continues receipt port form _) second port.sourceAt.frame.roots selected
          port.sourceAt.extended allocated bodyTrace matched⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNestedRoots
/-! Physical recursive expression results restore the same original named
packet using their actual returned frame. The pool and all reached records
remain the witnesses returned by that expression. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNestedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPhysicalNestedCanonicalState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {size : Nat}
local notation "canonicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)
local notation "nestedBridge" => bridge (headers := headers) owner caller

theorem preserves_at (meaning : PreservesAt canonicalBridge context model stages invocation certificate faults size) :
    PreservesAt nestedBridge context model stages invocation certificate faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome afterHeap environments heaps locals agrees nativeTyped initial admitted trace
  have originalAdmission : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge context
      (CallableIndexedOwnedPhysicalNestedCanonicalState.canonical owner caller initial) := ⟨admitted.heap, admitted.rows⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
    meaning certified found typed environments heaps locals agrees nativeTyped
      (CallableIndexedOwnedPhysicalNestedCanonicalState.canonical owner caller initial) originalAdmission trace
  let returned := after owner caller initial reached frame
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
    maps, worlds, frame, metadata, returned, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

theorem reflects_at (meaning : ReflectsAt canonicalBridge context model stages invocation certificate faults size) :
    ReflectsAt nestedBridge context model stages invocation certificate faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  have originalAdmission : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge context
      (CallableIndexedOwnedPhysicalNestedCanonicalState.canonical owner caller initial) := ⟨admitted.heap, admitted.rows⟩
  obtain ⟨sourceSize, outcome, afterHeap, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
    meaning certified found typed environments heaps locals agrees nativeTyped
      (CallableIndexedOwnedPhysicalNestedCanonicalState.canonical owner caller initial) originalAdmission completed
  let returned := after owner caller initial reached frame
  refine ⟨sourceSize, outcome, afterHeap, finalMap, finalWorld, trace, result, finalHeaps,
    maps, worlds, frame, metadata, returned, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNestedRoots
end
