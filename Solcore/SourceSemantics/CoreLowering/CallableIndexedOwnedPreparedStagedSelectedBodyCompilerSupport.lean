import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport

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
