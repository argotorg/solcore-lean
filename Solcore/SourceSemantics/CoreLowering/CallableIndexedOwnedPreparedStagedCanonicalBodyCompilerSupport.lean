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
