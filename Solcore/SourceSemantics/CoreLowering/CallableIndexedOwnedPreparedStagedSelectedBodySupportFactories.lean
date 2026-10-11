import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts

/-! Static selected-body support is built at the actual original parameter
context. Original frame typing supplies the child node and raw result type;
the compiler-root issuer constructs acceptance and the recursive certificate.
Every actual Source-selected scope is retained. Remaining declaration,
coercion, policy, diagnostic, runtime and reached-call authority is explicit.
No expression execution or called-body meaning is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedLambdaStaticBodySupport
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt SelectedBody NamedSupport ClosureSupportFor)


/-- Original static conditions omit child lookup and typing: the actual frame
or Header supplies those independently of the native projection. -/
structure OriginalConditions (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (semanticFaults : FunctionCalls.FaultRep) where
  declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context
  coercions : ∀ id node, Syntax invocation.source id →
    invocation.source.lookupExpression? id = some node → node.coercions = []
  sameLedger : context.solvedRequirements = compilation.solvedRequirements
  runtimeLedger : RuntimeRequirementLedgerValid context
  unique : NodeOccurrencesUnique invocation.source
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source
  covers : invocation.evidence.Covers context
  actualFunctionType : policy.callables.functionType = CallableContract.functionType
  uninitialized : ∀ current id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)

/-- Classical choice packages a genuinely proved raw Source node. It does not
choose an execution, body result or compiler action. -/
noncomputable def original_authority
    {compiled : SourceCoreUnifiedCompilation.Compiled} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat} {context : SourceSemantics.Context}
    {invocation : Staging.Recursive.Scope} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {rawType : TypeSystem.Ty}
    {semanticFaults : FunctionCalls.FaultRep}
    (conditions : OriginalConditions compiled policy compilation readFuel context invocation
      reasonAt scope semanticFaults)
    (raw : ∃ node, invocation.source.lookupExpression? expression = some node ∧
      node.type = rawType ∧ ExpressionHasType invocation.source context expression node.type) :
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.OriginalAuthority compiled policy compilation readFuel context invocation
      reasonAt scope expression rawType semanticFaults :=
  { node := Classical.choose raw
    found := (Classical.choose_spec raw).1
    rawResult := (Classical.choose_spec raw).2.1
    typed := (Classical.choose_spec raw).2.2
    declarations := conditions.declarations
    coercions := conditions.coercions
    sameLedger := conditions.sameLedger
    runtimeLedger := conditions.runtimeLedger
    unique := conditions.unique
    wellFormed := conditions.wellFormed
    runtime := conditions.runtime
    covers := conditions.covers
    actualFunctionType := conditions.actualFunctionType
    uninitialized := conditions.uninitialized }

section Closure
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (code : Code compiled.indexed function localScope administrative)


/-- The accepted BodyWith builds the terminal packet directly. Its reason
function and chosen child are literal fields. The expression callback link
is a genuine additional factory condition, not a consequence of body.callback. -/
theorem terminal_of_actual_body
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {registry : SourceCoreRawMetadata.Registry}
    (body : BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry semanticFaults)
    (expression : ExpressionId)
    (shape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal code.view expression function.body)
    (reader : body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked)
    (expressionCallback : body.policy.lowerExpression =
      FunctionCode.children code.policy code.lowerBody code.fuel code.compilation)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages,
      packet.policy.lowerExpression =
        FunctionCode.children code.policy code.lowerBody code.fuel code.compilation ∧
      packet.reasonAt = code.reasonAt ∧ packet.child = child ∧ packet.expression = expression ∧
      packet.certificate = CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) expression packet.receipt.child := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    reader shape body.accepted
  let packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages :=
    { policy := body.policy
      fuel := code.fuel
      expression := expression
      reasonAt := code.reasonAt
      fellThrough := code.compilation.internalReason
      escaped := code.compilation.internalReason
      receipt := receipt
      certificate := CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) expression receipt.child
      certifies := by
        intro lowered accepted
        exact ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans receipt.generated)⟩
      child := child
      selected := selected }
  exact ⟨packet, expressionCallback, rfl, rfl, rfl, rfl⟩

/-- Static admission is provided for every actual Source-selected child.
The frame supplies original raw child typing at the same parameter entry. -/
structure ClosureAuthority
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  readFuel : Nat
  changed : List ExpressionId
  edited : ∀ child, stages.Closure function child → LocalView child.source code.view changed
  avoids : ∀ child, stages.Closure function child →
    Avoids child.source (function.body.map NodeId.statement) changed
  sourceProfile : ∀ child, stages.Closure function child →
    PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      child.source (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) code.reasonAt
  viewProfile : PolicyFor code.policy code.compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    code.view (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) code.reasonAt
  tree : Syntax code.view packet.expression
  callback : packet.policy.lowerExpression =
    FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  conditions : ∀ child, stages.Closure function child →
    OriginalConditions compiled code.policy code.compilation readFuel inputs.context child
      code.reasonAt (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) semanticFaults

variable {code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}

/-- This exact certificate is constructed from the accepted packet and raw
frame typing. Ready authority can refer only to its actual reachable calls. -/
theorem closure_certificate
    (authority : ClosureAuthority code inputs packet (semanticFaults := semanticFaults))
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
      code.policy code.lowerBody code.compilation authority.readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      child.source inputs.context code.reasonAt
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child :=
  CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate (authority.edited child selected) (authority.avoids child selected)
    (authority.sourceProfile child selected) authority.viewProfile code.callables authority.tree
    (by simpa only [stages.source selected] using CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet)
    (original_authority (authority.conditions child selected)
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type code packet inputs authority.frame child selected))
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet authority.callback authority.reason)

def ClosureReady
    (authority : ClosureAuthority code inputs packet (semanticFaults := semanticFaults)) : Prop :=
  ∀ (child : Staging.Recursive.Scope) (selected : stages.Closure function child),
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) (closure_certificate authority child selected)

/-- The selected singleton and every original Root are built internally.
No universal arbitrary-terminal body law is required. -/
noncomputable def selected_body
    (authority : ClosureAuthority code inputs packet (semanticFaults := semanticFaults))
    (ready : ClosureReady authority) :
    SelectedBody code inputs stages (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closure code packet) semanticFaults where
  point := rfl
  readFuel := authority.readFuel
  roots := fun child selected =>
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_terminal code packet inputs child selected
      (authority.edited child selected) (authority.avoids child selected)
      (authority.sourceProfile child selected) authority.viewProfile authority.tree
      authority.callback authority.reason
      (original_authority (authority.conditions child selected)
        (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type code packet inputs authority.frame child selected))
      (ready child selected)).support
end Closure

section Associations
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  {stages : Staging.Recursive.Registry}

/-- Both branches retain their actual BodyWith.toContext, without a context cast. -/
def ClosureAuthorityFor
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Type :=
  match association, packet with
  | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
      ClosureAuthority code support.body.toContext packet (semanticFaults := semanticFaults)
  | .principal _ _ code _ support _ _ _ _ _ _, packet =>
      ClosureAuthority code support.body.toContext packet (semanticFaults := semanticFaults)

def ClosureReadyFor
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) :
    ClosureAuthorityFor association packet → Prop :=
  match association, packet with
  | .ordinary _ _ _ _ _ _ _ _ _ _ _, _ => fun authority => ClosureReady authority
  | .principal _ _ _ _ _ _ _ _ _ _ _, _ => fun authority => ClosureReady authority

/-- The original contextual Association chooses the actual parameter context
and narrows only its retained terminal certificate. -/
noncomputable def closure_support_for
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages)
    (authority : ClosureAuthorityFor association packet) (ready : ClosureReadyFor association packet authority) :
    ClosureSupportFor association stages (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closureFor association packet) := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals reference typed provenance =>
      exact selected_body authority ready
  | principal owner captured code history support origin globals leading reference typed provenance =>
      exact selected_body authority ready
end Associations

section Named
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header)


/-- The Header's callback must be identified with its actual expression
compiler at this real budget. This static function link is not an accepted
action equation, and it is not derived from the closure BodyWith callback. -/
structure NamedAuthority where
  policy : SourceCoreFunctions.Policy
  body : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  compilerFuel : Nat
  readFuel : Nat
  native : Option SourceCoreGeneralFunctions.CallableContext
  active : TypeSystem.Substitution
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active
  callback : header.policy.lowerExpression packet.receipt.childFuel header.function.source =
    SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation header.function.source
  profile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt
  tree : Syntax header.function.source packet.expression
  conditions : ∀ child, stages.Closure header.function child →
    OriginalConditions compiled policy compilation readFuel header.context child header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) semanticFaults

variable {header packet}

private theorem named_accepted
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults))
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) :
    SourceCoreFunctions.lowerExpressionWithPolicy authority.policy authority.body authority.compilerFuel
      authority.compilation child.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) packet.expression header.reasonAt =
      .ok packet.receipt.child := by
  have callbackAt := congrArg
    (fun lower : SourceCoreLocalCell.Scope → ExpressionId → (ExpressionId → Word) →
        Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr =>
      lower (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        packet.expression header.reasonAt) authority.callback
  have generated := callbackAt.symm.trans packet.receipt.generated
  simpa only [stages.source selected] using generated

private theorem named_raw
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults))
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) :
    ∃ node, child.source.lookupExpression? packet.expression = some node ∧
      node.type = header.function.resultType ∧
      ExpressionHasType child.source header.context packet.expression node.type := by
  have raw := CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child
    packet.receipt selected (authority.conditions child selected).wellFormed
  simpa only [stages.source selected] using raw

private theorem named_avoids (child : Staging.Recursive.Scope) :
    Avoids child.source [.expression packet.expression] [] := by
  intro id member
  cases member

/-- The selected Header's original callback generates this exact certificate.
Identity view transport here carries no changed expression metadata. -/
theorem named_certificate
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults))
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
      authority.policy authority.body authority.compilation authority.readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      packet.expression packet.receipt.child :=
  CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate (LocalView.refl child.source) (named_avoids (packet := packet) child)
    (by simpa only [stages.source selected] using authority.profile)
    (by simpa only [stages.source selected] using authority.profile)
    authority.callables (by simpa only [stages.source selected] using authority.tree)
    (.root (by simp))
    (original_authority (authority.conditions child selected) (named_raw authority child selected))
    (named_accepted authority child selected)

def NamedReady
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults)) : Prop :=
  ∀ (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child),
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) (named_certificate authority child selected)

/-- The original Source parameter context, raw result and reason function
remain this Header's fields, and all genuine selected child scopes are covered. -/
noncomputable def named_support
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults))
    (ready : NamedReady authority) :
    NamedSupport header stages (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named header packet) semanticFaults where
  point := rfl
  roots := by
    intro child selected
    simp only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named]
    exact ⟨CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_view_action (LocalView.refl child.source) (named_avoids (packet := packet) child)
      (by simpa only [stages.source selected] using authority.profile)
      (by simpa only [stages.source selected] using authority.profile)
      authority.callables (by simpa only [stages.source selected] using authority.tree)
      (.root (by simp))
      (original_authority (authority.conditions child selected) (named_raw authority child selected))
      (named_accepted authority child selected) (ready child selected), rfl, rfl⟩
end Named

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories
