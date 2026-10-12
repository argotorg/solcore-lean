import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping

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
  noDirect := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax _
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
