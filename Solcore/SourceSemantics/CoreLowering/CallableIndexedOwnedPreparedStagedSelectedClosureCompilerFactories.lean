import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories

/-! A produced contextual lambda keeps its compiler recipe through recapture
and ordinary Association construction. The Code, static body and terminal
packet all belong to that same Site. No emitted-value equality identifies an
unrelated Code, and arbitrary existing Associations do not gain this receipt.
Original policy coverage and reachable-call authority remain separate static
conditions at the literal chosen packet and every selected Source scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedClosureCompilerFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header OwnedKey)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (Produced loop_policy)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories
  (OriginalConditions ClosureAuthority ClosureReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}

section Seed
variable (produced : Produced compiled caller.named diagnostics namedCode compilation
  parameters result statements sourceContext evidence [] scope administrative id lowered)

/-- Recapture changes only the actual stored Source environment. -/
abbrev function (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named parameters result statements
    sourceContext evidence environment

def code (environment : Dynamic.Environment) :
    Code compiled.indexed (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) scope administrative :=
  RecursiveNamedLambdaFormationHeads.recaptureCode
    (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
    produced.site.code environment

variable (body : CallableIndexedLambdaStaticBodySupport.BodyWith
  (values := .initial compiled.compatible.checked) expressionSyntax certificates
  produced.site.code (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)

/-- The actual static body is recaptured beside the same compiler Site. -/
def ordinary_support (environment : Dynamic.Environment) :
    CallableIndexedOwnedOrdinaryLambdaSupport.Support
      (code produced environment) bodyRegistry semanticFaults :=
  (CallableIndexedOwnedOrdinaryLambdaSupport.Support.of_site
    caller produced.site expressionSyntax certificates body).recapture environment

variable (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code)
  (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named)
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)

include bodyView bodyReasons declarations in
/-- Source Syntax and the real binder policy remain original seed receipts. -/
theorem provenance
    (syntaxTree : GenericImperativeMatch.Syntax (source caller.named)
      (expressionSyntax (source caller.named)) body.context
      (.statements true statements) result)
    (environment : Dynamic.Environment)
    (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence) :
    OrdinaryAt (code produced environment) (ordinary_support produced body environment) :=
  .recaptured caller produced.site expressionSyntax certificates body produced.binder
    (CallableIndexedOwnedContextualLambdaBodyRecipes.Retained.of_recipe compilation produced.recipe)
    produced.compilerPolicy bodyView bodyReasons declarations syntaxTree environment callerGlobals callerReceipt

/-- The retained compiler recipe survives recapture without an equality cast
between different Codes or an assumption about a BodyWith expression callback. -/
theorem body_callback (environment : Dynamic.Environment) :
    (code produced environment).lowerBody
        (FunctionCode.children (code produced environment).policy
          (code produced environment).lowerBody (code produced environment).fuel
          (code produced environment).compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy
        (loop_policy compiled.indexed caller.named compilation.own.assignments diagnostics
          (FunctionCode.children (code produced environment).policy
            (code produced environment).lowerBody (code produced environment).fuel
            (code produced environment).compilation)) := by
  exact produced.callback

section Terminal
variable {stages : Staging.Recursive.Registry}

/-- The same production Code supplies the actual terminal compiler receipt. -/
theorem terminal (environment : Dynamic.Environment) (expression : ExpressionId)
    (shape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      (code produced environment).view expression statements)
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
        (code produced environment) stages,
      packet.policy.lowerExpression = FunctionCode.children (code produced environment).policy
        (code produced environment).lowerBody (code produced environment).fuel
        (code produced environment).compilation ∧
      packet.reasonAt = (code produced environment).reasonAt ∧
      packet.expression = expression ∧ packet.child = child := by
  let policy := loop_policy compiled.indexed caller.named compilation.own.assignments diagnostics
    (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
      (code produced environment).fuel (code produced environment).compilation)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (code produced environment) policy (body_callback produced environment)
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed caller.named compilation.own.assignments diagnostics
      (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
        (code produced environment).fuel (code produced environment).compilation)) shape accepted
  let packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
      (code produced environment) stages := {
    policy := policy
    fuel := (code produced environment).fuel
    expression := expression
    reasonAt := (code produced environment).reasonAt
    fellThrough := (code produced environment).compilation.internalReason
    escaped := (code produced environment).compilation.internalReason
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point
      ((code produced environment).receipt.loweredParameters.reverse.map
        (fun binding => (binding.1.id, binding.2)) ++ scope) expression receipt.child
    certifies := by
      intro actual generated
      exact ⟨rfl, rfl, Except.ok.inj (generated.symm.trans receipt.generated)⟩
    child := child
    selected := selected }
  exact ⟨packet, CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.expression_callback
    compiled.indexed caller.named compilation.own.assignments diagnostics
    (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
      (code produced environment).fuel (code produced environment).compilation), rfl, rfl, rfl⟩

/-- Choice retains the packet whose compiler callback was actually produced. -/
structure Choice (environment : Dynamic.Environment) (stages : Staging.Recursive.Registry) where
  packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
    (code produced environment) stages
  callback : packet.policy.lowerExpression = FunctionCode.children (code produced environment).policy
    (code produced environment).lowerBody (code produced environment).fuel
    (code produced environment).compilation
  reason : packet.reasonAt = (code produced environment).reasonAt
  requested : ExpressionId
  expression : packet.expression = requested
  child : Staging.Recursive.Scope
  sameChild : packet.child = child

theorem choose (environment : Dynamic.Environment) (expression : ExpressionId)
    (shape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      (code produced environment).view expression statements)
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child) :
    Nonempty (Choice produced environment stages) := by
  obtain ⟨packet, callback, reason, expressionEq, childEq⟩ :=
    terminal produced environment expression shape child selected
  exact ⟨{
    packet := packet
    callback := callback
    reason := reason
    requested := expression
    expression := expressionEq
    child := child
    sameChild := childEq }⟩

variable {environment : Dynamic.Environment}
  (choice : Choice produced environment stages)

/-- The Source policy and raw context remain independent of compiler success.
The actual frame is already present in the retained same-Site static body. -/
structure Conditions where
  readFuel : Nat
  changed : List ExpressionId
  edited : ∀ child, stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    CallableLambdaViewEdits.LocalView child.source (code produced environment).view changed
  avoids : ∀ child, stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    CallableLambdaBodyReachability.Avoids child.source (statements.map NodeId.statement) changed
  sourceProfile : ∀ child, stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    PolicyFor (code produced environment).policy (code produced environment).compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source
      ((code produced environment).receipt.loweredParameters.reverse.map
        (fun binding => (binding.1.id, binding.2)) ++ scope) (code produced environment).reasonAt
  viewProfile : PolicyFor (code produced environment).policy (code produced environment).compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (code produced environment).view
    ((code produced environment).receipt.loweredParameters.reverse.map
      (fun binding => (binding.1.id, binding.2)) ++ scope) (code produced environment).reasonAt
  tree : Syntax (code produced environment).view choice.packet.expression
  original : ∀ child, stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    OriginalConditions compiled (code produced environment).policy (code produced environment).compilation readFuel
      (ordinary_support produced body environment).body.toContext.context child (code produced environment).reasonAt
      ((code produced environment).receipt.loweredParameters.reverse.map
        (fun binding => (binding.1.id, binding.2)) ++ scope) semanticFaults

def authority (conditions : Conditions produced body choice) :
    ClosureAuthority (code produced environment)
      (ordinary_support produced body environment).body.toContext choice.packet
      (semanticFaults := semanticFaults) := {
  frame := (ordinary_support produced body environment).body.frame
  readFuel := conditions.readFuel
  changed := conditions.changed
  edited := conditions.edited
  avoids := conditions.avoids
  sourceProfile := conditions.sourceProfile
  viewProfile := conditions.viewProfile
  tree := conditions.tree
  callback := choice.callback
  reason := choice.reason
  conditions := conditions.original }

def Ready (conditions : Conditions produced body choice) : Prop :=
  ClosureReady (authority produced body choice conditions)

def selected_body (conditions : Conditions produced body choice)
    (ready : Ready produced body choice conditions) :
    CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.SelectedBody
      (code produced environment) (ordinary_support produced body environment).body.toContext stages
      (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closure
        (code produced environment) choice.packet) semanticFaults :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.selected_body
    (authority produced body choice conditions) ready
end Terminal
end Seed

section Association
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope environment actual)
  (produced : Produced compiled caller.named diagnostics namedCode compilation
    parameters result statements sourceContext evidence [] scope captured.administrative id lowered)
  (body : CallableIndexedLambdaStaticBodySupport.BodyWith
    (values := .initial compiled.compatible.checked) expressionSyntax certificates
    produced.site.code (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)

variable (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code)
  (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named)
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)

include bodyView bodyReasons declarations in
/-- The ordinary Association is constructed on the literal recaptured Code,
history and support. Its callback recipe remains available beside this object;
the usual runtime capture and formation fields are not reconstructed from a
native payload or its emitted expression. -/
def association
    (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence)
    (owner : OwnedKey keys) (history : CallableIndexedLambdaValues.History (code produced environment))
    (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin
      (ordinary_support produced body environment) history)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial compiled.compatible.checked) caller)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
    (referenceIndex : (code produced environment).referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (typed : RuntimeValueHasType world (value (code produced environment) captured.embedding history.native actual)
      (CallableContract.functionType (code produced environment).receipt.parameterCore
        (code produced environment).receipt.resultCore) compiled.indexed.layouts.definitions)
    (syntaxTree : GenericImperativeMatch.Syntax (source caller.named)
      (expressionSyntax (source caller.named)) body.context (.statements true statements) result) :
    Association headers keys bodyRegistry semanticFaults mapping world
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment)
      (value (code produced environment) captured.embedding history.native actual)
      (code produced environment).receipt.loweredParameters
      (code produced environment).receipt.parameterCore (code produced environment).receipt.resultCore := by
  exact @Association.ordinary compiled headers keys bodyRegistry semanticFaults mapping world
    (function (caller := caller) (parameters := parameters) (result := result)
      (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment)
    scope actual owner captured (code produced environment) history (ordinary_support produced body environment)
    origin prefixContext globals referenceIndex typed (provenance produced body bodyView bodyReasons declarations syntaxTree environment callerGlobals callerReceipt)

variable {stages : Staging.Recursive.Registry}
  (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence)
  (owner : OwnedKey keys) (history : CallableIndexedLambdaValues.History (code produced environment))
  (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin
    (ordinary_support produced body environment) history)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (referenceIndex : (code produced environment).referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
  (typed : RuntimeValueHasType world (value (code produced environment) captured.embedding history.native actual)
    (CallableContract.functionType (code produced environment).receipt.parameterCore
      (code produced environment).receipt.resultCore) compiled.indexed.layouts.definitions)
  (syntaxTree : GenericImperativeMatch.Syntax (source caller.named)
    (expressionSyntax (source caller.named)) body.context (.statements true statements) result)

/-- The authority belongs to the actual produced Association, not only a
closure with equal emitted payload. The Code and context reduce literally. -/
def authority_for (choice : Choice produced environment stages)
    (conditions : Conditions produced body choice) :
    CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureAuthorityFor
      (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
      choice.packet :=
  authority produced body choice conditions

/-- The usual checked support constructor retains this exact Association and
its chosen packet. Ready still concerns only its internally issued roots. -/
def support_for (choice : Choice produced environment stages)
    (conditions : Conditions produced body choice)
    (ready : Ready produced body choice conditions) :
    CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.ClosureSupportFor
      (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
      stages
      (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closureFor
        (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
        choice.packet) :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.closure_support_for
    (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
    choice.packet
    (authority_for captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree choice conditions)
    ready
end Association

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedClosureCompilerFactories
