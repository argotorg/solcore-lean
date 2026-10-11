import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedClosureCompilerFactories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport

/-! The same produced lambda Site supplies a discard-and-terminal packet on
its literal recaptured Code. The retained production recipe constructs the
whole compiler action, expression callback and statement reader internally.
Original frame and parameter typing supply both raw children at every selected
Source scope. Policy coverage, declarations, view edits and callsite authority
remain separate static inputs at the exact internally issued certificates.
The Association endpoint covers this actual ordinary formation only. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureCompilerFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header OwnedKey)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (Produced loop_policy)
open CallableIndexedOwnedPreparedStagedSelectedClosureCompilerFactories
  (function code ordinary_support association body_callback)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
  (Discard DiscardSupport PacketFor SupportFor parameterScope)
open CallableLambdaViewEdits CallableLambdaBodyReachability

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

section Produced
variable (produced : Produced compiled caller.named diagnostics namedCode compilation
  parameters result statements sourceContext evidence [] scope administrative id lowered)
  {environment : Dynamic.Environment} {stages : Staging.Recursive.Registry}

/-- The chosen receipt and its compiler identities belong to one produced
Code. No choice is extracted from Prop into a new Type-valued selector. -/
structure Choice where
  packet : Discard (code produced environment) stages
  callback : packet.policy.lowerExpression = FunctionCode.children (code produced environment).policy
    (code produced environment).lowerBody (code produced environment).fuel
    (code produced environment).compilation
  reason : packet.reasonAt = (code produced environment).reasonAt
  fuel : packet.fuel = (code produced environment).fuel

/-- The actual production body recipe and discard shape manufacture the
receipt. The selected Source child is retained unchanged in that receipt. -/
theorem choose (statement next : StatementId) (rest : List StatementId)
    (firstExpression terminalExpression : ExpressionId)
    (bodyShape : statements = statement :: next :: rest)
    (shape : CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.Shape
      (code produced environment).view statement firstExpression terminalExpression (next :: rest))
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child) :
    Nonempty (Choice produced (environment := environment) (stages := stages)) := by
  let policy := loop_policy compiled.indexed caller.named compilation.own.assignments diagnostics
    (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
      (code produced environment).fuel (code produced environment).compilation)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (code produced environment) policy (body_callback produced environment)
  have actualBody :
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment).body =
        statement :: next :: rest := bodyShape
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed caller.named compilation.own.assignments diagnostics
      (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
        (code produced environment).fuel (code produced environment).compilation))
    shape (by simpa only [actualBody] using accepted)
  let packet : Discard (code produced environment) stages := {
    policy := policy
    fuel := (code produced environment).fuel
    statement := statement
    next := next
    rest := rest
    firstExpression := firstExpression
    terminalExpression := terminalExpression
    reasonAt := (code produced environment).reasonAt
    fellThrough := (code produced environment).compilation.internalReason
    escaped := (code produced environment).compilation.internalReason
    body := actualBody
    receipt := receipt
    child := child
    selected := selected }
  exact ⟨{
    packet := packet
    callback := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.expression_callback
      compiled.indexed caller.named compilation.own.assignments diagnostics
      (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
        (code produced environment).fuel (code produced environment).compilation)
    reason := rfl
    fuel := rfl }⟩

private theorem terminal_reaches {source view : TypedSource}
    {statement next : StatementId} {rest : List StatementId} {expression : ExpressionId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      view expression (next :: rest)) :
    Reaches source ((statement :: next :: rest).map NodeId.statement) (.expression expression) := by
  cases terminal with
  | returning rest found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
  | tail found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])

variable (body : CallableIndexedLambdaStaticBodySupport.BodyWith
  (values := .initial compiled.compatible.checked) expressionSyntax certificates
  produced.site.code (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
  (choice : Choice produced (environment := environment) (stages := stages))

/-- These are original static facts at the retained parameter context. The
expression callback, frame, parameter typing and reachable child paths are
constructed from the produced Site and packet instead of being supplied. -/
structure Conditions where
  readFuel : Nat
  changed : List ExpressionId
  edited : ∀ child, stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    LocalView child.source (code produced environment).view changed
  avoids : ∀ child, stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    Avoids child.source (statements.map NodeId.statement) changed
  sourceProfile : ∀ child, stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    PolicyFor (code produced environment).policy (code produced environment).compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source
      (parameterScope (code produced environment)) choice.packet.reasonAt
  viewProfile : PolicyFor (code produced environment).policy (code produced environment).compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (code produced environment).view
    (parameterScope (code produced environment)) choice.packet.reasonAt
  firstSyntax : Syntax (code produced environment).view choice.packet.firstExpression
  terminalSyntax : Syntax (code produced environment).view choice.packet.terminalExpression
  original : ∀ child, stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    OriginalConditions compiled (code produced environment).policy (code produced environment).compilation readFuel
      (ordinary_support produced body environment).body.toContext.context child choice.packet.reasonAt
      (parameterScope (code produced environment)) semanticFaults

/-- The original discard occurrence supplies its child's reference path. -/
theorem first_reached : Reaches
    (function (caller := caller) (parameters := parameters) (result := result)
      (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment).source
    (statements.map NodeId.statement) (.expression choice.packet.firstExpression) := by
  have reached : Reaches
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment).source
      ((choice.packet.statement :: choice.packet.next :: choice.packet.rest).map NodeId.statement)
      (.expression choice.packet.firstExpression) :=
    .statement (.root (by simp))
      ((code produced environment).viewOfSource.statement choice.packet.receipt.shape.found)
      (by simp [choice.packet.receipt.shape.form, StatementForm.references])
  have bodyShape : statements = choice.packet.statement :: choice.packet.next :: choice.packet.rest :=
    choice.packet.body
  simpa only [bodyShape] using reached

/-- The tail occurrence keeps its own path through the same body roots. -/
theorem terminal_reached : Reaches
    (function (caller := caller) (parameters := parameters) (result := result)
      (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment).source
    (statements.map NodeId.statement) (.expression choice.packet.terminalExpression) := by
  have reached := terminal_reaches (statement := choice.packet.statement)
    (code produced environment).viewOfSource choice.packet.receipt.shape.terminal
  have bodyShape : statements = choice.packet.statement :: choice.packet.next :: choice.packet.rest :=
    choice.packet.body
  simpa only [bodyShape] using reached

/-- Actual BodyWith inputs and frame produce raw Source typing before the
checked original-root issuer is used at each genuine selected scope. -/
theorem static (conditions : Conditions produced body choice)
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child) :
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Static
      (statementPolicy := choice.packet.policy) (fuel := choice.packet.fuel)
      (view := (code produced environment).view) (scope := parameterScope (code produced environment))
      (statement := choice.packet.statement) (next := choice.packet.next) (rest := choice.packet.rest)
      (firstExpression := choice.packet.firstExpression) (terminalExpression := choice.packet.terminalExpression)
      (result := (code produced environment).receipt.resultCore) (reasonAt := choice.packet.reasonAt)
      (fellThrough := choice.packet.fellThrough) (escaped := choice.packet.escaped)
      (code := (code produced environment).receipt.body)
      (compiled := compiled)
      (function := function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment)
      (context := (ordinary_support produced body environment).body.toContext.context)
      (types := (ordinary_support produced body environment).body.toContext.types)
      (invocation := child) (changed := conditions.changed) (roots := statements.map NodeId.statement)
      (policy := (code produced environment).policy) (lowerBody := (code produced environment).lowerBody)
      (compilation := (code produced environment).compilation)
      (readFuel := conditions.readFuel) (bodyFuel := (code produced environment).fuel)
      (semanticFaults := semanticFaults)
      (native := some compiled.indexed.ancestry.graph.inputs.callable)
      (active := (code produced environment).active) choice.packet.receipt := {
  edited := conditions.edited child selected
  avoids := conditions.avoids child selected
  sourceProfile := conditions.sourceProfile child selected
  viewProfile := conditions.viewProfile
  callables := (code produced environment).callables
  expressionCallback := by
    funext childFuel actualSource current expression reasonAt
    have callbackAt := congrArg
      (fun lower : SourceCoreFunctions.ExpressionLowerer =>
        lower childFuel actualSource current expression reasonAt) choice.callback
    simpa only [FunctionCode.children] using callbackAt
  frame := (ordinary_support produced body environment).body.frame
  parameters := (ordinary_support produced body environment).body.toContext.extended
  sameSource := stages.source selected
  body := choice.packet.body
  firstSyntax := conditions.firstSyntax
  terminalSyntax := conditions.terminalSyntax
  firstReached := by simpa only [stages.source selected] using first_reached produced choice
  terminalReached := by simpa only [stages.source selected] using terminal_reached produced choice
  conditions := conditions.original child selected }

/-- Readiness concerns only the two certificates issued from this same
packet; it contains actual call authority and no execution theorem. -/
def Ready (conditions : Conditions produced body choice) : Prop :=
  ∀ child selected,
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Ready
      (static produced body choice conditions child selected)

/-- The real two original Roots and terminal result type are built internally. -/
def support (conditions : Conditions produced body choice)
    (ready : Ready produced body choice conditions) :
    DiscardSupport (code produced environment) (ordinary_support produced body environment).body.toContext
      stages choice.packet semanticFaults :=
  CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport.of_static choice.packet
    (static produced body choice conditions) ready
end Produced

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
  {stages : Staging.Recursive.Registry}
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

/-- This ordinary Association reduces to the same recaptured Code. -/
def packet_for (choice : Choice produced (environment := environment) (stages := stages)) :
    PacketFor
      (association captured produced body owner history origin prefixContext globals referenceIndex typed syntaxTree)
      stages := .discard choice.packet

/-- No callback or body law is supplied for arbitrary Associations. This
support is at the actual retained ordinary formation and its literal packet. -/
def support_for (choice : Choice produced (environment := environment) (stages := stages))
    (conditions : Conditions produced body choice)
    (ready : Ready produced body choice conditions) :
    SupportFor
      (association captured produced body owner history origin prefixContext globals referenceIndex typed syntaxTree)
      stages
      (packet_for captured produced body owner history origin prefixContext globals referenceIndex typed syntaxTree choice) :=
  support produced body choice conditions ready
end Association

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureCompilerFactories
