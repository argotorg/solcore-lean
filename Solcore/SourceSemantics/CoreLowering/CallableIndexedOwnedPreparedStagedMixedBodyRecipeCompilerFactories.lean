import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport

/-! The retained production recipe constructs a discard packet at the actual
Code and BodyWith context. Its concrete loop policy supplies expression and
statement callbacks internally. Ordinary and principal Associations keep their
own named seed, dictionary and Code; no Produced Site is reconstructed.
Discard shape, original policy and typing authority, declarations and readiness
at the exact issued child certificates remain genuine static inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyRecipeCompilerFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaBodyRecipes (Retained BodyRecipe)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
  (Discard DiscardSupport PacketFor SupportFor parameterScope)
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}

/-- One packet retains its exact compiler callback, reason and fuel. -/
structure Choice where
  packet : Discard code stages
  callback : packet.policy.lowerExpression =
    FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  fuel : packet.fuel = code.fuel

/-- Existential production data is consumed in a proof goal, at the same Code.
The body grammar and actual Source-selected child are independent inputs. -/
theorem choose (named : Named) (retained : Retained named code)
    (statement next : StatementId) (rest : List StatementId)
    (firstExpression terminalExpression : ExpressionId)
    (bodyShape : function.body = statement :: next :: rest)
    (shape : CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.Shape
      code.view statement firstExpression terminalExpression (next :: rest))
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Choice code (stages := stages)) := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have applied := congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    applied.trans (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) code policy callback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed named compilation.own.assignments diagnostics expression)
    shape (by simpa only [bodyShape] using accepted)
  let packet : Discard code stages := {
    policy := policy
    fuel := code.fuel
    statement := statement
    next := next
    rest := rest
    firstExpression := firstExpression
    terminalExpression := terminalExpression
    reasonAt := code.reasonAt
    fellThrough := code.compilation.internalReason
    escaped := code.compilation.internalReason
    body := bodyShape
    receipt := receipt
    child := child
    selected := selected }
  exact ⟨{
    packet := packet
    callback := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.expression_callback
      compiled.indexed named compilation.own.assignments diagnostics expression
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
  (values := .initial compiled.compatible.checked) expressionSyntax certificates code
  (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
  (choice : Choice code (stages := stages))

/-- Per-scope original authority remains independent of the retained recipe.
The actual frame, parameter inputs and child paths come from Code and BodyWith. -/
structure Conditions where
  readFuel : Nat
  changed : List ExpressionId
  edited : ∀ child, stages.Closure function child → LocalView child.source code.view changed
  avoids : ∀ child, stages.Closure function child →
    Avoids child.source (function.body.map NodeId.statement) changed
  sourceProfile : ∀ child, stages.Closure function child →
    PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source
      (parameterScope code) choice.packet.reasonAt
  viewProfile : PolicyFor code.policy code.compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) code.view
    (parameterScope code) choice.packet.reasonAt
  firstSyntax : Syntax code.view choice.packet.firstExpression
  terminalSyntax : Syntax code.view choice.packet.terminalExpression
  original : ∀ child, stages.Closure function child →
    OriginalConditions compiled code.policy code.compilation readFuel body.toContext.context child
      choice.packet.reasonAt (parameterScope code) semanticFaults

/-- Statement metadata transports only the actual first reference path. -/
theorem first_reached : Reaches function.source (function.body.map NodeId.statement)
    (.expression choice.packet.firstExpression) := by
  have reached : Reaches function.source
      ((choice.packet.statement :: choice.packet.next :: choice.packet.rest).map NodeId.statement)
      (.expression choice.packet.firstExpression) :=
    .statement (.root (by simp))
      (code.viewOfSource.statement choice.packet.receipt.shape.found)
      (by simp [choice.packet.receipt.shape.form, StatementForm.references])
  simpa only [choice.packet.body] using reached

/-- The terminal reference retains its literal second statement occurrence. -/
theorem terminal_reached : Reaches function.source (function.body.map NodeId.statement)
    (.expression choice.packet.terminalExpression) := by
  have reached := terminal_reaches (statement := choice.packet.statement)
    code.viewOfSource choice.packet.receipt.shape.terminal
  simpa only [choice.packet.body] using reached

/-- The checked original issuer receives genuine frame and parameter typing.
It does not obtain raw typing or a source action from metadata equality. -/
theorem static (conditions : Conditions code body choice)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Static
      (statementPolicy := choice.packet.policy) (fuel := choice.packet.fuel)
      (view := code.view) (scope := parameterScope code)
      (statement := choice.packet.statement) (next := choice.packet.next) (rest := choice.packet.rest)
      (firstExpression := choice.packet.firstExpression) (terminalExpression := choice.packet.terminalExpression)
      (result := code.receipt.resultCore) (reasonAt := choice.packet.reasonAt)
      (fellThrough := choice.packet.fellThrough) (escaped := choice.packet.escaped)
      (code := code.receipt.body) (compiled := compiled) (function := function)
      (context := body.toContext.context) (types := body.toContext.types)
      (invocation := child) (changed := conditions.changed) (roots := function.body.map NodeId.statement)
      (policy := code.policy) (lowerBody := code.lowerBody) (compilation := code.compilation)
      (readFuel := conditions.readFuel) (bodyFuel := code.fuel) (semanticFaults := semanticFaults)
      (native := some compiled.indexed.ancestry.graph.inputs.callable) (active := code.active)
      choice.packet.receipt := {
  edited := conditions.edited child selected
  avoids := conditions.avoids child selected
  sourceProfile := conditions.sourceProfile child selected
  viewProfile := conditions.viewProfile
  callables := code.callables
  expressionCallback := by
    funext childFuel actualSource current expression reasonAt
    have callbackAt := congrArg
      (fun lower : SourceCoreFunctions.ExpressionLowerer =>
        lower childFuel actualSource current expression reasonAt) choice.callback
    simpa only [FunctionCode.children] using callbackAt
  frame := body.frame
  parameters := body.toContext.extended
  sameSource := stages.source selected
  body := choice.packet.body
  firstSyntax := conditions.firstSyntax
  terminalSyntax := conditions.terminalSyntax
  firstReached := by simpa only [stages.source selected] using first_reached code choice
  terminalReached := by simpa only [stages.source selected] using terminal_reached code choice
  conditions := conditions.original child selected }

/-- Only the certificates issued from this same packet need call authority. -/
def Ready (conditions : Conditions code body choice) : Prop :=
  ∀ child selected, CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Ready
    (static code body choice conditions child selected)

/-- The actual issuer constructs both raw Roots and terminal result equality. -/
def support (conditions : Conditions code body choice)
    (ready : Ready code body choice conditions) :
    DiscardSupport code body.toContext stages choice.packet semanticFaults :=
  CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport.of_static choice.packet
    (static code body choice conditions) ready

section Association
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys bodyRegistry semanticFaults mapping world function native
    bindings parameterCore resultCore)

/-- Each Association retains the literal Code of its own ordinary or principal branch. -/
def ChoiceFor : Type :=
  match association with
  | .ordinary _ _ actualCode _ _ _ _ _ _ _ _ => Choice actualCode (stages := stages)
  | .principal _ _ actualCode _ _ _ _ _ _ _ _ => Choice actualCode (stages := stages)

/-- The supported discard form is a static input at the actual compiler view. -/
def ShapeFor : Prop :=
  match association with
  | .ordinary _ _ actualCode _ _ _ _ _ _ _ _ =>
      ∃ statement next rest firstExpression terminalExpression,
        function.body = statement :: next :: rest ∧
        Nonempty (CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.Shape
          actualCode.view statement firstExpression terminalExpression (next :: rest))
  | .principal _ _ actualCode _ _ _ _ _ _ _ _ =>
      ∃ statement next rest firstExpression terminalExpression,
        function.body = statement :: next :: rest ∧
        Nonempty (CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.Shape
          actualCode.view statement firstExpression terminalExpression (next :: rest))

/-- Production provenance supplies a recipe at the same branch Code; body shape
and actual child selection remain separate from that recipe. -/
theorem choose_for (shape : ShapeFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (ChoiceFor association (stages := stages)) := by
  cases association with
  | ordinary owner captured actualCode history actualSupport origin prefixContext globals referenceIndex typed provenance =>
      obtain ⟨statement, next, rest, firstExpression, terminalExpression, bodyShape, acceptedShape⟩ := shape
      obtain ⟨acceptedShape⟩ := acceptedShape
      exact choose actualCode actualSupport.caller.named provenance.body_recipe
        statement next rest firstExpression terminalExpression bodyShape acceptedShape child selected
  | principal owner captured actualCode history actualSupport origin globals leading referenceIndex typed provenance =>
      obtain ⟨statement, next, rest, firstExpression, terminalExpression, bodyShape, acceptedShape⟩ := shape
      obtain ⟨acceptedShape⟩ := acceptedShape
      exact choose actualCode actualSupport.principal.named provenance.body_recipe
        statement next rest firstExpression terminalExpression bodyShape acceptedShape child selected

/-- Static conditions use the retained branch's actual BodyWith input context. -/
def ConditionsFor (chosen : ChoiceFor association (stages := stages)) : Type :=
  match association with
  | .ordinary _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Conditions actualCode actualSupport.body chosen
  | .principal _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Conditions actualCode actualSupport.body chosen

/-- No execution law occurs in the per-issued-root readiness proposition. -/
def ReadyFor (chosen : ChoiceFor association (stages := stages))
    (conditions : ConditionsFor association chosen) : Prop :=
  match association with
  | .ordinary _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Ready actualCode actualSupport.body chosen conditions
  | .principal _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Ready actualCode actualSupport.body chosen conditions

/-- The same chosen discard packet enters the mixed body sum. -/
def packet_for (chosen : ChoiceFor association (stages := stages)) : PacketFor association stages :=
  match association with
  | .ordinary _ _ _ _ _ _ _ _ _ _ _ => .discard chosen.packet
  | .principal _ _ _ _ _ _ _ _ _ _ _ => .discard chosen.packet

/-- Ordinary and principal support keep their own exact Code and body.toContext.
This constructs support for the explicit chosen packet, without universal coverage. -/
def support_for (chosen : ChoiceFor association (stages := stages))
    (conditions : ConditionsFor association chosen) (ready : ReadyFor association chosen conditions) :
    SupportFor association stages (packet_for association chosen) := by
  cases association with
  | ordinary owner captured actualCode history actualSupport origin prefixContext globals referenceIndex typed provenance =>
      exact support actualCode actualSupport.body chosen conditions ready
  | principal owner captured actualCode history actualSupport origin globals leading referenceIndex typed provenance =>
      exact support actualCode actualSupport.body chosen conditions ready
end Association

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyRecipeCompilerFactories
