import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport

/-! The original retained production recipe constructs a recursive discard
sequence packet at the actual Code. The checked original-source issuer supplies
Roots for every recorded child at every genuinely selected scope. Ordinary and
principal Associations retain their own named seed, Code and BodyWith context.
Original policy, declarations, syntax and exact issued-call readiness remain
static inputs; the packet stores no execution or whole-body meaning law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaBodyRecipes (Retained BodyRecipe)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
  (Sequence SequenceSupport PacketFor SupportFor parameterScope)
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}

/-- One chosen sequence retains the same exact compiler callback, reason and fuel. -/
structure Choice where
  packet : Sequence code stages
  callback : packet.policy.lowerExpression =
    FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  fuel : packet.fuel = code.fuel

/-- Actual compilation supplies the ordered receipt and finish footer.
The supported grammar and genuine Source-selected child remain static inputs. -/
theorem choose (named : Named) (retained : Retained named code)
    (shape : CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.Shape
      code.view function.body)
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
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed named compilation.own.assignments diagnostics expression)
    shape accepted
  let packet : Sequence code stages := {
    policy := policy
    fuel := code.fuel
    reasonAt := code.reasonAt
    fellThrough := code.compilation.internalReason
    escaped := code.compilation.internalReason
    receipt := receipt
    child := child
    selected := selected }
  exact ⟨{
    packet := packet
    callback := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.expression_callback
      compiled.indexed named compilation.own.assignments diagnostics expression
    reason := rfl
    fuel := rfl }⟩

variable (body : CallableIndexedLambdaStaticBodySupport.BodyWith
  (values := .initial compiled.compatible.checked) expressionSyntax certificates code
  (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
  (choice : Choice code (stages := stages))

/-- Original policy and typing authority are independent of the retained recipe.
Each syntactic child and each issued-call proof belongs to this same receipt. -/
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
  syntaxTree : ∀ expression childCode,
    choice.packet.receipt.tree.Children expression childCode → Syntax code.view expression
  original : ∀ child, stages.Closure function child →
    OriginalConditions compiled code.policy code.compilation readFuel body.toContext.context child
      choice.packet.reasonAt (parameterScope code) semanticFaults

/-- The checked issuer transports actual reached actions to original Source.
Frame and parameter typing come from the same BodyWith input context. -/
theorem static (conditions : Conditions code body choice)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport.Static
      (statementPolicy := choice.packet.policy) (fuel := choice.packet.fuel)
      (view := code.view) (scope := parameterScope code) (statements := function.body)
      (result := code.receipt.resultCore) (reasonAt := choice.packet.reasonAt)
      (fellThrough := choice.packet.fellThrough) (escaped := choice.packet.escaped)
      (bodyCode := code.receipt.body) (compiled := compiled) (function := function)
      (context := body.toContext.context) (types := body.toContext.types)
      (invocation := child) (changed := conditions.changed)
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
  body := rfl
  syntaxTree := conditions.syntaxTree
  conditions := conditions.original child selected }

/-- Readiness quantifies only the exact certificates issued from this packet. -/
def Ready (conditions : Conditions code body choice) : Prop :=
  ∀ child selected, CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport.Ready
    (static code body choice conditions child selected)

/-- Every Source-selected scope receives its actual recorded original Roots.
The declared raw result is derived above the static packet layer. -/
def support (conditions : Conditions code body choice)
    (ready : Ready code body choice conditions) :
    SequenceSupport code body.toContext stages choice.packet semanticFaults := {
  frame := body.frame
  roots := fun child selected expression childCode used =>
    (static code body choice conditions child selected).root
      (ready child selected) expression childCode used }

section Association
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys bodyRegistry semanticFaults mapping world function native
    bindings parameterCore resultCore)

/-- The actual Association branch fixes its own Code and named seed. -/
def ChoiceFor : Type :=
  match association with
  | .ordinary _ _ actualCode _ _ _ _ _ _ _ _ => Choice actualCode (stages := stages)
  | .principal _ _ actualCode _ _ _ _ _ _ _ _ => Choice actualCode (stages := stages)

/-- The recursive grammar is witnessed at that same branch's compiler view. -/
def ShapeFor : Prop :=
  match association with
  | .ordinary _ _ actualCode _ _ _ _ _ _ _ _ =>
      CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.Shape actualCode.view function.body
  | .principal _ _ actualCode _ _ _ _ _ _ _ _ =>
      CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.Shape actualCode.view function.body

/-- The ordinary and principal recipes both come from authentic provenance.
The exact chosen Site is retained through recapture, with no data selector. -/
theorem choose_for (shape : ShapeFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (ChoiceFor association (stages := stages)) := by
  cases association with
  | ordinary owner captured actualCode history actualSupport origin prefixContext globals referenceIndex typed provenance =>
      exact choose actualCode actualSupport.caller.named provenance.body_recipe shape child selected
  | principal owner captured actualCode history actualSupport origin globals leading referenceIndex typed provenance =>
      exact choose actualCode actualSupport.principal.named provenance.body_recipe shape child selected

/-- Static authority uses the branch's literal BodyWith parameter input context. -/
def ConditionsFor (chosen : ChoiceFor association (stages := stages)) : Type :=
  match association with
  | .ordinary _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Conditions actualCode actualSupport.body chosen
  | .principal _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Conditions actualCode actualSupport.body chosen

/-- Call authority stays indexed by each exact internally issued certificate. -/
def ReadyFor (chosen : ChoiceFor association (stages := stages))
    (conditions : ConditionsFor association chosen) : Prop :=
  match association with
  | .ordinary _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Ready actualCode actualSupport.body chosen conditions
  | .principal _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Ready actualCode actualSupport.body chosen conditions

/-- The same chosen sequence packet enters the existing mixed body sum. -/
def packet_for (chosen : ChoiceFor association (stages := stages)) : PacketFor association stages :=
  match association with
  | .ordinary _ _ _ _ _ _ _ _ _ _ _ => .sequence chosen.packet
  | .principal _ _ _ _ _ _ _ _ _ _ _ => .sequence chosen.packet

/-- Both branches retain their own Code and actual body.toContext.
This produces support for the explicit chosen packet; no global coverage is inferred. -/
def support_for (chosen : ChoiceFor association (stages := stages))
    (conditions : ConditionsFor association chosen) (ready : ReadyFor association chosen conditions) :
    SupportFor association stages (packet_for association chosen) := by
  cases association with
  | ordinary owner captured actualCode history actualSupport origin prefixContext globals referenceIndex typed provenance =>
      exact support actualCode actualSupport.body chosen conditions ready
  | principal owner captured actualCode history actualSupport origin globals leading referenceIndex typed provenance =>
      exact support actualCode actualSupport.body chosen conditions ready
end Association

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories
