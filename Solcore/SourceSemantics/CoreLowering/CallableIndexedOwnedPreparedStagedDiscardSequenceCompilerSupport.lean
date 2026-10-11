import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories

/-! Every ordered child of the same sequence receipt is issued from genuine
 original raw typing and its actual accepted compiler action. The constructive
 view transport retains full reached metadata and production callable policy.
 Original body typing proves the final raw result before whole-body assembly.
 Static CallsReady is indexed by the exact issued proof; no meaning is stored.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts (FlowReceipt Receipt)
open CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds (Tree)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor Certificate)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)

private theorem tree_nonempty {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {result : Ty} {rawResult : TypeSystem.Ty} {statements : List StatementId} {flow : Expr}
    (tree : Tree compiled context invocation scope semanticFaults result rawResult statements flow) :
    statements ≠ [] := by
  cases tree with
  | terminal root head sameType sameRaw => cases head <;> simp
  | discard root contains form tail => simp

/-- Full original typing fixes the raw result of any actual issued tree.
The native child type and metadata view are not used to infer this equality. -/
theorem raw_result {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context final : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {result : Ty} {rawResult expected : TypeSystem.Ty} {facts : BodyFacts}
    {statements : List StatementId} {flow : Expr}
    (unique : NodeOccurrencesUnique invocation.source)
    (tree : Tree compiled context invocation scope semanticFaults result rawResult statements flow)
    (typed : StatementsHaveType invocation.source { returnType := expected }
      context statements final facts)
    (completes : BodyCompletes expected facts) : rawResult = expected := by
  induction tree generalizing final facts with
  | terminal root head sameType sameRaw =>
    obtain ⟨node, found, resultType, childTyped⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head typed completes
    have nodeEq : root.support.node = node :=
      Option.some.inj (root.support.found.symm.trans found)
    exact sameRaw.symm.trans ((congrArg ExpressionNode.type nodeEq).trans resultType)
  | discard root contains form tail ih =>
    obtain ⟨firstType, tailFacts, firstTyped, remaining, tailCompletes⟩ :=
      CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.discard_tail_typed
        unique contains form (tree_nonempty tail) typed completes
    exact ih remaining tailCompletes

private theorem tree_of_roots {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {policy : SourceCoreLoops.Policy} {view : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
    {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView invocation.source view)
    (roots : ∀ expression child, receipt.Children expression child →
      Nonempty (RootAt compiled context invocation scope expression child semanticFaults)) :
    ∃ rawResult, Nonempty (Tree compiled context invocation scope semanticFaults result rawResult
      statements flow) := by
  revert roots
  induction receipt with
  | terminal terminal generated =>
    intro roots
    obtain ⟨root⟩ := roots _ _ ⟨rfl, rfl⟩
    exact ⟨root.support.node.type, ⟨.terminal root
      (CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head terminal metadata)
      terminal.sameType rfl⟩⟩
  | discard found form first generated tail accepted ih =>
    intro roots
    obtain ⟨root⟩ := roots _ _ (.inl ⟨rfl, rfl⟩)
    obtain ⟨rawResult, ⟨tailTree⟩⟩ := ih (fun expression child used =>
      roots expression child (.inr used))
    exact ⟨rawResult, ⟨.discard root (lookupStatement?_sound (metadata.statement found)) form tailTree⟩⟩

private theorem child_generated {policy : SourceCoreLoops.Policy} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {result : Ty} {reasonAt : ExpressionId → Word}
    {fellThrough escaped : Word} {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    {expression : ExpressionId} {child : SourceCoreBasic.LoweredExpr}
    (used : receipt.Children expression child) :
    ∃ childFuel, policy.lowerExpression childFuel view scope expression reasonAt = .ok child := by
  revert used
  induction receipt with
  | terminal terminal generated =>
    intro used
    rcases used with ⟨rfl, rfl⟩
    exact ⟨terminal.childFuel, terminal.generated⟩
  | discard found form first generated tail accepted ih =>
    intro used
    rcases used with ⟨rfl, rfl⟩ | tailUsed
    · exact ⟨_, generated⟩
    · exact ih tailUsed

section Static
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {statementPolicy : SourceCoreLoops.Policy} {fuel : Nat} {view : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {result : Ty}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {bodyCode : Expr}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {invocation : Staging.Recursive.Scope} {changed : List ExpressionId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {semanticFaults : FunctionCalls.FaultRep}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}

/-- The same original frame and accepted receipt cover all actual children.
The compiler recipe, policy, declarations and static call authority stay real. -/
structure Static (receipt : Receipt statementPolicy fuel view scope statements result
    reasonAt fellThrough escaped bodyCode) where
  edited : LocalView invocation.source view changed
  avoids : Avoids invocation.source (statements.map NodeId.statement) changed
  sourceProfile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source scope reasonAt
  viewProfile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) view scope reasonAt
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active
  expressionCallback : statementPolicy.lowerExpression = fun childFuel source current id token =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min childFuel bodyFuel)
      compilation source current id token
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  parameters : MonoBindersExtend function.source.owner function.context function.parameters types context
  sameSource : invocation.source = function.source
  body : function.body = statements
  syntaxTree : ∀ expression child, receipt.tree.Children expression child → Syntax view expression
  conditions : OriginalConditions compiled policy compilation readFuel context invocation
    reasonAt scope semanticFaults

variable {receipt : Receipt statementPolicy fuel view scope statements result reasonAt
    fellThrough escaped bodyCode}
  (packet : Static (compiled := compiled) (function := function) (context := context)
    (types := types) (invocation := invocation) (changed := changed)
    (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
    (native := native) (active := active) receipt)
include packet

private theorem original_available (expression : ExpressionId) (child : SourceCoreBasic.LoweredExpr)
    (used : receipt.tree.Children expression child) :
    (invocation.source.lookupExpression? expression).isSome := by
  obtain ⟨node, found, typed⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.at_parameters receipt.tree
      packet.edited.metadata packet.frame packet.parameters packet.sameSource packet.body
      expression child used
  exact Option.isSome_of_eq_some found

/-- The actual lookup selects data; frame-derived existence supplies its proof. -/
def Static.originalNode (expression : ExpressionId) (child : SourceCoreBasic.LoweredExpr)
    (used : receipt.tree.Children expression child) : ExpressionNode :=
  (invocation.source.lookupExpression? expression).get (original_available packet expression child used)

/-- Each child's original raw type is its own actual stored node type. -/
def Static.authority (expression : ExpressionId) (child : SourceCoreBasic.LoweredExpr)
    (used : receipt.tree.Children expression child) :
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.OriginalAuthority
      compiled policy compilation readFuel context invocation reasonAt scope expression
      (packet.originalNode expression child used).type semanticFaults := by
  let node := packet.originalNode expression child used
  have found : invocation.source.lookupExpression? expression = some node :=
    Option.eq_some_of_isSome (original_available packet expression child used)
  have typed : ExpressionHasType invocation.source context expression node.type := by
    obtain ⟨original, originalFound, originalTyped⟩ :=
      CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.at_parameters receipt.tree
        packet.edited.metadata packet.frame packet.parameters packet.sameSource packet.body
        expression child used
    have same : original = node := Option.some.inj (originalFound.symm.trans found)
    simpa only [same] using originalTyped
  exact CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.original_authority
    packet.conditions ⟨node, found, rfl, typed⟩

private theorem view_action {expression : ExpressionId} {child : SourceCoreBasic.LoweredExpr}
    (used : receipt.tree.Children expression child) :
    ∃ childFuel, SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody
      (min childFuel bodyFuel) compilation view scope expression reasonAt = .ok child := by
  obtain ⟨childFuel, generated⟩ := child_generated receipt.tree used
  exact ⟨childFuel, by simpa only [packet.expressionCallback] using generated⟩

/-- Constructive full-node action transport precedes the genuine331 extractor. -/
theorem Static.certificate (expression : ExpressionId) (child : SourceCoreBasic.LoweredExpr)
    (used : receipt.tree.Children expression child) :
    Certificate policy lowerBody compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression child := by
  obtain ⟨childFuel, generated⟩ := view_action packet used
  exact CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate
    packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
    (packet.syntaxTree expression child used)
    (CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.children_reached
      receipt.tree packet.edited.metadata expression child used)
    (packet.authority expression child used) generated

/-- CallsReady belongs to every exact internally issued used-child proof. -/
structure Ready : Prop where
  calls : ∀ expression child (used : receipt.tree.Children expression child),
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) (packet.certificate expression child used)

/-- Existence packaging keeps each actual child fuel; no Type chooser is exposed. -/
theorem Static.root (ready : Ready packet) (expression : ExpressionId)
    (child : SourceCoreBasic.LoweredExpr) (used : receipt.tree.Children expression child) :
    Nonempty (RootAt compiled context invocation scope expression child semanticFaults) := by
  obtain ⟨childFuel, generated⟩ := view_action packet used
  exact ⟨CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_view_action
    packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
    (packet.syntaxTree expression child used)
    (CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.children_reached
      receipt.tree packet.edited.metadata expression child used)
    (packet.authority expression child used) generated (ready.calls expression child used)⟩

/-- Original full body typing aligns the internally issued sequence tree with
its declaration's raw result at the actual parameter context and chosen scope. -/
theorem issued_tree (ready : Ready packet) :
    Nonempty (Tree compiled context invocation scope semanticFaults result function.resultType
      statements receipt.flow) := by
  obtain ⟨rawResult, ⟨tree⟩⟩ := tree_of_roots receipt.tree packet.edited.metadata
    (fun expression child used => packet.root ready expression child used)
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters packet.frame packet.parameters
  rw [packet.body, ← packet.sameSource] at typed
  have sameRaw : rawResult = function.resultType :=
    raw_result packet.conditions.unique tree typed completes
  subst rawResult
  exact ⟨tree⟩
end Static
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport
