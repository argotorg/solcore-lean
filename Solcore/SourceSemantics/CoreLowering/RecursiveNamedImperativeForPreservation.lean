import Solcore.SourceSemantics.CoreLowering.ProtectedImperativeCatalogPayloadContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderAssignmentPayloadContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeControlBounds
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeadBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchRuntimeHead
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeLexicalBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedImperativeForPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBitNotStatementContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderPost
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogGoals

/-! The existing Match Tree closes lexical, assignment, loop and match children
at one fixed budget. The original For entry is a static inclusion wrapper. The reached header retains an inclusive loop continuation;
source and Core sizes are independent and no finite loop proof is duplicated. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored restored restore_rep)
open TypedLexicalControl (LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (ExecutesAt StatementOutcome)
namespace ContextTransport
/-- Only the actual source binder extensions transport the chosen context condition. -/
theorem binders {source : TypedSource} (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next binder}, validity context →
      BinderExtends source.owner context binder next → validity next)
    {context next : SourceSemantics.Context} {binders : List TypedBinder}
    (valid : validity context) (extended : BindersExtend source.owner context binders next) :
    validity next := by
  induction extended with
  | nil => exact valid
  | cons head tail ih => exact ih (extend valid head)

/-- The selected arm uses its ordered source binders; the default keeps the parent. -/
theorem scoped_context {source : TypedSource} (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next binder}, validity context →
      BinderExtends source.owner context binder next → validity next)
    {context next : SourceSemantics.Context} {hiddenIds : List Resolved.LocalId}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request}
    (valid : validity context)
    (related : GenericMatchChildren.ScopedContextFor source context hiddenIds
      scrutineeType cases fallback request next) : validity next := by
  cases related with
  | arm _ _ _ extended _ => exact binders validity extend valid extended
  | default _ _ => exact valid
/-- The original source loop returns its initial context. -/
theorem loop_context {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before
      condition post statements finalContext outcome after) : finalContext = context := by
  cases trace <;> rfl

end ContextTransport

namespace Control
abbrev PreservesAt := @RecursiveNamedLoopContracts.PreservesAt
abbrev ReflectsAt := @RecursiveNamedLoopContracts.ReflectsAt
abbrev PreservesAtWith := @RecursiveNamedLoopContracts.PreservesAtFor
abbrev ReflectsAtWith := @RecursiveNamedLoopContracts.ReflectsAtFor
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
include unique in
theorem block_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → PreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadPreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.block_preserves_at_with_state (canonical := canonical) (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol (fun _ _ _ _ _ _ => True)) validity budget size bounded found form ⟨trivial⟩
      (fun child childBound {_ _} innerTrace => by
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
          inner child childBound valid environments heaps locals agrees actualTyped reference read unmapped installed innerTrace
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
          ⟨⟨trivial⟩, trivial⟩⟩) trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata⟩

include unique in
theorem block_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → PreservesAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadPreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  apply block_preserves_at_with (functions := functions) (program := program) (evidence := evidence)
    (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
  all_goals assumption

include unique transport in
theorem sequence_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → PreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    PreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    Stateful.sequence_preserves_at_with (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (staticCondition := fun _ _ => True)
      validity budget size bounded found notTail
      (fun child childBound => Compatibility.legacy_head_preserves functions program evidence transport (first child childBound))
      (fun child childBound => Compatibility.legacy_preserves functions program evidence transport (remaining child childBound))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

include unique transport in
theorem sequence_preserves_at (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply sequence_preserves_at_with (functions := functions) (program := program) (evidence := evidence)
    (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
  all_goals assumption

include unique in
private theorem sequence_stopped_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    PreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    Stateful.sequence_stopped_preserves_at_with_state (canonical := canonical) (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol (fun _ _ _ _ _ _ => True)) validity budget size bounded found notTail environments locals ⟨trivial⟩
      (fun child childBound {_ _ _} headTrace => by
        obtain ⟨same, restores, headValue, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
          first child childBound valid environments heaps locals agrees actualTyped reference read unmapped installed headTrace
        exact ⟨same, restores, headValue, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps, maps, worlds, frame, metadata, ⟨⟨trivial⟩, trivial⟩⟩)
      stops trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

include unique in
private theorem sequence_stopped_preserves_at (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply sequence_stopped_preserves_at_with (functions := functions) (program := program) (evidence := evidence)
    (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
  all_goals assumption

include transport in
theorem conditional_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → PreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → PreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreservesAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.conditional_preserves_at_with (functions := functions) (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (staticCondition := fun _ _ => True)
      validity budget size bounded unique (fun child childBound context valid => Compatibility.legacy_expression_preserves functions program evidence transport (expressionPreserves child childBound context valid))
      found form conditionFound _conditionType conditionTree
      (fun child childBound => Compatibility.legacy_preserves functions program evidence transport (thenCorrect child childBound))
      (fun child childBound => Compatibility.legacy_preserves functions program evidence transport (elseCorrect child childBound))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata⟩

include transport in
theorem conditional_preserves_at (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  apply conditional_preserves_at_with (functions := functions) (program := program) (evidence := evidence)
    (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
  all_goals assumption

end Control

namespace AssignmentSourceAt
private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) :
    ∀ other, ContainsStatement source id other → other.form = node.form := by
  intro other present
  exact congrArg StatementNode.form (Option.some.inj ((lookupStatement?_complete unique present).symm.trans found))

variable {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

theorem value_success (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ child updated,
      SourceExecutionSize.SourcePlaceAssignment program child context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧ child < size := by
  have shapes := shape unique found
  clear found
  cases trace <;> have same := shapes _ (by assumption) <;> simp_all
  exact ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩

theorem unary_success (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ child updated,
      SourceExecutionSize.SourcePlaceSnapshotUpdate program child context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after ∧ child < size := by
  have shapes := shape unique found
  clear found
  cases trace <;> have same := shapes _ (by assumption) <;> simp_all
  exact ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩

theorem value_fault (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.SourcePlaceAssignmentFaults program child context evidence source
      environment before assignment.target operator rhs reason after ∧ child < size := by
  have shapes := shape unique found
  have present : ¬ Dynamic.StatementMissing source id :=
    fun absent => Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  clear found
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have same := shapes _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

theorem unary_fault (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.SourcePlaceBitNotFaults program child context evidence source
      environment before assignment.target reason after ∧ child < size := by
  have shapes := shape unique found
  have present : ¬ Dynamic.StatementMissing source id :=
    fun absent => Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  clear found
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have same := shapes _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩
end AssignmentSourceAt

namespace ForSourceAt
private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

theorem success_at
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome} {size : Nat}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (executed : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ initialSize loopSize loopContext loopFinalContext loopEnvironment initialized loopOutcome,
      outcome = Dynamic.restoreControl environment loopOutcome ∧
      SourceExecutionSize.ForItemsExecute program initialSize context evidence source environment before items loopContext loopEnvironment initialized ∧
      SourceExecutionSize.ForLoopExecutes program loopSize loopContext evidence source loopEnvironment initialized condition post statements loopFinalContext loopOutcome after ∧ initialSize < size ∧ loopSize < size := by
  have formShape := shape unique contains form
  clear contains form
  cases executed <;> have actualForm := formShape _ (by assumption) <;> simp_all
  exact ⟨_, _, _, _, _, _, _, rfl, by assumption, by assumption, SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

theorem fault_at
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {reason : Dynamic.SemanticFault} {size : Nat}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    (∃ initialSize finalContext, SourceExecutionSize.ForItemsFault program initialSize context evidence source environment before items finalContext reason after ∧ initialSize < size) ∨
    (∃ initialSize loopSize loopContext loopEnvironment initialized,
      SourceExecutionSize.ForItemsExecute program initialSize context evidence source environment before items loopContext loopEnvironment initialized ∧
      SourceExecutionSize.ForLoopFaults program loopSize loopContext evidence source loopEnvironment initialized condition post statements reason after ∧ initialSize < size ∧ loopSize < size) := by
  have formShape := shape unique contains form
  have present : ¬ Dynamic.StatementMissing source id := fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := formShape _ (by assumption); simp_all
  · exact Or.inl ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  · exact .inr ⟨_, _, _, _, _, by assumption, by assumption, SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

end ForSourceAt

open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
private theorem breaking_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible
    · exact ScalarStatementViews.breaking unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.breaking_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible

private theorem continuing_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible
    · exact ScalarStatementViews.continuing unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.continuing_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible


open GenericImperativeFor (Tree Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (producer : OrdinaryAllocation.Producer protocol layouts frame (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, conditionGate location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (budget : Nat)
  {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.AssignmentPrefixPreservesAt protocol functions (registry := registry)
    program evidence source (certificates context) context administrative budget)
  (assignmentFaults : ∀ context, validity context → ProtectedForHeader.Stateful.AssignmentFaultPreservesAt protocol functions (registry := registry)
    program evidence source (certificates context) context administrative faults budget)
  (meaning : ∀ context, validity context → Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
    (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size))
include definitions registered observations producer acquire stateTransport stateBindings assignments assignmentFaults meaning extend solved in
theorem header_preserves_at_with (size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    (header : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type continuation context scope items code)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults header)
    (loopCorrect : ∀ {nextContext nextScope nextCode}, continuation nextContext nextScope nextCode →
      AtMost budget (fun child => ProtectedFor.Body.Stateful.LoopPreservesAtFor protocol conditionGate functions program evidence
        validity child (source := source) (context := nextContext) (registry := registry) (faults := faults)
        (frameLayout := frame) (globals := globals) (administrative := administrative)
        (scope := nextScope) condition post statements expected type nextCode)) :
    Control.Stateful.HeadPreservesAtWith protocol conditionGate (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped initial guarded trace
  cases trace with
  | control executed =>
    obtain ⟨rfl, initialSize, loopSize, loopContext, loopFinalContext, loopEnvironment, initialized, loopOutcome, rfl, initialization, loop, initialSmall, loopSmall⟩ :=
      ForSourceAt.success_at unique (lookupStatement?_sound found) form executed
    have sameContext : loopFinalContext = loopContext := ContextTransport.loop_context loop
    subst loopFinalContext
    obtain ⟨tail, maps, worlds, frame, metadata, headerRelated, ⟨returnTo⟩, agreement⟩ :=
      ProtectedForHeader.Stateful.Tree.preserves_prefix_bounded_for_with_return (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
        (program := program) (evidence := evidence) (observations := observations)
        (protocol := protocol) (condition := conditionGate) (producer := producer) (acquire := acquire)
        (stateTransport := stateTransport) (stateBindings := stateBindings)
        validity extend budget assignments meaning header
        valid environments heaps locals agrees actualTyped reference read unmapped initial guarded initialization (Nat.le_trans (Nat.le_of_lt initialSmall) bounded)
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, loopHeaps, loopMaps, loopWorlds, loopFrame, loopMetadata, loopTransition⟩ :=
      (loopCorrect tail.certificate) _ (Nat.le_trans (Nat.le_of_lt loopSmall) bounded) tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.state tail.gate (.control loop)
    obtain ⟨loopState, loopRelated⟩ := loopTransition
    exact ⟨rfl, restored environment loopOutcome, value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
      restore_rep represented environment, loopHeaps, maps.trans loopMaps, worlds.trans loopWorlds,
      frame.trans loopFrame, metadata.trans loopMetadata,
      ⟨returnTo.restore loopState, protocol.trans headerRelated (protocol.trans loopRelated (returnTo.related loopState))⟩⟩
  | fault failed =>
    rcases ForSourceAt.fault_at unique (lookupStatement?_sound found) form failed with initialFailure | loopFailure
    · obtain ⟨_, _, fault, smaller⟩ := initialFailure
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, frame, metadata, transition⟩ :=
        ProtectedForHeader.Stateful.Tree.preserves_fault_reachable_bounded_for (functions := functions) (definitions := definitions) (registered := registered)
        (program := program) (evidence := evidence) (observations := observations)
        (protocol := protocol) (condition := conditionGate) (producer := producer) (acquire := acquire)
        (stateTransport := stateTransport) (stateBindings := stateBindings)
        validity extend budget assignments assignmentFaults meaning header errors
          valid environments heaps locals agrees actualTyped reference read unmapped initial guarded fault (Nat.le_trans (Nat.le_of_lt smaller) bounded)
      exact ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld,
        evaluated, .fault matched, heaps, maps, worlds, frame, metadata, transition⟩
    · obtain ⟨initialSize, loopSize, loopContext, loopEnvironment, initialized, initialization, loop, initialSmall, loopSmall⟩ := loopFailure
      obtain ⟨tail, maps, worlds, frame, metadata, headerRelated, ⟨returnTo⟩, agreement⟩ :=
        ProtectedForHeader.Stateful.Tree.preserves_prefix_bounded_for_with_return (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
        (program := program) (evidence := evidence) (observations := observations)
        (protocol := protocol) (condition := conditionGate) (producer := producer) (acquire := acquire)
        (stateTransport := stateTransport) (stateBindings := stateBindings)
        validity extend budget assignments meaning header
          valid environments heaps locals agrees actualTyped reference read unmapped initial guarded initialization (Nat.le_trans (Nat.le_of_lt initialSmall) bounded)
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, loopHeaps, loopMaps, loopWorlds, loopFrame, loopMetadata, loopTransition⟩ :=
        (loopCorrect tail.certificate) _ (Nat.le_trans (Nat.le_of_lt loopSmall) bounded) tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.state tail.gate (.fault loop)
      obtain ⟨loopState, loopRelated⟩ := loopTransition
      exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
        represented, loopHeaps, maps.trans loopMaps, worlds.trans loopWorlds,
        frame.trans loopFrame, metadata.trans loopMetadata,
      ⟨returnTo.restore loopState, protocol.trans headerRelated (protocol.trans loopRelated (returnTo.related loopState))⟩⟩

include definitions registered observations producer acquire stateTransport stateBindings assignments assignmentFaults meaning extend solved in
theorem loop_preserves_at_with (size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Below budget (fun child => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol conditionGate (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) child false statements expected type code)) :
    ProtectedFor.Body.Stateful.LoopPreservesAtFor protocol conditionGate (validity := validity) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped initial gate trace
  have result := ProtectedFor.Body.Stateful.loop_preserves_bounded_for (protocol := protocol) (guard := conditionGate) (validity := validity) functions program evidence stateTransport budget (meaning _ valid)
    conditionFound conditionTree typed unique correct
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        child small mapping world before after store finalContext finalEnvironment state native realRead guarded continued execution
      exact ProtectedForHeader.Stateful.post_preserves_bounded_for (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
        (program := program) (evidence := evidence) (observations := observations)
        (protocol := protocol) (guard := conditionGate) (producer := producer) (acquire := acquire)
        (stateTransport := stateTransport) (stateBindings := stateBindings)
        validity extend budget assignments meaning postTree
        actualValid actualAgrees actualReference state realRead guarded continued execution (Nat.le_of_lt small))
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        child small mapping world before after store finalContext reason state native realRead guarded continued execution
      exact ProtectedForHeader.Stateful.post_fault_reachable_bounded_for (functions := functions) (definitions := definitions) (registered := registered)
        (program := program) (evidence := evidence) (observations := observations)
        (protocol := protocol) (guard := conditionGate) (producer := producer) (acquire := acquire)
        (stateTransport := stateTransport) (stateBindings := stateBindings)
        validity extend budget assignments assignmentFaults meaning postTree postErrors
        actualValid actualAgrees actualReference state realRead guarded continued execution (Nat.le_of_lt small))
  exact result size bounded valid environments heaps locals agrees actualTyped reference read unmapped initial gate trace

end Stateful

namespace Stateful.WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateImperativeCatalogReady
section CatalogSites
universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerSites : InitializerSites initializerFacts loopFacts source)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts headFacts exprFacts program evidence source)
  (assignmentSites : AssignmentSites headFacts assignmentFacts snapshotFacts source)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)
  (transfers : AllocationTransfers protocol readiness stateBindings source)
  (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
  (assignments : ∀ context, validity context → Assignment.AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions
    (registry := registry) program evidence source (certificates context) context administrative budget)
  (assignmentFaults : ∀ context, validity context → Assignment.AssignmentFaultPreservesAt protocol readiness assignmentFacts functions
    (registry := registry) program evidence source (certificates context) context administrative faults budget)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


variable (meaningMost : ∀ context, validity context →
  AtMost budget (fun size => ExpressionPreservesAt protocol readiness program evidence
    (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
    (context := context) (source := source) (faults := faults) size))
include definitions registered stateTransport stateBindings producer acquire meaningMost observations extend sites transfers assignmentSites initializerSites snapshots assignments in
theorem preservesAt_match_with_eliminator
    (AP : GenericImperativeMatch.Structural.AssignmentPayload (values := values) (source := source) (certificates := certificates) (administrative := administrative) (definitions := ambient.definitions)) (UP : GenericImperativeMatch.Structural.UnaryPayload)
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative)) (MP : GenericImperativeMatch.Structural.MatchPayload)
    (R : ProtectedStateImperativeCatalogPayload.HeaderReceiptFamily)
    (headerAlgebra : ProtectedStateImperativeCatalogPayload.HeaderReceiptAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) R AP UP)
    (unaryErrors : ∀ {context scope assignment} {head : CompatibleBitNotStatements.Head context scope assignment}, UP head → head.Errors faults)
    (matchFields : ∀ compilation context, MP compilation context →
      SignatureCatalogWellFormed values.checked.signatures ∧ GenericImperativeMatch.Tree.MatchContextFields compilation context)
    (assignmentFaultsWithPayload : ∀ context, validity context →
      ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt protocol readiness assignmentFacts functions
        (registry := registry) program evidence source (certificates context) context administrative faults budget (fun head => AP head))
    (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (headFor : PreservingHeads protocol readiness conditionGate headFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget R))
    (loopFor : ProtectedStateImperativeCatalogPayload.PreservingLoopsWithPayload protocol readiness conditionGate loopFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget R) HP)
    (eliminator : GenericImperativeMatch.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative)
      AP UP HP MP context scope position expected type code) :
    ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) functions program evidence budget R
      (frame := frame) (globals := globals)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  have meaning : ∀ context, validity context →
      Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (context := context) (source := source) (faults := faults) size) :=
    fun context valid child smaller => meaningMost context valid child (Nat.le_of_lt smaller)
  have algebra : GenericImperativeMatch.Structural.BranchAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) AP UP HP MP
      (ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) functions program evidence budget R (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults)) := by
    clear context scope position expected type code eliminator
    constructor
    · intro context scope mode statements expected type code syntaxTree body
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
        RecursiveNamedLexicalTreeBounds.Stateful.WithReady.preserves_at_for (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (transfers := transfers) (validity := validity) (extend := extend) functions definitions registered program evidence protocol conditionGate producer.toOrdinary stateBindings acquire size size (Nat.le_refl size)
          (fun child within context valid => meaningMost context valid child (Nat.le_trans within bounded))
          body contextValid sourceFacts unique environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩
    · intro context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      obtain ⟨location, middle, tailSize, allocated, tailTrace, smaller⟩ :=
        RecursiveNamedLexicalTreeSourceBounds.absent unique found form mono extended trace
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
        TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer.toOrdinary mono extended ordinary projected allocation annotation same
          environments heaps locals agrees actualTyped reference read allocated installed ((acquire _ _ guarded) installed read)
      obtain ⟨nextState, allocationRelated⟩ := allocationTransition
      have nextReady := transfers.absent installed nextState initialReady extended allocated preservation
      have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form])
        (.letUninitialized (lookupStatement?_sound found) form mono extended allocated)
      obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical, tailTransition⟩ :=
        ih _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (extend contextValid extended) tailFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          nextState guarded nextReady tailTrace
      obtain ⟨tailState, tailRelated, tailReady⟩ := tailTransition
      let finalState := stateBindings.restore
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      have finalRelated := protocol.trans tailRelated (stateBindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)
      have finalReady := AllocationTransfers.restore_post (protocol := protocol) (readiness := readiness)
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (binder := binder) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) transfers extended tailState tailReady
      exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended, ⟨finalState, protocol.trans allocationRelated finalRelated, finalReady⟩⟩
    · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      rw [sequence_rename]
      rcases RecursiveNamedLexicalTreeSourceBounds.initialized unique found form mono extended trace with
        ⟨childSize, reason, rfl, rfl, failed, smaller⟩ |
        ⟨childSize, tailSize, sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace, smaller, tailSmaller⟩
      · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata, transition⟩ :=
          meaning _ contextValid childSize (Nat.lt_of_lt_of_le smaller bounded) initial initialFound (sites.expression (sites.head sourceFacts) (.initialized found form) initialFound)
            environments heaps locals agrees actualTyped installed initialReady (.fault failed)
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
      · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata, transition⟩ :=
          meaning _ contextValid childSize (Nat.lt_of_lt_of_le smaller bounded) initial initialFound (sites.expression (sites.head sourceFacts) (.initialized found form) initialFound)
            environments heaps locals agrees actualTyped installed initialReady (.value initialTrace)
        cases represented with
        | value payload =>
          obtain ⟨middleState, expressionRelated, middleReady, valueFacts⟩ := transition
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
            TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer.toOrdinary mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated middleState ((acquire _ _ guarded) middleState frameRead)
          obtain ⟨nextState, allocationRelated⟩ := allocationTransition
          have nextReady := transfers.initialized middleState nextState middleReady extended (sourceType ▸ valueFacts) allocated allocationFrame
          have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form])
            (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended allocated)
          obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical, tailTransition⟩ :=
            ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) (extend contextValid extended) tailFacts
              nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
                (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1
                nextState guarded nextReady tailTrace
          obtain ⟨tailState, tailRelated, tailReady⟩ := tailTransition
          let finalState := stateBindings.restore
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
          have finalRelated := protocol.trans tailRelated (stateBindings.restore_related
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState)
          have finalReady := AllocationTransfers.restore_post (protocol := protocol) (readiness := readiness)
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (binder := binder) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) transfers extended tailState tailReady
          exact ⟨result, finalStore, finalMap, finalWorld,
            LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), lexical.bind extended,
            ⟨finalState, protocol.trans expressionRelated (protocol.trans allocationRelated finalRelated), finalReady⟩⟩
    · intro context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      rcases RecursiveNamedLexicalTreeSourceBounds.discard unique found form guard trace with
        ⟨childSize, reason, rfl, rfl, failed, smaller⟩ |
        ⟨childSize, tailSize, sourceValue, middle, childTrace, tail, smaller, tailSmaller⟩
      · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
          meaning _ contextValid childSize (Nat.lt_of_lt_of_le smaller bounded) child expressionFound (sites.expression (sites.head sourceFacts) (.expression found form) expressionFound)
            environments heaps locals agrees actualTyped installed initialReady (.fault failed)
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
      · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, transition⟩ :=
          meaning _ contextValid childSize (Nat.lt_of_lt_of_le smaller bounded) child expressionFound (sites.expression (sites.head sourceFacts) (.expression found form) expressionFound)
            environments heaps locals agrees actualTyped installed initialReady (.value childTrace)
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨middleState, expressionRelated, middleReady, _valueFacts⟩ := transition
          obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata, lexical, tailTransition⟩ :=
            ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid (sites.tail (environment := environment) (before := before) sourceFacts found (not_tail form guard)
              (.expression (lookupStatement?_sound found) form childTrace.sound)) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState guarded middleReady tail
          obtain ⟨finalState, tailRelated, tailReady⟩ := tailTransition
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
            firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical, ⟨finalState, protocol.trans expressionRelated tailRelated, tailReady⟩⟩
          rw [LoopRenaming.discard]
          rw [GenericExpressionMeaning.rename_prefix] at second
          exact LocalSequence.discard_success _ first second
    · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH remainingIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      exact Control.Stateful.WithReady.sequence_preserves_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => Control.Stateful.WithReady.block_preserves_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
          (frameLayout := frame) (globals := globals) (unique := unique) size child within found form
          (fun child within => innerIH child (Nat.le_trans within bounded)))
        (fun child within => remainingIH child (Nat.le_trans within bounded))
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
    · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      exact Control.Stateful.WithReady.sequence_preserves_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => Control.Stateful.WithReady.conditional_preserves_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
           (frameLayout := frame) (globals := globals) size child within unique
          (fun child within context valid => meaningMost context valid child (Nat.le_trans within bounded))
          found form conditionFound conditionType conditionTree
          (fun child within => thenIH child (Nat.le_trans within bounded))
          (fun child within => elseIH child (Nat.le_trans within bounded)))
        (fun child within => remainingIH child (Nat.le_trans within bounded))
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
    · intro context scope mode id node rest expected type found form
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      obtain ⟨rfl, rfl, rfl⟩ := breaking_view unique found form trace.sound
      exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates _ actual store,
        .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, ⟨installed, protocol.refl installed, initialReady⟩⟩
    · intro context scope mode id node rest expected type found form
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      obtain ⟨rfl, rfl, rfl⟩ := continuing_view unique found form trace.sound
      exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates _ actual store,
        .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, ⟨installed, protocol.refl installed, initialReady⟩⟩
    · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopIH restIH
      intro size bounded
      exact Control.Stateful.WithReady.sequence_preserves_at_with (protocol := protocol) (staticCondition := conditionGate)
        (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
        (headFor (.whileLoop found form conditionFound conditionType conditionTree loopTree nativeTyped loopIH)) restIH
    · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining ih headErrors
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      have go {headSize tailSize : Nat} {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
          (first : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id middleContext (.fallthrough next) middle)
          (tail : ExecutesAt tailSize mode program middleContext evidence source next middle rest resultContext outcome after) (headSmaller : headSize < size) (tailSmaller : tailSize < size) :
          ∃ value finalStore finalMap finalWorld,
            Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
            FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
            CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
            LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
            AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
            LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
              context scope environment resultContext after ∧
            Reached readiness context outcome installed ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
        obtain ⟨rfl, same, childSize, updated, assigned, childSmaller⟩ := AssignmentSourceAt.value_success unique found form first
        cases same
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, assignmentPost, continuation⟩ :=
          assignments _ contextValid head (assignmentSites.assignment (sites.head sourceFacts) found form)
            environments heaps locals agrees actualTyped installed initialReady assigned
            (Nat.le_of_lt (Nat.lt_trans childSmaller (Nat.lt_of_lt_of_le headSmaller bounded)))
        obtain ⟨writeState, assignmentRelated, writeReady⟩ := assignmentPost
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical, tailPost⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid (sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form]) first.sound) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference frameRead
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 writeState guarded writeReady tail
        exact ⟨value, finalStore, finalMap, finalWorld,
          (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count,
            SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
          represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, lexical, Reached.continue (protocol := protocol) (readiness := readiness) assignmentRelated tailPost⟩
      cases RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found) (by intro _ _; simp [form]) trace with
      | next first tail headSmaller tailSmaller => exact go first tail headSmaller tailSmaller
      | terminal first terminal _ =>
        obtain ⟨_, rfl, _⟩ := AssignmentSourceAt.value_success unique found form first
        cases terminal
      | fault first smaller =>
        obtain ⟨childSize, failed, childSmaller⟩ := AssignmentSourceAt.value_fault unique found form first
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, assignmentPost⟩ :=
          assignmentFaultsWithPayload _ contextValid head (assignmentSites.assignment (sites.head sourceFacts) found form)
            environments heaps locals agrees actualTyped installed initialReady headErrors failed
            (Nat.le_of_lt (Nat.lt_trans childSmaller (Nat.lt_of_lt_of_le smaller bounded))) body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, assignmentPost⟩
    · intro context scope mode id node assignment rest expected type body found form head remaining ih headErrors
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      have go {headSize tailSize : Nat} {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
          (first : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id middleContext (.fallthrough next) middle)
          (tail : ExecutesAt tailSize mode program middleContext evidence source next middle rest resultContext outcome after) (_headSmaller : headSize < size) (tailSmaller : tailSize < size) :
          ∃ value finalStore finalMap finalWorld,
            Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
            FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
            CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
            LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
            AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
            TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
              context scope environment resultContext after ∧
            Reached readiness context outcome installed ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
        obtain ⟨rfl, same, _childSize, updated, assigned, _childSmaller⟩ := AssignmentSourceAt.unary_success unique found form first
        cases same
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
          head.preserves_prefix functions program evidence observations
            environments heaps locals agrees actualTyped assigned.sound
        let writtenState := stateTransport.extend installed maps worlds frame metadata
        have writtenReady := snapshots.ready installed writtenState
          initialReady contextValid (assignmentSites.snapshot (sites.head sourceFacts) found form) assigned.sound locals frame
        obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical, tailPost⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid (sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form]) first.sound) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            writtenState guarded writtenReady tail
        exact ⟨value, finalStore, finalMap, finalWorld,
          (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
          represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical, Reached.continue (protocol := protocol) (readiness := readiness) (stateTransport.related installed maps worlds frame metadata) tailPost⟩
      cases RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found) (by intro _ _; simp [form]) trace with
      | next first tail headSmaller tailSmaller => exact go first tail headSmaller tailSmaller
      | terminal first terminal _ =>
        obtain ⟨_, rfl, _⟩ := AssignmentSourceAt.unary_success unique found form first
        cases terminal
      | fault first _ =>
        obtain ⟨_, failed, _⟩ := AssignmentSourceAt.unary_fault unique found form first
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩ :=
          head.preserves_fault functions program evidence observations environments heaps locals agrees (unaryErrors headErrors) failed.sound body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩,
          ⟨stateTransport.extend installed maps worlds preservation metadata, stateTransport.related installed maps worlds preservation metadata, readiness.fault_after installed _ (readiness.ready_fault initialReady) preservation⟩⟩
    · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialIH restIH
      intro size bounded
      exact Control.Stateful.WithReady.sequence_preserves_at_with (protocol := protocol) (staticCondition := conditionGate)
        (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
        (headFor (.forLoop found form initialIH)) restIH
    · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopIH postErrors
      intro initializerStatic
      have completed := And.intro (initializerSites.done initializerStatic) (loopFor (.mk conditionFound conditionType conditionTree loopTree postTree postErrors nativeTyped loopIH) (initializerSites.done initializerStatic))
      exact (headerAlgebra type _).nil completed
    · intro context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining ih
      intro initializerStatic
      exact (headerAlgebra type _).uninitialized mono extended ordinary projected allocation annotation same (ih (initializerSites.absent initializerStatic extended))
    · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining ih
      intro initializerStatic
      exact (headerAlgebra type _).initialized mono extended ordinary found sourceType child allocation annotation same (ih (initializerSites.initialized initializerStatic extended))
    · intro context scope expression expressionNode rest lowered body condition post statements expected type found child remaining ih
      intro initializerStatic
      exact (headerAlgebra type _).discard found child (ih (initializerSites.discard initializerStatic))
    · intro context scope assignment operator rhs rest body condition post statements expected type head remaining ih headErrors
      intro initializerStatic
      exact (headerAlgebra type _).assign head headErrors (ih (initializerSites.assignment initializerStatic))
    · intro context scope assignment rest body condition post statements expected type head remaining ih headErrors
      intro initializerStatic
      exact (headerAlgebra type _).bitNot head headErrors (ih (initializerSites.snapshot initializerStatic))
    · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining matchPayload childrenIH remainingIH
      obtain ⟨catalogValid, patternContext⟩ := matchFields compilation context matchPayload
      intro size bounded
      exact Control.Stateful.WithReady.sequence_preserves_at_with (protocol := protocol) (staticCondition := conditionGate)
        (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
        (headFor (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions
          allocator requests receipt ordinary children catalogValid patternContext childrenIH))
        remainingIH
    · intro context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      exact Control.Stateful.WithReady.sequence_stopped_preserves_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => Control.Stateful.WithReady.block_preserves_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
          (frameLayout := frame) (globals := globals) (unique := unique) size child within found form
          (fun child within => innerIH child (Nat.le_trans within bounded)))
        (GenericLexicalStatements.block_terminates exactUnique found form stops)
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
    · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
      exact Control.Stateful.WithReady.sequence_stopped_preserves_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => Control.Stateful.WithReady.conditional_preserves_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
           (frameLayout := frame) (globals := globals) size child within unique
          (fun child within context valid => meaningMost context valid child (Nat.le_trans within bounded))
          found form conditionFound conditionType conditionTree
          (fun child within => thenIH child (Nat.le_trans within bounded))
          (fun child within => elseIH child (Nat.le_trans within bounded)))
        (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady trace
    · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued matchPayload childrenIH
      obtain ⟨catalogValid, patternContext⟩ := matchFields compilation context matchPayload
      intro size bounded
      exact Control.Stateful.WithReady.sequence_stopped_preserves_at_with (protocol := protocol) (staticCondition := conditionGate)
        (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
        (headFor (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions
          allocator requests receipt ordinary children catalogValid patternContext childrenIH))
        (ReachableMatchContinuations.DefaultStopped.terminates exactUnique stops)
  exact eliminator _ algebra

include definitions registered stateTransport stateBindings producer acquire meaningMost observations extend sites transfers assignmentSites initializerSites snapshots assignments assignmentFaults in
theorem preservesAt_match_with (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (headFor : PreservingHeads protocol readiness conditionGate headFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (PreservesAtWith protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy)
        (certificates := certificates) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget))
    (loopFor : PreservingLoops protocol readiness conditionGate loopFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (PreservesAtWith protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy)
        (certificates := certificates) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget) diagnosticPolicy)
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    PreservesAtWith protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact preservesAt_match_with_eliminator (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (protocol := protocol) (readiness := readiness)
    (conditionGate := conditionGate) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts)
    (loopFacts := loopFacts) (initializerFacts := initializerFacts) (assignmentFacts := assignmentFacts)
    (snapshotFacts := snapshotFacts) (producer := producer) (stateTransport := stateTransport)
    (stateBindings := stateBindings) (acquire := acquire) (validity := validity) (extend := extend)
    (budget := budget) (sites := sites) (assignmentSites := assignmentSites) (initializerSites := initializerSites)
    (transfers := transfers) (snapshots := snapshots) (observations := observations)
    (assignments := assignments) (meaningMost := meaningMost)
    (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults)
    (fun postTree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree)
    (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ GenericImperativeMatch.Tree.MatchContextFields compilation context)
    (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (ProtectedStateImperativeCatalogPayload.legacy_header_algebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (fun receipt => receipt) (fun _ _ receipt => receipt)
    (by
      intro context valid scope assignment operator rhs head sourceFacts mapping world environment canonical actual before store actualContext ξ environments heaps locals agrees typed installed ready receipt reason after size failed bounded next output
      exact assignmentFaults context valid head sourceFacts environments heaps locals agrees typed installed ready receipt.reachable failed bounded next output)
    unique headFor
    (fun recipe => loopFor (recipe.to_legacy diagnosticPolicy))
    (GenericImperativeMatch.Structural.of_catalog_sites errors)

end CatalogSites
end Stateful.WithReady
namespace Stateful.WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateImperativeCatalogReady
section Compatibility
universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


variable (meaningMost : ∀ context, validity context →
  AtMost budget (fun size => ProtectedStateTransition.PreservesAt protocol
    (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source (certificates context) faults size))
include extension stateTransport meaningMost faithful observations in
theorem assignment_prefix_uniform : ∀ context, validity context → ProtectedForHeader.Stateful.AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative budget := by
    intro context valid scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
      environments heaps locals agrees typed state updated after child assigned within
    exact ProtectedAssignmentHeads.Stateful.Head.preserves_prefix_bounded functions extension program evidence protocol stateTransport faithful observations
      head environments heaps locals agrees typed state budget (fun child smaller => meaningMost context valid child (Nat.le_of_lt smaller)) assigned within
include extension stateTransport meaningMost faithful observations in
theorem assignment_fault_uniform : ∀ context, validity context → ProtectedForHeader.Stateful.AssignmentFaultPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget := by
    intro context valid scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
      environments heaps locals agrees typed state errors reason after child failed within next output
    exact ProtectedAssignmentHeads.Stateful.Head.preserves_fault_reachable_bounded functions extension program evidence protocol stateTransport faithful observations
      head environments heaps locals agrees typed state budget (fun child smaller => meaningMost context valid child (Nat.le_of_lt smaller)) errors failed within next output
include definitions registered extension stateTransport stateBindings producer acquire meaningMost faithful observations extend runtimeOf solved in
theorem preserving_heads_trivial (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source) :
    PreservingHeads protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ => True) functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults) (PreservesAtWith protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget) := by
  have meaning : ∀ context, validity context → Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size) :=
    fun context valid child smaller => meaningMost context valid child (Nat.le_of_lt smaller)
  have assignments := assignment_prefix_uniform (administrative := administrative) (protocol := protocol) (functions := functions) (program := program) (evidence := evidence)
    (extension := extension) (stateTransport := stateTransport) (faithful := faithful) (observations := observations) (meaningMost := meaningMost) (validity := validity) (budget := budget)
  have assignmentFaults := assignment_fault_uniform (administrative := administrative) (protocol := protocol) (functions := functions) (program := program) (evidence := evidence)
    (extension := extension) (stateTransport := stateTransport) (faithful := faithful) (observations := observations) (meaningMost := meaningMost) (validity := validity) (budget := budget)
  intro context scope id expected type code recipe size bounded
  apply Control.Stateful.WithReady.HeadPreservesAtWith.of_true (protocol := protocol) (condition := conditionGate)
    (functions := functions) (program := program) (evidence := evidence)
  cases recipe with
  | whileLoop found form conditionFound _conditionType conditionTree loopTree nativeTyped child =>
    intro valid
    exact ProtectedWhile.Body.Stateful.while_preserves_bounded_for (protocol := protocol) (guard := conditionGate)
      (validity := validity) (functions := functions) (program := program) (evidence := evidence) (transport := stateTransport)
      budget (meaning _ valid) found form conditionFound conditionTree nativeTyped unique
      (fun childSize smaller => (preserves_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
        (functions := functions) (program := program) (evidence := evidence) child) childSize (Nat.le_of_lt smaller)) size bounded valid
  | forLoop found form child =>
    obtain ⟨header, errors⟩ := preserves_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
      (functions := functions) (program := program) (evidence := evidence) child
    exact Stateful.header_preserves_at_with (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (producer := producer.toOrdinary) (acquire := acquire) (stateTransport := stateTransport) (stateBindings := stateBindings)
      (validity := validity) (extend := extend) (budget := budget) (solved := solved)
      (assignments := assignments) (assignmentFaults := assignmentFaults) (meaning := meaning)
      size bounded unique found form header errors.reachable (fun correct => correct)
  | matchWith found form scrutineeFound _scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children catalogValid patternContext child =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    intro contextValid
    exact CompatibleMatchRuntimeHead.Stateful.head_preserves_bounded onError allocator functions definitions registered extension receipt ordinary
      patternContext.signatures catalogValid scrutineeFound casesTyped defaultTyped
      (patternContext.ledger.symm.trans (runtimeOf context contextValid).ledger)
      unique budget size bounded protocol conditionGate producer stateBindings acquire validity
      (fun extended valid => ContextTransport.binders validity extend valid extended)
      (fun valid => runtimeOf context valid) (fun _ => meaning context contextValid)
      (fun request member childContext related childSize smaller _ =>
        (preserves_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
          (functions := functions) (program := program) (evidence := evidence) (child request member childContext related))
          childSize (Nat.le_of_lt smaller) (ContextTransport.scoped_context validity extend contextValid related))
      contextValid

include definitions registered extension stateTransport stateBindings producer acquire meaningMost faithful observations extend solved in
theorem preserving_loops_trivial (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source) :
    PreservingLoops protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ _ => True) functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults) (PreservesAtWith protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget) diagnosticPolicy := by
  have meaning : ∀ context, validity context → Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size) :=
    fun context valid child smaller => meaningMost context valid child (Nat.le_of_lt smaller)
  have assignments := assignment_prefix_uniform (administrative := administrative) (protocol := protocol) (functions := functions) (program := program) (evidence := evidence)
    (extension := extension) (stateTransport := stateTransport) (faithful := faithful) (observations := observations) (meaningMost := meaningMost) (validity := validity) (budget := budget)
  have assignmentFaults := assignment_fault_uniform (administrative := administrative) (protocol := protocol) (functions := functions) (program := program) (evidence := evidence)
    (extension := extension) (stateTransport := stateTransport) (faithful := faithful) (observations := observations) (meaningMost := meaningMost) (validity := validity) (budget := budget)
  intro context scope condition post statements expected type code recipe _static size bounded
  cases recipe with
  | mk conditionFound _conditionType conditionTree loopTree postTree postErrors nativeTyped child =>
    apply loop_preserves_of_true (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
    exact Stateful.loop_preserves_at_with (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (producer := producer.toOrdinary) (acquire := acquire) (stateTransport := stateTransport) (stateBindings := stateBindings)
      (validity := validity) (extend := extend) (budget := budget) (solved := solved)
      (assignments := assignments) (assignmentFaults := assignmentFaults) (meaning := meaning)
      size bounded unique conditionFound conditionTree nativeTyped postTree postErrors.reachable
      (fun childSize smaller => (preserves_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
        (functions := functions) (program := program) (evidence := evidence) child) childSize (Nat.le_of_lt smaller))

end Compatibility
end Stateful.WithReady


namespace Stateful
section CatalogSites
universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


variable (meaningMost : ∀ context, validity context →
  AtMost budget (fun size => ProtectedStateTransition.PreservesAt protocol
    (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source (certificates context) faults size))
include definitions registered extension stateTransport stateBindings producer acquire meaningMost faithful observations extend runtimeOf in
theorem preservesAt_match_with (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    PreservesAtWith protocol conditionGate (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  have headFor : ProtectedStateImperativeCatalogReady.PreservingHeads protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) conditionGate (fun _ _ _ => True) functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults) (WithReady.PreservesAtWith protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget) := WithReady.preserving_heads_trivial (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
    (definitions := definitions) (registered := registered) (extension := extension)
    (producer := producer) (stateTransport := stateTransport) (stateBindings := stateBindings) (acquire := acquire)
    (validity := validity) (extend := extend) (runtimeOf := runtimeOf) (solved := solved)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := meaningMost) diagnosticPolicy unique
  have loopFor : ProtectedStateImperativeCatalogReady.PreservingLoops protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) conditionGate (fun _ _ _ _ _ => True) functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults) (WithReady.PreservesAtWith protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget) diagnosticPolicy := WithReady.preserving_loops_trivial (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
    (definitions := definitions) (registered := registered) (extension := extension)
    (producer := producer) (stateTransport := stateTransport) (stateBindings := stateBindings) (acquire := acquire)
    (validity := validity) (extend := extend) (solved := solved)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := meaningMost) diagnosticPolicy unique
  have prefixMeaning := WithReady.assignment_prefix_uniform (protocol := protocol) (functions := functions) (program := program) (evidence := evidence)
    (administrative := administrative) (extension := extension) (stateTransport := stateTransport) (validity := validity)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := meaningMost)
  have fault := WithReady.assignment_fault_uniform (protocol := protocol) (functions := functions) (program := program) (evidence := evidence)
    (administrative := administrative) (extension := extension) (stateTransport := stateTransport) (validity := validity)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := meaningMost)
  apply ProtectedStateImperativeCatalogReady.preserves_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
    (functions := functions) (program := program) (evidence := evidence)
  exact WithReady.preservesAt_match_with (protocol := protocol) (conditionGate := conditionGate)
    (functions := functions) (definitions := definitions) (registered := registered) (program := program) (evidence := evidence)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (loopFacts := fun _ _ _ _ _ => True) (initializerFacts := fun _ _ _ _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (initializerSites := ProtectedStateImperativeCatalogReady.InitializerSites.trivial source)
    (assignmentSites := ProtectedStateImperativeCatalogReady.AssignmentSites.trivial source)
    (producer := producer) (stateTransport := stateTransport) (stateBindings := stateBindings) (acquire := acquire)
    (validity := validity) (extend := extend) (budget := budget) (observations := observations)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial (protocol := protocol) stateBindings source)
    (snapshots := ProtectedForHeader.Stateful.WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
    (assignments := fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_prefix_trivial
      protocol functions program evidence source (certificates context) context administrative budget (prefixMeaning context valid))
    (assignmentFaults := fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_fault_trivial
      protocol functions program evidence source (certificates context) context administrative faults budget (fault context valid))
    (meaningMost := fun context valid child within => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true
      (protocol := protocol) (program := program) (evidence := evidence) (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := certificates context) (meaningMost context valid child within))
    diagnosticPolicy unique headFor loopFor tree errors

end CatalogSites
end Stateful

section WithValidity
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)
  (meaning : ∀ context, validity context →
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry))
  (reflection : ∀ context, validity context →
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry))

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


namespace ForCompatibility
def legacyBindings (bindings : ProtectedExpressionMeaning.Binds entry) :
    ProtectedStateTransition.Bindings (ProtectedStateTransition.Lexical.legacyProtocol entry) where
  prepend state _id _type _value := ⟨bindings.prepend state.down⟩
  prepend_related _state _id _type _value := trivial
  prepend_records _state _id _type _value := rfl
  restore state := ⟨bindings.restore state.down⟩
  restore_related _state := trivial
  restore_records _state := rfl

def legacyProducer (functions : FunctionModel values.checked.catalog ambient)
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry) :
    ProtectedStateTransition.OrdinaryAllocation.Producer (ProtectedStateTransition.Lexical.legacyProtocol entry) layouts frame
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) :=
  ProtectedStateTransition.OrdinaryAllocation.of_administrative _
    (ProtectedStateTransition.Lexical.legacyTransport transport) (legacyBindings bindings)
    layouts frame (CompatibleAmbientHeap.payloadModel values.checked registry functions)

include extension faithful observations transport in
theorem legacyAssignmentPrefix (context : SourceSemantics.Context) (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) :
    ProtectedForHeader.Stateful.AssignmentPrefixPreservesAt (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry)
      program evidence source (certificates context) context administrative budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed state updated after size assigned within
  obtain ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed, installed, agreement⟩ :=
    ProtectedAssignmentHeads.Head.preserves_prefix_bounded functions extension program evidence transport faithful observations head
      environments heaps locals agrees typed state.down budget boundedMeaning assigned within
  exact ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed,
    ⟨⟨installed⟩, trivial⟩, agreement⟩

include extension faithful observations transport in
theorem legacyAssignmentFault (context : SourceSemantics.Context) (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) :
    ProtectedForHeader.Stateful.AssignmentFaultPreservesAt (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed state errors reason after size failed within next output
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, installed⟩ :=
    ProtectedAssignmentHeads.Head.preserves_fault_reachable_bounded functions extension program evidence transport faithful observations head
      environments heaps locals agrees typed state.down budget boundedMeaning errors failed within next output
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata,
    ⟨⟨installed⟩, trivial⟩⟩

include extension faithful observations transport in
theorem legacyAssignmentReflection (context : SourceSemantics.Context) (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry))
    (functionTypes : FunctionRuntimeViews functions) :
    ProtectedForHeader.Stateful.AssignmentReflectsAt (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed state errors next output value finalStore size evaluated within
  have result := ProtectedAssignmentHeads.Head.reflects_reachable_bounded functions extension program evidence transport faithful observations head
    environments heaps locals agrees typed state.down budget boundedReflection functionTypes errors evaluated within
  cases result with
  | fault trace same matched finalHeaps maps worlds preservation metadata installed =>
    exact .fault trace same matched finalHeaps maps worlds preservation metadata ⟨⟨installed⟩, trivial⟩
  | success trace finalHeaps maps worlds preservation metadata count typed installed smaller remaining =>
    exact .success trace finalHeaps maps worlds preservation metadata count typed ⟨⟨installed⟩, trivial⟩ smaller remaining


variable {loopContext : SourceSemantics.Context} {loopScope : Scope} {loopCode : Expr} {child : Nat}

theorem legacyLoopPreserves
    (old : RecursiveNamedForContracts.LoopPreservesAtFor (validity := validity) (entry := entry) functions program evidence child
      (source := source) (context := loopContext) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := loopScope) condition post statements expected type loopCode) :
    ProtectedFor.Body.Stateful.LoopPreservesAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      functions program evidence validity child (source := source) (context := loopContext) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := loopScope) condition post statements expected type loopCode := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped initial _gate trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, installed⟩ :=
    old valid environments heaps locals agrees actualTyped reference read unmapped initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, ⟨⟨installed⟩, trivial⟩⟩

theorem legacyLoopReflects
    (old : RecursiveNamedForContracts.LoopReflectsAtFor (validity := validity) (entry := entry) functions program evidence child
      (source := source) (context := loopContext) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := loopScope) condition post statements expected type loopCode) :
    ProtectedFor.Body.Stateful.LoopReflectsAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      functions program evidence validity child (source := source) (context := loopContext) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := loopScope) condition post statements expected type loopCode := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial _gate evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, installed⟩ :=
    old valid environments heaps locals agrees actualTyped reference read unmapped initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, ⟨⟨installed⟩, trivial⟩⟩

end ForCompatibility

abbrev PreservingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => RecursiveNamedForContracts.LoopPreservesAtFor (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev ReflectingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => RecursiveNamedForContracts.LoopReflectsAtFor (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev PreservesAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => AtMost budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => PreservingHeaderWith (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAtFor (validity := validity) (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => ReflectingHeaderWith (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

include definitions registered extension transport bindings meaning faithful observations extend solved in
set_option linter.unusedSectionVars false in
theorem header_preserves_at_with (size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : PreservingHeaderWith (validity := validity) (diagnosticPolicy := .reachable) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    Control.HeadPreservesAtWith (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨header, errors⟩ := headers
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, _transition⟩ :=
    Stateful.header_preserves_at_with
      (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (conditionGate := fun _ _ => True)
      (producer := ForCompatibility.legacyProducer functions transport bindings)
      (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport)
      (stateBindings := ForCompatibility.legacyBindings bindings)
      (validity := validity) (extend := extend) (budget := budget)
      (assignments := fun context valid => ForCompatibility.legacyAssignmentPrefix functions extension program evidence transport faithful observations context budget
        (meaning context valid))
      (assignmentFaults := fun context valid => ForCompatibility.legacyAssignmentFault functions extension program evidence transport faithful observations context budget (meaning context valid))
      (meaning := fun context valid child smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        functions program evidence transport (meaning context valid child smaller))
      size bounded unique found form header errors
      (fun old child within => ForCompatibility.legacyLoopPreserves functions program evidence validity (old child within))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata⟩

include extension meaning transport bindings definitions registered faithful observations extend solved in
set_option linter.unusedSectionVars false in
theorem loop_preserves_at_with (size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Below budget (fun child => RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) child false statements expected type code)) :
    RecursiveNamedForContracts.LoopPreservesAtFor (validity := validity) (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, transition⟩ :=
    Stateful.loop_preserves_at_with
      (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (conditionGate := fun _ _ => True)
      (producer := ForCompatibility.legacyProducer functions transport bindings)
      (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport)
      (stateBindings := ForCompatibility.legacyBindings bindings)
      (validity := validity) (extend := extend) (budget := budget)
      (assignments := fun context valid => ForCompatibility.legacyAssignmentPrefix functions extension program evidence transport faithful observations context budget
        (meaning context valid))
      (assignmentFaults := fun context valid => ForCompatibility.legacyAssignmentFault functions extension program evidence transport faithful observations context budget (meaning context valid))
      (meaning := fun context valid child smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        functions program evidence transport (meaning context valid child smaller))
      size bounded unique conditionFound conditionTree typed postTree postErrors
      (fun child smaller => ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport (correct child smaller)))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace
  obtain ⟨reached, _related⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, reached.down⟩

variable (meaningMost : ∀ context, validity context →
  AtMost budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
    (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source (certificates context) faults entry))
include definitions registered extension transport bindings meaningMost faithful observations extend runtimeOf in
theorem preservesAt_match_with (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    PreservesAtWith (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  let stateBindings := ForCompatibility.legacyBindings bindings
  let producer := ProtectedStateTransition.MarkedAllocation.of_administrative
    (ProtectedStateTransition.Lexical.legacyProtocol entry)
    (ProtectedStateTransition.Lexical.legacyTransport transport) stateBindings layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions)
  have actual := Stateful.preservesAt_match_with
    (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
    (program := program) (evidence := evidence) (faithful := faithful) (observations := observations)
    (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (conditionGate := fun _ _ => True)
    (producer := producer) (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport)
    (stateBindings := stateBindings) (acquire := fun _ _ _ => fun _ _ => True.intro)
    (validity := validity) (extend := extend) (runtimeOf := runtimeOf) (budget := budget)
    (meaningMost := fun context valid child within => ProtectedStateMatchBodyContracts.legacy_expression_preserves
      transport (meaningMost context valid child within))
    diagnosticPolicy unique tree errors
  cases position with
  | statements mode statements =>
    intro size bounded
    exact CatalogCompatibility.preserves functions program evidence (actual size bounded)
  | initializers items condition post statements =>
    obtain ⟨header, errors⟩ := actual
    exact ⟨header.mapContinuation (fun actual child within =>
      CatalogCompatibility.loop_preserves functions program evidence (actual child within)),
      errors.mapContinuation (fun actual child within =>
        CatalogCompatibility.loop_preserves functions program evidence (actual child within))⟩

include definitions registered extension transport bindings meaningMost faithful observations extend runtimeOf in
theorem preservesAt_for_with (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    PreservesAtWith (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact preservesAt_match_with (validity := validity) (extend := extend) (runtimeOf := runtimeOf) functions definitions registered extension program evidence transport bindings budget faithful observations meaningMost
    diagnosticPolicy unique (GenericImperativeMatch.Tree.of_for tree) (GenericImperativeMatch.Tree.CatalogSites.of_for errors)

include definitions registered extension transport bindings meaning faithful observations extend runtimeOf in
/-- A caller with only strictly smaller expression laws can use the same main
induction at each actual statement size. The empty header remains inclusive
inside that invocation. -/
theorem preserves_below_with (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  intro size smaller
  exact preservesAt_for_with (validity := validity) (extend := extend) (runtimeOf := runtimeOf) functions definitions registered extension program evidence transport bindings size faithful observations
    (fun context valid child within => meaning context valid child (Nat.lt_of_le_of_lt within smaller))
    diagnosticPolicy unique tree errors size (Nat.le_refl size)

end WithValidity

section Ordinary
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (budget : Nat)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry))
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry))

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

abbrev PreservingHeaderFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => RecursiveNamedForContracts.LoopPreservesAt functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev ReflectingHeaderFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => RecursiveNamedForContracts.LoopReflectsAt functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev PreservesAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => AtMost budget (fun size => RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => PreservingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => ReflectingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

include definitions registered extension transport bindings meaning faithful observations in
theorem header_preserves_at (size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : PreservingHeaderFor (diagnosticPolicy := .reachable) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    Control.HeadPreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) id expected type code := by
  apply header_preserves_at_with (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption


include extension meaning transport bindings definitions registered faithful observations in
theorem loop_preserves_at (size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Below budget (fun child => RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) child false statements expected type code)) :
    RecursiveNamedForContracts.LoopPreservesAt (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  apply loop_preserves_at_with (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption


variable (meaningMost : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
  AtMost budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
    (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source (certificates context) faults entry))

include definitions registered extension transport bindings meaningMost faithful observations in
theorem preservesAt_match (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    PreservesAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply preservesAt_match_with (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
    (runtimeOf := fun _ valid => CompatibleRuntimeContextValidity.of_ordinary valid)
  all_goals assumption


include definitions registered extension transport bindings meaningMost faithful observations in
theorem preservesAt_for (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    PreservesAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply preservesAt_for_with (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
    (runtimeOf := fun _ valid => CompatibleRuntimeContextValidity.of_ordinary valid)
  all_goals assumption


include definitions registered extension transport bindings meaning faithful observations in
/-- A caller with only strictly smaller expression laws can use the same main
induction at each actual statement size. The empty header remains inclusive
inside that invocation. -/
theorem preserves_below (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    Below budget (fun size => RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply preserves_below_with (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
    (runtimeOf := fun _ valid => CompatibleRuntimeContextValidity.of_ordinary valid)
  all_goals assumption

end Ordinary

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor
