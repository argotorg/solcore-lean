import Solcore.SourceSemantics.Graph
import Solcore.SourceSemantics.Static

/-!
# Occurrence subtrees

Only a returned subtree must keep its complete records, and rooted typing follows it.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceChildTransport
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend.SourceInference TypeSystem

/-- Every proper child occurrence keeps its complete substituted record.
The root may receive an output coercion while its children remain unchanged. -/
structure ProperDescendantsPreserved (substitution : Substitution)
    (before after : TypedSource) (root : NodeId) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes → Descends before root node.id →
    node.applySubstitution substitution ∈ after.nodes

/-- Actual proper descendants retain their original records before final
substitution. A later attachment may still replace the enclosing root. -/
structure RawProperDescendantsPreserved (before after : TypedSource) (root : NodeId) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes → Descends before root node.id → node ∈ after.nodes

namespace RawProperDescendantsPreserved

theorem ofTypingSourceExtends {before after : TypedSource} {root : NodeId}
    (extension : TypingSourceExtends before after) : RawProperDescendantsPreserved before after root :=
  ⟨extension.owner_eq, fun _ member _ => extension.nodes_prefix.subset member⟩

private theorem path_prefix {before after : TypedSource} {root child : NodeId}
    (extension : TypingSourceExtends before after) (path : Descends before root child) :
    Descends after root child := by
  induction path with
  | direct edge =>
    obtain ⟨parent, contains, edge⟩ := edge
    exact .direct ⟨parent, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, edge⟩
  | step edge _ next =>
    obtain ⟨parent, contains, edge⟩ := edge
    exact .step ⟨parent, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, edge⟩ next

theorem monoBefore {before middle after : TypedSource} {root : NodeId}
    (preserved : RawProperDescendantsPreserved middle after root)
    (extension : TypingSourceExtends before middle) : RawProperDescendantsPreserved before after root := by
  refine ⟨preserved.owner_eq.trans extension.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node (extension.nodes_prefix.subset member) (path_prefix extension path)

end RawProperDescendantsPreserved

namespace ProperDescendantsPreserved

theorem ofTypingSourceExtends
    {substitution : Substitution} {before after : TypedSource} {root : NodeId}
    (extension : TypingSourceExtends
      (before.applySubstitution substitution) after) :
    ProperDescendantsPreserved substitution before after root := by
  refine ⟨extension.owner_eq, ?_⟩
  intro node member _
  exact extension.nodes_prefix.subset (List.mem_map.mpr ⟨node, member, rfl⟩)

theorem child
    {substitution : Substitution} {before after : TypedSource}
    {root child : NodeId}
    (preserved : ProperDescendantsPreserved substitution before after root)
    (edge : DirectChild before root child) :
    ProperDescendantsPreserved substitution before after child := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node member (.step edge path)

theorem containsNode
    {substitution : Substitution} {before after : TypedSource}
    {root child : NodeId} {node : Node}
    (preserved : ProperDescendantsPreserved substitution before after root)
    (path : Descends before root child)
    (contains : ContainsNode before child node) :
    ContainsNode after child (node.applySubstitution substitution) := by
  refine ⟨preserved.nodes node contains.1 ?_, ?_⟩
  · simpa [contains.2] using path
  · simpa using contains.2

theorem transExtension
    {substitution : Substitution} {before middle after : TypedSource}
    {root : NodeId}
    (preserved : ProperDescendantsPreserved substitution before middle root)
    (extension : TypingSourceExtends middle after) :
    ProperDescendantsPreserved substitution before after root := by
  exact ⟨extension.owner_eq.trans preserved.owner_eq,
    fun node member path => extension.nodes_prefix.subset
      (preserved.nodes node member path)⟩

end ProperDescendantsPreserved

/-- A source transport is restricted to a set closed under actual source
edges. It contains no declarative typing assumption. -/
structure SourceSubgraphTransport (before after : TypedSource)
    (reached : NodeId → Prop) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes → reached node.id → node ∈ after.nodes
  children : ∀ node, node ∈ before.nodes → reached node.id →
    ∀ child, child ∈ node.references → reached child

namespace SourceSubgraphTransport

theorem containsExpression
    {before after : TypedSource} {reached : NodeId → Prop}
    {id : ExpressionId} {node : ExpressionNode}
    (transport : SourceSubgraphTransport before after reached)
    (contains : ContainsExpression before id node)
    (selected : reached (.expression id)) : ContainsExpression after id node := by
  exact ⟨transport.nodes (.expression node) contains.1
    (by simpa [Node.id, contains.2] using selected), contains.2⟩

theorem containsStatement
    {before after : TypedSource} {reached : NodeId → Prop}
    {id : StatementId} {node : StatementNode}
    (transport : SourceSubgraphTransport before after reached)
    (contains : ContainsStatement before id node)
    (selected : reached (.statement id)) : ContainsStatement after id node := by
  exact ⟨transport.nodes (.statement node) contains.1
    (by simpa [Node.id, contains.2] using selected), contains.2⟩

theorem expression_children
    {before after : TypedSource} {reached : NodeId → Prop}
    {id : ExpressionId} {node : ExpressionNode}
    (transport : SourceSubgraphTransport before after reached)
    (contains : ContainsExpression before id node)
    (selected : reached (.expression id)) :
    ∀ child ∈ node.form.references, reached child := by
  exact transport.children (.expression node) contains.1
    (by simpa [Node.id, contains.2] using selected)

theorem statement_children
    {before after : TypedSource} {reached : NodeId → Prop}
    {id : StatementId} {node : StatementNode}
    (transport : SourceSubgraphTransport before after reached)
    (contains : ContainsStatement before id node)
    (selected : reached (.statement id)) :
    ∀ child ∈ node.form.references, reached child := by
  exact transport.children (.statement node) contains.1
    (by simpa [Node.id, contains.2] using selected)

end SourceSubgraphTransport

theorem ProperDescendantsPreserved.subgraph
    {substitution : Substitution} {before after : TypedSource} {root : NodeId}
    (preserved : ProperDescendantsPreserved substitution before after root) :
    SourceSubgraphTransport (before.applySubstitution substitution) after
      (Descends before root) := by
  refine ⟨preserved.owner_eq, ?_, ?_⟩
  · intro node member path
    change node ∈ before.nodes.map (Node.applySubstitution substitution) at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact preserved.nodes original originalMember (by simpa using path)
  · intro node member path child edge
    have found : ContainsNode (before.applySubstitution substitution)
        node.id node := ⟨member, rfl⟩
    obtain ⟨original, contains, same⟩ :=
      FlexibleSubstitution.containsNode_of_applySubstitution found
    have originalEdge : DirectChild before node.id child :=
      ⟨original, contains, by simpa [nodeChildIds, ← same] using edge⟩
    exact path.trans (.direct originalEdge)

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRootedTyping
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend.SourceInference

namespace SourceSubgraphTransport

private theorem binder {before after : TypedSource} {reached : NodeId → Prop}
    (transport : SourceSubgraphTransport before after reached)
    {context final : Context} {binding : TypedBinder}
    (valid : BinderExtends before.owner context binding final) :
    BinderExtends after.owner context binding final := by
  rw [transport.owner_eq]
  exact valid

private theorem binders {before after : TypedSource} {reached : NodeId → Prop}
    (transport : SourceSubgraphTransport before after reached)
    {context final : Context} {bindings : List TypedBinder}
    (valid : BindersExtend before.owner context bindings final) :
    BindersExtend after.owner context bindings final := by
  rw [transport.owner_eq]
  exact valid

private theorem monoBinders {before after : TypedSource} {reached : NodeId → Prop}
    (transport : SourceSubgraphTransport before after reached)
    {context final : Context} {bindings : List TypedBinder} {types : List TypeSystem.Ty}
    (valid : MonoBindersExtend before.owner context bindings types final) :
    MonoBindersExtend after.owner context bindings types final := by
  rw [transport.owner_eq]
  exact valid

private theorem declarationCallee {before after : TypedSource}
    {reached : NodeId → Prop}
    (transport : SourceSubgraphTransport before after reached)
    {context : Context} {id : ExpressionId} {instantiation : DeclarationInstantiation}
    (valid : DirectDeclarationCalleeValid context before id instantiation)
    (live : reached (.expression id)) :
    DirectDeclarationCalleeValid context after id instantiation := by
  cases valid with
  | intro contains form valid type requirements coercions =>
    exact .intro (transport.containsExpression contains live) form valid type
      requirements coercions

private theorem builtinCallee {before after : TypedSource}
    {reached : NodeId → Prop}
    (transport : SourceSubgraphTransport before after reached)
    {id : ExpressionId} {function : Frontend.BuiltinFunctionId}
    (valid : DirectBuiltinCalleeValid before id function)
    (live : reached (.expression id)) :
    DirectBuiltinCalleeValid after id function := by
  cases valid with
  | intro contains form type requirements coercions =>
    exact .intro (transport.containsExpression contains live) form type
      requirements coercions

local macro "rooted_live" "(" refs:term ")" : tactic =>
  `(tactic| first
    | assumption
    | (apply $refs; simp_all [ExpressionForm.references, StatementForm.references,
            ForItemForm.references, PlaceResolution.references,
            AssignmentResolution.references, PlaceProjection.references,
            MatchResolution.references, TypedMatchCase.references,
            List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap,
            List.mem_singleton, forall_exists_index, and_imp,
            Option.toList_some, Option.toList_none, Option.getD_some, Option.getD_none])
    | (intro id member; apply $refs; simp_all [ExpressionForm.references, StatementForm.references,
            ForItemForm.references, PlaceResolution.references,
            AssignmentResolution.references, PlaceProjection.references,
            MatchResolution.references, TypedMatchCase.references,
            List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap,
            List.mem_singleton, forall_exists_index, and_imp,
            Option.toList_some, Option.toList_none, Option.getD_some, Option.getD_none]))

local macro "transport_rooted" "(" recursor:term "," before:term ","
    after:term "," reached:term "," transport:term "," typing:term ")" : term =>
  `($recursor (source := $before)
    (motive_1 := fun context id type _ =>
      $reached (.expression id) → ExpressionHasType $after context id type)
    (motive_2 := fun context form rawType plan _ =>
      (∀ child ∈ form.references, $reached child) →
        ExpressionFormHasRawType $after context form rawType plan)
    (motive_3 := fun context expressions types _ =>
      (∀ id ∈ expressions, $reached (.expression id)) →
        ExpressionsHaveTypes $after context expressions types)
    (motive_4 := fun context initial projections final _ =>
      (∀ child ∈ projections.flatMap PlaceProjection.references, $reached child) →
        SourceProjectionsHaveType $after context initial projections final)
    (motive_5 := fun context place type _ =>
      (∀ child ∈ place.references, $reached child) →
        SourcePlaceHasType $after context place type)
    (motive_6 := fun context assignment operator value _ =>
      (∀ child ∈ assignment.references ++ [.expression value], $reached child) →
        SourceAssignmentHasType $after context assignment operator value)
    (motive_7 := fun context assignment _ =>
      (∀ child ∈ assignment.references, $reached child) →
        SourceBitNotAssignmentValid $after context assignment)
    (motive_8 := fun control context id final facts _ =>
      $reached (.statement id) → StatementHasType $after control context id final facts)
    (motive_9 := fun control context statements final facts _ =>
      (∀ id ∈ statements, $reached (.statement id)) →
        StatementsHaveType $after control context statements final facts)
    (motive_10 := fun control context item final _ =>
      (∀ child ∈ item.references, $reached child) →
        ForItemHasType $after control context item final)
    (motive_11 := fun control context items final _ =>
      (∀ child ∈ items.flatMap ForItemForm.references, $reached child) →
        ForItemsHaveType $after control context items final)
    (motive_12 := fun control context scrutineeType matchCase facts _ =>
      (∀ child ∈ matchCase.references, $reached child) →
        MatchCaseHasType $after control context scrutineeType matchCase facts)
    (motive_13 := fun control context scrutineeType cases facts _ =>
      (∀ child ∈ cases.flatMap TypedMatchCase.references, $reached child) →
        MatchCasesHaveType $after control context scrutineeType cases facts)
    (fun contains formType rawTypeEq rawWellFormed typeWellFormed requirements ih live =>
      .intro (($transport).containsExpression contains live)
        (ih (($transport).expression_children contains live)) rawTypeEq
        rawWellFormed typeWellFormed requirements)
    (fun valid _ => .literal valid)
    (fun valid _ => .integerLiteral valid)
    (fun valid _ => .reference valid)
    (fun _ ih refs => .group (ih (by rooted_live(refs))))
    (fun _ ih refs => .tuple (ih (by rooted_live(refs))))
    (fun _ operator ih refs => .unary (ih (by rooted_live(refs))) operator)
    (fun _ _ operator left right refs => .binary (left (by rooted_live(refs))) (right (by rooted_live(refs))) operator)
    (fun _ _ _ condition left right refs => .conditional (condition (by rooted_live(refs))) (left (by rooted_live(refs))) (right (by rooted_live(refs))))
    (fun names parameters _ completes body refs => .lambda names (($transport).monoBinders parameters) (body (by rooted_live(refs))) completes)
    (fun callee application _ args refs => .directCall (($transport).declarationCallee callee (by rooted_live(refs))) application (args (by rooted_live(refs))))
    (fun callee _ args refs => .builtinCall (($transport).builtinCallee callee (by rooted_live(refs))) (args (by rooted_live(refs))))
    (fun _ _ application callee args refs => .indirectCall (callee (by rooted_live(refs))) (args (by rooted_live(refs))) application)
    (fun valid _ args refs => .constructor valid (args (by rooted_live(refs))))
    (fun _ member base refs => .member (base (by rooted_live(refs))) member)
    (fun valid _ => .proxy valid)
    (fun _ _ base key refs => .index (base (by rooted_live(refs))) (key (by rooted_live(refs))))
    (fun context _ => .nil context)
    (fun _ _ head tail refs => .cons (head (by rooted_live(refs))) (tail (by rooted_live(refs))))
    (fun type _ => .nil type)
    (fun _ _ key tail refs => .index (key (by rooted_live(refs))) (tail (by rooted_live(refs))))
    (fun selected _ tail refs => .member selected (tail (by rooted_live(refs))))
    (fun root _ same projections refs => .intro root (projections (by rooted_live(refs))) same)
    (fun _ _ requirements target value refs => .equal (target (by rooted_live(refs))) (value (by rooted_live(refs))) requirements)
    (fun operator _ _ requirements target value refs => .wordCompound operator (target (by rooted_live(refs))) (value (by rooted_live(refs))) requirements)
    (fun _ requirements target refs => .intro (target (by rooted_live(refs))) requirements)
    (fun contains form mono generalizes binding type live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .letUninitialized (($transport).containsStatement contains live) form mono generalizes (($transport).binder binding) type)
    (fun contains form _ mono generalizes binding type initializer live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .letInitialized (($transport).containsStatement contains live) form (initializer (by rooted_live(refs))) mono generalizes (($transport).binder binding) type)
    (fun contains form poly requirements generalizes _ binding type initializer live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .letInitializedGeneralized (($transport).containsStatement contains live) form poly requirements generalizes (initializer (by rooted_live(refs))) (($transport).binder binding) type)
    (fun contains form result type live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .returnUnit (($transport).containsStatement contains live) form result type)
    (fun contains form _ type value live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .returnValue (($transport).containsStatement contains live) form (value (by rooted_live(refs))) type)
    (fun contains form _ type value live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .expressionValue (($transport).containsStatement contains live) form (value (by rooted_live(refs))) type)
    (fun contains form _ type value live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .expressionDiscard (($transport).containsStatement contains live) form (value (by rooted_live(refs))) type)
    (fun contains form _ type assignment live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .assignValue (($transport).containsStatement contains live) form (assignment (by rooted_live(refs))) type)
    (fun contains form _ type assignment live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .assignBitNot (($transport).containsStatement contains live) form (assignment (by rooted_live(refs))) type)
    (fun contains form _ _ type condition body live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .ifWithoutElse (($transport).containsStatement contains live) form (condition (by rooted_live(refs))) (body (by rooted_live(refs))) type)
    (fun contains form _ _ _ type condition left right live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .ifWithElse (($transport).containsStatement contains live) form (condition (by rooted_live(refs))) (left (by rooted_live(refs))) (right (by rooted_live(refs))) type)
    (fun contains form _ type body live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .block (($transport).containsStatement contains live) form (body (by rooted_live(refs))) type)
    (fun contains form default _ _ requirements exhaustive merged type scrutinee cases live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .matchWithoutDefault (($transport).containsStatement contains live) form default (scrutinee (by rooted_live(refs))) (cases (by rooted_live(refs))) requirements exhaustive merged type)
    (fun contains form default _ _ _ requirements merged type scrutinee cases body live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .matchWithDefault (($transport).containsStatement contains live) form default (scrutinee (by rooted_live(refs))) (cases (by rooted_live(refs))) (body (by rooted_live(refs))) requirements merged type)
    (fun contains form _ _ _ _ type initializer condition body post live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .forLoop (($transport).containsStatement contains live) form (initializer (by rooted_live(refs))) (condition (by rooted_live(refs))) (body (by rooted_live(refs))) (post (by rooted_live(refs))) type)
    (fun contains form _ _ type condition body live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .whileLoop (($transport).containsStatement contains live) form (condition (by rooted_live(refs))) (body (by rooted_live(refs))) type)
    (fun contains form allowed type live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .breakStmt (($transport).containsStatement contains live) form allowed type)
    (fun contains form allowed type live => by
      have refs := ($transport).statement_children contains live
      rw [form] at refs
      exact .continueStmt (($transport).containsStatement contains live) form allowed type)
    (fun control context _ => .nil control context)
    (fun _ head refs => .singleton (head (by rooted_live(refs))))
    (fun _ _ head tail refs => .cons (head (by rooted_live(refs))) (tail (by rooted_live(refs))))
    (fun mono generalizes binding _ => .letUninitialized mono generalizes (($transport).binder binding))
    (fun _ mono generalizes binding initializer refs => .letInitialized (initializer (by rooted_live(refs))) mono generalizes (($transport).binder binding))
    (fun poly requirements generalizes _ binding initializer refs => .letInitializedGeneralized poly requirements generalizes (initializer (by rooted_live(refs))) (($transport).binder binding))
    (fun _ value refs => .expression (value (by rooted_live(refs))))
    (fun _ assignment refs => .assignValue (assignment (by rooted_live(refs))))
    (fun _ assignment refs => .assignBitNot (assignment (by rooted_live(refs))))
    (fun control context _ => .nil control context)
    (fun _ _ head tail refs => .cons (head (by rooted_live(refs))) (tail (by rooted_live(refs))))
    (fun pattern bindings _ body refs => .intro pattern (($transport).binders bindings) (body (by rooted_live(refs))))
    (fun control context type _ => .nil control context type)
    (fun _ _ head tail refs => .cons (head (by rooted_live(refs))) (tail (by rooted_live(refs))))
    $typing)

theorem expression
    {before after : TypedSource} {reached : NodeId → Prop}
    (transport : SourceSubgraphTransport before after reached)
    {context : Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (typing : ExpressionHasType before context id type)
    (live : reached (.expression id)) :
    ExpressionHasType after context id type :=
  transport_rooted(ExpressionHasType.rec, before, after, reached, transport, typing) live

theorem form
    {before after : TypedSource} {reached : NodeId → Prop}
    (transport : SourceSubgraphTransport before after reached)
    {context : Context} {form : ExpressionForm} {type : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (typing : ExpressionFormHasRawType before context form type plan)
    (live : ∀ child ∈ form.references, reached child) :
    ExpressionFormHasRawType after context form type plan :=
  transport_rooted(ExpressionFormHasRawType.rec, before, after, reached, transport, typing) live

theorem statement
    {before after : TypedSource} {reached : NodeId → Prop}
    (transport : SourceSubgraphTransport before after reached)
    {control : ControlContext} {context final : Context} {id : StatementId} {facts : StatementFacts}
    (typing : StatementHasType before control context id final facts)
    (live : reached (.statement id)) :
    StatementHasType after control context id final facts :=
  transport_rooted(StatementHasType.rec, before, after, reached, transport, typing) live

theorem statements
    {before after : TypedSource} {reached : NodeId → Prop}
    (transport : SourceSubgraphTransport before after reached)
    {control : ControlContext} {context final : Context} {ids : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType before control context ids final facts)
    (live : ∀ id ∈ ids, reached (.statement id)) :
    StatementsHaveType after control context ids final facts :=
  transport_rooted(StatementsHaveType.rec, before, after, reached, transport, typing) live

end SourceSubgraphTransport

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSubtreeTransport
/-! Only the returned occurrence subtree must retain its complete records.
Unrelated earlier roots may change during enclosing coercion attachment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend.SourceInference TypeSystem

structure SubtreePreserved (substitution : Substitution)
    (before after : TypedSource) (root : NodeId) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes →
    (node.id = root ∨ Descends before root node.id) →
    node.applySubstitution substitution ∈ after.nodes

namespace SubtreePreserved
variable {substitution : Substitution} {before middle after : TypedSource}
  {root childId : NodeId}

theorem ofTypingSourceExtends
    (extension : TypingSourceExtends (before.applySubstitution substitution) after) :
    SubtreePreserved substitution before after root := by
  refine ⟨extension.owner_eq, ?_⟩
  intro node member _
  exact extension.nodes_prefix.subset (List.mem_map.mpr ⟨node, member, rfl⟩)

theorem proper (preserved : SubtreePreserved substitution before after root) :
    ProperDescendantsPreserved substitution before after root :=
  ⟨preserved.owner_eq, fun node member path => preserved.nodes node member (.inr path)⟩

theorem child (preserved : SubtreePreserved substitution before after root)
    (edge : DirectChild before root childId) :
    SubtreePreserved substitution before after childId := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  apply preserved.nodes node member
  rcases path with same | path
  · exact .inr (same ▸ Descends.direct edge)
  · exact .inr (.step edge path)

theorem transExtension (preserved : SubtreePreserved substitution before middle root)
    (extension : TypingSourceExtends middle after) :
    SubtreePreserved substitution before after root :=
  ⟨extension.owner_eq.trans preserved.owner_eq,
    fun node member path => extension.nodes_prefix.subset (preserved.nodes node member path)⟩

private theorem path_prefix (extension : TypingSourceExtends before middle)
    (path : Descends before root childId) : Descends middle root childId := by
  induction path with
  | direct edge =>
      rcases edge with ⟨node, contains, member⟩
      exact .direct ⟨node, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, member⟩
  | step edge _ next =>
      rcases edge with ⟨node, contains, member⟩
      exact .step ⟨node, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, member⟩ next

theorem monoBefore (preserved : SubtreePreserved substitution middle after root)
    (extension : TypingSourceExtends before middle) :
    SubtreePreserved substitution before after root := by
  refine ⟨preserved.owner_eq.trans extension.owner_eq, ?_⟩
  intro node member path
  apply preserved.nodes node (extension.nodes_prefix.subset member)
  exact path.elim Or.inl (fun path => .inr (path_prefix extension path))

theorem subgraph (preserved : SubtreePreserved substitution before after root) :
    SourceSubgraphTransport (before.applySubstitution substitution) after
      (fun id => id = root ∨ Descends before root id) := by
  refine ⟨preserved.owner_eq, ?_, ?_⟩
  · intro node member path
    change node ∈ before.nodes.map (Node.applySubstitution substitution) at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact preserved.nodes original originalMember (by simpa using path)
  · intro node member path child edge
    have found : ContainsNode (before.applySubstitution substitution) node.id node := ⟨member, rfl⟩
    obtain ⟨original, contains, same⟩ :=
      FlexibleSubstitution.containsNode_of_applySubstitution found
    have originalEdge : DirectChild before node.id child :=
      ⟨original, contains, by simpa [nodeChildIds, ← same] using edge⟩
    exact .inr (path.elim (fun same => same ▸ Descends.direct originalEdge)
      (fun path => path.trans (.direct originalEdge)))

end SubtreePreserved
/-- The exact unmodified records used by the actual finalization state. -/
structure RawSubtreePreserved (before after : TypedSource) (root : NodeId) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes →
    (node.id = root ∨ Descends before root node.id) → node ∈ after.nodes

theorem RawProperDescendantsPreserved.childSubtree
    {before after : TypedSource} {root child : NodeId}
    (preserved : RawProperDescendantsPreserved before after root)
    (edge : DirectChild before root child) : RawSubtreePreserved before after child := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node member
    (path.elim (fun same => same ▸ Descends.direct edge) (fun path => .step edge path))

namespace RawSubtreePreserved
variable {before middle after : TypedSource} {root childId : NodeId}

theorem proper (preserved : RawSubtreePreserved before after root) :
    RawProperDescendantsPreserved before after root :=
  ⟨preserved.owner_eq, fun node member path => preserved.nodes node member (.inr path)⟩

theorem ofTypingSourceExtends (extension : TypingSourceExtends before after) :
    RawSubtreePreserved before after root :=
  ⟨extension.owner_eq, fun _ member _ => extension.nodes_prefix.subset member⟩

theorem monoBefore (preserved : RawSubtreePreserved middle after root)
    (extension : TypingSourceExtends before middle) :
    RawSubtreePreserved before after root := by
  refine ⟨preserved.owner_eq.trans extension.owner_eq, ?_⟩
  intro node member path
  apply preserved.nodes node (extension.nodes_prefix.subset member)
  exact path.elim Or.inl (fun path => .inr (SubtreePreserved.path_prefix extension path))

theorem child (preserved : RawSubtreePreserved before after root)
    (edge : DirectChild before root childId) : RawSubtreePreserved before after childId := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  apply preserved.nodes node member
  exact .inr (path.elim (fun same => same ▸ Descends.direct edge) (fun path => .step edge path))

theorem substituted (preserved : RawSubtreePreserved before after root)
    (substitution : Substitution) :
    SubtreePreserved substitution before (after.applySubstitution substitution) root := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  exact List.mem_map.mpr ⟨node, preserved.nodes node member path, rfl⟩

end RawSubtreePreserved
end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSubtreeInverseClosure
/-! A closed earlier subtree cannot acquire descendants when its complete
records are preserved in a later source with unique occurrence identities. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness.RawSubtreePreserved
open Frontend.SourceInference

private theorem node_unique {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {left right : Node} (leftMember : left ∈ source.nodes)
    (rightMember : right ∈ source.nodes) (same : left.id = right.id) :
    left = right := by
  have occurrence : left.occurrenceId = right.occurrenceId :=
    congrArg NodeId.occurrenceId same
  have leftLookup := lookupNode?_complete unique leftMember occurrence
  have rightLookup := lookupNode?_complete unique rightMember rfl
  exact Option.some.inj (leftLookup.symm.trans rightLookup)

private theorem direct_inverse {before after : TypedSource} {root child : NodeId}
    (preserved : RawSubtreePreserved before after root)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after) (edge : DirectChild after root child) :
    DirectChild before root child ∧ child ∈ nodeIds before := by
  obtain ⟨original, member, id⟩ := List.mem_map.mp present
  obtain ⟨later, contains, reference⟩ := edge
  have retained := preserved.nodes original member (.inl id)
  have same : original = later :=
    node_unique unique retained contains.1 (id.trans contains.2.symm)
  subst later
  exact ⟨⟨original, ⟨member, id⟩, reference⟩, closed original member child reference⟩

/-- Every later path from the preserved root was already an earlier path. -/
theorem descends_inverse {before after : TypedSource} {root child : NodeId}
    (preserved : RawSubtreePreserved before after root)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after) (path : Descends after root child) :
    Descends before root child ∧ child ∈ nodeIds before := by
  induction path with
  | direct edge =>
      have earlier := direct_inverse preserved closed present unique edge
      exact ⟨.direct earlier.1, earlier.2⟩
  | step edge tail ih =>
      have earlier := direct_inverse preserved closed present unique edge
      have rest := ih (preserved.child earlier.1) earlier.2
      exact ⟨.step earlier.1 rest.1, rest.2⟩

/-- The same inclusion holds for the root together with all its descendants. -/
theorem reflexive_inverse {before after : TypedSource} {root child : NodeId}
    (preserved : RawSubtreePreserved before after root)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after)
    (path : child = root ∨ Descends after root child) :
    (child = root ∨ Descends before root child) ∧ child ∈ nodeIds before := by
  rcases path with same | path
  · exact ⟨.inl same, same ▸ present⟩
  · have earlier := preserved.descends_inverse closed present unique path
    exact ⟨.inr earlier.1, earlier.2⟩

/-- Recover the complete earlier record, including its local reference target. -/
theorem node_inverse {before after : TypedSource} {root : NodeId}
    (preserved : RawSubtreePreserved before after root)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after) {node : Node} (member : node ∈ after.nodes)
    (path : node.id = root ∨ Descends after root node.id) :
    node ∈ before.nodes := by
  have earlier := preserved.reflexive_inverse closed present unique path
  obtain ⟨original, originalMember, id⟩ := List.mem_map.mp earlier.2
  have originalPath : original.id = root ∨ Descends before root original.id := by
    simpa only [id] using earlier.1
  have retained := preserved.nodes original originalMember originalPath
  have same := node_unique unique retained member id
  exact same ▸ originalMember

end Solcore.SourceSemantics.SourceInferenceSoundness.RawSubtreePreserved
end
