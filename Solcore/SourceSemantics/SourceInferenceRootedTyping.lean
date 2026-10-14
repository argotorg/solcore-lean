import Solcore.SourceSemantics.SourceInferenceChildTransport

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
