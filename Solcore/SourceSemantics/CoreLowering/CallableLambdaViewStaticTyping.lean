import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability

/-! All thirteen independent source typing judgments transport along exact
reached nodes of a local compiler view. Recursion follows finite typing
proofs, including lambda bodies, calls, places, loops and match arms.
The source graph may contain cycles. Compiler acceptance, static lowering
trees and runtime history remain separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewStaticTyping
open Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

/-- Every occurrence referenced by a typing judgment is in the retained
reference closure. The order and repeated references remain unchanged. -/
def Within (source : TypedSource) (roots ids : List NodeId) : Prop :=
  ∀ id ∈ ids, Reaches source roots id

@[simp] private theorem within_nil (source : TypedSource) (roots : List NodeId) :
    Within source roots [] := by intro id member; cases member
@[simp] private theorem within_cons {source : TypedSource} {roots : List NodeId}
    {id : NodeId} {ids : List NodeId} :
    Within source roots (id :: ids) ↔ Reaches source roots id ∧ Within source roots ids := by
  constructor
  · intro all; exact ⟨all id (by simp), fun child member => all child (by simp [member])⟩
  · rintro ⟨head, tail⟩ child member
    rcases List.mem_cons.mp member with same | member
    · subst child; exact head
    · exact tail child member
@[simp] private theorem within_append {source : TypedSource} {roots first second : List NodeId} :
    Within source roots (first ++ second) ↔ Within source roots first ∧ Within source roots second := by
  simp only [Within, List.mem_append, or_imp, forall_and]
@[simp] private theorem within_flatMap_cons {α : Type} {source : TypedSource} {roots : List NodeId}
    {f : α → List NodeId} {head : α} {tail : List α} :
    Within source roots ((head :: tail).flatMap f) ↔
      Within source roots (f head) ∧ Within source roots (tail.flatMap f) := by
  simp only [List.flatMap_cons, within_append]

theorem Within.view {source view : TypedSource} {roots ids : List NodeId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (within : Within source roots ids) : Within view roots ids :=
  fun id member => (within id member).metadata metadata

private theorem expression_contains {source view : TypedSource} {roots : List NodeId}
    {changed : List ExpressionId} (edited : LocalView source view changed)
    (avoids : Avoids source roots changed) (unique : NodeOccurrencesUnique source)
    {id : ExpressionId} {node : ExpressionNode} (reached : Reaches source roots (.expression id))
    (contains : ContainsExpression source id node) : ContainsExpression view id node :=
  lookupExpression?_sound ((expression_lookup edited avoids reached).symm.trans
    (lookupExpression?_complete unique contains))

private theorem statement_contains {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) (unique : NodeOccurrencesUnique source)
    {id : StatementId} {node : StatementNode} (contains : ContainsStatement source id node) :
    ContainsStatement view id node :=
  lookupStatement?_sound (edited.metadata.symm.statement (lookupStatement?_complete unique contains))

private theorem expression_children {source : TypedSource} {roots : List NodeId}
    (unique : NodeOccurrencesUnique source) {id : ExpressionId} {node : ExpressionNode}
    (contains : ContainsExpression source id node) (reached : Reaches source roots (.expression id)) :
    Within source roots node.form.references :=
  fun _ member => .expression reached (lookupExpression?_complete unique contains) member

private theorem statement_children {source : TypedSource} {roots : List NodeId}
    (unique : NodeOccurrencesUnique source) {id : StatementId} {node : StatementNode} {form : StatementForm}
    (contains : ContainsStatement source id node) (same : node.form = form)
    (reached : Reaches source roots (.statement id)) : Within source roots form.references := by
  intro child member
  exact .statement reached (lookupStatement?_complete unique contains) (same ▸ member)

private theorem binder {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) {context final : Context} {item : TypedBinder}
    (extended : BinderExtends source.owner context item final) : BinderExtends view.owner context item final := by
  rw [← edited.metadata.owner]; exact extended
private theorem binders {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) {context final : Context} {items : List TypedBinder}
    (extended : BindersExtend source.owner context items final) : BindersExtend view.owner context items final := by
  rw [← edited.metadata.owner]; exact extended
private theorem monoBinders {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) {context final : Context} {items : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend source.owner context items types final) :
    MonoBindersExtend view.owner context items types final := by
  rw [← edited.metadata.owner]; exact extended

private theorem declaration_callee {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed) (unique : NodeOccurrencesUnique source)
    {context : Context} {id : ExpressionId} {instantiation : DeclarationInstantiation}
    (reached : Reaches source roots (.expression id))
    (typed : DirectDeclarationCalleeValid context source id instantiation) :
    DirectDeclarationCalleeValid context view id instantiation := by
  cases typed with
  | intro contains form valid raw requirements coercions =>
    exact .intro (expression_contains edited avoids unique reached contains) form valid raw requirements coercions

private theorem builtin_callee {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed) (unique : NodeOccurrencesUnique source)
    {id : ExpressionId} {function : BuiltinFunctionId} (reached : Reaches source roots (.expression id))
    (typed : DirectBuiltinCalleeValid source id function) : DirectBuiltinCalleeValid view id function := by
  cases typed with
  | intro contains form raw requirements coercions =>
    exact .intro (expression_contains edited avoids unique reached contains) form raw requirements coercions

section Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

local macro "transport_static" "(" recursor:term "," before:term "," after:term ","
    roots:term "," edited:term "," avoids:term "," unique:term "," typing:term ")" : term =>
  `($recursor (source := $before)
    (motive_1 := fun context id type _ => Reaches $before $roots (.expression id) → ExpressionHasType $after context id type)
    (motive_2 := fun context form raw plan _ => Within $before $roots form.references → ExpressionFormHasRawType $after context form raw plan)
    (motive_3 := fun context ids types _ => Within $before $roots (ids.map NodeId.expression) → ExpressionsHaveTypes $after context ids types)
    (motive_4 := fun context initial projections final _ => Within $before $roots (projections.flatMap PlaceProjection.references) → SourceProjectionsHaveType $after context initial projections final)
    (motive_5 := fun context place type _ => Within $before $roots place.references → SourcePlaceHasType $after context place type)
    (motive_6 := fun context assignment operator value _ => Within $before $roots (assignment.references ++ [.expression value]) → SourceAssignmentHasType $after context assignment operator value)
    (motive_7 := fun context assignment _ => Within $before $roots assignment.references → SourceBitNotAssignmentValid $after context assignment)
    (motive_8 := fun control context id final facts _ => Reaches $before $roots (.statement id) → StatementHasType $after control context id final facts)
    (motive_9 := fun control context ids final facts _ => Within $before $roots (ids.map NodeId.statement) → StatementsHaveType $after control context ids final facts)
    (motive_10 := fun control context item final _ => Within $before $roots item.references → ForItemHasType $after control context item final)
    (motive_11 := fun control context items final _ => Within $before $roots (items.flatMap ForItemForm.references) → ForItemsHaveType $after control context items final)
    (motive_12 := fun control context type arm facts _ => Within $before $roots arm.references → MatchCaseHasType $after control context type arm facts)
    (motive_13 := fun control context type arms facts _ => Within $before $roots (arms.flatMap TypedMatchCase.references) → MatchCasesHaveType $after control context type arms facts)
    (fun contains _ raw wfRaw wfType requirements ih reached =>
      .intro (expression_contains $edited $avoids $unique reached contains)
        (ih (expression_children $unique contains reached)) raw wfRaw wfType requirements)
    (fun valid _ => .literal valid)
    (fun valid _ => .integerLiteral valid)
    (fun valid _ => .reference valid)
    (fun _ ih h => .group (ih (by simpa [ExpressionForm.references] using h)))
    (fun _ ih h => .tuple (ih h))
    (fun _ operator ih h => .unary (ih (by simpa [ExpressionForm.references] using h)) operator)
    (fun _ _ operator left right h => by
      simp only [ExpressionForm.references, within_cons, within_nil, and_true] at h
      exact .binary (left h.1) (right h.2) operator)
    (fun _ _ _ condition first second h => by
      simp only [ExpressionForm.references, within_cons, within_nil, and_true] at h
      exact .conditional (condition h.1) (first h.2.1) (second h.2.2))
    (fun names extended _ completes ih h => .lambda names (monoBinders $edited extended) (ih h) completes)
    (fun callee application _ ih h => by
      simp only [ExpressionForm.references, within_cons] at h
      exact .directCall (declaration_callee $edited $avoids $unique h.1 callee) application (ih h.2))
    (fun callee _ ih h => by
      simp only [ExpressionForm.references, within_cons] at h
      exact .builtinCall (builtin_callee $edited $avoids $unique h.1 callee) (ih h.2))
    (fun _ _ application callee arguments h => by
      simp only [ExpressionForm.references, within_cons] at h
      exact .indirectCall (callee h.1) (arguments h.2) application)
    (fun valid _ ih h => .constructor valid (ih h))
    (fun _ selected ih h => .member (ih (by simpa [ExpressionForm.references] using h)) selected)
    (fun valid _ => .proxy valid)
    (fun _ _ first second h => by
      simp only [ExpressionForm.references, within_cons, within_nil, and_true] at h
      exact .index (first h.1) (second h.2))
    (fun _ _ => .nil _)
    (fun _ _ head tail h => by
      simp only [List.map_cons, within_cons] at h
      exact .cons (head h.1) (tail (by simpa only [List.map_cons, within_cons] using h.2)))
    (fun type _ => .nil type)
    (fun _ _ key rest h => by
      simp only [within_flatMap_cons, PlaceProjection.references, within_cons, within_nil, and_true] at h
      exact .index (key h.1) (rest h.2))
    (fun selected _ ih h => by
      simp only [within_flatMap_cons, PlaceProjection.references, within_nil, true_and] at h
      exact .member selected (ih h))
    (fun root _ same ih h => .intro root (ih h) same)
    (fun _ _ requirements target value h => by
      simp only [within_append, within_cons, within_nil, and_true] at h
      exact .equal (target h.1) (value h.2) requirements)
    (fun operator _ _ requirements target value h => by
      simp only [within_append, within_cons, within_nil, and_true] at h
      exact .wordCompound operator (target h.1) (value h.2) requirements)
    (fun _ requirements ih h => .intro (ih h) requirements)
    (fun contains form mono generalizes extended type _ =>
      .letUninitialized (statement_contains $edited $unique contains) form mono generalizes (binder $edited extended) type)
    (fun contains form _ mono generalizes extended type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, Option.map_some, Option.toList_some, within_cons, within_nil, and_true] at reached
      exact .letInitialized (statement_contains $edited $unique contains) form (ih reached) mono generalizes (binder $edited extended) type)
    (fun contains form poly wellFormed generalizes _ extended type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, Option.map_some, Option.toList_some, within_cons, within_nil, and_true] at reached
      exact .letInitializedGeneralized (statement_contains $edited $unique contains) form poly wellFormed generalizes (ih reached) (binder $edited extended) type)
    (fun contains form raw type _ => .returnUnit (statement_contains $edited $unique contains) form raw type)
    (fun contains form _ type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, Option.map_some, Option.toList_some, within_cons, within_nil, and_true] at reached
      exact .returnValue (statement_contains $edited $unique contains) form (ih reached) type)
    (fun contains form _ type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_cons, within_nil, and_true] at reached
      exact .expressionValue (statement_contains $edited $unique contains) form (ih reached) type)
    (fun contains form _ type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_cons, within_nil, and_true] at reached
      exact .expressionDiscard (statement_contains $edited $unique contains) form (ih reached) type)
    (fun contains form _ type ih h =>
      .assignValue (statement_contains $edited $unique contains) form (ih (statement_children $unique contains form h)) type)
    (fun contains form _ type ih h =>
      .assignBitNot (statement_contains $edited $unique contains) form (ih (statement_children $unique contains form h)) type)
    (fun contains form _ _ type condition first h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_append, within_cons, within_nil, and_true] at reached
      exact .ifWithoutElse (statement_contains $edited $unique contains) form (condition reached.1.1) (first reached.1.2) type)
    (fun contains form _ _ _ type condition first second h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, Option.getD_some, within_append, within_cons, within_nil, and_true] at reached
      exact .ifWithElse (statement_contains $edited $unique contains) form (condition reached.1.1) (first reached.1.2) (second reached.2) type)
    (fun contains form _ type ih h =>
      .block (statement_contains $edited $unique contains) form (ih (statement_children $unique contains form h)) type)
    (fun contains form default _ _ requirements exhaustive merged type scrutinee arms h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, MatchResolution.references, within_append, within_cons, within_nil, and_true] at reached
      exact .matchWithoutDefault (statement_contains $edited $unique contains) form default (scrutinee reached.1.1) (arms reached.1.2) requirements exhaustive merged type)
    (fun contains form default _ _ _ requirements merged type scrutinee arms fallback h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, MatchResolution.references, default, Option.getD_some, within_append, within_cons, within_nil, and_true] at reached
      exact .matchWithDefault (statement_contains $edited $unique contains) form default (scrutinee reached.1.1) (arms reached.1.2) (fallback reached.2) requirements merged type)
    (fun contains form _ _ _ _ type initial condition body post h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_append, within_cons, within_nil, and_true] at reached
      exact .forLoop (statement_contains $edited $unique contains) form (initial reached.1.1.1) (condition reached.1.1.2) (body reached.2) (post reached.1.2) type)
    (fun contains form _ _ type condition body h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_cons] at reached
      exact .whileLoop (statement_contains $edited $unique contains) form (condition reached.1) (body reached.2) type)
    (fun contains form allowed type _ => .breakStmt (statement_contains $edited $unique contains) form allowed type)
    (fun contains form allowed type _ => .continueStmt (statement_contains $edited $unique contains) form allowed type)
    (fun _ _ _ => .nil _ _)
    (fun _ ih h => .singleton (ih (by simpa using h)))
    (fun _ _ head tail h => by
      simp only [List.map_cons, within_cons] at h
      exact .cons (head h.1) (tail (by simpa only [List.map_cons, within_cons] using h.2)))
    (fun mono generalizes extended _ => .letUninitialized mono generalizes (binder $edited extended))
    (fun _ mono generalizes extended ih h =>
      .letInitialized (ih (by simpa [ForItemForm.references] using h)) mono generalizes (binder $edited extended))
    (fun poly wellFormed generalizes _ extended ih h =>
      .letInitializedGeneralized poly wellFormed generalizes (ih (by simpa [ForItemForm.references] using h)) (binder $edited extended))
    (fun _ ih h => .expression (ih (by simpa [ForItemForm.references] using h)))
    (fun _ ih h => .assignValue (ih h))
    (fun _ ih h => .assignBitNot (ih h))
    (fun _ _ _ => .nil _ _)
    (fun _ _ head tail h => by
      simp only [within_flatMap_cons] at h
      exact .cons (head h.1) (tail h.2))
    (fun pattern extended _ ih h => .intro pattern (binders $edited extended) (ih h))
    (fun _ _ _ _ => .nil _ _ _)
    (fun _ _ head tail h => by
      simp only [within_flatMap_cons] at h
      exact .cons (head h.1) (tail h.2))
    $typing)

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  (unique : NodeOccurrencesUnique source)

include edited avoids unique in
theorem expression {context : Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (typed : ExpressionHasType source context id type) (reached : Reaches source roots (.expression id)) :
    ExpressionHasType view context id type :=
  transport_static(ExpressionHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem form {context : Context} {form : ExpressionForm} {type : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (typed : ExpressionFormHasRawType source context form type plan) (reached : Within source roots form.references) :
    ExpressionFormHasRawType view context form type plan :=
  transport_static(ExpressionFormHasRawType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem expressions {context : Context} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source context ids types) (reached : Within source roots (ids.map NodeId.expression)) :
    ExpressionsHaveTypes view context ids types :=
  transport_static(ExpressionsHaveTypes.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem projections {context : Context} {initial final : TypeSystem.Ty} {projections : List PlaceProjection}
    (typed : SourceProjectionsHaveType source context initial projections final) (reached : Within source roots (projections.flatMap PlaceProjection.references)) :
    SourceProjectionsHaveType view context initial projections final :=
  transport_static(SourceProjectionsHaveType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem place {context : Context} {place : PlaceResolution} {type : TypeSystem.Ty}
    (typed : SourcePlaceHasType source context place type) (reached : Within source roots place.references) :
    SourcePlaceHasType view context place type :=
  transport_static(SourcePlaceHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem assignment {context : Context} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {value : ExpressionId}
    (typed : SourceAssignmentHasType source context assignment operator value) (reached : Within source roots (assignment.references ++ [.expression value])) :
    SourceAssignmentHasType view context assignment operator value :=
  transport_static(SourceAssignmentHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem bitNot {context : Context} {assignment : AssignmentResolution}
    (typed : SourceBitNotAssignmentValid source context assignment) (reached : Within source roots assignment.references) :
    SourceBitNotAssignmentValid view context assignment :=
  transport_static(SourceBitNotAssignmentValid.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem statement {control : ControlContext} {context final : Context} {id : StatementId} {facts : StatementFacts}
    (typed : StatementHasType source control context id final facts) (reached : Reaches source roots (.statement id)) :
    StatementHasType view control context id final facts :=
  transport_static(StatementHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem statements {control : ControlContext} {context final : Context} {ids : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context ids final facts) (reached : Within source roots (ids.map NodeId.statement)) :
    StatementsHaveType view control context ids final facts :=
  transport_static(StatementsHaveType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem forItem {control : ControlContext} {context final : Context} {item : ForItemForm}
    (typed : ForItemHasType source control context item final) (reached : Within source roots item.references) :
    ForItemHasType view control context item final :=
  transport_static(ForItemHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem forItems {control : ControlContext} {context final : Context} {items : List ForItemForm}
    (typed : ForItemsHaveType source control context items final) (reached : Within source roots (items.flatMap ForItemForm.references)) :
    ForItemsHaveType view control context items final :=
  transport_static(ForItemsHaveType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem matchCase {control : ControlContext} {context : Context} {type : TypeSystem.Ty} {arm : TypedMatchCase} {facts : BodyFacts}
    (typed : MatchCaseHasType source control context type arm facts) (reached : Within source roots arm.references) :
    MatchCaseHasType view control context type arm facts :=
  transport_static(MatchCaseHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem matchCases {control : ControlContext} {context : Context} {type : TypeSystem.Ty} {arms : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type arms facts) (reached : Within source roots (arms.flatMap TypedMatchCase.references)) :
    MatchCasesHaveType view control context type arms facts :=
  transport_static(MatchCasesHaveType.rec, source, view, roots, edited, avoids, unique, typed) reached

/-- The reverse transport uses the same canonical exclusion of edits.
The metadata receipt carries occurrence uniqueness and graph paths to the view. -/
private theorem reverse_view {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) : LocalView view source changed :=
  ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩

include edited avoids unique in
theorem expression_original {context : Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (typed : ExpressionHasType view context id type) (reached : Reaches source roots (.expression id)) :
    ExpressionHasType source context id type :=
  expression (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.metadata edited.metadata)

include edited avoids unique in
theorem form_original {context : Context} {form : ExpressionForm} {type : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (typed : ExpressionFormHasRawType view context form type plan) (reached : Within source roots form.references) :
    ExpressionFormHasRawType source context form type plan :=
  CallableLambdaViewStaticTyping.form (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem expressions_original {context : Context} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes view context ids types) (reached : Within source roots (ids.map NodeId.expression)) :
    ExpressionsHaveTypes source context ids types :=
  expressions (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem projections_original {context : Context} {initial final : TypeSystem.Ty} {projections : List PlaceProjection}
    (typed : SourceProjectionsHaveType view context initial projections final) (reached : Within source roots (projections.flatMap PlaceProjection.references)) :
    SourceProjectionsHaveType source context initial projections final :=
  CallableLambdaViewStaticTyping.projections (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem place_original {context : Context} {place : PlaceResolution} {type : TypeSystem.Ty}
    (typed : SourcePlaceHasType view context place type) (reached : Within source roots place.references) :
    SourcePlaceHasType source context place type :=
  CallableLambdaViewStaticTyping.place (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem assignment_original {context : Context} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {value : ExpressionId}
    (typed : SourceAssignmentHasType view context assignment operator value) (reached : Within source roots (assignment.references ++ [.expression value])) :
    SourceAssignmentHasType source context assignment operator value :=
  CallableLambdaViewStaticTyping.assignment (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem bitNot_original {context : Context} {assignment : AssignmentResolution}
    (typed : SourceBitNotAssignmentValid view context assignment) (reached : Within source roots assignment.references) :
    SourceBitNotAssignmentValid source context assignment :=
  bitNot (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem statement_original {control : ControlContext} {context final : Context} {id : StatementId} {facts : StatementFacts}
    (typed : StatementHasType view control context id final facts) (reached : Reaches source roots (.statement id)) :
    StatementHasType source control context id final facts :=
  statement (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.metadata edited.metadata)

include edited avoids unique in
theorem statements_original {control : ControlContext} {context final : Context} {ids : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType view control context ids final facts) (reached : Within source roots (ids.map NodeId.statement)) :
    StatementsHaveType source control context ids final facts :=
  statements (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem forItem_original {control : ControlContext} {context final : Context} {item : ForItemForm}
    (typed : ForItemHasType view control context item final) (reached : Within source roots item.references) :
    ForItemHasType source control context item final :=
  forItem (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem forItems_original {control : ControlContext} {context final : Context} {items : List ForItemForm}
    (typed : ForItemsHaveType view control context items final) (reached : Within source roots (items.flatMap ForItemForm.references)) :
    ForItemsHaveType source control context items final :=
  forItems (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem matchCase_original {control : ControlContext} {context : Context} {type : TypeSystem.Ty} {arm : TypedMatchCase} {facts : BodyFacts}
    (typed : MatchCaseHasType view control context type arm facts) (reached : Within source roots arm.references) :
    MatchCaseHasType source control context type arm facts :=
  matchCase (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem matchCases_original {control : ControlContext} {context : Context} {type : TypeSystem.Ty} {arms : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType view control context type arms facts) (reached : Within source roots (arms.flatMap TypedMatchCase.references)) :
    MatchCasesHaveType source control context type arms facts :=
  matchCases (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

end Transport

/-- Whole body typing, without a restricted expression syntax or a lowering
Tree. All raw types, lexical output contexts and control facts are retained. -/
theorem body_iff {source view : TypedSource} {body : List StatementId} {changed : List ExpressionId}
    (edited : LocalView source view changed)
    (avoids : Avoids source (body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : Context} {facts : BodyFacts} :
    StatementsHaveType source control context body final facts ↔
      StatementsHaveType view control context body final facts :=
  ⟨fun typed => statements edited avoids unique typed (fun _ member => .root member),
   fun typed => statements_original edited avoids unique typed (fun _ member => .root member)⟩

theorem expression_iff {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source) {context : Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (reached : Reaches source roots (.expression id)) :
    ExpressionHasType source context id type ↔ ExpressionHasType view context id type :=
  ⟨fun typed => expression edited avoids unique typed reached,
   fun typed => expression_original edited avoids unique typed reached⟩

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewStaticTyping
