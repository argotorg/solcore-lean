import Solcore.SourceSemantics.CoreLowering.GenericMatchScopedContexts
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree

/-! Original match typing fixes each arm's full lexical context. The hidden
scrutinee is a compiler cell, so it is excluded from these Source contexts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
open Frontend SourceInference

private theorem binders_unique {owner : Resolved.DeclarationId}
    {context first second : SourceSemantics.Context} {binders : List TypedBinder}
    (left : BindersExtend owner context binders first)
    (right : BindersExtend owner context binders second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons head tail ih =>
    cases head
    cases right with
    | cons head tail => cases head; exact ih tail

theorem case_typing {source : TypedSource} {control : ControlContext}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts} {arm : TypedMatchCase}
    (typed : MatchCasesHaveType source control context type cases facts)
    (member : arm ∈ cases) :
    ∃ binders arity armContext final bodyFacts,
      TypedMatchPatternHasType context arm.pattern type binders arity ∧
      BindersExtend source.owner context binders armContext ∧
      StatementsHaveType source control armContext arm.body final bodyFacts := by
  induction cases generalizing facts with
  | nil => cases member
  | cons first rest ih =>
    cases typed with
    | cons head tail =>
      rcases List.mem_cons.mp member with rfl | member
      · cases head with
        | intro pattern extended body => exact ⟨_, _, _, _, _, pattern, extended, body⟩
      · exact ih tail member

/-- A compiler request's native scope cannot substitute for the original
pattern binders. The two genuine typing derivations determine equal contexts. -/
theorem request_typing {source : TypedSource} {control : ControlContext}
    {context child : SourceSemantics.Context} {type : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts}
    {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request}
    (typed : MatchCasesHaveType source control context type cases facts)
    (defaultTyped : ∀ statements, fallback = some statements →
      ∃ final bodyFacts, StatementsHaveType source control context statements final bodyFacts)
    (selected : GenericMatchChildren.ContextFor source context type cases fallback request child) :
    ∃ final bodyFacts, StatementsHaveType source control child request.statements final bodyFacts := by
  cases selected with
  | arm member same pattern extended =>
    obtain ⟨binders, arity, armContext, final, bodyFacts, original, extension, body⟩ :=
      case_typing typed member
    have sameBinders := (CompatiblePatternSourceBinders.pattern_binders original).symm.trans
      (CompatiblePatternSourceBinders.pattern_binders pattern)
    cases sameBinders
    have sameContext := binders_unique extension extended
    cases sameContext
    exact ⟨final, bodyFacts, same ▸ body⟩
  | default same => exact defaultTyped _ same

private theorem defined_ordinary {source : TypedSource} {node : Node}
    {localId : Resolved.LocalId} (ownership : LocalIdentityOwnership source)
    (member : node ∈ source.nodes) (defined : localId ∈ node.definedLocalIds) :
    source.inputs.any (fun input => decide (input.id = localId)) = false := by
  have inNodes : localId ∈ source.nodes.flatMap Node.definedLocalIds :=
    List.mem_flatMap.mpr ⟨node, member, defined⟩
  have disjoint := (List.nodup_append.mp (show
    (source.inputs.map (·.id) ++ source.nodes.flatMap Node.definedLocalIds).Nodup from
    by simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.2
  apply Bool.eq_false_iff.mpr
  intro present
  obtain ⟨input, member, same⟩ := List.any_eq_true.mp present
  exact disjoint input.id (List.mem_map.mpr ⟨input, member, rfl⟩)
    localId inNodes (of_decide_eq_true same)

theorem ordinary_bindings {source : TypedSource} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution}
    (ownership : LocalIdentityOwnership source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution) :
    source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false ∧
    ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
      source.inputs.any (fun input => decide (input.id = binder)) = false := by
  have member := (lookupStatement?_sound found).1
  constructor
  · apply defined_ordinary ownership member
    simp [Node.definedLocalIds, StatementForm.definedLocalIds, form]
  · intro arm present binder bound
    apply defined_ordinary ownership member
    simp only [Node.definedLocalIds, StatementForm.definedLocalIds, form, List.mem_cons]
    exact .inr (List.mem_flatMap.mpr ⟨arm, present, bound⟩)

theorem statement_type {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (typed : StatementHasType source control context id final facts) :
    node.type = .unit ∨ node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all only [reduceCtorEq]
  all_goals
    split at * <;> simp_all

/-- Match arms restore the parent context. The default and every pattern body
keep the original control context, including its actual enclosing loop depth. -/
theorem statement_sites {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {facts : StatementFacts}
    {scrutinee : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee)
    (typed : StatementHasType source control context id final facts) :
    final = context ∧ ∃ caseFacts,
      ExpressionHasType source context resolution.scrutinee scrutinee.type ∧
      MatchCasesHaveType source control context scrutinee.type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ last bodyFacts, StatementsHaveType source control context statements last bodyFacts) := by
  obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases same
  rw [form] at formTyped
  have core : final = context ∧ ∃ type caseFacts,
      ExpressionHasType source context resolution.scrutinee type ∧
      MatchCasesHaveType source control context type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ last bodyFacts, StatementsHaveType source control context statements last bodyFacts) := by
    cases formTyped with
    | matchWithoutDefault absent value casesTyped =>
      exact ⟨rfl, _, _, value, casesTyped, fun statements present => by simp_all⟩
    | matchWithDefault present value casesTyped defaultTyped =>
      exact ⟨rfl, _, _, value, casesTyped, fun statements selected => by
        cases Option.some.inj (present.symm.trans selected)
        exact ⟨_, _, defaultTyped⟩⟩
  obtain ⟨sameContext, type, caseFacts, value, casesTyped, defaultTyped⟩ := core
  obtain ⟨stored, contains, sameType⟩ := value.stored_type
  have sameNode := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans scrutineeFound)
  cases sameNode
  exact ⟨sameContext, caseFacts, sameType ▸ value, sameType ▸ casesTyped, defaultTyped⟩

end Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
