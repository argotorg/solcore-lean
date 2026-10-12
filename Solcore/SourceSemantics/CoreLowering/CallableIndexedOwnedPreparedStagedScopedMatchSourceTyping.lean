import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites

/-! Original Source typing supplies the actual scrutinee, ordered arm typing,
fallback and restored-context suffix. No selected branch or execution is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping
open Frontend SourceInference
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : MatchResolution}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution) : Statements source context rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, context, _, .nil _ _⟩
  | cons head tail =>
      obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
      have same : actual = node := Option.some.inj
        ((lookupStatement?_complete unique contains).symm.trans found)
      subst actual
      rw [form] at formTyped
      cases formTyped <;> exact ⟨control, final, _, tail⟩

theorem sites {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : MatchResolution} {scrutinee : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee) :
    ∃ control caseFacts,
      ExpressionHasType source context resolution.scrutinee scrutinee.type ∧
      MatchCasesHaveType source control context scrutinee.type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ final facts, StatementsHaveType source control context statements final facts) := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have head : ∃ middle headFacts, StatementHasType source control context id middle headFacts := by
    cases typed with
    | singleton head => exact ⟨_, _, head⟩
    | cons head _ => exact ⟨_, _, head⟩
  obtain ⟨middle, headFacts, head⟩ := head
  obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
  have same : actual = node := Option.some.inj
    ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  rw [form] at formTyped
  have common : ∃ type caseFacts,
      ExpressionHasType source context resolution.scrutinee type ∧
      MatchCasesHaveType source control context type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ final facts, StatementsHaveType source control context statements final facts) := by
    cases formTyped with
    | matchWithoutDefault absent scrutineeTyped casesTyped =>
        exact ⟨_, _, scrutineeTyped, casesTyped, fun statements present => by simp_all⟩
    | matchWithDefault present scrutineeTyped casesTyped defaultTyped =>
        exact ⟨_, _, scrutineeTyped, casesTyped, fun statements selected => by
          cases Option.some.inj (present.symm.trans selected)
          exact ⟨_, _, defaultTyped⟩⟩
  obtain ⟨type, caseFacts, scrutineeTyped, casesTyped, defaults⟩ := common
  obtain ⟨stored, storedContains, sameType⟩ := scrutineeTyped.stored_type
  have sameNode : stored = scrutinee := Option.some.inj
    ((lookupExpression?_complete unique storedContains).symm.trans scrutineeFound)
  subst stored
  exact ⟨control, caseFacts, sameType ▸ scrutineeTyped, sameType ▸ casesTyped, defaults⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping
