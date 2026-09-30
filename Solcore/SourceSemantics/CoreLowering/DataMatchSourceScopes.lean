import Solcore.SourceSemantics.CoreLowering.DataMatchBranchPrefix

/-! The lexical context of a selected arm comes from independent source static
pattern/body typing. Binder identities can be recovered without assuming source
value typing or a source body execution. The hidden Core local is never added
to this declarative context. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes
open Frontend Frontend.SourceInference

private theorem instruction_binders {context : Context}
    {instructions rest : List MatchPatternInstruction} {type : TypeSystem.Ty}
    {requirements : List RequirementId} {binders : List TypedBinder}
    (typed : PatternInstructionHasType context instructions type requirements binders rest) :
    ∀ {value bindings sourceRest}, Dynamic.PatternInstructionMatches context value instructions bindings sourceRest →
      sourceRest = rest ∧ bindings.map Prod.fst = binders := by
  induction typed using PatternInstructionHasType.rec
    (motive_2 := fun instructions types _ binders rest _ =>
      ∀ {values bindings sourceRest}, values.length = types.length →
        Dynamic.PatternInstructionsMatch context values instructions bindings sourceRest →
        sourceRest = rest ∧ bindings.map Prod.fst = binders) with
  | wildcard => intro value bindings sourceRest matched; cases matched; exact ⟨rfl, rfl⟩
  | integerLiteral => intro value bindings sourceRest matched; cases matched; exact ⟨rfl, rfl⟩
  | binder => intro value bindings sourceRest matched; cases matched; exact ⟨rfl, rfl⟩
  | constructor valid arity typed ih =>
    intro value bindings sourceRest matched
    cases matched with
    | constructor agreement length children => exact ih (length.trans arity) children
  | tuple arity typed ih =>
    intro value bindings sourceRest matched
    cases matched with
    | tuple packed length children => exact ih (length.trans arity) children
  | nil =>
    rename_i values bindings sourceRest length matched
    have empty : values = [] := by simpa using length
    subst values
    cases matched
    exact ⟨rfl, rfl⟩
  | cons head tail headIH tailIH =>
    rename_i values bindings sourceRest length matched
    cases values with
    | nil => simp at length
    | cons value values =>
      cases matched with
      | cons first rest =>
        obtain ⟨same, firstBinders⟩ := headIH first
        subst same
        obtain ⟨same, restBinders⟩ := tailIH (Nat.succ.inj length) rest
        exact ⟨same, by simp [List.map_append, firstBinders, restBinders]⟩

theorem PatternMatches.binders {context : Context} {pattern : TypedMatchPattern}
    {type : TypeSystem.Ty} {binders : List TypedBinder} {arity : Nat}
    {value : Dynamic.Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (typed : TypedMatchPatternHasType context pattern type binders arity)
    (matched : Dynamic.PatternMatches context pattern value bindings) : bindings.map Prod.fst = binders := by
  cases matched with
  | intro source instruction =>
    have same := Dynamic.MatchPatternSourceRepresents.rootArity_eq typed.source_represents source
    subst same
    exact (instruction_binders typed.resolution_type instruction).2

/-- Static source typing supplies the selected body's actual source context.
This is a source-static premise, not a lowering certificate or a body runtime
premise. It can be obtained from declaratively typed function statements. -/
theorem MatchCasesSelect.arm_scope
    {source : TypedSource} {control : ControlContext} {context : Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase} {caseFacts : List BodyFacts}
    {fallback : Option (List StatementId)} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)}
    (typed : MatchCasesHaveType source control context scrutineeType cases caseFacts)
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.arm body bindings)) :
    ∃ armContext finalContext facts,
      BindersExtend source.owner context (bindings.map Prod.fst) armContext ∧
      StatementsHaveType source control armContext body finalContext facts ∧ facts ∈ caseFacts := by
  cases selected with
  | head matched =>
    cases typed with
    | cons head tail =>
      cases head with
      | intro patternTyped extended bodyTyped =>
        exact ⟨_, _, _, PatternMatches.binders patternTyped matched ▸ extended, bodyTyped, by simp⟩
  | tail notMatched selected =>
    cases typed with
    | cons head tail =>
      obtain ⟨armContext, finalContext, facts, extended, bodyTyped, member⟩ := arm_scope tail selected
      exact ⟨armContext, finalContext, facts, extended, bodyTyped, List.mem_cons_of_mem _ member⟩
termination_by cases.length
decreasing_by simp_all

end Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes
