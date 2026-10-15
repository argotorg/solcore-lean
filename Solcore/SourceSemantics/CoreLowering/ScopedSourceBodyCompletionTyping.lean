import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission

/-! Original control summaries identify a body's raw result type. Values at the
end of a nested statement sequence remain discarded by the actual body mode. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
open Frontend SourceInference

private def ResultCompatible (expected actual : TypeSystem.Ty) (mode : Bool)
    (summary : ControlSummary) : Prop :=
  (summary.mayReturn = true → actual = expected) ∧
    (mode = true → ∀ type, summary.fallthrough = some type → type = expected)

private theorem sequence_compatible {expected actual : TypeSystem.Ty} {mode : Bool}
    {head tail : ControlSummary}
    (first : ResultCompatible expected actual false head)
    (remaining : ResultCompatible expected actual mode tail) :
    ResultCompatible expected actual mode (head.sequence tail) := by
  constructor
  · intro returned
    simp only [ControlSummary.sequence, Bool.or_eq_true, Bool.and_eq_true] at returned
    exact returned.elim first.1 (fun h => remaining.1 h.2)
  · intro returning type fallen
    simp only [ControlSummary.sequence] at fallen
    split at fallen
    · exact remaining.2 returning type fallen
    · cases fallen

private theorem head_tail_control {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts ∧
      facts.control = if rest.isEmpty then headFacts.control else headFacts.control.sequence tailFacts.control := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _, rfl⟩
  | cons head tail => exact ⟨_, _, _, head, tail, rfl⟩

private theorem form_control_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementControlFormTyping source control context node.form facts := by
  obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.controlFormTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact formTyped

private theorem nil_expected {source approved expected mode statements}
    (scan : Scan source approved expected mode statements) (returning : mode = true)
    (empty : statements = []) : expected = .unit := by
  subst statements
  cases scan with
  | nil allowed => exact allowed.resolve_left (by simp [returning])

private theorem prefix_compatible {source approved expected mode statements}
    (scan : Scan source approved expected mode statements)
    {actual : TypeSystem.Ty} {head tail : ControlSummary}
    (first : ResultCompatible expected actual false head)
    (unitFallthrough : ∀ type, head.fallthrough = some type → type = .unit)
    (remaining : ResultCompatible expected actual mode tail) :
    ResultCompatible expected actual mode
      (if statements.isEmpty then head else head.sequence tail) := by
  split
  · rename_i empty
    constructor
    · exact first.1
    · intro returning type fallen
      exact (unitFallthrough type fallen).trans (nil_expected scan returning (List.isEmpty_iff.mp empty)).symm
  · exact sequence_compatible first remaining

private theorem terminal_compatible {expected actual : TypeSystem.Ty} {mode : Bool}
    {statements : List StatementId} {head tail : ControlSummary}
    (stopped : head.fallthrough = none)
    (returned : head.mayReturn = true → actual = expected) :
    ResultCompatible expected actual mode
      (if statements.isEmpty then head else head.sequence tail) := by
  have whole : (if statements.isEmpty then head else head.sequence tail) = head := by
    split
    · rfl
    · cases head
      simp_all [ControlSummary.sequence, ControlSummary.canFallthrough]
  rw [whole]
  exact ⟨returned, fun _ _ impossible => by rw [stopped] at impossible; cases impossible⟩

private theorem ordinary_return_compatible {expected actual type : TypeSystem.Ty} :
    ResultCompatible expected actual false (.ordinary type) := by
  simp [ResultCompatible, ControlSummary.ordinary]

private theorem branches_return_compatible {expected actual : TypeSystem.Ty}
    {left right : ControlSummary}
    (first : ResultCompatible expected actual false left)
    (second : ResultCompatible expected actual false right) :
    ResultCompatible expected actual false (left.branches right) := by
  constructor
  · intro returned
    simp only [ControlSummary.branches, Bool.or_eq_true] at returned
    exact returned.elim first.1 second.1
  · simp

private theorem erase_return_compatible {expected actual : TypeSystem.Ty}
    {summary : ControlSummary} (compatible : ResultCompatible expected actual false summary) :
    ResultCompatible expected actual false summary.eraseValue := by
  exact ⟨compatible.1, by simp⟩

private theorem erased_unit {summary : ControlSummary} {type : TypeSystem.Ty}
    (fallen : summary.eraseValue.fallthrough = some type) : type = .unit := by
  cases summary.fallthrough <;> simp_all [ControlSummary.eraseValue]

private theorem branches_unit {left right : ControlSummary} {type : TypeSystem.Ty}
    (fallen : (left.branches right).fallthrough = some type) : type = .unit := by
  simp only [ControlSummary.branches] at fallen
  split at fallen
  · exact (Option.some.inj fallen).symm
  · cases fallen

private theorem returned_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : Option ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt expression)
    (typed : StatementHasType source control context id final facts) : node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem expression_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression false)
    (typed : StatementHasType source control context id final facts) :
    facts.control = .ordinary node.type := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem statement_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) : node.type = facts.type := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    assumption

theorem stopped_statement_result {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (stopped : ScopedSourceBodyStopping.ReturnStopped source [id])
    (typed : StatementHasType source control context id final facts) : node.type = control.returnType := by
  obtain ⟨_, returned, same⟩ := stopped.facts unique (StatementsHaveType.singleton typed)
  simp only [BodyFacts.singleton] at returned same
  simp only [returned, Bool.true_or, ↓reduceIte] at same
  exact (statement_annotation unique found typed).trans same

private theorem stopped_compatible {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    {expected : TypeSystem.Ty} {mode : Bool} {rest : List StatementId} {tail : ControlSummary}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (sourceType : node.type = expected)
    (stopped : ScopedSourceBodyStopping.ReturnStopped source [id])
    (typed : StatementHasType source control context id final facts) :
    ResultCompatible expected control.returnType mode
      (if rest.isEmpty then facts.control else facts.control.sequence tail) := by
  obtain ⟨stops, returned, same⟩ := stopped.facts unique (StatementsHaveType.singleton typed)
  simp only [BodyFacts.singleton] at returned same
  simp only [returned, Bool.true_or, ↓reduceIte] at same
  have original := statement_annotation unique found typed
  have result : control.returnType = expected := same.symm.trans (original.symm.trans sourceType)
  exact terminal_compatible stops.no_fallthrough (fun _ => result)

private theorem case_controls {source : TypedSource} {control : ControlContext}
    {context : SourceSemantics.Context} {type expected : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type cases facts)
    (arms : ∀ arm ∈ cases, ∀ child final bodyFacts,
      StatementsHaveType source control child arm.body final bodyFacts →
      ResultCompatible expected control.returnType false bodyFacts.control) :
    ∀ bodyFacts ∈ facts, ResultCompatible expected control.returnType false bodyFacts.control := by
  induction cases generalizing facts with
  | nil => cases typed; simp
  | cons first rest ih =>
    cases typed with
    | cons head tail =>
      intro bodyFacts member
      rcases List.mem_cons.mp member with rfl | member
      · cases head with
        | intro _ _ body => exact arms _ (by simp) _ _ _ body
      · exact ih tail (fun arm member => arms arm (List.mem_cons_of_mem _ member)) bodyFacts member

private theorem merged_compatible {expected actual : TypeSystem.Ty}
    {facts : List BodyFacts} {fallback : Option BodyFacts} {summary : ControlSummary}
    (arms : ∀ body ∈ facts, ResultCompatible expected actual false body.control)
    (default : ∀ body, fallback = some body → ResultCompatible expected actual false body.control)
    (merged : mergeBodyControls facts fallback = some summary) :
    ResultCompatible expected actual false summary := by
  induction facts generalizing summary with
  | nil =>
    cases fallback with
    | none => simp [mergeBodyControls] at merged
    | some body =>
      simp only [mergeBodyControls, Option.some.injEq] at merged
      exact merged ▸ default body rfl
  | cons head tail ih =>
    have first := arms head (by simp)
    cases selected : mergeBodyControls tail fallback with
    | none =>
      simp only [mergeBodyControls, selected, Option.some.injEq] at merged
      exact merged ▸ first
    | some next =>
      simp only [mergeBodyControls, selected, Option.some.injEq] at merged
      exact merged ▸ branches_return_compatible first (ih (fun body member => arms body (List.mem_cons_of_mem _ member)) selected)

/-- Scanned statements retain the raw type of every reachable return. Only a
function-mode sequence treats its final ordinary value as a body result. -/
private theorem Scan.control_compatible {source approved expected mode statements}
    (scan : Scan source approved expected mode statements) (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    ResultCompatible expected control.returnType mode facts.control := by
  induction scan generalizing control context final facts with
  | nil allowed =>
    cases typed
    constructor
    · simp [BodyFacts.empty, ControlSummary.ordinary]
    · intro returning type fallen
      have same := allowed.resolve_left (by simp [returning])
      simpa [BodyFacts.empty, ControlSummary.ordinary, same] using fallen.symm
  | breaking rest found form =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact terminal_compatible rfl (by simp [ControlSummary.breaking])
  | continuing rest found form =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact terminal_compatible rfl (by simp [ControlSummary.continuing])
  | returnUnit rest found form sourceType result =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    have resultEq := (returned_annotation unique found form head).symm.trans (sourceType.trans result.symm)
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact terminal_compatible rfl (fun _ => resultEq)
  | returning rest found form sourceType =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    have resultEq := (returned_annotation unique found form head).symm.trans sourceType
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact terminal_compatible rfl (fun _ => resultEq)
  | tail found form sourceType =>
    cases typed with
    | singleton head =>
      have same := expression_annotation unique found form head
      simp only [BodyFacts.singleton]
      rw [same, sourceType]
      exact ⟨by simp [ControlSummary.ordinary], fun _ _ fallen => (Option.some.inj fallen).symm⟩
  | absent found form declaration monomorphic ordinary remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)
  | initialized found form declaration monomorphic ordinary expressionFound valueType value remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)
  | discard found form continuing sourceType expressionFound value remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original with
    | expressionValue actual =>
      have modeFalse := continuing.resolve_left (by decide)
      rw [same, modeFalse]
      split
      · exact ordinary_return_compatible
      · exact sequence_compatible ordinary_return_compatible (modeFalse ▸ ih tail)
    | expressionDiscard actual =>
      rw [same]
      exact prefix_compatible remaining ordinary_return_compatible
        (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)
  | block found form body remaining inner tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original with
    | block bodyTyped =>
      rw [same]
      exact prefix_compatible remaining (erase_return_compatible (inner bodyTyped))
        (fun _ => erased_unit) (tailIH tail)
  | conditional found form sourceType conditionFound conditionType value left right remaining leftIH rightIH tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original with
    | ifWithoutElse condition thenTyped =>
      rw [same]
      exact prefix_compatible remaining
        (branches_return_compatible (leftIH thenTyped) ordinary_return_compatible)
        (fun _ => branches_unit) (tailIH tail)
    | ifWithElse condition thenTyped elseTyped =>
      rw [same]
      exact prefix_compatible remaining
        (branches_return_compatible (leftIH thenTyped) (rightIH elseTyped))
        (fun _ => branches_unit) (tailIH tail)
  | whileLoop found form conditionFound conditionType value body remaining inner tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    cases head
    all_goals
      have nodeEq := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
      cases nodeEq
      simp_all only [reduceCtorEq]
    cases form
    apply prefix_compatible remaining _ (fun _ fallen => (Option.some.inj fallen).symm) (tailIH tail)
    exact ⟨(inner (control := control.enterLoop) (by assumption)).1, by simp⟩
  | matching found form scrutineeFound value hiddenOrdinary armsOrdinary arms fallback remaining armsIH fallbackIH tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original with
    | matchWithoutDefault absent scrutinee casesTyped exhaustive merged =>
      rw [same]
      apply prefix_compatible remaining _ (fun _ => erased_unit) (tailIH tail)
      apply erase_return_compatible
      exact merged_compatible (case_controls casesTyped (fun arm member _ _ _ typed => armsIH arm member typed))
        (fun _ impossible => by cases impossible) merged
    | matchWithDefault present scrutinee casesTyped defaultTyped merged =>
      rw [same]
      apply prefix_compatible remaining _ (fun _ => erased_unit) (tailIH tail)
      apply erase_return_compatible
      exact merged_compatible (case_controls casesTyped (fun arm member _ _ _ typed => armsIH arm member typed))
        (fun _ same => by cases same; exact fallbackIH _ present defaultTyped) merged
  | forLoop found form sourceType initial conditionFound conditionType value body after remaining inner tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    cases head
    all_goals
      have nodeEq := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
      cases nodeEq
      simp_all only [reduceCtorEq]
    cases form
    apply prefix_compatible remaining _ (fun _ fallen => (Option.some.inj fallen).symm) (tailIH tail)
    exact ⟨(inner (control := control.enterLoop) (by assumption)).1, by simp⟩
  | assign found form declaration targetType profile bare rhsFound rhsType value remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)
  | assignProjected found form declaration route profile projected keys rhsFound rhsType value remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)

  | bitNot found form declaration targetType profile bare remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)

  | terminalBlock found form sourceType _ stops _ _ =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    rw [same]
    exact stopped_compatible unique found sourceType (.block found form stops) head
  | terminalConditional found form sourceType _ _ _ _ _ first second _ _ _ =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    rw [same]
    exact stopped_compatible unique found sourceType (.conditional found form first second) head
  | terminalMatch found form sourceType _ _ _ _ _ _ present arms fallback _ _ _ =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    rw [same]
    exact stopped_compatible unique found sourceType (.matching found form present arms fallback) head

/-- Actual source completion determines the raw result, independently of how
nominal types share native representations. -/
theorem Scan.result_eq_of_completes {source approved expected statements}
    (scan : Scan source approved expected true statements) (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts)
    (completed : BodyCompletes control.returnType facts) : control.returnType = expected := by
  have compatible := scan.control_compatible unique typed
  rcases completed.2.2 with ⟨_, returned⟩ | fallen
  · exact compatible.1 returned
  · exact compatible.2 rfl _ fallen

end Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
