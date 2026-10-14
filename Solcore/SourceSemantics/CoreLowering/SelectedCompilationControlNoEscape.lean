import Solcore.SourceSemantics.CoreLowering.GenericImperativeForControlShape

/-! Function-boundary control follows from the selected Source body's typing.
This argument depends only on syntax and control flow; calls and values do not
require typing of unrelated declarations in the original program. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationControlNoEscape
open Frontend SourceInference

private def StatementClosed (source : TypedSource) (id : StatementId) : Prop :=
  ∀ {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome},
    Dynamic.StatementExecutes program context evidence source environment before
      id finalContext outcome after → outcome.NoEscapedControl

private def StatementsClosed (source : TypedSource) (ids : List StatementId) : Prop :=
  ∀ id ∈ ids, StatementClosed source id

private theorem statements_closed {source : TypedSource} {ids : List StatementId}
    (closed : StatementsClosed source ids)
    {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.StatementsExecute program context evidence source environment
      before ids finalContext outcome after) : outcome.NoEscapedControl := by
  induction ids generalizing context environment before with
  | nil => cases execution; exact .fallthrough _
  | cons head tail induction =>
    cases execution with
    | cons head tail => exact induction (fun id member => closed id (.tail _ member)) tail
    | terminal head _ => exact closed _ (.head _) head

private structure CasesClosed (source : TypedSource) (cases : List TypedMatchCase) : Prop where
  bodies : ∀ matchCase ∈ cases, StatementsClosed source matchCase.body

private theorem execution_closed {source : TypedSource} {ids : List StatementId}
    {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.StatementsExecute program context evidence source environment
      before ids finalContext outcome after)
    (closed : StatementsClosed source ids) : outcome.NoEscapedControl :=
  statements_closed closed execution

private theorem selected_arm_closed {source : TypedSource}
    {context : Context} {value : Dynamic.Value} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)}
    (closed : ∀ matchCase ∈ cases, StatementsClosed source matchCase.body)
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.arm body bindings)) :
    StatementsClosed source body := by
  induction cases with
  | nil => cases selected
  | cons head tail induction =>
    cases selected with
    | head => exact closed head (.head _)
    | tail _ next => exact induction (fun item member => closed item (.tail _ member)) next

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

set_option linter.unusedSimpArgs false in
private theorem typed_statements_closed {source : TypedSource}
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context finalContext : Context}
    {ids : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType source control context ids finalContext facts) :
    control.loopDepth = 0 → StatementsClosed source ids := by
  apply StatementsHaveType.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True)
    (motive_8 := fun control _ id _ _ _ => control.loopDepth = 0 → StatementClosed source id)
    (motive_9 := fun control _ ids _ _ _ => control.loopDepth = 0 → StatementsClosed source ids)
    (motive_10 := fun _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ => True)
    (motive_12 := fun control _ _ matchCase _ _ =>
      control.loopDepth = 0 → StatementsClosed source matchCase.body)
    (motive_13 := fun control _ _ cases _ _ =>
      control.loopDepth = 0 → ∀ matchCase ∈ cases, StatementsClosed source matchCase.body)
    (t := typing)
  all_goals intros
  all_goals try exact True.intro
  all_goals try solve | simp_all [StatementsClosed, ControlContext.loopAllowed]
  case cons =>
    rename_i head tail headIH tailIH zero selected member
    rcases List.mem_cons.mp member with same | member
    · subst selected; exact headIH zero
    · exact tailIH zero selected member
  case' matchWithoutDefault =>
    rename_i expressionIH casesIH zero
    have closedCases : CasesClosed source _ := ⟨casesIH zero⟩
    clear casesIH
  case' matchWithDefault =>
    rename_i expressionIH casesIH defaultIH zero
    have closedCases : CasesClosed source _ := ⟨casesIH zero⟩
    clear casesIH
  all_goals
    have shape := statement_shape unique (by assumption) (by assumption)
    intro program runtimeContext runtimeFinal evidence environment before after outcome execution
    cases execution <;> have actualForm := shape _ (by assumption) <;> simp_all only [reduceCtorEq, StatementForm.ifThen.injEq, StatementForm.block.injEq, StatementForm.matchWith.injEq, StatementForm.forLoop.injEq, StatementForm.whileLoop.injEq, Option.some.injEq, true_implies, and_true, true_and, and_self, and_false, false_and]
  all_goals first | exact .fallthrough _ | exact .returned _ | skip
  all_goals try exact (execution_closed (by assumption) (by assumption)).restore _
  all_goals try exact (execution_closed (by assumption) (selected_arm_closed (CasesClosed.bodies (by assumption)) (by assumption))).restore _
  case matchWithoutDefault.matchDefault =>
    have impossible := Dynamic.MatchCasesSelect.defaultBody_eq (by assumption)
    simp_all
  case matchWithDefault.matchDefault =>
    have same := Dynamic.MatchCasesSelect.defaultBody_eq (by assumption)
    simp_all only [Option.some.injEq]
    exact (execution_closed (by assumption) (by assumption)).restore _
  case forLoop.forLoop =>
    rcases GenericImperativeFor.for_control_shape (by assumption) with ⟨_, same⟩ | ⟨_, same⟩
    · simp_all [Dynamic.restoreControl, Dynamic.ControlOutcome.NoEscapedControl]
    · simp_all [Dynamic.restoreControl, Dynamic.ControlOutcome.NoEscapedControl]
  case whileLoop.whileLoop =>
    rcases TypedLexicalWhile.while_control_shape (by assumption) with ⟨_, same⟩ | ⟨_, same⟩
    · simp_all [Dynamic.restoreControl, Dynamic.ControlOutcome.NoEscapedControl]
    · simp_all [Dynamic.restoreControl, Dynamic.ControlOutcome.NoEscapedControl]


/-- A typed body at the original function depth cannot export a loop transfer.
No heap invariant or validity of another declaration is required. -/
theorem function {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context staticFinal : Context}
    {ids : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType source control context ids staticFinal facts)
    (depth : control.loopDepth = 0)
    {program : Program} {runtimeContext finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.FunctionStatementsExecute program runtimeContext evidence source
      environment before ids finalContext outcome after) : outcome.NoEscapedControl := by
  have closed := typed_statements_closed unique typing depth
  clear typing depth
  induction ids generalizing runtimeContext environment before with
  | nil => cases execution; exact .fallthrough _
  | cons head tail induction =>
    cases execution with
    | tailExpression => exact .returned _
    | singleton _ _ trace => exact closed _ (.head _) trace
    | cons _ trace => exact induction trace (fun id member => closed id (.tail _ member))
    | terminal trace _ => exact closed _ (.head _) trace

/-- Scoped sequencing shares the same control-only boundary argument. -/
theorem statements {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context staticFinal : Context}
    {ids : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType source control context ids staticFinal facts)
    (depth : control.loopDepth = 0)
    {program : Program} {runtimeContext finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.StatementsExecute program runtimeContext evidence source
      environment before ids finalContext outcome after) : outcome.NoEscapedControl :=
  statements_closed (typed_statements_closed unique typing depth) execution

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationControlNoEscape
