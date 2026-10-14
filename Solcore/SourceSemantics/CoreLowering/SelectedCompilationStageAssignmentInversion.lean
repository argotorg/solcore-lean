import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds
open Staging.Recursive (BareTarget)

private theorem target_functional {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {place : PlaceResolution} {left right : Dynamic.ResolvedPlace}
    (first : BareTarget environment heap place left) (second : BareTarget environment heap place right) : left = right := by
  cases first with
  | intro _ leftLookup leftRead leftValue =>
    cases second with
    | intro _ rightLookup rightRead rightValue =>
      cases leftLookup.functional rightLookup
      cases leftRead.functional rightRead
      cases leftValue.functional rightValue
      rfl

private theorem resolve_same {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {target actual : Dynamic.ResolvedPlace} {size : Nat}
    (snapshot : BareTarget environment before place target)
    (resolved : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place actual after) :
    after = before ∧ actual = target := by
  have bare : place.projections = [] := by cases snapshot; assumption
  obtain ⟨same, other⟩ := BareTarget.of_resolves bare resolved.sound
  exact ⟨same.symm, target_functional other snapshot⟩

private theorem target_fault_excluded {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {target : Dynamic.ResolvedPlace} {reason : Dynamic.SemanticFault}
    (snapshot : BareTarget environment before place target)
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after) : False := by
  cases snapshot with
  | intro bare present cell initial =>
    cases fault with
    | unbound missing => exact missing.excludes_lookup present
    | dangling lookup missing =>
      cases lookup.functional present
      exact missing.excludes_read cell
    | projectionExpression _ _ failed => rw [bare] at failed; cases failed
    | danglingAfterProjections lookup _ evaluated missing =>
      rw [bare] at evaluated
      cases evaluated
      cases lookup.functional present
      exact missing.excludes_read cell
    | projectionRead _ _ evaluated _ _ failed =>
      rw [bare] at evaluated
      cases evaluated
      cases failed
    | uninitialized _ _ evaluated _ _ _ nonempty =>
      rw [bare] at evaluated
      cases evaluated
      exact nonempty rfl

private theorem equal_valid {left : Option Dynamic.Value} {right : Dynamic.Value}
    (invalid : Dynamic.AssignmentOperandsInvalid .equal left right) : False := by
  cases invalid with
  | uninitialized impossible => exact impossible rfl
  | compound corresponds _ => cases corresponds

variable {program : Program} {source : TypedSource}
  {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution} {rhs : ExpressionId}
  {target : Dynamic.ResolvedPlace} {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem statement_value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment .equal rhs)
    (snapshot : BareTarget environment before assignment.target target)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    ∃ child value middle updated, child < size ∧ finalContext = context ∧ outcome = .fallthrough environment ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before rhs value middle ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.AssignmentValueApplies .equal target.selected value replacement)
        middle target updated after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›
  rename_i assigned
  cases assigned with
  | intro resolved evaluated written =>
    obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
    refine ⟨_, ?_, _, _, evaluated, _, written⟩
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
    omega

private theorem statement_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment .equal rhs)
    (snapshot : BareTarget environment before assignment.target target)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before rhs reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars
  all_goals simp_all
  obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›
  rename_i failed
  cases failed with
  | target failed => exact (target_fault_excluded snapshot failed.sound).elim
  | rhs resolved failed =>
    obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
    refine ⟨_, ?_, failed⟩
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
    omega
  | operands _ _ _ _ _ _ invalid => exact (equal_valid invalid).elim
  | structuralUpdate resolved _ _ _ _ failed =>
    obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
    cases snapshot
    cases failed

/-- The exact pre-expression target determines the ordinary write after the
right-hand expression. Equal assignment has no operand-rejection branch. -/
theorem child_and_tail {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal rhs)
    (snapshot : BareTarget environment before assignment.target target)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.fault reason) after) ∨
    (∃ child tailSize value middle updated written, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.AssignmentValueApplies .equal target.selected value replacement)
        middle target updated written ∧
      PlainStatements program mode tailSize invocation context environment written rest finalContext outcome after) := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, reason, strict, equalContext, equalOutcome, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, head, tail⟩
  · obtain ⟨child, childStrict, failed⟩ := statement_fault unique found form snapshot failed
    exact .inl ⟨child, reason, Nat.lt_trans childStrict strict, equalContext, equalOutcome, .fault failed⟩
  · obtain ⟨child, value, middle, updated, childStrict, equalContext, equalOutcome, evaluated, written⟩ :=
      statement_value unique found form snapshot head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · refine .inr ⟨child, SourceExecutionSize.stepSize [], value, middle, updated, after,
        Nat.lt_trans childStrict strict, ?_, .value evaluated, written, ?_⟩
      · simp only [SourceExecutionSize.stepSize, List.sum_nil]; omega
      · cases mode <;> exact .control .nil
  · obtain ⟨child, value, expressionHeap, updated, childStrict, equalContext, equalOutcome, evaluated, written⟩ :=
      statement_value unique found form snapshot head
    subst middleContext
    cases equalOutcome
    exact .inr ⟨child, tailSize, value, expressionHeap, updated, middle,
      Nat.lt_trans childStrict strict, tailStrict, .value evaluated, written, tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentInversion
