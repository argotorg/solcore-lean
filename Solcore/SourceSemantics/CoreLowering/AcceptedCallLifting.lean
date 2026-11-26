import Solcore.SourceSemantics.CoreLowering.AcceptedShapes
import Solcore.SourceSemantics.CoreLowering.AcceptedNestedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceExecutionSize
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ElementTargetLifting
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.StoredFunctions

/-!
# Accepted bodies: lifting call-containing Source traces

Original Source executions of call-containing bodies are staged executions.
The lifting of `CellAwareInvocationAcceptedStatementLifting` runs over sized
derivations, and a direct call's callee body, whose derivation is smaller than
the call's, is lifted by one strong induction on the size across bodies, as is
the body of a named function an indirect call applies. Their fault executions
are staged fault executions with the same reason, for every reason the staged
traces express, in families without an indirect call.

Main declarations:
- `CellAwareInvocationAcceptedStoredFunctions.Kept`, the stored functions of a
  heap in a mode, which every lifting keeps, and
  `CellAwareInvocationAcceptedStoredFunctions.FamilyIndirect`, the mode of a
  body family with an indirect call;
- `CellAwareInvocationAcceptedSizedLifting.statements`, the sized lifting of a
  supported statement list given the lifting of its expressions below the size;
- `CellAwareInvocationAcceptedCallLifting.nested_value` and
  `CellAwareInvocationAcceptedCallLifting.nested_roots`, the value execution of
  every nested site, given the facts an indirect call reads (`IndirectFacts`):
  the guard frame of its scope (`Framed`), the arity of the plan's named
  contracts (`Aligned`) and that the mode stores no closure;
- `CellAwareInvocationAcceptedCallLifting.bodies` and
  `CellAwareInvocationAcceptedCallLifting.body`, the induction across bodies and
  the staged trace of a call-containing body, given the static receipts of the
  admitted callees (`Callees`) and the frames of the registry's closure scopes
  (`ClosuresFramed`), with `ClosuresFramed.stages` and `Aligned.of_wellFormed`
  for a compilation's stages registry and a well-formed program;
- `CellAwareInvocationAcceptedFaultLifting.nested_fault`,
  `CellAwareInvocationAcceptedFaultLifting.statements_fault`,
  `CellAwareInvocationAcceptedFaultLifting.bodies_fault` and
  `CellAwareInvocationAcceptedFaultLifting.body_fault`, the same for fault
  executions with an `Expressible` reason, given that the direct calls have
  plain callees and there is no indirect call (`CalleesPlain`,
  `CalleesPlain.no_indirect`).
-/

section
/-! Sized original Source executions of supported statement lists are staged
executions, given the lifting of their expressions below the size. This is
`CellAwareInvocationAcceptedStatementLifting` over the sized derivations of
`SourceExecutionSize`: every child derivation has a smaller size than its
statement, so a child lifting below the size of a list is enough to lift the
list. Every control outcome is carried unchanged, with the context, environment
and heap of the original execution. Fault executions are lifted by
`CellAwareInvocationAcceptedFaultLifting`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSizedLifting
open Core Frontend SourceInference
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedStatementLifting (control)
open CellAwareInvocationAcceptedStoredFunctions (Kept KeptValue KeptOutcome KeptKeys Value)

/-- The sized ordinary statement-list judgment of each compiler mode. -/
def Original (program : Program) (size : Nat) : Bool → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
    TypedSource → Dynamic.Environment → Dynamic.Heap → List StatementId → SourceSemantics.Context →
    Dynamic.ControlOutcome → Dynamic.Heap → Prop
  | true => SourceExecutionSize.FunctionStatementsExecute program size
  | false => SourceExecutionSize.StatementsExecute program size

/-- The staged lifting of the value executions of the expressions that `child`
admits, below a size, which keep the stored functions of a mode. -/
def ChildLifts (program : Program) (registry : Staging.Recursive.Registry) (scope : Staging.Recursive.Scope)
    (child : ExpressionId → Prop) (bound : Nat) (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop)
    (guard : Prop) : Prop :=
  ∀ {id : ExpressionId}, child id → ∀ {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size < bound →
    SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before id
      value after →
    Kept plan closures guard before → Kept plan closures guard after ∧ KeptValue plan closures guard value ∧
    Staging.Recursive.Expression program registry scope context environment before id (.value value) after

theorem ChildLifts.mono {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
    {child : ExpressionId → Prop} {smaller larger : Nat} {plan : SourceCompilationPlan.Plan}
    {closures : Dynamic.Closure → Prop} {guard : Prop}
    (lifts : ChildLifts program registry scope child larger plan closures guard)
    (le : smaller ≤ larger) : ChildLifts program registry scope child smaller plan closures guard := by
  intro _ admitted _ _ _ _ _ _ less trace
  exact lifts admitted (Nat.lt_of_lt_of_le less le) trace

section Inversion
variable {program : Program} {source : TypedSource} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome} {size : Nat}

private theorem same_node (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {other : StatementNode} (contains : ContainsStatement source id other) : other = node :=
  Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)

private theorem below_one {first : Nat} : first < SourceExecutionSize.stepSize [first] :=
  SourceExecutionSize.child_lt_stepSize (by simp)

private theorem below_left {first second : Nat} : first < SourceExecutionSize.stepSize [first, second] :=
  SourceExecutionSize.child_lt_stepSize (by simp)

private theorem below_right {first second : Nat} : second < SourceExecutionSize.stepSize [first, second] :=
  SourceExecutionSize.child_lt_stepSize (by simp)

private theorem nil_below {first : Nat} (positive : 0 < first) :
    SourceExecutionSize.stepSize [] < SourceExecutionSize.stepSize [first] := by
  simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
  omega

private theorem returned_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child value, child < size ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression
        value after ∧
      finalContext = context ∧ outcome = .returned value := by
  cases head with
  | returnValue contains formEq evaluate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, below_one, evaluate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem return_unit_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt none)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  cases head with
  | returnUnit => exact ⟨rfl, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem declared_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {binder : TypedBinder} {expression : ExpressionId} (form : node.form = .letDecl binder (some expression))
    (monomorphic : binder.scheme.quantified = [])
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child value middle location, child < size ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression
        value middle ∧
      BinderExtends source.owner context binder finalContext ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after ∧
      outcome = .fallthrough ((binder.id, location) :: environment) := by
  cases head with
  | letInitialized contains formEq evaluate _ extension allocate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, _, below_one, evaluate, extension, allocate, rfl⟩
  | letInitializedGeneralized contains formEq _ _ polymorphic _ _ =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact absurd monomorphic polymorphic
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem uninitialized_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {binder : TypedBinder} (form : node.form = .letDecl binder none)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ location, BinderExtends source.owner context binder finalContext ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location after ∧
      outcome = .fallthrough ((binder.id, location) :: environment) := by
  cases head with
  | letUninitialized contains formEq _ extension allocate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, extension, allocate, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem assigned_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {expression : ExpressionId}
    (form : node.form = .assignValue assignment operator expression)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child updatedRoot, child < size ∧
      SourceExecutionSize.SourcePlaceAssignment program child context evidence source
        (Dynamic.CompoundAssignmentApplies assignment.target.type operator) environment before assignment.target
        expression updatedRoot after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | assignValue contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, below_one, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem bitNotted_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {assignment : AssignmentResolution} (form : node.form = .assignBitNot assignment)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child updatedRoot, child < size ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program child context evidence source
        (Dynamic.BitNotAssignmentApplies assignment.target.type) environment before assignment.target updatedRoot after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | assignBitNot contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, below_one, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem discarded_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {expression : ExpressionId} (form : node.form = .expression expression true)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child value, child < size ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression
        value after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | expression contains formEq evaluate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, below_one, evaluate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem block_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {statements : List StatementId} (form : node.form = .block statements)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child innerContext inner, child < size ∧
      SourceExecutionSize.StatementsExecute program child context evidence source environment before statements
        innerContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | block contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, below_one, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem conditional_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} (form : node.form = .ifThen condition thenBody elseBody)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    finalContext = context ∧ ∃ test inner truth middle innerContext innerOutcome, test < size ∧ inner < size ∧
      SourceExecutionSize.ExpressionEvaluates program test context evidence source environment before condition
        (.bool truth) middle ∧
      SourceExecutionSize.StatementsExecute program inner context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext innerOutcome after ∧
      outcome = Dynamic.restoreControl environment innerOutcome := by
  cases head with
  | ifTrue contains formEq test executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, _, _, true, _, _, _, below_left, below_right, test, executes, rfl⟩
  | ifFalseWithoutElse contains formEq test =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    refine ⟨rfl, _, SourceExecutionSize.stepSize [], false, _, _, _, below_one, ?_, test, .nil, rfl⟩
    have positive := test.positive
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at positive ⊢
    omega
  | ifFalseWithElse contains formEq test executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, _, _, false, _, _, _, below_left, below_right, test, executes, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem break_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  cases head with
  | breakStmt => exact ⟨rfl, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem continue_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  cases head with
  | continueStmt => exact ⟨rfl, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem while_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {condition : ExpressionId} {body : List StatementId} (form : node.form = .whileLoop condition body)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child loopContext inner, child < size ∧
      SourceExecutionSize.WhileExecutes program child context evidence source environment before condition body
        loopContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | whileLoop contains formEq iterate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, below_one, iterate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem for_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {initializer : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId}
    (form : node.form = .forLoop initializer condition post body)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ first second loopContext loopEnvironment initialized loopFinalContext inner, first < size ∧ second < size ∧
      SourceExecutionSize.ForItemsExecute program first context evidence source environment before initializer
        loopContext loopEnvironment initialized ∧
      SourceExecutionSize.ForLoopExecutes program second loopContext evidence source loopEnvironment initialized
        condition post body loopFinalContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | forLoop contains formEq initial iterate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, _, _, _, _, below_left, below_right, initial, iterate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all
end Inversion

variable {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
  {expected : TypeSystem.Ty} {plan : SourceCompilationPlan.Plan} {closures : Dynamic.Closure → Prop} {guard : Prop}

/-- A bare target has no keys. -/
private theorem bare_keys {environment : Dynamic.Environment} {heap : Dynamic.Heap} {place : PlaceResolution}
    {target : Dynamic.ResolvedPlace} (snapshot : Staging.Recursive.BareTarget environment heap place target) :
    KeptKeys plan closures guard target.projections := by
  cases snapshot
  exact fun _ _ member => nomatch member

private theorem element_split {key index : ExpressionId} {leading : List PlaceProjection}
    (equal : [PlaceProjection.element key] = leading ++ [.element index]) : leading = [] ∧ index = key := by
  cases leading with
  | nil =>
    simp at equal
    exact ⟨rfl, equal.symm⟩
  | cons head tail => simp at equal

/-- The sized resolution of a place of one element whose key `child` admits is
the staged `ElementTarget` that resolves it, given the lifting of `child` within
the bound: the bare root, then the key from the same heap, then the array's own
cell. -/
private theorem element_resolved {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {place : PlaceResolution}
    {key : ExpressionId}
    (single : place.projections = [.element key]) (admitted : child key) {size : Nat}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {target : Dynamic.ResolvedPlace} (within : size ≤ bound) (kept : Kept plan closures guard before)
    (resolve : SourceExecutionSize.SourcePlaceResolves program size context scope.evidence scope.source environment
      before place target after) :
    Staging.Recursive.ElementTarget program registry scope context environment before place (.resolved target)
      after := by
  cases resolve with
  | intro _ _ evaluate =>
    rw [single] at evaluate
    cases evaluate
  | element projectionsEq prefixResolves prefixSelected indexed read initialValue selection =>
    obtain ⟨rfl, rfl⟩ := element_split (single.symm.trans projectionsEq)
    obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves rfl prefixResolves.sound
    cases snapshot with
    | intro _ lookup rootRead rootValue =>
      exact .elementStep projectionsEq (.elementRoot rfl lookup rootRead rootValue) prefixSelected
        (lift admitted (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) indexed kept).2.2
        read initialValue selection

/-- The sized resolution of a place of one element whose key `child` admits
keeps the stored functions, and its path has no keys. -/
private theorem element_kept {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {place : PlaceResolution}
    {key : ExpressionId}
    (single : place.projections = [.element key]) (admitted : child key) {size : Nat}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {target : Dynamic.ResolvedPlace} (within : size ≤ bound)
    (resolve : SourceExecutionSize.SourcePlaceResolves program size context scope.evidence scope.source environment
      before place target after) (kept : Kept plan closures guard before) :
    Kept plan closures guard after ∧ KeptKeys plan closures guard target.projections := by
  cases resolve with
  | intro _ _ evaluate =>
    rw [single] at evaluate
    cases evaluate
  | element projectionsEq prefixResolves _ indexed =>
    obtain ⟨rfl, rfl⟩ := element_split (single.symm.trans projectionsEq)
    obtain ⟨rfl, _⟩ := Staging.Recursive.BareTarget.of_resolves rfl prefixResolves.sound
    exact ⟨(lift admitted (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) indexed kept).1,
      fun _ _ member => by simp at member⟩

/-- A sized Source match whose scrutinee `child` admits and whose selected body lifts within the bound is the
staged match at its entry context. The outcome is the selected body's, restored to the entry bindings; without
a selected body it falls through. -/
private theorem match_lift {child : ExpressionId → Prop} {bound : Nat} (unique : NodeOccurrencesUnique scope.source)
    (lift : ChildLifts program registry scope child bound plan closures guard) {id : StatementId} {node : StatementNode}
    (found : scope.source.lookupStatement? id = some node) {resolution : MatchResolution}
    (form : node.form = .matchWith resolution) (scrutinee : child resolution.scrutinee)
    (body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
      ∀ {size : Nat} {context environment before innerContext inner after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before
        statements innerContext inner after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard inner ∧
      Staging.Recursive.StatementsIn program registry false scope context environment before statements
        innerContext (control inner) after)
    {size : Nat} {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome} (within : size ≤ bound)
    (head : SourceExecutionSize.StatementExecutes program size context scope.evidence scope.source environment
      before id finalContext outcome after) (kept : Kept plan closures guard before) :
    finalContext = context ∧ ∃ inner, outcome = Dynamic.restoreControl environment inner ∧
      Kept plan closures guard after ∧ KeptOutcome plan closures guard inner ∧
      Staging.Recursive.Match program registry scope context environment before resolution
        ((control inner).restore environment) after := by
  cases head with
  | matchArm contains formEq scrutineeContains evaluate allocate select bindersEq valuesEq extended allocated
      executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    subst bindersEq valuesEq
    obtain ⟨arm, member, same⟩ := (CellAwareInvocationAcceptedStatementLifting.selected_body select).1 _ _ rfl
    have tested := lift scrutinee (Nat.lt_of_lt_of_le below_left within) evaluate kept
    have ran := body (.inl ⟨arm, member, same⟩) (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes
      ((tested.1.allocates tested.2.1 allocate).binders (fun on => Value.of_arm select (tested.2.1 on)) allocated)
    exact ⟨rfl, _, rfl, ran.1, ran.2.1, .arm scrutineeContains tested.2.2
      allocate select extended allocated
      ran.2.2⟩
  | matchDefault contains formEq scrutineeContains evaluate allocate select executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    have tested := lift scrutinee (Nat.lt_of_lt_of_le below_left within) evaluate kept
    have ran := body (.inr ((CellAwareInvocationAcceptedStatementLifting.selected_body select).2 _ rfl))
      (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes (tested.1.allocates tested.2.1 allocate)
    exact ⟨rfl, _, rfl, ran.1, ran.2.1, .default scrutineeContains tested.2.2
      allocate select ran.2.2⟩
  | matchNoBranch contains formEq scrutineeContains evaluate allocate select =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    have tested := lift scrutinee (Nat.lt_of_lt_of_le below_one within) evaluate kept
    exact ⟨rfl, .fallthrough environment, rfl, tested.1.allocates tested.2.1 allocate, trivial,
      .noBranch scrutineeContains
      tested.2.2 allocate select⟩
  | _ =>
    exfalso
    clear lift body kept
    obtain rfl := same_node unique found (by assumption)
    simp_all

/-- One statement followed by the rest of its list, over sized derivations. A
falling-through head runs the rest; a terminal head ends the list. -/
private theorem sequence {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {size : Nat} (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (step : ∀ {context environment before middleContext nextEnvironment middle finalContext outcome after}
        {headSize tailSize : Nat}, headSize < size → tailSize < size →
      SourceExecutionSize.StatementExecutes program headSize context scope.evidence scope.source environment before id
        middleContext (.fallthrough nextEnvironment) middle →
      Original program tailSize mode middleContext scope.evidence scope.source nextEnvironment middle rest finalContext
        outcome after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after)
    (stop : ∀ {context environment before finalContext outcome after} {headSize : Nat}, headSize < size →
      SourceExecutionSize.StatementExecutes program headSize context scope.evidence scope.source environment before id
        finalContext outcome after →
      Dynamic.TerminalControl outcome →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after) :
    ∀ {context environment before finalContext outcome after},
      Original program size mode context scope.evidence scope.source environment before (id :: rest) finalContext
        outcome after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after := by
  intro context environment before finalContext outcome after original
  cases mode with
  | false =>
    unfold Original at original
    cases original with
    | cons head next => exact step below_left below_right head next
    | terminal head terminal => exact stop below_one head terminal
  | true =>
    unfold Original at original
    cases original with
    | tailExpression contains form _ =>
      obtain rfl := same_node unique found contains
      exact absurd form (notTail _)
    | singleton _ _ head =>
      have nilBelow := nil_below head.positive
      cases outcome with
      | fallthrough nextEnvironment => exact step below_one nilBelow head .nil
      | returned value => exact stop below_one head (.returned value)
      | breaking environment => exact stop below_one head (.breaking environment)
      | continuing environment => exact stop below_one head (.continuing environment)
      | fault reason => exact stop below_one head (.fault reason)
    | cons head next => exact step below_left below_right head next
    | terminal head terminal => exact stop below_one head terminal

/-- The sized Source evaluation of a path of mapping indices whose keys `child`
admits is the staged evaluation of its keys, in order, given the lifting of
`child` below the size. -/
private theorem projections_values {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} :
    ∀ {projections : List PlaceProjection},
    (∀ projection ∈ projections, ∃ key, projection = .index key ∧ child key) →
    ∀ {size : Nat} {before after : Dynamic.Heap} {evaluated : List Dynamic.EvaluatedProjection}, size ≤ bound →
      SourceExecutionSize.SourceProjectionsEvaluate program size context scope.evidence scope.source environment
        before projections evaluated after →
      Kept plan closures guard before →
      ∃ values, Staging.Recursive.Expressions program registry scope context environment before
          (Staging.Recursive.ProjectedTarget.keys projections) (.values values) after ∧
        Staging.Recursive.ProjectedTarget.Values projections values evaluated := by
  intro projections
  induction projections with
  | nil =>
    intro _ size before after evaluated _ evaluate
    cases evaluate
    exact fun _ => ⟨[], .nil, .nil⟩
  | cons projection rest ih =>
    intro keys size before after evaluated within evaluate
    intro kept
    obtain ⟨key, rfl, admitted⟩ := keys projection List.mem_cons_self
    cases evaluate with
    | index head tail =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
      obtain ⟨values, staged, ordered⟩ :=
        ih (fun other member => keys other (List.mem_cons_of_mem _ member)) (by omega) tail
          (lift admitted (by omega) head kept).1
      exact ⟨_ :: values, .cons (lift admitted (by omega) head kept).2.2 staged, .index ordered⟩

/-- The sized Source evaluation of a path of mapping indices whose keys `child`
admits keeps the stored functions, and its keys are stored. -/
private theorem projections_kept {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} :
    ∀ {projections : List PlaceProjection},
    (∀ projection ∈ projections, ∃ key, projection = .index key ∧ child key) →
    ∀ {size : Nat} {before after : Dynamic.Heap} {evaluated : List Dynamic.EvaluatedProjection}, size ≤ bound →
      SourceExecutionSize.SourceProjectionsEvaluate program size context scope.evidence scope.source environment
        before projections evaluated after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptKeys plan closures guard evaluated := by
  intro projections
  induction projections with
  | nil =>
    intro _ size before after evaluated _ evaluate kept
    cases evaluate
    exact ⟨kept, fun _ _ member => nomatch member⟩
  | cons projection rest ih =>
    intro keys size before after evaluated within evaluate kept
    obtain ⟨key, rfl, admitted⟩ := keys projection List.mem_cons_self
    cases evaluate with
    | index head tail =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
      have evaluatedKey := lift admitted (by omega) head kept
      obtain ⟨keptAfter, keptKeys⟩ :=
        ih (fun other member => keys other (List.mem_cons_of_mem _ member)) (by omega) tail evaluatedKey.1
      exact ⟨keptAfter, fun on other member => by
        rcases List.mem_cons.mp member with same | member
        · cases same
          exact evaluatedKey.2.1 on
        · exact keptKeys on other member⟩

/-- The sized Source resolution of a place through mapping indices whose keys
`child` admits is the staged evaluation of its keys followed by its staged
snapshot, given the lifting of `child` below the size. -/
private theorem projected_target {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    (keys : ∀ projection ∈ place.projections, ∃ key, projection = .index key ∧ child key)
    {size : Nat} {before after : Dynamic.Heap} {target : Dynamic.ResolvedPlace} (within : size ≤ bound)
    (resolve : SourceExecutionSize.SourcePlaceResolves program size context scope.evidence scope.source environment
      before place target after) (kept : Kept plan closures guard before) :
    ∃ values, Staging.Recursive.Expressions program registry scope context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values values) after ∧
      Staging.Recursive.ProjectedTarget.Snapshot environment before after place values target := by
  cases resolve with
  | intro lookup initialRead evaluate currentRead initialValue selection =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
    obtain ⟨values, staged, ordered⟩ := projections_values lift keys (by omega) evaluate kept
    exact ⟨values, staged, .intro lookup initialRead ordered currentRead initialValue selection⟩
  | element projectionsEq => exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)

/-- The sized Source resolution of a place through mapping indices whose keys
`child` admits keeps the stored functions, and its keys are stored. -/
private theorem target_kept {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    (keys : ∀ projection ∈ place.projections, ∃ key, projection = .index key ∧ child key)
    {size : Nat} {before after : Dynamic.Heap} {target : Dynamic.ResolvedPlace} (within : size ≤ bound)
    (resolve : SourceExecutionSize.SourcePlaceResolves program size context scope.evidence scope.source environment
      before place target after) (kept : Kept plan closures guard before) :
    Kept plan closures guard after ∧ KeptKeys plan closures guard target.projections := by
  cases resolve with
  | intro _ _ evaluate =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
    exact projections_kept lift keys (by omega) evaluate kept
  | element projectionsEq => exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)

/-- The sized Source iterations of a `while` loop whose condition `child`
admits and whose body lifts within the bound are the staged iterations, with
the same outcome and heap. The loop falls through at its own bindings or
returns. -/
private theorem while_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {condition : ExpressionId}
    {body : List StatementId} (test : child condition)
    (inner : ∀ {size : Nat} {context environment before innerContext outcome after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before body
        innerContext outcome after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (control outcome) after) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {loopContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      size ≤ bound →
      SourceExecutionSize.WhileExecutes program size context scope.evidence scope.source environment before condition
        body loopContext outcome after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.While program registry scope context environment before condition body (control outcome)
          after ∧
        (outcome = .fallthrough environment ∨ ∃ value, outcome = .returned value) := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context environment before after loopContext outcome within loop
    intro kept
    cases loop with
    | done evaluate =>
      have tested := lift test (Nat.lt_of_lt_of_le below_one within) evaluate kept
      exact ⟨tested.1, trivial, .done tested.2.2, .inl rfl⟩
    | nextFallthrough evaluate executes next =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      obtain ⟨held, safe, staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) next
        ran.1
      exact ⟨held, safe, .next tested.2.2 ran.2.2 staged, ended⟩
    | nextContinue evaluate executes next =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      obtain ⟨held, safe, staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) next
        ran.1
      exact ⟨held, safe, .continueNext tested.2.2 ran.2.2 staged, ended⟩
    | breaks evaluate executes =>
      have tested := lift test (Nat.lt_of_lt_of_le below_left within) evaluate kept
      have ran := inner (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes tested.1
      exact ⟨ran.1, trivial, .breakFromBody tested.2.2
        ran.2.2, .inl rfl⟩
    | returns evaluate executes =>
      have tested := lift test (Nat.lt_of_lt_of_le below_left within) evaluate kept
      have ran := inner (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes tested.1
      exact ⟨ran.1, ran.2.1, .returned tested.2.2
        ran.2.2, .inr ⟨_, rfl⟩⟩

/-- The sized Source execution of a supported header vector whose expressions
`child` admits is the staged execution of the vector, with the same context,
bindings and heap, given the lifting of `child` within the bound. The vector
keeps the signatures of its context. -/
private theorem items_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {items : List ForItemForm}
    (shape : CellAwareInvocationAcceptedBodyShape.ItemsShape scope.source child items) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment},
      size ≤ bound →
      SourceExecutionSize.ForItemsExecute program size context scope.evidence scope.source environment before items
        finalContext finalEnvironment after →
      Kept plan closures guard before → Kept plan closures guard after ∧
      Staging.Recursive.ForItems program registry scope context environment before items finalContext
          (.done finalEnvironment) after ∧
        finalContext.signatures = context.signatures := by
  induction shape with
  | nil =>
    intro size context environment before after finalContext finalEnvironment _ executes
    cases executes
    exact fun kept => ⟨kept, .empty, rfl⟩
  | absent monomorphic _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    intro kept
    cases executes with
    | cons head tail =>
      cases head with
      | letUninitialized _ extension allocate =>
        obtain ⟨keptAfter, staged, signatures⟩ := tailIH (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) tail
          (kept.allocates_none allocate)
        exact ⟨keptAfter, .absent monomorphic extension allocate staged, signatures.trans extension.context_fields.1⟩
  | initialized monomorphic value _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    intro kept
    cases executes with
    | cons head tail =>
      cases head with
      | letInitialized evaluate _ extension allocate =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        have evaluated := lift value (by omega) evaluate kept
        obtain ⟨keptAfter, staged, signatures⟩ := tailIH (by omega) tail
          (evaluated.1.allocates evaluated.2.1 allocate)
        exact ⟨keptAfter, .initialized monomorphic extension evaluated.2.2 allocate staged,
          signatures.trans extension.context_fields.1⟩
      | letInitializedGeneralized _ _ polymorphic => exact absurd monomorphic polymorphic
  | discarded value _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    intro kept
    cases executes with
    | cons head tail =>
      cases head with
      | expression evaluate =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        have evaluated := lift value (by omega) evaluate kept
        obtain ⟨keptAfter, staged, signatures⟩ := tailIH (by omega) tail evaluated.1
        exact ⟨keptAfter, .expression evaluated.2.2 staged, signatures⟩
  | assigned assignable value _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    intro kept
    cases executes with
    | cons head tail =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          have evaluated := lift value (by omega) evaluate kept
          obtain ⟨keptAfter, staged, signatures⟩ := tailIH (by omega) tail
            (evaluated.1.assigns (bare_keys snapshot) evaluated.2.1 write)
          exact ⟨keptAfter, .assignment snapshot evaluated.2.2 write staged, signatures⟩
  | projectedAssigned assignable keys value _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    intro kept
    cases executes with
    | cons head tail =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ := projected_target lift keys (by omega) resolve kept
          have target := target_kept lift keys (by omega) resolve kept
          have evaluated := lift value (by omega) evaluate target.1
          obtain ⟨keptAfter, remaining, signatures⟩ := tailIH (by omega) tail
            (evaluated.1.assigns target.2 evaluated.2.1 write)
          exact ⟨keptAfter, .projectedAssignment assignable.2.1 staged snapshot evaluated.2.2 write remaining,
            signatures⟩
  | bitNotted assignable _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    intro kept
    cases executes with
    | cons head tail =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          obtain ⟨keptAfter, staged, signatures⟩ := tailIH (by omega) tail (kept.bitNots (bare_keys snapshot) write)
          exact ⟨keptAfter, .bitNot snapshot write staged, signatures⟩
  | projectedBitNotted assignable keys _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    intro kept
    cases executes with
    | cons head tail =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ := projected_target lift keys (by omega) resolve kept
          have target := target_kept lift keys (by omega) resolve kept
          obtain ⟨keptAfter, remaining, signatures⟩ := tailIH (by omega) tail (target.1.bitNots target.2 write)
          exact ⟨keptAfter, .projectedBitNot assignable.2.1 staged snapshot write remaining, signatures⟩

/-- The sized Source iterations of a `for` loop whose condition `child` admits,
whose body lifts within the bound and whose post header is supported are the
staged iterations, with the same outcome and heap. The loop falls through at
its own bindings or returns. -/
private theorem for_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {condition : ExpressionId}
    {post : List ForItemForm} {body : List StatementId} (test : child condition)
    (inner : ∀ {size : Nat} {context environment before innerContext outcome after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before body
        innerContext outcome after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (control outcome) after)
    (postShape : CellAwareInvocationAcceptedBodyShape.ItemsShape scope.source child post) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {loopContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      size ≤ bound →
      SourceExecutionSize.ForLoopExecutes program size context scope.evidence scope.source environment before
        condition post body loopContext outcome after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.ForLoop program registry scope context environment before condition post body
          (control outcome) after ∧
        (outcome = .fallthrough environment ∨ ∃ value, outcome = .returned value) := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context environment before after loopContext outcome within loop
    intro kept
    cases loop with
    | done evaluate =>
      have tested := lift test (Nat.lt_of_lt_of_le below_one within) evaluate kept
      exact ⟨tested.1, trivial, .finished tested.2.2, .inl rfl⟩
    | nextFallthrough evaluate executes postExecutes next =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      have posted := items_lift lift postShape (by omega) postExecutes ran.1
      obtain ⟨held, safe, staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) next
        posted.1
      exact ⟨held, safe, .iterate tested.2.2 ran.2.2
        posted.2.1 staged, ended⟩
    | nextContinue evaluate executes postExecutes next =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      have posted := items_lift lift postShape (by omega) postExecutes ran.1
      obtain ⟨held, safe, staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) next
        posted.1
      exact ⟨held, safe, .continueIterate tested.2.2 ran.2.2
        posted.2.1 staged, ended⟩
    | breaks evaluate executes =>
      have tested := lift test (Nat.lt_of_lt_of_le below_left within) evaluate kept
      have ran := inner (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes tested.1
      exact ⟨ran.1, trivial, .forBreakFromBody tested.2.2
        ran.2.2, .inl rfl⟩
    | returns evaluate executes =>
      have tested := lift test (Nat.lt_of_lt_of_le below_left within) evaluate kept
      have ran := inner (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes tested.1
      exact ⟨ran.1, ran.2.1, .returnedFromBody tested.2.2
        ran.2.2, .inr ⟨_, rfl⟩⟩

/-- A sized ordinary execution of a supported statement list is a staged
execution with the same context, outcome and heap, given the lifting of its
expressions below the size. It keeps the stored functions, and a returned value
is stored. -/
theorem statements (unique : NodeOccurrencesUnique scope.source) {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard) {mode : Bool}
    {statements : List StatementId}
    (shape : Shape scope.source expected child mode statements) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      size ≤ bound →
      Original program size mode context scope.evidence scope.source environment before statements finalContext
        outcome after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.StatementsIn program registry mode scope context environment before statements finalContext
        (control outcome) after := by
  induction shape with
  | @nil mode _ =>
    intro size context environment before after finalContext outcome _ original
    cases mode <;> unfold Original at original <;> cases original <;> exact fun kept => ⟨kept, trivial, .nil⟩
  | returned found form value =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after _ _ _ _ head _
      obtain ⟨_, _, _, _, _, impossible⟩ := returned_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after headSize below head _
      intro kept
      obtain ⟨_, _, childBelow, evaluate, rfl, rfl⟩ := returned_inv unique found form head
      have evaluated := lift value (by omega) evaluate kept
      refine ⟨evaluated.1, evaluated.2.1, ?_⟩
      exact .returnValue (lookupStatement?_sound found) form
        evaluated.2.2
  | returnUnit found form =>
    intro size context environment before after finalContext outcome _
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := return_unit_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after _ _ head _
      obtain ⟨rfl, rfl, rfl⟩ := return_unit_inv unique found form head
      exact fun kept => ⟨kept, fun _ => .unit, .returnUnit (lookupStatement?_sound found) form⟩
  | declared found form monomorphic value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, _, _, childBelow, evaluate, extension, allocate, same⟩ :=
        declared_inv unique found form monomorphic head
      cases same
      have evaluated := lift value (by omega) evaluate kept
      have rest := tailIH (by omega) next (evaluated.1.allocates evaluated.2.1 allocate)
      refine ⟨rest.1, rest.2.1, ?_⟩
      exact .letInitialized (lookupStatement?_sound found) form evaluated.2.2
        monomorphic extension allocate rest.2.2
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, _, _, _, same⟩ := declared_inv unique found form monomorphic head
      subst same
      cases terminal
  | uninitialized found form monomorphic _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, extension, allocate, same⟩ := uninitialized_inv unique found form head
      cases same
      have rest := tailIH (by omega) next (kept.allocates_none allocate)
      refine ⟨rest.1, rest.2.1, ?_⟩
      exact .letUninitialized (lookupStatement?_sound found) form monomorphic extension allocate
        rest.2.2
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, same⟩ := uninitialized_inv unique found form head
      subst same
      cases terminal
  | assigned found form assignable value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        have below := childBelow
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        have evaluated := lift value (by omega) evaluate kept
        have rest := tailIH (by omega) next (evaluated.1.assigns (bare_keys snapshot) evaluated.2.1 write)
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .assignBare (lookupStatement?_sound found) form snapshot
          (lift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) evaluate kept).2.2
          write rest.2.2
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | projectedAssigned found form assignable keys value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ := projected_target lift keys (by omega) resolve kept
        have target := target_kept lift keys (by omega) resolve kept
        have evaluated := lift value (by omega) evaluate target.1
        have rest := tailIH (by omega) next (evaluated.1.assigns target.2 evaluated.2.1 write)
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .assignProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot
          evaluated.2.2 write rest.2.2
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | bitNotted found form assignable _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, _, executes, rfl, same⟩ := bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        have rest := tailIH (by omega) next (kept.bitNots (bare_keys snapshot) write)
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .bitNotBare (lookupStatement?_sound found) form snapshot write rest.2.2
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := bitNotted_inv unique found form head
      subst same
      cases terminal
  | projectedBitNotted found form assignable keys _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ := projected_target lift keys (by omega) resolve kept
        have target := target_kept lift keys (by omega) resolve kept
        have rest := tailIH (by omega) next (target.1.bitNots target.2 write)
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .bitNotProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot write
          rest.2.2
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := bitNotted_inv unique found form head
      subst same
      cases terminal
  | elementAssigned found form _ single index value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        have target := element_kept lift single index (by omega) resolve kept
        have evaluated := lift value (by omega) evaluate target.1
        have rest := tailIH (by omega) next (evaluated.1.assigns target.2 evaluated.2.1 write)
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .assignElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (element_resolved lift single index (by omega) kept
            resolve)
          evaluated.2.2 write rest.2.2
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | elementBitNotted found form _ single index _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        have target := element_kept lift single index (by omega) resolve kept
        have rest := tailIH (by omega) next (target.1.bitNots target.2 write)
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .bitNotElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (element_resolved lift single index (by omega) kept
            resolve)
          write rest.2.2
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := bitNotted_inv unique found form head
      subst same
      cases terminal
  | discarded found form value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, childBelow, evaluate, rfl, same⟩ := discarded_inv unique found form head
      cases same
      have evaluated := lift value (by omega) evaluate kept
      have rest := tailIH (by omega) next evaluated.1
      refine ⟨rest.1, rest.2.1, ?_⟩
      exact .discard (lookupStatement?_sound found) form evaluated.2.2 rest.2.2
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := discarded_inv unique found form head
      subst same
      cases terminal
  | block found form _ _ innerIH tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, inner, innerBelow, executes, rfl, same⟩ := block_inv unique found form head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        have ran := innerIH (by omega) executes kept
        have rest := tailIH (by omega) next ran.1
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .blockFallthrough (lookupStatement?_sound found) form ran.2.2
          rest.2.2
      | _ => cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      intro kept
      obtain ⟨_, _, inner, innerBelow, executes, rfl, rfl⟩ := block_inv unique found form head
      have ran := innerIH (by omega) executes kept
      refine ⟨ran.1, ran.2.1.restore, ?_⟩
      have staged := ran.2.2
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .blockReturned (lookupStatement?_sound found) form staged
      | breaking => exact .blockBreaking (lookupStatement?_sound found) form staged
      | continuing => exact .blockContinuing (lookupStatement?_sound found) form staged
      | fault => exact .blockFault (lookupStatement?_sound found) form staged
  | @conditional mode id rest node condition thenBody elseBody found form test _ _ _ leftIH rightIH tailIH =>
    intro size context environment before after finalContext outcome within
    have branch : ∀ {truth : Bool} {innerSize : Nat} {context environment before innerContext inner after},
        innerSize ≤ bound →
        SourceExecutionSize.StatementsExecute program innerSize context scope.evidence scope.source environment before
          (if truth then thenBody else elseBody.getD []) innerContext inner after →
        Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard inner ∧
        Staging.Recursive.StatementsIn program registry false scope context environment before
          (if truth then thenBody else elseBody.getD []) innerContext (control inner) after := by
      intro truth innerSize context environment before innerContext inner after within executes
      cases truth
      · exact rightIH within executes
      · exact leftIH within executes
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨rfl, _, _, truth, _, _, inner, testBelow, innerBelow, evaluate, executes, same⟩ :=
        conditional_inv unique found form head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        have tested := lift test (by omega) evaluate kept
        have ran := branch (by omega) executes tested.1
        have rest := tailIH (by omega) next ran.1
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .ifFallthrough (lookupStatement?_sound found) form tested.2.2
          ran.2.2 rest.2.2
      | _ => cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      intro kept
      obtain ⟨rfl, _, _, truth, _, _, inner, testBelow, innerBelow, evaluate, executes, rfl⟩ :=
        conditional_inv unique found form head
      have lifted := lift test (by omega) evaluate kept
      have ran := branch (by omega) executes lifted.1
      refine ⟨ran.1, ran.2.1.restore, ?_⟩
      have staged := ran.2.2
      have tested := lifted.2.2
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .ifReturned (lookupStatement?_sound found) form tested staged
      | breaking => exact .ifBreaking (lookupStatement?_sound found) form tested staged
      | continuing => exact .ifContinuing (lookupStatement?_sound found) form tested staged
      | fault => exact .ifFault (lookupStatement?_sound found) form tested staged
  | @matched mode id rest node resolution found form scrutinee _ _ _ armsIH fallbackIH tailIH =>
    intro size context environment before after finalContext outcome within
    have body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
        ∀ {innerSize : Nat} {context environment before innerContext inner after}, innerSize ≤ bound →
        SourceExecutionSize.StatementsExecute program innerSize context scope.evidence scope.source environment
          before statements innerContext inner after →
        Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard inner ∧
        Staging.Recursive.StatementsIn program registry false scope context environment before statements
          innerContext (control inner) after := by
      intro statements selected innerSize context environment before innerContext inner after within executes
      rcases selected with ⟨arm, member, rfl⟩ | same
      · exact armsIH arm member within executes
      · rw [same] at fallbackIH
        exact fallbackIH within executes
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨rfl, inner, same, keptMiddle, _, staged⟩ :=
        match_lift unique lift found form scrutinee body (by omega) head kept
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        have rest := tailIH (by omega) next keptMiddle
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .matchFallthrough (lookupStatement?_sound found) form staged rest.2.2
      | _ => cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      intro kept
      obtain ⟨rfl, inner, rfl, held, safe, staged⟩ :=
        match_lift unique lift found form scrutinee body (by omega) head kept
      refine ⟨held, safe.restore, ?_⟩
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .matchReturned (lookupStatement?_sound found) form staged
      | breaking => exact .matchBreaking (lookupStatement?_sound found) form staged
      | continuing => exact .matchContinuing (lookupStatement?_sound found) form staged
      | fault => exact .matchFault (lookupStatement?_sound found) form staged
  | breaking found form =>
    intro size context environment before after finalContext outcome _
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := break_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after _ _ head _
      obtain ⟨rfl, rfl, rfl⟩ := break_inv unique found form head
      exact fun kept => ⟨kept, trivial, .breaking (lookupStatement?_sound found) form⟩
  | continuing found form =>
    intro size context environment before after finalContext outcome _
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := continue_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after _ _ head _
      obtain ⟨rfl, rfl, rfl⟩ := continue_inv unique found form head
      exact fun kept => ⟨kept, trivial, .continuing (lookupStatement?_sound found) form⟩
  | whileLooped found form test _ _ innerIH tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, loopOutcome, loopBelow, iterate, rfl, same⟩ := while_inv unique found form head
      obtain ⟨keptMiddle, _, loop, ended⟩ := while_lift lift test (fun within executes => innerIH within executes)
        (by omega) iterate kept
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        have rest := tailIH (by omega) next keptMiddle
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .whileFallthrough (lookupStatement?_sound found) form loop rest.2.2
      · cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      intro kept
      obtain ⟨_, _, loopOutcome, loopBelow, iterate, rfl, rfl⟩ := while_inv unique found form head
      obtain ⟨held, safe, loop, ended⟩ := while_lift lift test (fun within executes => innerIH within executes)
        (by omega) iterate kept
      rcases ended with rfl | ⟨_, rfl⟩
      · cases terminal
      · exact ⟨held, safe, .whileReturned (lookupStatement?_sound found) form loop⟩
  | forLooped found form initialItems test _ postItems _ innerIH tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      intro kept
      obtain ⟨_, _, _, _, _, _, loopOutcome, firstBelow, secondBelow, initialized, iterate, rfl, same⟩ :=
        for_inv unique found form head
      have initial := items_lift lift initialItems (by omega) initialized kept
      obtain ⟨held, _, loop, ended⟩ := for_lift lift test (fun within executes => innerIH within executes) postItems
        (by omega) iterate initial.1
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        have rest := tailIH (by omega) next held
        refine ⟨rest.1, rest.2.1, ?_⟩
        exact .forFallthrough (lookupStatement?_sound found) form initial.2.1
          loop rest.2.2
      · cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      intro kept
      obtain ⟨_, _, _, _, _, _, loopOutcome, firstBelow, secondBelow, initialized, iterate, rfl, rfl⟩ :=
        for_inv unique found form head
      have initial := items_lift lift initialItems (by omega) initialized kept
      obtain ⟨held, safe, loop, ended⟩ := for_lift lift test (fun within executes => innerIH within executes) postItems
        (by omega) iterate initial.1
      rcases ended with rfl | ⟨_, rfl⟩
      · cases terminal
      · exact ⟨held, safe, .forReturned (lookupStatement?_sound found) form initial.2.1
          loop⟩
  | tail found form _ value =>
    intro size context environment before after finalContext outcome within original
    intro kept
    unfold Original at original
    cases original with
    | tailExpression contains formEq evaluate =>
      obtain rfl := same_node unique found contains
      rw [form] at formEq
      cases formEq
      have evaluated := lift value (Nat.lt_of_lt_of_le below_one within) evaluate kept
      exact ⟨evaluated.1, evaluated.2.1, .tail (lookupStatement?_sound found) form evaluated.2.2⟩
    | singleton contains notTail _ =>
      obtain rfl := same_node unique found contains
      exact absurd form (notTail _)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSizedLifting
end

section
/-! Original executions of bodies whose expressions are nested sites are
staged executions. A direct call's original rule runs the callee body, so the
lifting is one strong induction on the size of the original derivation across
bodies: at a call of a given size, the callee body's derivation is smaller, and
its lifting below that size gives the staged global application. A
conversion's and a builtin closure call's original rule applies the builtin as
the staged rule does, a reference to a builtin closure is the staged atomic
value, a mapping index's original rules give the staged index outcome, a
tuple's original rule packs its elements' values as the staged rule does, and
an array form's original rules evaluate its children in the order of the
staged rule and take its step. A named function value is the staged atomic
value, and an uncoerced indirect call applies its callee's value as the staged
rule does: the mode holds in a Source with one, so the value is a builtin or a
named function at a planned instantiation with the empty dictionary, whose body
the induction lifts and whose runtime contract the scope's guard frame accepts
at the call's arity, and not a closure, which the mode does not yet store
(`IndirectFacts`).
Inside one
body, a nested site is lifted by induction on the site, over the sized
derivations of its operands, branches, elements and arguments. The admitted
callees are static inputs (`Callees`): the registry scope of each callee's
global view at the empty dictionary and the shape of its body, whose
expressions are nested sites of its own cache row. Every lifting keeps the
stored functions of a mode (`CellAwareInvocationAcceptedStoredFunctions.Kept`),
as no nested site makes a closure. Fault executions are lifted by
`CellAwareInvocationAcceptedFaultLifting`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedStatementLifting (control)
open CellAwareInvocationAcceptedSizedLifting (ChildLifts)
open CellAwareInvocationAcceptedSourceLifting (expression_value)
open CellAwareInvocationAcceptedStoredFunctions (Kept KeptValue KeptValues KeptOutcome Value FamilyIndirect HasIndirect)

section Sites
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope} {id : ExpressionId}

private theorem requirements_of (site : Site prepared named scope.source id)
    {form : ExpressionForm} (same : site.node.form = form)
    (notInteger : ∀ literal resolution, form ≠ .integerLiteral literal resolution) :
    site.node.requirements = [] := by
  have requirements := site.requirements
  split at requirements
  · rename_i literal resolution integer
    exact absurd (same.symm.trans integer) (notInteger literal resolution)
  · exact requirements

private theorem occurrence (site : Site prepared named scope.source id)
    {form : ExpressionForm} (same : site.node.form = form)
    (notInteger : ∀ literal resolution, form ≠ .integerLiteral literal resolution) :
    Staging.Recursive.Occurrence scope id form :=
  ⟨site.node, lookupExpression?_sound site.found, same, requirements_of site same notInteger, site.coercions⟩

end Sites

variable {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
  (program : Program) (registry : Staging.Recursive.Registry) (called : DeclarationInstantiation → Prop)

/-- The static receipts of every admitted callee: the registry scope of the
global view of its body instance at the empty dictionary, the uniqueness of its
nodes, and a supported shape of its body whose expressions are nested sites of
its own cache row. -/
def Callees : Prop :=
  ∀ {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance} {roots : List StatementId},
    called instantiation → Dynamic.FunctionInstantiates program instantiation bodyInstance →
    Dynamic.StatementRoots bodyInstance.source.roots roots →
    ∃ (child : Staging.Recursive.Scope) (named : SourceCoreGeneralFunctions.Function) (expected : TypeSystem.Ty),
      registry.Closure (Staging.Recursive.globalView bodyInstance [] roots) child ∧
      NodeOccurrencesUnique bodyInstance.source ∧
      Shape bodyInstance.source expected (Nested prepared named bodyInstance.source called) true roots

/-- Every admitted callee's original body derivation below a size is a staged
execution in the registry scope of its global view, which keeps the stored
functions of a mode. -/
def BodiesLift (bound : Nat) (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop) (guard : Prop) :
    Prop :=
  ∀ {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance} {roots : List StatementId},
    called instantiation → Dynamic.FunctionInstantiates program instantiation bodyInstance →
    Dynamic.StatementRoots bodyInstance.source.roots roots →
    ∃ child : Staging.Recursive.Scope,
      registry.Closure (Staging.Recursive.globalView bodyInstance [] roots) child ∧
      ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
        {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
        size < bound →
        SourceExecutionSize.FunctionStatementsExecute program size context [] bodyInstance.source environment before
          roots finalContext outcome after →
        Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
        Staging.Recursive.StatementsIn program registry true child context environment before roots finalContext
          (control outcome) after

/-- A direct call without requirements or coercions to a monomorphic
instantiation passes the empty dictionary. -/
theorem evidence_nil {context : SourceSemantics.Context} {caller produced : Dynamic.EvidenceEnvironment}
    (produces : Dynamic.DirectCallProducesEvidence context caller [] [] [] produced) : produced = [] := by
  cases produces with
  | intro coercions requirements produces =>
    rename_i selected contextual signatureRequirements
    have selectedNil : selected = [] := (List.append_eq_nil_iff.mp coercions.symm).1
    have contextualNil : contextual = [] := (List.append_eq_nil_iff.mp coercions.symm).2
    subst selectedNil contextualNil
    have signatureNil : signatureRequirements = [] := by
      simpa [coercionRequirementIds] using requirements.symm
    subst signatureNil
    cases produces
    rfl

/-- A scope whose guard frame is the call ledger of a sidecar of the plan. -/
def Framed (plan : SourceCompilationPlan.Plan) (scope : Staging.Recursive.Scope) : Prop :=
  ∃ sidecar : SourceCoreStageContracts.Sidecar, sidecar.plan = plan ∧ scope.guards = CallableLedger.frame sidecar

/-- Every closure scope of a registry is framed by the plan. -/
def ClosuresFramed (plan : SourceCompilationPlan.Plan) (registry : Staging.Recursive.Registry) : Prop :=
  ∀ {function : Dynamic.Closure} {child : Staging.Recursive.Scope}, registry.Closure function child →
    Framed plan child

/-- The named contract of every instantiation the plan records has as many
parameters as the program's body of the instantiation has inputs. -/
def Aligned (plan : SourceCompilationPlan.Plan) (program : Program) : Prop :=
  ∀ {instantiation : DeclarationInstantiation} {key : SourceSpecialization.SpecializationKey}
    {contract : SourceCoreStageContracts.Contract} {bodyInstance : Dynamic.BodyInstance},
    SourceCompilationPlan.exactInstantiationKey plan instantiation = .ok key →
    SourceCoreStageContracts.Contract.named plan key = .ok contract →
    Dynamic.FunctionInstantiates program instantiation bodyInstance →
    contract.parameters.length = bodyInstance.source.inputs.length

/-- The facts an indirect call of a scope's Source reads, asked only when the
Source has one: the mode, the scope's frame, the alignment of the plan with
the program, and that the mode stores no closure, as the lifting does not yet
apply one. -/
def IndirectFacts (plan : SourceCompilationPlan.Plan) (program : Program) (closures : Dynamic.Closure → Prop)
    (guard : Prop) (scope : Staging.Recursive.Scope) : Prop :=
  HasIndirect scope.source → guard ∧ Framed plan scope ∧ Aligned plan program ∧ ∀ function, ¬ closures function

/-- Every closure scope of the stages registry of a compilation is framed by its
plan: it is the scope of a sidecar the plan prepares. -/
theorem ClosuresFramed.stages (compiled : SourceCoreUnifiedCompilation.Compiled) :
    ClosuresFramed compiled.indexed.base.plan (SelectedCompilationPhysicalProgramSupport.stages compiled) := by
  intro function child selected
  obtain ⟨sidecar, _, issued, rfl, _⟩ := RecursiveNamedPreparedScopeCoherence.selected_canonical
    (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled) selected
  exact ⟨sidecar, (CallContractCertificates.sidecar_of_accepted issued).1, rfl⟩

private theorem signature_unique {signatures : List ProgramFunctionSignature}
    (unique : (signatures.map fun signature => signature.id).Nodup) {left right : ProgramFunctionSignature}
    (leftMem : left ∈ signatures) (rightMem : right ∈ signatures) (same : left.id = right.id) : left = right := by
  induction signatures with
  | nil => cases leftMem
  | cons head tail ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    simp only [List.mem_cons] at leftMem rightMem
    rcases leftMem with rfl | leftMem <;> rcases rightMem with rfl | rightMem
    · rfl
    · exact absurd (List.mem_map.mpr ⟨right, rightMem, same.symm⟩) absent
    · exact absurd (List.mem_map.mpr ⟨left, leftMem, same⟩) absent
    · exact ih unique leftMem rightMem

private theorem target_row {plan : SourceCompilationPlan.Plan} {instantiation : DeclarationInstantiation}
    {key : SourceSpecialization.SpecializationKey}
    (target : SourceCompilationPlan.exactInstantiationKey plan instantiation = .ok key) :
    ∃ row ∈ plan.specializations, SourceCompilationPlan.specializationMatchesInstantiation row instantiation ∧
      row.key = key := by
  unfold SourceCompilationPlan.exactInstantiationKey at target
  split at target
  · cases target
  · rename_i row filtered
    cases target
    have member : row ∈ [row] := .head _
    rw [← filtered] at member
    exact ⟨row, (List.mem_filter.mp member).1, (List.mem_filter.mp member).2, rfl⟩
  · cases target

/-- A well-formed program's bodies have the arity of the plan's named contracts:
the contract's parameters are the inputs of the plan's specialization, whose
comptime flags are the instantiation's, which are the flags of the inputs of
the program's body. -/
theorem Aligned.of_wellFormed {plan : SourceCompilationPlan.Plan} {program : Program}
    (wellFormed : ProgramWellFormed program) : Aligned plan program := by
  intro instantiation key contract bodyInstance target named instantiates
  obtain ⟨receipt⟩ := CallContractCertificates.named_of_accepted named
  obtain ⟨row, member, matching, rfl⟩ := target_row target
  have selected := CallableIndexedOwnedContextualDiagnosticSources.selected_filter
    (LambdaSourceAlignment.sidecar_lookup receipt.prepared)
  have same : row = receipt.sidecar.caller := by
    have filtered : row ∈ plan.specializations.filter (fun actual => decide (actual.key = row.key)) :=
      List.mem_filter.mpr ⟨member, by simp⟩
    rw [selected] at filtered
    exact List.mem_singleton.mp filtered
  have flags : row.function.typedBody.inputs.map (fun binder => binder.comptime) =
      instantiation.parameterComptime := by
    simp only [SourceCompilationPlan.specializationMatchesInstantiation, Bool.and_eq_true, beq_iff_eq] at matching
    exact matching.1.2
  cases instantiates with
  | @intro signature definition _ signatureMem definitionMem declarationEq ownerEq valid sourceEq _ _ =>
    cases valid with
    | intro catalogued cataloguedMem cataloguedEq _ _ _ _ comptimeEq _ =>
      cases wellFormed.functions_valid definition definitionMem with
      | @intro defining _ definingMem definingOwner bodyValid =>
        cases bodyValid with
        | intro _ _ _ _ _ _ _ _ inputFlags =>
          have sameSignature : catalogued = defining := signature_unique wellFormed.signatures.function_ids
            cataloguedMem definingMem (cataloguedEq.symm.trans (declarationEq.trans (ownerEq.symm.trans definingOwner)))
          subst sameSignature
          rw [receipt.parameters, sourceEq]
          have lengths := congrArg List.length (flags.trans (comptimeEq.trans inputFlags.symm))
          simp only [List.length_map] at lengths
          simpa [SourceCoreStageContracts.Sidecar.source, ← same, StructuralSubstitution.applyTypedSource] using lengths

variable {program registry called}
variable {plan : SourceCompilationPlan.Plan} {closures : Dynamic.Closure → Prop} {guard : Prop}

private theorem node_unique {scope : Staging.Recursive.Scope} (unique : NodeOccurrencesUnique scope.source)
    {id : ExpressionId} {left right : ExpressionNode} (first : ContainsExpression scope.source id left)
    (second : ContainsExpression scope.source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

/-- A sized value execution at a node without coercions that is not a local
read runs the node's form below the same size. -/
private theorem form_below {scope : Staging.Recursive.Scope} (unique : NodeOccurrencesUnique scope.source)
    {id : ExpressionId} {node : ExpressionNode} (found : scope.source.lookupExpression? id = some node)
    (coercions : node.coercions = []) (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
      before id value after) :
    ∃ formSize, formSize < size ∧ SourceExecutionSize.ExpressionFormEvaluates program formSize context
      scope.evidence scope.source environment before node.form node.requirements [] value after := by
  have contains := lookupExpression?_sound found
  cases trace with
  | intro traceFound form path =>
    cases node_unique unique traceFound contains
    rw [coercions] at path form
    cases path
    exact ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), form⟩
  | generalizedLocal traceFound formEq =>
    cases node_unique unique traceFound contains
    exact absurd formEq (notLocal _ _)

/-- A child of a step below a size is within a bound of the size. -/
private theorem child_le {children : List Nat} {child size bound : Nat} (member : child ∈ children)
    (below : SourceExecutionSize.stepSize children < size) (within : size ≤ bound) : child ≤ bound := by
  have := SourceExecutionSize.child_lt_stepSize member
  omega

/-- A literal or a reference to a builtin closure evaluates, at the same heap,
to data. -/
private theorem leaf_kept {form : ExpressionForm}
    (leaf : CompatibleExpressionLiterals.Atomic form ∨
      ∃ name function, form = .reference name (.builtinFunction function))
    {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {requirements : List RequirementId}
    {value : Dynamic.Value}
    (raw : SourceExecutionSize.ExpressionFormEvaluates program size context evidence source environment before form
      requirements [] value after) (kept : Kept plan closures guard before) :
    Kept plan closures guard after ∧ KeptValue plan closures guard value := by
  rcases leaf with atomic | ⟨_, _, rfl⟩
  · cases atomic with
    | unit =>
      cases raw with
      | tuple _ evaluated pack =>
        cases evaluated
        cases pack
        exact ⟨kept, fun _ => .unit⟩
    | bool => cases raw; exact ⟨kept, fun _ => .bool _⟩
    | word => cases raw with | literal _ constructs => exact ⟨kept, fun _ => Value.of_literal constructs⟩
    | integer =>
      cases raw with
      | integerLiteral _ constructs => exact ⟨kept, fun _ => Value.of_integer_literal constructs⟩
  · cases raw
    exact ⟨kept, fun _ => .builtin _⟩

/-- A local read evaluates to a stored value from a heap that keeps the stored
functions, and keeps them: an uninitialized mapping local holds the empty
mapping, and no cell of a stored heap holds a generalized closure. -/
private theorem read_kept {scope : Staging.Recursive.Scope} (unique : NodeOccurrencesUnique scope.source)
    {id : ExpressionId} {node : ExpressionNode} (found : scope.source.lookupExpression? id = some node)
    (coercions : node.coercions = []) {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
      before id value after) (kept : Kept plan closures guard before) :
    Kept plan closures guard after ∧ KeptValue plan closures guard value := by
  have contains := lookupExpression?_sound found
  cases trace with
  | intro traceFound raw path =>
    cases node_unique unique traceFound contains
    rw [coercions] at raw path
    cases path
    rw [form] at raw
    cases raw with
    | «local» _ _ read _ initialized => exact ⟨kept, fun active => ((kept active).read read).2 _ initialized⟩
    | localEmptyMapping _ _ _ _ _ _ write =>
      exact ⟨kept.writes (fun _ => Value.empty_mapping _ _) write, fun _ => Value.empty_mapping _ _⟩
  | generalizedLocal traceFound _ _ _ read descriptor _ _ path =>
    cases node_unique unique traceFound contains
    rw [coercions] at path
    cases path
    refine ⟨kept, fun active => ?_⟩
    rw [((kept active).read read).1] at descriptor
    cases descriptor

/-- A sized evaluation of an argument list has one value for each argument. -/
private theorem values_length : ∀ {ids : List ExpressionId} {size : Nat} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {values : List Dynamic.Value},
    SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids values after →
    values.length = ids.length
  | [], _, _, _, _, _, _, _, _, evaluated => by cases evaluated; rfl
  | _ :: _, _, _, _, _, _, _, _, _, evaluated => by
    cases evaluated with
    | cons _ tail => exact congrArg Nat.succ (values_length tail)

/-- A body invocation binds one argument to each of the body's inputs. -/
private theorem invokes_arity {size : Nat} {bodyInstance : Dynamic.BodyInstance}
    {evidence : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {arguments : List Dynamic.Value}
    {result : Dynamic.Value}
    (invokes : SourceExecutionSize.BodyInvokes program size bodyInstance evidence before arguments result after) :
    bodyInstance.source.inputs.length = arguments.length := by
  have binders : ∀ {environment final : Dynamic.Environment} {heap bound : Dynamic.Heap}
      {binders : List TypedBinder} {values : List Dynamic.Value},
      Dynamic.BindersAllocate environment heap binders values final bound → binders.length = values.length := by
    intro environment final heap bound binders values allocate
    induction allocate with
    | nil => rfl
    | cons _ _ ih => exact congrArg Nat.succ ih
  cases invokes with
  | returned _ _ _ allocate | unit _ _ _ _ allocate => exact binders allocate

/-- The value executions of nested arguments are staged executions. -/
private theorem arguments_value {scope : Staging.Recursive.Scope} {bound : Nat} :
    ∀ {ids : List ExpressionId},
    (∀ argument ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        argument value after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptValue plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before argument (.value value) after) →
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {values : List Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionsEvaluate program size context scope.evidence scope.source environment before ids
        values after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptValues plan closures guard values ∧
      Staging.Recursive.Expressions program registry scope context environment before ids (.values values) after := by
  intro ids
  induction ids with
  | nil =>
    intro _ size context environment before after values _ evaluated
    cases evaluated
    exact fun kept => ⟨kept, (fun _ _ member => nomatch member), .nil⟩
  | cons head rest ih =>
    intro lifts size context environment before after values within evaluated
    intro kept
    cases evaluated with
    | cons first tail =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have evaluated := lifts head List.mem_cons_self (by omega) first kept
      have remaining := ih (fun argument member => lifts argument (List.mem_cons_of_mem _ member)) (by omega) tail
        evaluated.1
      refine ⟨remaining.1, fun on value member => by
        rcases List.mem_cons.mp member with rfl | member
        · exact evaluated.2.1 on
        · exact remaining.2.1 on value member, ?_⟩
      exact .cons
        (lifts head List.mem_cons_self (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) first kept).2.2
        (ih (fun argument member => lifts argument (List.mem_cons_of_mem _ member)) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) tail evaluated.1).2.2

/-- The value execution of a memref composite's `lidx` is a staged execution,
given those of its array and its index. -/
private theorem reference_value {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) {bound : Nat} {id reference : ExpressionId}
    (site : CellAwareInvocationAcceptedMemrefSites.MemrefSite prepared named scope.source id reference)
    (first : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        site.base value after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptValue plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before site.base (.value value) after)
    (second : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        site.subscript value after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptValue plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before site.subscript (.value value)
        after) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        reference value after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptValue plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before reference (.value value) after := by
  intro size context environment before after value within trace
  intro kept
  obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.referenceFound site.referenceCoercions
    (fun name binder same => by rw [site.referenceForm] at same; cases same) trace
  rw [site.referenceForm, site.referenceRequirements] at raw
  cases raw with
  | elementRef _ baseEvaluates subscriptEvaluates counted inside =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    have base := first (by omega) baseEvaluates kept
    have subscript := second (by omega) subscriptEvaluates base.1
    refine ⟨subscript.1, fun _ => .memref _ _ _, ?_⟩
    exact .arrayResult ⟨site.referenceNode, lookupExpression?_sound site.referenceFound, site.referenceForm,
        site.referenceRequirements, site.referenceCoercions⟩ rfl
      (.cons base.2.2 (.cons subscript.2.2 .nil))
      (.elementRef counted inside)

/-- The value execution of an uncoerced indirect call is the staged application
of its callee's value, given those of its callee and its arguments, the lifting
of the admitted callee bodies below a bound of its size and the facts its call
reads. The mode holds, so the callee's value is stored: a builtin applies as
the staged builtin, and a named function is at a planned instantiation with the
empty dictionary, which `covers` admits, so its body lifts below the call, and
the scope's guard frame accepts its runtime contract at the call's arity; the
mode stores no closure. -/
private theorem indirect_value {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) {bound : Nat}
    (bodies : BodiesLift program registry called bound prepared.base.plan closures guard)
    (indirect : IndirectFacts prepared.base.plan program closures guard scope)
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    (site : CellAwareInvocationAcceptedIndirectSites.IndirectSite prepared named scope.source id callee ids metadata)
    (covers : CellAwareInvocationAcceptedIndirectPremises.CoversPlan prepared.base.plan called)
    (runtime : CellAwareInvocationAcceptedNestedTrees.RuntimeContracts prepared.base.plan)
    (first : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        callee value after →
      Kept prepared.base.plan closures guard before →
      Kept prepared.base.plan closures guard after ∧ KeptValue prepared.base.plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before callee (.value value) after)
    (arguments : ∀ argument ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context}
      {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        argument value after →
      Kept prepared.base.plan closures guard before →
      Kept prepared.base.plan closures guard after ∧ KeptValue prepared.base.plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before argument (.value value)
        after) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before id
        value after →
      Kept prepared.base.plan closures guard before →
      Kept prepared.base.plan closures guard after ∧ KeptValue prepared.base.plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before id (.value value) after := by
  intro size context environment before after value within trace kept
  obtain ⟨active, framed, aligned, noClosures⟩ := indirect ⟨id, site.node, site.found, callee, ids, metadata, site.form⟩
  have contains := lookupExpression?_sound site.found
  have occurrence : Staging.Recursive.Occurrence scope id (.call callee ids (.indirect metadata)) :=
    ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
  cases trace with
  | generalizedLocal found formEq =>
    cases node_unique unique found contains
    rw [site.form] at formEq
    cases formEq
  | intro found form coercions =>
    cases node_unique unique found contains
    rw [site.coercions] at coercions
    cases coercions
    rw [site.form, site.requirements, site.coercions] at form
    cases form with
    | indirectCall _ calleeEvaluates argumentsEvaluate packBefore argumentCoercions packAfter sourceArity appliedArity
        applies =>
      rw [site.uncoerced] at argumentCoercions
      cases argumentCoercions
      obtain rfl := Dynamic.ValuesPack.injective_of_length_eq packAfter packBefore
        (appliedArity.trans (sourceArity.symm.trans (values_length argumentsEvaluate).symm))
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
      have lifted := first (by omega) calleeEvaluates kept
      have passed := arguments_value (registry := registry) arguments (by omega) argumentsEvaluate lifted.1
      cases applies with
      | builtin applied =>
        refine ⟨passed.1, fun _ => Value.of_builtin applied, ?_⟩
        exact .applied occurrence site.uncoerced lifted.2.2 (.builtin _) passed.2.2 sourceArity (.builtin applied)
      | @global _ _ _ _ _ _ function _ _ bodyInstance instantiates invocationEq covered invokes =>
        have stored := lifted.2.1 active
        cases stored with
        | global planned empty =>
          obtain ⟨key, target⟩ := planned
          obtain ⟨contract, issued, _⟩ := runtime.contract target
          have accepted : Staging.CallBoundary.GuardAccepts scope.guards id ids (.global function) := by
            obtain ⟨sidecar, samePlan, guards⟩ := framed
            rw [guards]
            refine .contract (contract := CallContractCertificates.semanticContract contract) ?_
              (runtime.accepts target issued ((aligned target issued instantiates).trans
                ((invokes_arity invokes).trans (values_length argumentsEvaluate))) _)
            show CallableLedger.Binds sidecar.plan _ _
            rw [samePlan]
            exact .named target issued
          subst invocationEq
          obtain ⟨instantiation, evidence⟩ := function
          dsimp only at empty
          subst empty
          cases invokes with
          | returned _ rootsEq parameters allocate execute returned =>
            obtain ⟨child, closure, lifts⟩ := bodies (covers _ key target) instantiates rootsEq
            have ran := lifts (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within ⊢
              omega) execute (passed.1.binders passed.2.1 allocate)
            subst returned
            refine ⟨ran.1, ran.2.1, ?_⟩
            exact .applied occurrence site.uncoerced lifted.2.2 accepted passed.2.2 sourceArity
              (.global instantiates covered rootsEq closure parameters allocate ran.2.2 .returned)
          | unit _ resultUnit rootsEq parameters allocate execute fellThrough =>
            obtain ⟨child, closure, lifts⟩ := bodies (covers _ key target) instantiates rootsEq
            have ran := lifts (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within ⊢
              omega) execute (passed.1.binders passed.2.1 allocate)
            obtain ⟨finalEnvironment, rfl⟩ := fellThrough
            refine ⟨ran.1, fun _ => .unit, ?_⟩
            exact .applied occurrence site.uncoerced lifted.2.2 accepted passed.2.2 sourceArity
              (.global instantiates covered rootsEq closure parameters allocate ran.2.2
                (by rw [resultUnit]; exact .unit))
      | closure | closureUnit =>
        cases lifted.2.1 active with
        | closure stored => exact absurd stored (noClosures _)

/-- A sized value execution of a nested site is a staged execution with the
same value and heap, given the lifting of the admitted callee bodies below a
bound of its size and, in a Source with an indirect call, the facts its calls
read. It keeps the stored functions, and its value is stored. -/
theorem nested_value {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) {bound : Nat}
    (bodies : BodiesLift program registry called bound prepared.base.plan closures guard)
    (indirect : IndirectFacts prepared.base.plan program closures guard scope)
    {id : ExpressionId} (nested : Nested prepared named scope.source called id) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before id
        value after →
      Kept prepared.base.plan closures guard before →
      Kept prepared.base.plan closures guard after ∧ KeptValue prepared.base.plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before id (.value value) after := by
  induction nested with
  | literal site atomic =>
    intro size context environment before after value _ trace
    intro kept
    obtain ⟨_, _, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [same] at atomic; cases atomic) trace
    refine ⟨(leaf_kept (.inl atomic) raw kept).1, (leaf_kept (.inl atomic) raw kept).2, ?_⟩
    exact expression_value unique (.literal site atomic) trace.sound
  | read site form =>
    intro size context environment before after value _ trace
    intro kept
    have read := read_kept unique site.found site.coercions form trace kept
    refine ⟨read.1, read.2, ?_⟩
    exact expression_value unique (.read site form) trace.sound
  | unary site form _ child =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | unary layout operand applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive applied =>
        refine ⟨(child (child_le (by simp) formBelow within) operand kept).1, fun _ => Value.of_unary applied, ?_⟩
        exact .unary (occurrence site form (fun _ _ same => by cases same))
          (child (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) operand kept).2.2 applied
      | method _ selected _ => cases selected
  | binary site form _ _ left right =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | binaryShortCircuit _ first circuit _ =>
      refine ⟨(left (child_le (by simp) formBelow within) first kept).1, fun _ => Value.of_short circuit, ?_⟩
      exact .binaryShortCircuit (occurrence site form (fun _ _ same => by cases same))
        (left (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2 circuit
    | binaryEvaluateRight layout first continues second applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive applied =>
        have stagedLeft := left (child_le (by simp) formBelow within) first kept
        refine ⟨(right (child_le (by simp) formBelow within) second stagedLeft.1).1, fun _ => Value.of_binary applied,
          ?_⟩
        exact .binary (occurrence site form (fun _ _ same => by cases same))
          (left (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) first kept).2.2 continues
          (right (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) second stagedLeft.1).2.2 applied
      | method _ selected _ => cases selected
  | conditional site form _ _ _ test yes no =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | conditionalTrue _ first second =>
      have tested := test (child_le (by simp) formBelow within) first kept
      have chosen := yes (child_le (by simp) formBelow within) second tested.1
      refine ⟨chosen.1, chosen.2.1, ?_⟩
      exact .conditional (occurrence site form (fun _ _ same => by cases same))
        (test (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (yes (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second tested.1).2.2
    | conditionalFalse _ first second =>
      have tested := test (child_le (by simp) formBelow within) first kept
      have chosen := no (child_le (by simp) formBelow within) second tested.1
      refine ⟨chosen.1, chosen.2.1, ?_⟩
      exact .conditional (occurrence site form (fun _ _ same => by cases same))
        (test (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (no (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second tested.1).2.2
  | group site form _ child =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | group _ inner =>
      have grouped := child (child_le (by simp) formBelow within) inner kept
      refine ⟨grouped.1, grouped.2.1, ?_⟩
      exact .group (occurrence site form (fun _ _ same => by cases same))
        (child (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) inner kept).2.2
  | pair site form _ _ left right =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | tuple _ elements pack =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second tail =>
          cases tail
          cases pack with
          | cons tail =>
            cases tail
            have below := formBelow
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            have stagedLeft := left (by omega) first kept
            have stagedRight := right (by omega) second stagedLeft.1
            refine ⟨stagedRight.1, fun on => .product (stagedLeft.2.1 on) (stagedRight.2.1 on), ?_⟩
            exact .pair (occurrence site form (fun _ _ same => by cases same))
              (left (by
                simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
                omega) first kept).2.2
              (right (by
                simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
                omega) second stagedLeft.1).2.2
  | @call id callee ids instantiation site selected _ arguments =>
    intro size context environment before after value within trace
    intro kept
    have contains := lookupExpression?_sound site.found
    cases trace with
    | intro found form coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      rw [site.form, site.requirements, site.coercions] at form
      cases form with
      | directCall calleeContains calleeForm calleeRequirements calleeCoercions valid evaluated produced applies =>
        have argumentsLifted := arguments_value (registry := registry) arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) evaluated kept
        have stagedArguments := argumentsLifted.2.2
        have nilEvidence := evidence_nil (site.monomorphic.predicates ▸ produced)
        subst nilEvidence
        cases applies with
        | global instantiates invocationEq covers invokes =>
          cases invokes with
          | returned _ rootsEq parameters allocate execute returned =>
            obtain ⟨child, closure, lifts⟩ := bodies selected instantiates rootsEq
            have ran := lifts (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within ⊢
              omega) execute (argumentsLifted.1.binders argumentsLifted.2.1 allocate)
            have staged := ran.2.2
            subst returned
            refine ⟨ran.1, ran.2.1, ?_⟩
            exact .directApplied ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
              ⟨_, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩ valid stagedArguments produced
              (.global instantiates covers rootsEq closure parameters allocate staged .returned)
          | unit _ resultUnit rootsEq parameters allocate execute fellThrough =>
            obtain ⟨child, closure, lifts⟩ := bodies selected instantiates rootsEq
            have ran := lifts (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within ⊢
              omega) execute (argumentsLifted.1.binders argumentsLifted.2.1 allocate)
            have staged := ran.2.2
            obtain ⟨finalEnvironment, rfl⟩ := fellThrough
            refine ⟨ran.1, fun _ => .unit, ?_⟩
            exact .directApplied ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
              ⟨_, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩ valid stagedArguments produced
              (.global instantiates covers rootsEq closure parameters allocate staged (by rw [resultUnit]; exact .unit))
    | generalizedLocal found formEq =>
      cases node_unique unique found contains
      rw [site.form] at formEq
      cases formEq
  | @conversion id callee argument function target site _ child =>
    intro size context environment before after value within trace
    intro kept
    have contains := lookupExpression?_sound site.found
    cases trace with
    | intro found form coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      rw [site.form, site.requirements, site.coercions] at form
      cases form with
      | builtinCall layout evaluated applies =>
        have argumentsLifted := arguments_value (registry := registry)
          (fun other member => by
            cases List.mem_singleton.mp member
            exact child) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) evaluated kept
        have stagedArguments := argumentsLifted.2.2
        cases applies with
        | builtin applied =>
          refine ⟨argumentsLifted.1, fun _ => Value.of_builtin applied, ?_⟩
          exact .builtinApplied ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
            stagedArguments (.builtin applied)
    | generalizedLocal found formEq =>
      cases node_unique unique found contains
      rw [site.form] at formEq
      cases formEq
  | index site form _ _ base key =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | indexFound _ first second lookup =>
      have stagedBase := base (child_le (by simp) formBelow within) first kept
      refine ⟨(key (child_le (by simp) formBelow within) second stagedBase.1).1,
        fun on => (stagedBase.2.1 on).of_mapping_lookup lookup, ?_⟩
      exact .indexResult (occurrence site form (fun _ _ same => by cases same))
        (base (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (key (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second stagedBase.1).2.2 (.found rfl lookup)
    | indexDefault _ first second absent defaulted =>
      have stagedBase := base (child_le (by simp) formBelow within) first kept
      refine ⟨(key (child_le (by simp) formBelow within) second stagedBase.1).1, fun _ => Value.of_default defaulted,
        ?_⟩
      exact .indexResult (occurrence site form (fun _ _ same => by cases same))
        (base (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (key (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second stagedBase.1).2.2 (.default rfl absent defaulted)
  | builtinValue site form =>
    intro size context environment before after value _ trace
    intro kept
    obtain ⟨_, _, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    refine ⟨(leaf_kept (.inr ⟨_, _, form⟩) raw kept).1, (leaf_kept (.inr ⟨_, _, form⟩) raw kept).2, ?_⟩
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound site.found)
      (by rw [form]; exact .reference _ _) site.coercions
      (fun name binder same => by rw [form] at same; cases same) (.value trace.sound)
  | @builtin id callee ids function site _ arguments =>
    intro size context environment before after value within trace
    intro kept
    have contains := lookupExpression?_sound site.found
    cases trace with
    | intro found form coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      rw [site.form, site.requirements, site.coercions] at form
      cases form with
      | builtinCall layout evaluated applies =>
        have argumentsLifted := arguments_value (registry := registry) arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) evaluated kept
        have stagedArguments := argumentsLifted.2.2
        cases applies with
        | builtin applied =>
          refine ⟨argumentsLifted.1, fun _ => Value.of_builtin applied, ?_⟩
          exact .builtinApplied ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
            stagedArguments (.builtin applied)
    | generalizedLocal found formEq =>
      cases node_unique unique found contains
      rw [site.form] at formEq
      cases formEq
  | @tuple id ids site _ elements =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    cases raw with
    | tuple _ evaluated pack =>
      have lifted :=
        arguments_value (registry := registry) elements (child_le (by simp) formBelow within) evaluated kept
      refine ⟨lifted.1, fun on => Value.of_pack pack (lifted.2.1 on), ?_⟩
      exact .tupleValue ⟨site.node, lookupExpression?_sound site.found, site.form, site.requirements, site.coercions⟩
        (arguments_value (registry := registry) elements (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated kept).2.2 pack
  | @constructor id instantiation ids site _ arguments =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    cases raw with
    | constructor _ valid evaluated =>
      have lifted :=
        arguments_value (registry := registry) arguments (child_le (by simp) formBelow within) evaluated kept
      refine ⟨lifted.1, fun on => .constructed (lifted.2.1 on), ?_⟩
      exact .constructorValue
        ⟨site.node, lookupExpression?_sound site.found, site.form, site.requirements, site.coercions⟩ valid
        (arguments_value (registry := registry) arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated kept).2.2
  | @array id form site _ children =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (CellAwareInvocationAcceptedArraySites.not_local site) trace
    have occurrence : Staging.Recursive.Occurrence scope id form :=
      ⟨site.node, lookupExpression?_sound site.found, site.formEq, site.requirements, site.coercions⟩
    rw [site.formEq, site.requirements] at raw
    cases site.shape with
    | arrayLength base =>
      cases raw with
      | arrayLength _ first counted =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have lifted := children base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        refine ⟨lifted.1, fun _ => .word _, ?_⟩
        exact .arrayResult occurrence rfl
          (.cons lifted.2.2 .nil)
          (.arrayLength counted)
    | arrayIndex base subscript =>
      cases raw with
      | arrayIndex _ first second reads =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := children base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        have stagedIndex :=
          children subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second stagedBase.1
        refine ⟨stagedIndex.1, fun on => (stagedIndex.1 on).view_reads reads, ?_⟩
        exact .arrayResult occurrence rfl
          (.cons stagedBase.2.2
            (.cons stagedIndex.2.2 .nil))
          (.arrayIndex reads)
    | elementRef base subscript =>
      cases raw with
      | elementRef _ first second counted inside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := children base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        have stagedIndex :=
          children subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second stagedBase.1
        refine ⟨stagedIndex.1, fun _ => .memref _ _ _, ?_⟩
        exact .arrayResult occurrence rfl
          (.cons stagedBase.2.2
            (.cons stagedIndex.2.2 .nil))
          (.elementRef counted inside)
    | arraySlice base start stop =>
      cases raw with
      | arraySlice _ first bounds counted chosen ordered inside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := children base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        have stagedBounds := arguments_value (registry := registry) (ids := start.toList ++ stop.toList)
          (fun bound member => children bound (List.mem_cons_of_mem _ member)) (by omega) bounds stagedBase.1
        refine ⟨stagedBounds.1, fun on => .arraySlice _ _ (stagedBase.2.1 on), ?_⟩
        exact .arrayResult occurrence rfl
          (.cons stagedBase.2.2
            stagedBounds.2.2)
          (.arraySlice counted chosen ordered inside)
    | newArray length _ =>
      cases raw with
      | newArray _ first fits default allocates =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have lifted := children length (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        refine ⟨lifted.1.new_array default allocates, fun _ => .arrayRef _ _, ?_⟩
        exact .arrayResult occurrence rfl
          (.cons lifted.2.2 .nil)
          (.newArray fits default allocates)
    | arrayLiteral _ _ =>
      cases raw with
      | arrayLiteral _ evaluated allocates =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have lifted := arguments_value (registry := registry) children (by omega) evaluated kept
        refine ⟨lifted.1.allocates (fun on => .arrayObject (lifted.2.1 on)) allocates, fun _ => .arrayRef _ _, ?_⟩
        exact .arrayResult occurrence rfl
          lifted.2.2 (.arrayLiteral allocates)
    | @toArray _ _ slice _ _ _ _ _ _ _ =>
      cases raw with
      | toArray _ first copies allocates =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have lifted := children slice (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        refine ⟨lifted.1.allocates (fun on => .arrayObject ((lifted.1 on).view_copies copies)) allocates,
          fun _ => .arrayRef _ _, ?_⟩
        exact .arrayResult occurrence rfl
          (.cons lifted.2.2 .nil)
          (.toArray copies allocates)
  | @memrefLoad id reference site form _ _ first second =>
    intro size context environment before after value within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, site.requirements] at raw
    cases raw with
    | memrefLoad _ referenceEvaluates reads =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      have lifted := reference_value prepared unique site first second (by omega) referenceEvaluates kept
      refine ⟨lifted.1, fun on => (lifted.1 on).view_reads reads, ?_⟩
      exact .arrayResult ⟨site.node, lookupExpression?_sound site.found, form, site.requirements, site.coercions⟩ rfl
        (.cons lifted.2.2 .nil)
        (.memrefLoad reads)
  | @memrefStore id reference value site form _ _ _ first second third =>
    intro size context environment before after result within trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, site.requirements] at raw
    cases raw with
    | memrefStore _ referenceEvaluates valueEvaluates read current replace write =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      have lifted := reference_value prepared unique site first second (by omega) referenceEvaluates kept
      have stored := third (by omega) valueEvaluates lifted.1
      refine ⟨stored.1.stores stored.2.1 read current replace write, fun _ => .unit, ?_⟩
      exact .arrayResult ⟨site.node, lookupExpression?_sound site.found, form, site.requirements, site.coercions⟩ rfl
        (.cons lifted.2.2
          (.cons stored.2.2 .nil))
        (.memrefStore read current replace write)
  | namedValue site planned =>
    intro size context environment before after value _ trace
    intro kept
    obtain ⟨_, _, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    cases raw with
    | declaration _ _ produced =>
      rw [site.monomorphic.predicates] at produced
      cases produced
      exact ⟨kept, fun _ => .global planned rfl, CellAwareInvocationAcceptedValueLifting.value_lift unique site trace⟩
  | indirect site covers _ runtime _ _ first arguments =>
    exact indirect_value prepared unique bodies indirect site covers runtime first arguments

/-- The value lifting of every nested site below a size, given the lifting of
the callee bodies below it and the facts the Source's indirect calls read. -/
theorem nested_roots {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) {bound : Nat}
    (bodies : BodiesLift program registry called bound prepared.base.plan closures guard)
    (indirect : IndirectFacts prepared.base.plan program closures guard scope) :
    ChildLifts program registry scope (Nested prepared named scope.source called) bound prepared.base.plan closures
      guard := by
  intro id nested size context environment before after value below trace
  exact nested_value prepared unique bodies indirect nested (Nat.le_of_lt below) trace

/-- Every admitted callee's original body derivation is a staged execution at
every size: one strong induction on the size across bodies, given, for a body
with an indirect call, the mode, the frames of the registry's closure scopes,
the alignment of the plan with the program and that the mode stores no
closure. -/
theorem bodies (callees : Callees prepared program registry called)
    (indirect : ∀ {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance},
      called instantiation → Dynamic.FunctionInstantiates program instantiation bodyInstance →
      HasIndirect bodyInstance.source →
      guard ∧ ClosuresFramed prepared.base.plan registry ∧ Aligned prepared.base.plan program ∧
        ∀ function, ¬ closures function)
    (bound : Nat) :
    BodiesLift program registry called bound prepared.base.plan closures guard := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro instantiation bodyInstance statements admitted instantiates rootsEq
    obtain ⟨child, named, expected, closure, unique, shape⟩ := callees admitted instantiates rootsEq
    refine ⟨child, closure, ?_⟩
    intro size context environment before after finalContext outcome below trace
    have sourceEq : child.source = bodyInstance.source := registry.source closure
    have evidenceEq : child.evidence = [] := registry.evidence closure
    have childUnique : NodeOccurrencesUnique child.source := sourceEq ▸ unique
    have childShape : Shape child.source expected (Nested prepared named child.source called) true statements := by
      rw [sourceEq]
      exact shape
    have facts : IndirectFacts prepared.base.plan program closures guard child := fun indirectAt =>
      have read := indirect admitted instantiates (sourceEq ▸ indirectAt)
      ⟨read.1, read.2.1 closure, read.2.2⟩
    have lift : ChildLifts program registry child (Nested prepared named child.source called) size prepared.base.plan
        closures guard :=
      nested_roots prepared childUnique (ih size below) facts
    refine CellAwareInvocationAcceptedSizedLifting.statements childUnique lift childShape (Nat.le_refl size) ?_
    show SourceExecutionSize.FunctionStatementsExecute program size context child.evidence child.source environment
      before statements finalContext outcome after
    rw [sourceEq, evidenceEq]
    exact trace

/-- An ordinary function-body execution of a supported list whose expressions
are nested sites is a staged execution with the same context, outcome and
heap, at any scope with the execution's Source and evidence, given the static
receipts of the admitted callees and, in a family with an indirect call, the
stored functions of its starting heap, which hold no closure, the frames of its
scope and of the registry's closure scopes and the alignment of the plan with
the program. -/
theorem body {scope : Staging.Recursive.Scope} {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
    (sourceEq : scope.source = source) (evidenceEq : scope.evidence = evidence)
    (unique : NodeOccurrencesUnique source) (callees : Callees prepared program registry called)
    (framed : FamilyIndirect program called source → Framed prepared.base.plan scope)
    (closures : FamilyIndirect program called source → ClosuresFramed prepared.base.plan registry)
    (aligned : FamilyIndirect program called source → Aligned prepared.base.plan program)
    {named : SourceCoreGeneralFunctions.Function} {expected : TypeSystem.Ty} {statements : List StatementId}
    (shape : Shape source expected (Nested prepared named source called) true statements)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (kept : Kept prepared.base.plan (fun _ => False) (FamilyIndirect program called source) before)
    (trace : Dynamic.FunctionStatementsExecute program context evidence source environment before statements
      finalContext outcome after) :
    ∃ size, Staging.Recursive.Size.Statements program registry size scope context environment before statements
      finalContext (control outcome) after := by
  subst sourceEq evidenceEq
  obtain ⟨size, sized⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size trace
  have lift : ChildLifts program registry scope (Nested prepared named scope.source called) size prepared.base.plan
      (fun _ => False) (FamilyIndirect program called scope.source) :=
    nested_roots prepared unique
      (bodies prepared callees (fun admitted instantiates indirect =>
        have family : FamilyIndirect program called scope.source := Or.inr ⟨_, _, admitted, instantiates, indirect⟩
        ⟨family, closures family, aligned family, fun _ none => none⟩) size)
      (fun indirect => ⟨Or.inl indirect, framed (Or.inl indirect), aligned (Or.inl indirect), fun _ none => none⟩)
  exact Staging.Recursive.Size.Statements.of_trace
    (CellAwareInvocationAcceptedSizedLifting.statements unique lift shape (Nat.le_refl size) sized kept).2.2

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallLifting
end

section
/-! Original fault executions of bodies whose expressions are nested sites are
staged fault executions with the same reason and heap. A fault keeps its reason
from the innermost failing rule to the body, and the staged traces express
every reason but two (`Expressible`): a type mismatch, since a condition whose
value is not a boolean has no staged rule, and a missing declaration, since a
call of a function without a catalogued body has none. A direct call's staged
rules read its callee's occurrence, which the original rule of a fault after
its arguments does not record, so the Source's direct calls are required to
have a plain callee node and the Source no indirect call (`CalleesPlain`, a
finite check), so a family with one keeps no fault lifting; a missing node is
then excluded, as every site is a node of the Source. They also read the
validity of the call's instantiation at the caller's context, which holds at a
monomorphic instantiation once that context keeps the program's signatures. A
callee body's fault is lifted by the strong induction on the size that lifts
its values. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFaultLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedCallLifting (BodiesLift evidence_nil nested_value child_le)
open CellAwareInvocationAcceptedStoredFunctions (Kept KeptValue)

/-- The fault reasons that the staged traces express: all but a type mismatch
and a missing declaration. -/
def Expressible : Dynamic.SemanticFault → Prop
  | .typeMismatch _ _ | .missingDeclaration _ => False
  | _ => True

/-- A node that refers to `instantiation` at `target` without requirements or
coercions. -/
def CalleeAt (target : ExpressionId) (instantiation : DeclarationInstantiation) : Node → Bool
  | .expression callee =>
    decide (callee.id = target) && callee.requirements.isEmpty && callee.coercions.isEmpty &&
      match callee.form with
      | .reference _ (.declaration other) => decide (other = instantiation)
      | _ => false
  | .statement _ => false

/-- A direct call at a node has its callee among `nodes`, and the node is not an
indirect call. -/
def CalleePlainAt (nodes : List Node) : Node → Bool
  | .expression caller =>
    match caller.form with
    | .call target _ (.declaration instantiation) => nodes.any (CalleeAt target instantiation)
    | .call _ _ (.indirect _) => false
    | _ => true
  | .statement _ => true

/-- Every direct call of a Source has a callee node that refers to the call's
declaration without requirements or coercions, and the Source has no indirect
call. -/
def CalleesPlain (source : TypedSource) : Prop :=
  source.nodes.all (CalleePlainAt source.nodes) = true

instance (source : TypedSource) : Decidable (CalleesPlain source) :=
  inferInstanceAs (Decidable (source.nodes.all (CalleePlainAt source.nodes) = true))

/-- A Source whose calls are plain has no indirect call. -/
theorem CalleesPlain.no_indirect {source : TypedSource} (plain : CalleesPlain source) :
    ¬ CellAwareInvocationAcceptedStoredFunctions.HasIndirect source := by
  rintro ⟨id, node, found, callee, ids, metadata, form⟩
  have atCaller := List.all_eq_true.mp plain (.expression node) (lookupExpression?_sound found).1
  simp [CalleePlainAt, form] at atCaller

section Sites
variable {program : Program} {scope : Staging.Recursive.Scope}

private theorem atomic_form {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    Staging.Recursive.AtomicForm form := by
  cases atomic <;> constructor

private theorem atomic_not_local {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form)
    (name : String) (binder : Resolved.LocalId) : form ≠ .reference name (.local binder) := by
  cases atomic <;> intro same <;> cases same

private theorem calleeAt_sound {target : ExpressionId} {instantiation : DeclarationInstantiation} {node : Node}
    (found : CalleeAt target instantiation node = true) :
    ∃ (callee : ExpressionNode) (name : String), node = .expression callee ∧ callee.id = target ∧
      callee.form = .reference name (.declaration instantiation) ∧ callee.requirements = [] ∧
      callee.coercions = [] := by
  cases node with
  | statement _ => simp [CalleeAt] at found
  | expression callee =>
    simp only [CalleeAt] at found
    cases form : callee.form with
    | reference name resolution =>
      cases resolution with
      | declaration other =>
        rw [form] at found
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at found
        obtain ⟨⟨⟨idEq, requirements⟩, coercions⟩, same⟩ := found
        exact ⟨callee, name, rfl, idEq, by rw [form, same], requirements, coercions⟩
      | _ =>
        rw [form] at found
        simp at found
    | _ =>
      rw [form] at found
      simp at found

/-- A direct call's callee is an occurrence without requirements or
coercions. -/
private theorem callee_occurrence (plain : CalleesPlain scope.source)
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (contains : ContainsExpression scope.source id node)
    (form : node.form = .call callee ids (.declaration instantiation)) :
    ∃ name, Staging.Recursive.Occurrence scope callee (.reference name (.declaration instantiation)) := by
  have atCaller := List.all_eq_true.mp plain (.expression node) contains.1
  simp only [CalleePlainAt, form] at atCaller
  obtain ⟨calleeNode, member, found⟩ := List.any_eq_true.mp atCaller
  obtain ⟨calleeExpression, name, rfl, idEq, calleeForm, requirements, coercions⟩ := calleeAt_sound found
  exact ⟨name, calleeExpression, ⟨member, idEq⟩, calleeForm, requirements, coercions⟩

/-- A monomorphic instantiation of a program function is valid at every context
with the program's signatures. -/
private theorem valid_at {context : SourceSemantics.Context}
    {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance}
    (signatures : context.signatures = program.signatures)
    (substitution : instantiation.parameterSubstitution = [])
    (instantiates : Dynamic.FunctionInstantiates program instantiation bodyInstance) :
    SourceSemantics.DeclarationInstantiation.Valid context instantiation := by
  cases instantiates with
  | intro _ _ _ _ valid =>
    cases valid with
    | intro signature member declaration exactness _ type predicates parameterComptime returnComptime =>
      refine .intro signature (by rw [signatures]; exact member) declaration exactness ?_ type predicates
        parameterComptime returnComptime
      intro parameter replacement inMember
      rw [substitution] at inMember
      cases inMember

/-- The empty dictionary covers the body of a program function whose
instantiation has no predicates. -/
private theorem covers_nil {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance}
    (instantiates : Dynamic.FunctionInstantiates program instantiation bodyInstance)
    (predicates : instantiation.predicates = []) :
    Dynamic.EvidenceEnvironment.Covers bodyInstance.context [] := by
  cases instantiates with
  | intro _ _ _ _ _ _ _ contextEq =>
    rw [contextEq]
    refine ⟨fun _ _ looks => (by cases looks), ?_⟩
    intro predicate member
    simp [declarationContext, SourceSemantics.Context.withResidualTypeVariables,
      SourceSemantics.Context.withSolvedRequirements, SourceSemantics.Context.withAssumptions,
      predicates] at member

/-- A program function's body context keeps the program's signatures. -/
private theorem body_signatures {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance}
    (instantiates : Dynamic.FunctionInstantiates program instantiation bodyInstance) :
    bodyInstance.context.signatures = program.signatures := by
  cases instantiates with
  | intro _ _ _ _ _ _ _ contextEq =>
    rw [contextEq]
    rfl

/-- A sized fault at a node without coercions that is not a local read faults
in the node's form below the same size. -/
private theorem form_fault (unique : NodeOccurrencesUnique scope.source)
    {id : ExpressionId} {node : ExpressionNode} (found : scope.source.lookupExpression? id = some node)
    (coercions : node.coercions = []) (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment
      before id reason after) :
    ∃ formSize, formSize < size ∧ SourceExecutionSize.ExpressionFormFaults program formSize context
      scope.evidence scope.source environment before node.form node.requirements [] reason after := by
  have contains := lookupExpression?_sound found
  cases trace with
  | missing absent => exact (Dynamic.ExpressionAbsentIn.excludes_contains absent contains).elim
  | form traceFound fault =>
    cases CellAwareInvocationAcceptedCallLifting.node_unique unique traceFound contains
    rw [coercions] at fault
    exact ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), fault⟩
  | coercion traceFound _ fault =>
    cases CellAwareInvocationAcceptedCallLifting.node_unique unique traceFound contains
    rw [coercions] at fault
    cases fault
  | generalizedLocalRequirement traceFound formEq =>
    cases CellAwareInvocationAcceptedCallLifting.node_unique unique traceFound contains
    exact absurd formEq (notLocal _ _)
  | generalizedLocalCoercion traceFound formEq =>
    cases CellAwareInvocationAcceptedCallLifting.node_unique unique traceFound contains
    exact absurd formEq (notLocal _ _)

end Sites

variable {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
  (program : Program) (registry : Staging.Recursive.Registry) (called : DeclarationInstantiation → Prop)

/-- The staged fault lifting of the expressions that `child` admits, below a
size, at contexts with the program's signatures, from heaps that keep the stored
functions of a mode. -/
def ChildFaultLifts (scope : Staging.Recursive.Scope) (child : ExpressionId → Prop) (bound : Nat)
    (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop) (guard : Prop) : Prop :=
  ∀ {id : ExpressionId}, child id → ∀ {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault},
    size < bound → context.signatures = program.signatures → Expressible reason →
    SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before id
      reason after →
    Kept plan closures guard before →
    Staging.Recursive.Expression program registry scope context environment before id (.fault (.semantic reason)) after

/-- The direct calls of every admitted callee's body have plain callees, and no
such body has an indirect call. -/
def CalleesFault : Prop :=
  ∀ {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance},
    called instantiation → Dynamic.FunctionInstantiates program instantiation bodyInstance →
    CalleesPlain bodyInstance.source

/-- Every admitted callee's original body fault with an expressible reason
below a size, at a context with the program's signatures and from a heap that
keeps the stored functions of a mode, is a staged fault execution in the
registry scope of its global view. -/
def BodiesFaultLift (bound : Nat) (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop)
    (guard : Prop) : Prop :=
  ∀ {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance} {roots : List StatementId},
    called instantiation → Dynamic.FunctionInstantiates program instantiation bodyInstance →
    Dynamic.StatementRoots bodyInstance.source.roots roots →
    ∃ child : Staging.Recursive.Scope,
      registry.Closure (Staging.Recursive.globalView bodyInstance [] roots) child ∧
      ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
        {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
        size < bound → context.signatures = program.signatures → Expressible reason →
        SourceExecutionSize.FunctionStatementsFault program size context [] bodyInstance.source environment before
          roots finalContext reason after →
        Kept plan closures guard before →
        Staging.Recursive.StatementsIn program registry true child context environment before roots finalContext
          (.fault (.semantic reason)) after

variable {program registry called}
variable {plan : SourceCompilationPlan.Plan} {closures : Dynamic.Closure → Prop} {guard : Prop}

/-- The fault executions of argument lists whose elements lift. -/
private theorem arguments_fault {scope : Staging.Recursive.Scope} {bound : Nat} :
    ∀ {ids : List ExpressionId},
    (∀ argument ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        argument value after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptValue plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before argument (.value value) after) →
    (∀ argument ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before
        argument reason after →
      Kept plan closures guard before →
      Staging.Recursive.Expression program registry scope context environment before argument
        (.fault (.semantic reason)) after) →
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionsFault program size context scope.evidence scope.source environment before ids
        reason after →
      Kept plan closures guard before →
      Staging.Recursive.Expressions program registry scope context environment before ids
        (.fault (.semantic reason)) after := by
  intro ids
  induction ids with
  | nil =>
    intro _ _ size context environment before after reason _ _ _ failed
    cases failed
  | cons head rest ih =>
    intro values faults size context environment before after reason within signatures expressible failed
    intro kept
    cases failed with
    | head fault =>
      exact .headFault (faults head List.mem_cons_self (by
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
        omega) signatures expressible fault kept)
    | tail first tail =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have evaluated := values head List.mem_cons_self (by omega) first kept
      exact .tailFault
        (values head List.mem_cons_self (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) first kept).2.2
        (ih (fun argument member => values argument (List.mem_cons_of_mem _ member))
          (fun argument member => faults argument (List.mem_cons_of_mem _ member)) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) signatures expressible tail evaluated.1)

/-- The fault execution of a memref composite's `lidx` is a staged fault
execution, given the value and fault liftings of its array and its index. -/
private theorem reference_fault {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) {bound : Nat} {id reference : ExpressionId}
    (site : CellAwareInvocationAcceptedMemrefSites.MemrefSite prepared named scope.source id reference)
    (firstValue : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        site.base value after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptValue plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before site.base (.value value) after)
    (secondValue : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        site.subscript value after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptValue plan closures guard value ∧
      Staging.Recursive.Expression program registry scope context environment before site.subscript (.value value)
        after)
    (firstFault : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before
        site.base reason after →
      Kept plan closures guard before →
      Staging.Recursive.Expression program registry scope context environment before site.base
        (.fault (.semantic reason)) after)
    (secondFault : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before
        site.subscript reason after →
      Kept plan closures guard before →
      Staging.Recursive.Expression program registry scope context environment before site.subscript
        (.fault (.semantic reason)) after) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before
        reference reason after →
      Kept plan closures guard before →
      Staging.Recursive.Expression program registry scope context environment before reference
        (.fault (.semantic reason)) after := by
  intro size context environment before after reason within signatures expressible trace
  intro kept
  have occurrence : Staging.Recursive.Occurrence scope reference (.elementRef site.base site.subscript) :=
    ⟨site.referenceNode, lookupExpression?_sound site.referenceFound, site.referenceForm, site.referenceRequirements,
      site.referenceCoercions⟩
  obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.referenceFound site.referenceCoercions
    (fun name binder same => by rw [site.referenceForm] at same; cases same) trace
  rw [site.referenceForm, site.referenceRequirements] at raw
  cases raw with
  | elementRefBase _ failed =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    exact .arrayFault occurrence rfl (.headFault (firstFault (by omega) signatures expressible failed kept))
  | elementRefIndex _ evaluated failed =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    have base := firstValue (by omega) evaluated kept
    exact .arrayFault occurrence rfl (.tailFault base.2.2
      (.headFault (secondFault (by omega) signatures expressible failed base.1)))
  | elementRefIndexType _ first second notWord actual =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    have base := firstValue (by omega) first kept
    exact .arrayResult occurrence rfl (.cons base.2.2 (.cons (secondValue (by omega) second base.1).2.2 .nil))
      (.elementRefIndexType notWord actual)
  | elementRefOutOfBounds _ first second outside =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    have base := firstValue (by omega) first kept
    exact .arrayResult occurrence rfl (.cons base.2.2 (.cons (secondValue (by omega) second base.1).2.2 .nil))
      (.elementRefOutOfBounds outside)

/-- A sized fault execution of a nested site with an expressible reason, at a
context with the program's signatures and from a heap that keeps the stored
functions, is a staged fault execution with the same reason and heap, given
that the Source's direct calls have plain callees and the value and fault
liftings of the admitted callee bodies below a bound of its size. -/
theorem nested_fault {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) (plain : CalleesPlain scope.source) {bound : Nat}
    (bodies : BodiesLift program registry called bound prepared.base.plan closures guard)
    (faults : BodiesFaultLift program registry called bound prepared.base.plan closures guard)
    {id : ExpressionId} (nested : Nested prepared named scope.source called id) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before id
        reason after →
      Kept prepared.base.plan closures guard before →
      Staging.Recursive.Expression program registry scope context environment before id
        (.fault (.semantic reason)) after := by
  have nested_value {id : ExpressionId} (_ : Prepared checked) (_ : NodeOccurrencesUnique scope.source)
      (bodies : BodiesLift program registry called bound prepared.base.plan closures guard)
      (nested : Nested prepared named scope.source called id) :=
    @CellAwareInvocationAcceptedCallLifting.nested_value _ prepared _ _ _ _ _ _ _ unique _ bodies
      (fun indirect => (plain.no_indirect indirect).elim) _ nested
  induction nested with
  | literal site atomic =>
    intro size context environment before after reason _ _ _ trace
    intro _
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound site.found)
      (atomic_form atomic) site.coercions (atomic_not_local atomic) (.fault trace.sound)
  | read site form =>
    intro size context environment before after reason _ _ _ trace
    intro _
    have contains := lookupExpression?_sound site.found
    cases trace with
    | missing absent => exact (Dynamic.ExpressionAbsentIn.excludes_contains absent contains).elim
    | form found raw =>
      cases CellAwareInvocationAcceptedCallLifting.node_unique unique found contains
      rw [site.coercions] at raw
      exact .atomicFault contains (by rw [form]; exact .reference _ _) site.coercions raw.sound
    | coercion found _ failed =>
      cases CellAwareInvocationAcceptedCallLifting.node_unique unique found contains
      rw [site.coercions] at failed
      cases failed
    | generalizedLocalRequirement found formEq layout lookup read descriptor contextFields selection failed =>
      cases CellAwareInvocationAcceptedCallLifting.node_unique unique found contains
      exact .generalizedLocalRequirement contains formEq layout lookup read descriptor contextFields selection
        failed
    | generalizedLocalCoercion found _ _ _ _ _ _ _ failed =>
      cases CellAwareInvocationAcceptedCallLifting.node_unique unique found contains
      rw [site.coercions] at failed
      cases failed
  | unary site form operandNested child =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | unaryOperand _ operand =>
      exact .unaryOperandFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (child (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible operand kept)
    | unaryApply layout operand applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive invalid =>
        exact .unaryInvalid (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
          (nested_value prepared unique bodies operandNested (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) operand kept).2.2 invalid
      | requirement failed => cases failed
      | method _ selected _ => cases selected
  | binary site form leftNested rightNested left right =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | binaryLeft _ first =>
      exact .binaryLeftFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (left (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible first kept)
    | binaryLeftOperand _ first invalid =>
      exact .binaryLeftInvalid (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies leftNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2 invalid
    | binaryRight _ first continues second =>
      have stagedLeft := nested_value prepared unique bodies leftNested (child_le (by simp) formBelow within) first kept
      exact .binaryRightFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies leftNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2 continues
        (right (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible second stagedLeft.1)
    | binaryApply layout first continues second applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      have leftLifted := nested_value prepared unique bodies leftNested (by
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        omega) first kept
      have stagedLeft := leftLifted.2.2
      have rightLifted := nested_value prepared unique bodies rightNested (by
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        omega) second leftLifted.1
      have stagedRight := rightLifted.2.2
      cases applies with
      | primitive invalid =>
        exact .binaryInvalid (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same)) stagedLeft continues
          stagedRight invalid
      | panic panics =>
        exact .binaryPanic (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same)) stagedLeft continues
          stagedRight panics
      | requirement failed => cases failed
      | method _ selected _ => cases selected
  | conditional site form testNested _ _ test yes no =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | conditionalCondition _ first =>
      exact .conditionalFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (test (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible first kept)
    | conditionalType _ _ _ _ => simp [Expressible] at expressible
    | conditionalTrueBranch _ first second =>
      have tested := nested_value prepared unique bodies testNested (child_le (by simp) formBelow within) first kept
      exact .conditional (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies testNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (yes (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible second tested.1)
    | conditionalFalseBranch _ first second =>
      have tested := nested_value prepared unique bodies testNested (child_le (by simp) formBelow within) first kept
      exact .conditional (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies testNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (no (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible second tested.1)
  | group site form _ child =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | group _ inner =>
      exact .group (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (child (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible inner kept)
  | pair site form leftNested _ left right =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | tuple _ elements =>
      cases elements with
      | head first =>
        exact .pairLeftFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
          (left (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) signatures expressible first kept)
      | tail first rest =>
        cases rest with
        | head second =>
          have below := formBelow
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          have stagedLeft := nested_value prepared unique bodies leftNested (by omega) first kept
          exact .pairRightFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
            (nested_value prepared unique bodies leftNested (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
              omega) first kept).2.2
            (right (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
              omega) signatures expressible second stagedLeft.1)
        | tail _ rest => cases rest
  | @call id callee ids instantiation site selected argumentsNested arguments =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    have contains := lookupExpression?_sound site.found
    obtain ⟨name, calleeOccurrence⟩ := callee_occurrence plain contains site.form
    have callOccurrence : Staging.Recursive.Occurrence scope id (.call callee ids (.declaration instantiation)) :=
      ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    cases raw with
    | directCalleeMissing absent =>
      obtain ⟨_, calleeContains, _⟩ := calleeOccurrence
      exact (Dynamic.ExpressionAbsentIn.excludes_contains absent calleeContains).elim
    | directArguments _ _ failed =>
      exact .directArgumentsFault callOccurrence calleeOccurrence
        (arguments_fault (fun argument member => nested_value prepared unique bodies (argumentsNested argument member))
          arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed kept)
    | directRequirements _ failed =>
      rw [site.monomorphic.predicates] at failed
      cases failed
    | directApply evaluated produced failed =>
      have argumentsLifted := CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
        (fun argument member => nested_value prepared unique bodies (argumentsNested argument member)) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated kept
      have stagedArguments := argumentsLifted.2.2
      have nilEvidence := evidence_nil (site.monomorphic.predicates ▸ produced)
      subst nilEvidence
      cases failed with
      | notCallable invalid => exact (invalid trivial).elim
      | globalSignatureMissing _ => simp [Expressible] at expressible
      | globalBodyMissing _ => simp [Expressible] at expressible
      | globalArity instantiates mismatch =>
        exact .directApplied callOccurrence calleeOccurrence
          (valid_at signatures site.monomorphic.substitution instantiates) stagedArguments produced
          (.globalArity instantiates mismatch)
      | globalBody instantiates _ failed =>
        have valid := valid_at signatures site.monomorphic.substitution instantiates
        have covers := covers_nil instantiates site.monomorphic.predicates
        cases failed with
        | arity mismatch =>
          exact .directApplied callOccurrence calleeOccurrence valid stagedArguments produced
            (.globalArity instantiates mismatch)
        | statements rootsEq parameters allocate failed =>
          obtain ⟨child, closure, lifts⟩ := faults selected instantiates rootsEq
          have staged := lifts (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega)
            ((SourceSemantics.StructuralSubstitution.MonoBindersExtend.signatures_eq parameters).trans
              (body_signatures instantiates))
            expressible failed (argumentsLifted.1.binders argumentsLifted.2.1 allocate)
          exact .directApplied callOccurrence calleeOccurrence valid stagedArguments produced
            (.global instantiates covers rootsEq closure parameters allocate staged .fault)
        | controlEscape rootsEq parameters allocate execute escaped =>
          obtain ⟨child, closure, lifts⟩ := bodies selected instantiates rootsEq
          have staged := (lifts (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) execute (argumentsLifted.1.binders argumentsLifted.2.1 allocate)).2.2
          rcases escaped with ⟨escapedEnvironment, rfl⟩ | ⟨escapedEnvironment, rfl⟩
          · exact .directApplied callOccurrence calleeOccurrence valid stagedArguments produced
              (.global instantiates covers rootsEq closure parameters allocate staged .breaking)
          · exact .directApplied callOccurrence calleeOccurrence valid stagedArguments produced
              (.global instantiates covers rootsEq closure parameters allocate staged .continuing)
  | @conversion id callee argument function target site argumentNested child =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    have contains := lookupExpression?_sound site.found
    have callOccurrence :
        Staging.Recursive.Occurrence scope id (.call callee [argument] (.builtinFunction function)) :=
      ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    have values : ∀ other ∈ [argument], ∀ {size : Nat} {context : SourceSemantics.Context}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Kept prepared.base.plan closures guard before → Kept prepared.base.plan closures guard after ∧
          KeptValue prepared.base.plan closures guard value ∧
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after := by
      intro other member
      cases List.mem_singleton.mp member
      exact nested_value prepared unique bodies argumentNested
    cases raw with
    | builtinArguments _ failed =>
      exact .builtinArgumentsFault callOccurrence
        (arguments_fault values (fun other member => by
          cases List.mem_singleton.mp member
          exact child) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed kept)
    | builtinApply _ evaluated failed =>
      have stagedArguments := (CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
        values (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated kept).2.2
      cases failed with
      | notCallable invalid => exact (invalid trivial).elim
      | builtinArity mismatch => exact .builtinApplied callOccurrence stagedArguments (.builtinArity mismatch)
      | builtinArgumentType arity mismatch =>
        exact .builtinApplied callOccurrence stagedArguments (.builtinType arity mismatch)
      | builtinFaults failed => exact .builtinApplied callOccurrence stagedArguments (.builtinFault failed)
  | index site form baseNested keyNested base key =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | indexBase _ failed =>
      exact .indexBaseFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (base (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed kept)
    | indexKey _ first failed =>
      have stagedBase := nested_value prepared unique bodies baseNested (child_le (by simp) formBelow within) first kept
      exact .indexKeyFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies baseNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (key (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed stagedBase.1)
    | indexShape _ first second notMapping =>
      have stagedBase := nested_value prepared unique bodies baseNested (child_le (by simp) formBelow within) first kept
      exact .indexResult (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies baseNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (nested_value prepared unique bodies keyNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second stagedBase.1).2.2 (.shape notMapping)
    | indexKeyType _ first second actual mismatch =>
      have stagedBase := nested_value prepared unique bodies baseNested (child_le (by simp) formBelow within) first kept
      exact .indexResult (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies baseNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (nested_value prepared unique bodies keyNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second stagedBase.1).2.2 (.keyType rfl actual mismatch)
    | indexDefaultUnavailable _ first second keyTyped absent unavailable =>
      have stagedBase := nested_value prepared unique bodies baseNested (child_le (by simp) formBelow within) first kept
      exact .indexResult (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies baseNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first kept).2.2
        (nested_value prepared unique bodies keyNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second stagedBase.1).2.2
        (.unavailable rfl keyTyped absent unavailable)
  | builtinValue site form =>
    intro size context environment before after reason _ _ _ trace
    intro _
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound site.found)
      (by rw [form]; exact .reference _ _) site.coercions
      (fun name binder same => by rw [form] at same; cases same) (.fault trace.sound)
  | @builtin id callee ids function site argumentsNested arguments =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    have contains := lookupExpression?_sound site.found
    have callOccurrence :
        Staging.Recursive.Occurrence scope id (.call callee ids (.builtinFunction function)) :=
      ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    have values : ∀ other ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Kept prepared.base.plan closures guard before → Kept prepared.base.plan closures guard after ∧
          KeptValue prepared.base.plan closures guard value ∧
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after :=
      fun other member => nested_value prepared unique bodies (argumentsNested other member)
    cases raw with
    | builtinArguments _ failed =>
      exact .builtinArgumentsFault callOccurrence
        (arguments_fault values arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed kept)
    | builtinApply _ evaluated failed =>
      have stagedArguments := (CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
        values (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated kept).2.2
      cases failed with
      | notCallable invalid => exact (invalid trivial).elim
      | builtinArity mismatch => exact .builtinApplied callOccurrence stagedArguments (.builtinArity mismatch)
      | builtinArgumentType arity mismatch =>
        exact .builtinApplied callOccurrence stagedArguments (.builtinType arity mismatch)
      | builtinFaults failed => exact .builtinApplied callOccurrence stagedArguments (.builtinFault failed)
  | @tuple id ids site elementsNested elements =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    have values : ∀ other ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Kept prepared.base.plan closures guard before → Kept prepared.base.plan closures guard after ∧
          KeptValue prepared.base.plan closures guard value ∧
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after :=
      fun other member => nested_value prepared unique bodies (elementsNested other member)
    cases raw with
    | tuple _ failed =>
      exact .tupleFault ⟨site.node, lookupExpression?_sound site.found, site.form, site.requirements, site.coercions⟩
        (arguments_fault values elements (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed kept)
  | @constructor id instantiation ids site argumentsNested arguments =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    have occurrence : Staging.Recursive.Occurrence scope id (.constructor instantiation ids) :=
      ⟨site.node, lookupExpression?_sound site.found, site.form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    have values : ∀ other ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Kept prepared.base.plan closures guard before → Kept prepared.base.plan closures guard after ∧
          KeptValue prepared.base.plan closures guard value ∧
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after :=
      fun other member => nested_value prepared unique bodies (argumentsNested other member)
    cases raw with
    | constructorArgument _ failed =>
      exact .constructorFault occurrence
        (arguments_fault values arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed kept)
    | constructorMetadata _ metadata => exact .constructorMetadataFault occurrence metadata
  | @array id form site childrenNested children =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (CellAwareInvocationAcceptedArraySites.not_local site) trace
    have occurrence : Staging.Recursive.Occurrence scope id form :=
      ⟨site.node, lookupExpression?_sound site.found, site.formEq, site.requirements, site.coercions⟩
    rw [site.formEq, site.requirements] at raw
    have values : ∀ other ∈ (Staging.Recursive.arrayChildren form).getD [], ∀ {size : Nat}
        {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
        {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Kept prepared.base.plan closures guard before → Kept prepared.base.plan closures guard after ∧
          KeptValue prepared.base.plan closures guard value ∧
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after :=
      fun other member => nested_value prepared unique bodies (childrenNested other member)
    cases site.shape with
    | arrayLength base =>
      cases raw with
      | arrayLengthBase _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures expressible
            failed kept))
    | arrayIndex base subscript =>
      cases raw with
      | arrayIndexBase _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures expressible
            failed kept))
      | arrayIndexIndex _ first failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        exact .arrayFault occurrence rfl
          (.tailFault stagedBase.2.2
            (.headFault (children subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures
              expressible failed stagedBase.1)))
      | arrayIndexType _ first second notWord actual =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        exact .arrayResult occurrence rfl
          (.cons stagedBase.2.2
            (.cons (values subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second
              stagedBase.1).2.2 .nil))
          (.arrayIndexType notWord actual)
      | arrayIndexOutOfBounds _ first second outside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        exact .arrayResult occurrence rfl
          (.cons stagedBase.2.2
            (.cons (values subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second
              stagedBase.1).2.2 .nil))
          (.arrayIndexOutOfBounds outside)
    | elementRef base subscript =>
      cases raw with
      | elementRefBase _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures expressible
            failed kept))
      | elementRefIndex _ first failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        exact .arrayFault occurrence rfl
          (.tailFault stagedBase.2.2
            (.headFault (children subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures
              expressible failed stagedBase.1)))
      | elementRefIndexType _ first second notWord actual =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        exact .arrayResult occurrence rfl
          (.cons stagedBase.2.2
            (.cons (values subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second
              stagedBase.1).2.2 .nil))
          (.elementRefIndexType notWord actual)
      | elementRefOutOfBounds _ first second outside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        exact .arrayResult occurrence rfl
          (.cons stagedBase.2.2
            (.cons (values subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second
              stagedBase.1).2.2 .nil))
          (.elementRefOutOfBounds outside)
    | arraySlice base start stop =>
      cases raw with
      | arraySliceBase _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures expressible
            failed kept))
      | arraySliceBounds _ first failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        exact .arrayFault occurrence rfl
          (.tailFault stagedBase.2.2
            (arguments_fault (ids := start.toList ++ stop.toList)
              (fun bound member => values bound (List.mem_cons_of_mem _ member))
              (fun bound member => children bound (List.mem_cons_of_mem _ member)) (by omega) signatures
              expressible failed stagedBase.1))
      | arraySliceBoundType _ first bounds member notWord actual =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        exact .arrayResult occurrence rfl
          (.cons stagedBase.2.2
            (CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
              (ids := start.toList ++ stop.toList)
              (fun bound member => values bound (List.mem_cons_of_mem _ member)) (by omega) bounds stagedBase.1).2.2)
          (.arraySliceBoundType member notWord actual)
      | arraySliceOutOfBounds _ first bounds counted chosen outside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        have stagedBase := values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept
        exact .arrayResult occurrence rfl
          (.cons stagedBase.2.2
            (CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
              (ids := start.toList ++ stop.toList)
              (fun bound member => values bound (List.mem_cons_of_mem _ member)) (by omega) bounds stagedBase.1).2.2)
          (.arraySliceOutOfBounds counted chosen outside)
    | newArray length _ =>
      cases raw with
      | newArrayLength _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children length (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures
            expressible failed kept))
      | newArrayLengthType _ first notWord actual =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values length (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept).2.2 .nil)
          (.newArrayLengthType notWord actual)
      | newArrayTooLong _ first tooLong =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values length (by simp [Staging.Recursive.arrayChildren]) (by omega) first kept).2.2 .nil)
          (.newArrayTooLong tooLong)
    | arrayLiteral _ _ =>
      cases raw with
      | arrayLiteralElements _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (arguments_fault values children (by omega) signatures expressible failed kept)
    | @toArray _ _ slice _ _ _ _ _ _ _ =>
      cases raw with
      | toArraySlice _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children slice (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures
            expressible failed kept))
  | @memrefLoad id reference site form firstNested secondNested first second =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    have occurrence : Staging.Recursive.Occurrence scope id (.memrefLoad reference) :=
      ⟨site.node, lookupExpression?_sound site.found, form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, site.requirements] at raw
    cases raw with
    | memrefLoadReference _ failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      exact .arrayFault occurrence rfl (.headFault (reference_fault prepared unique site
        (nested_value prepared unique bodies firstNested) (nested_value prepared unique bodies secondNested) first
        second (by omega) signatures expressible failed kept))
  | @memrefStore id reference value site form firstNested secondNested thirdNested first second third =>
    intro size context environment before after reason within signatures expressible trace
    intro kept
    have occurrence : Staging.Recursive.Occurrence scope id (.memrefStore reference value) :=
      ⟨site.node, lookupExpression?_sound site.found, form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, site.requirements] at raw
    cases raw with
    | memrefStoreReference _ failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      exact .arrayFault occurrence rfl (.headFault (reference_fault prepared unique site
        (nested_value prepared unique bodies firstNested) (nested_value prepared unique bodies secondNested) first
        second (by omega) signatures expressible failed kept))
    | memrefStoreValue _ referenceEvaluates failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      have referenced := CellAwareInvocationAcceptedCallLifting.reference_value prepared unique site
        (nested_value prepared unique bodies firstNested) (nested_value prepared unique bodies secondNested)
        (by omega) referenceEvaluates kept
      exact .arrayFault occurrence rfl (.tailFault
        (CellAwareInvocationAcceptedCallLifting.reference_value prepared unique site
          (nested_value prepared unique bodies firstNested) (nested_value prepared unique bodies secondNested)
          (by omega) referenceEvaluates kept).2.2
        (.headFault (third (by omega) signatures expressible failed referenced.1)))
  | namedValue site _ =>
    intro size context environment before after reason _ _ _ trace
    intro _
    exact CellAwareInvocationAcceptedValueLifting.value_lift_fault unique site trace
  | indirect site => exact (plain.no_indirect ⟨_, _, site.found, _, _, _, site.form⟩).elim

/-- The fault lifting of every nested site below a size, given that the
Source's direct calls have plain callees and the value and fault liftings of
the callee bodies below it. -/
theorem nested_fault_roots {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) (plain : CalleesPlain scope.source) {bound : Nat}
    (bodies : BodiesLift program registry called bound prepared.base.plan closures guard)
    (faults : BodiesFaultLift program registry called bound prepared.base.plan closures guard) :
    ChildFaultLifts program registry scope (Nested prepared named scope.source called) bound prepared.base.plan
      closures guard := by
  intro id nested size context environment before after reason below signatures expressible trace
  exact nested_fault prepared unique plain bodies faults nested (Nat.le_of_lt below) signatures expressible trace

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFaultLifting
end

section
/-! Original fault executions of supported statement lists are staged fault
executions with the same reason and heap, given the value and fault liftings
of their expressions below the size. A statement faults in its expression, its
target, bare or through mapping indices, the operand of its in-place `~`, its
inner list, the pattern or selected body of its match, a header item or an
iteration of its loop, or a
falling-through statement is followed by a fault in the rest of its list; the
staged rule of the same form carries the fault, at the context, environment
and heap of the original execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFaultLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedSizedLifting (ChildLifts)
open CellAwareInvocationAcceptedCallLifting (BodiesLift Callees)
open CellAwareInvocationAcceptedStoredFunctions (Kept KeptValue KeptOutcome FamilyIndirect Value)

/-- The sized fault judgment of each compiler mode's statement lists. -/
def FaultOriginal (program : Program) (size : Nat) : Bool → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
    TypedSource → Dynamic.Environment → Dynamic.Heap → List StatementId → SourceSemantics.Context →
    Dynamic.SemanticFault → Dynamic.Heap → Prop
  | true => SourceExecutionSize.FunctionStatementsFault program size
  | false => SourceExecutionSize.StatementsFault program size

section Inversion
variable {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {reason : Dynamic.SemanticFault} {size : Nat}

private theorem return_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {expression : ExpressionId}
    (form : node.form = .returnStmt (some expression))
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.ExpressionFaults program child context evidence source environment
      before expression reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | returnValue contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem return_unit_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) : False := by
  cases fault with
  | missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  | _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem declared_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {binder : TypedBinder} {expression : ExpressionId}
    (form : node.form = .letDecl binder (some expression)) (monomorphic : binder.scheme.quantified = [])
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.ExpressionFaults program child context evidence source environment
      before expression reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | polymorphicLet contains formEq polymorphic _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact absurd monomorphic polymorphic
  | letInitializer contains formEq _ fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem uninitialized_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {binder : TypedBinder}
    (form : node.form = .letDecl binder none) (monomorphic : binder.scheme.quantified = [])
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) : False := by
  cases fault with
  | missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  | polymorphicLet contains formEq polymorphic _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact polymorphic monomorphic
  | _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem assigned_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {expression : ExpressionId}
    (form : node.form = .assignValue assignment operator expression)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.SourcePlaceAssignmentFaults program child context evidence source
      environment before assignment.target operator expression reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | assignValue contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem bitNotted_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {assignment : AssignmentResolution}
    (form : node.form = .assignBitNot assignment)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.SourcePlaceBitNotFaults program child context evidence source
      environment before assignment.target reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | assignBitNot contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem expression_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {expression : ExpressionId} {semicolon : Bool}
    (form : node.form = .expression expression semicolon)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.ExpressionFaults program child context evidence source environment
      before expression reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | expression contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem block_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {statements : List StatementId}
    (form : node.form = .block statements)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child innerContext, child < size ∧ SourceExecutionSize.StatementsFault program child context evidence source
      environment before statements innerContext reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | block contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem conditional_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} (form : node.form = .ifThen condition thenBody elseBody)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    (∃ test, test < size ∧ SourceExecutionSize.ExpressionFaults program test context evidence source environment
      before condition reason after) ∨
    (∃ expected actual, reason = .typeMismatch expected actual) ∨
    (∃ test inner truth middle innerContext, test < size ∧ inner < size ∧
      SourceExecutionSize.ExpressionEvaluates program test context evidence source environment before condition
        (.bool truth) middle ∧
      SourceExecutionSize.StatementsFault program inner context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext reason after) := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | ifCondition contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inl ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | ifConditionType => exact .inr (.inl ⟨_, _, rfl⟩)
  | ifTrueBody contains formEq test fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inr (.inr ⟨_, _, true, _, _, CellAwareInvocationAcceptedSizedLifting.below_left,
      CellAwareInvocationAcceptedSizedLifting.below_right, test, fault⟩)
  | ifFalseBody contains formEq test fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inr (.inr ⟨_, _, false, _, _, CellAwareInvocationAcceptedSizedLifting.below_left,
      CellAwareInvocationAcceptedSizedLifting.below_right, test, fault⟩)
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem jump_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt ∨ node.form = .continueStmt)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) : False := by
  cases fault with
  | missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  | _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    rcases form with form | form <;> simp_all

private theorem while_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {body : List StatementId}
    (form : node.form = .whileLoop condition body)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.WhileFaults program child context evidence source environment before
      condition body reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | whileIteration contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem for_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {initializer : List ForItemForm} {condition : ExpressionId}
    {post : List ForItemForm} {body : List StatementId} (form : node.form = .forLoop initializer condition post body)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    (∃ child failedContext, child < size ∧ SourceExecutionSize.ForItemsFault program child context evidence source
      environment before initializer failedContext reason after) ∨
    (∃ first second loopContext loopEnvironment initialized, first < size ∧ second < size ∧
      SourceExecutionSize.ForItemsExecute program first context evidence source environment before initializer
        loopContext loopEnvironment initialized ∧
      SourceExecutionSize.ForLoopFaults program second loopContext evidence source loopEnvironment initialized
        condition post body reason after) := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | forInitializer contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inl ⟨_, _, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | forIteration contains formEq initial fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inr ⟨_, _, _, _, _, CellAwareInvocationAcceptedSizedLifting.below_left,
      CellAwareInvocationAcceptedSizedLifting.below_right, initial, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all
end Inversion

variable {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) {program : Program}
  {registry : Staging.Recursive.Registry} {called : DeclarationInstantiation → Prop}
  {scope : Staging.Recursive.Scope} {expected : TypeSystem.Ty} {plan : SourceCompilationPlan.Plan}
  {closures : Dynamic.Closure → Prop} {guard : Prop}

/-- An assignment whose bare target faults: its root is unbound or dangling. -/
private theorem bare_target_fault {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (contains : ContainsStatement scope.source id node) (form : node.form = .assignValue assignment operator rhs)
    (bare : assignment.target.projections = [])
    (failed : SourceExecutionSize.SourcePlaceFaults program size context scope.evidence scope.source environment
      before assignment.target reason after) :
    Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest) context
      (.fault (.semantic reason)) after := by
  cases failed with
  | unbound missing => exact .assignBareUnbound contains form bare missing
  | dangling lookup missing => exact .assignBareDangling contains form bare lookup missing
  | projectionExpression _ _ failed =>
    rw [bare] at failed
    cases failed
  | danglingAfterProjections lookup _ evaluated missing =>
    rw [bare] at evaluated
    cases evaluated
    exact .assignBareDangling contains form bare lookup missing
  | projectionRead _ _ evaluated _ _ failed =>
    rw [bare] at evaluated
    cases evaluated
    cases failed
  | uninitialized _ _ evaluated _ _ _ projected =>
    rw [bare] at evaluated
    cases evaluated
    exact absurd rfl projected
  | elementPrefix projectionsEq _
  | elementIndex projectionsEq _ _ _
  | elementIndexType projectionsEq _ _ _ _ _
  | elementOutOfBounds projectionsEq _ _ _ _ _ _
  | elementUninitialized projectionsEq _ _ =>
    rw [bare] at projectionsEq
    simp at projectionsEq

/-- A sized Source fault of a bare place is its root's, at the same heap. -/
private theorem root_fault {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {place : PlaceResolution} (bare : place.projections = []) {before after : Dynamic.Heap}
    {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.SourcePlaceFaults program size context scope.evidence scope.source environment
      before place reason after) :
    after = before ∧ Staging.Recursive.ProjectedTarget.RootFault environment before place reason := by
  cases failed with
  | unbound missing => exact ⟨rfl, .unbound missing⟩
  | dangling lookup missing => exact ⟨rfl, .dangling lookup missing⟩
  | projectionExpression _ _ failed =>
    rw [bare] at failed
    cases failed
  | danglingAfterProjections lookup _ evaluate missing =>
    rw [bare] at evaluate
    cases evaluate
    exact ⟨rfl, .dangling lookup missing⟩
  | projectionRead _ _ evaluate _ _ failed =>
    rw [bare] at evaluate
    cases evaluate
    cases failed
  | uninitialized _ _ evaluate _ _ _ projected =>
    rw [bare] at evaluate
    cases evaluate
    exact absurd rfl projected
  | elementPrefix projectionsEq | elementIndex projectionsEq | elementIndexType projectionsEq
  | elementOutOfBounds projectionsEq | elementUninitialized projectionsEq =>
    rw [bare] at projectionsEq
    simp at projectionsEq

/-- A sized Source fault of a place of one element whose key `child` admits,
with an expressible reason at a context with the program's signatures, is the
staged `ElementTarget` fault with the same reason and heap, given the value and
fault liftings of `child` within the bound: the root's, through the bare
leading place, a root not yet initialized, the key's from the same heap, a key
that is not a word, and `0x32` from the array's length on. -/
private theorem element_fault {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard)
    (faultLift : ChildFaultLifts program registry scope child bound plan closures guard) {place : PlaceResolution}
    {key : ExpressionId} (single : place.projections = [.element key]) (admitted : child key) {size : Nat}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {reason : Dynamic.SemanticFault} (within : size ≤ bound)
    (signatures : context.signatures = program.signatures) (expressible : Expressible reason)
    (failed : SourceExecutionSize.SourcePlaceFaults program size context scope.evidence scope.source environment
      before place reason after) (kept : Kept plan closures guard before) :
    Staging.Recursive.ElementTarget program registry scope context environment before place
      (.fault (.semantic reason)) after := by
  have projectionsEq : place.projections = [] ++ [.element key] := single
  have keyBelow : ∀ {first second : Nat}, SourceExecutionSize.stepSize [first, second] ≤ bound → second < bound :=
    fun below => Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) below
  cases failed with
  | unbound missing => exact .elementPrefixFault projectionsEq (.elementRootFault rfl (.unbound missing))
  | dangling lookup missing =>
    exact .elementPrefixFault projectionsEq (.elementRootFault rfl (.dangling lookup missing))
  | projectionExpression _ _ failed =>
    rw [single] at failed
    cases failed
  | danglingAfterProjections _ _ evaluate | projectionRead _ _ evaluate | uninitialized _ _ evaluate =>
    rw [single] at evaluate
    cases evaluate
  | elementPrefix leadingEq failed =>
    obtain ⟨rfl, rfl⟩ := CellAwareInvocationAcceptedSizedLifting.element_split (single.symm.trans leadingEq)
    obtain ⟨rfl, root⟩ := root_fault rfl failed
    exact .elementPrefixFault leadingEq (.elementRootFault rfl root)
  | elementIndex leadingEq prefixResolves initialized failed =>
    obtain ⟨rfl, rfl⟩ := CellAwareInvocationAcceptedSizedLifting.element_split (single.symm.trans leadingEq)
    obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves rfl prefixResolves.sound
    cases snapshot with
    | intro _ lookup rootRead rootValue =>
      exact .elementIndexFault leadingEq (.elementRoot rfl lookup rootRead rootValue) initialized
        (faultLift admitted (keyBelow within) signatures expressible failed kept)
  | elementIndexType leadingEq prefixResolves initialized indexed notWord actualType =>
    obtain ⟨rfl, rfl⟩ := CellAwareInvocationAcceptedSizedLifting.element_split (single.symm.trans leadingEq)
    obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves rfl prefixResolves.sound
    cases snapshot with
    | intro _ lookup rootRead rootValue =>
      exact .elementIndexType leadingEq (.elementRoot rfl lookup rootRead rootValue) initialized
        (lift admitted (keyBelow within) indexed kept).2.2 notWord actualType
  | elementOutOfBounds leadingEq prefixResolves prefixSelected indexed read stored outOfBounds =>
    obtain ⟨rfl, rfl⟩ := CellAwareInvocationAcceptedSizedLifting.element_split (single.symm.trans leadingEq)
    obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves rfl prefixResolves.sound
    cases snapshot with
    | intro _ lookup rootRead rootValue =>
      exact .elementOutOfBounds leadingEq (.elementRoot rfl lookup rootRead rootValue) prefixSelected
        (lift admitted (keyBelow within) indexed kept).2.2 read stored outOfBounds
  | elementUninitialized leadingEq prefixResolves prefixEmpty =>
    obtain ⟨rfl, rfl⟩ := CellAwareInvocationAcceptedSizedLifting.element_split (single.symm.trans leadingEq)
    obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves rfl prefixResolves.sound
    cases snapshot with
    | intro _ lookup rootRead rootValue =>
      exact .elementUninitialized leadingEq (.elementRoot rfl lookup rootRead rootValue) prefixEmpty

/-- A sized Source fault in a path of mapping indices whose keys `child` admits
is a staged fault of its keys, given the value and fault liftings of `child`
below the size. -/
private theorem projections_fault {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard)
    (faultLift : ChildFaultLifts program registry scope child bound plan closures guard)
    {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} :
    ∀ {projections : List PlaceProjection},
    (∀ projection ∈ projections, ∃ key, projection = .index key ∧ child key) →
    ∀ {size : Nat} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.SourceProjectionsFault program size context scope.evidence scope.source environment
        before projections reason after →
      Kept plan closures guard before →
      Staging.Recursive.Expressions program registry scope context environment before
        (Staging.Recursive.ProjectedTarget.keys projections) (.fault (.semantic reason)) after := by
  intro projections
  induction projections with
  | nil =>
    intro _ size before after reason _ _ _ failed
    cases failed
  | cons projection rest ih =>
    intro keys size before after reason within signatures expressible failed
    intro kept
    obtain ⟨key, rfl, admitted⟩ := keys projection List.mem_cons_self
    cases failed with
    | indexHead failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
      exact .headFault (faultLift admitted (by omega) signatures expressible failed kept)
    | indexTail head failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
      have evaluatedKey := lift admitted (by omega) head kept
      exact .tailFault evaluatedKey.2.2
        (ih (fun other member => keys other (List.mem_cons_of_mem _ member)) (by omega) signatures expressible failed
          evaluatedKey.1)

/-- A read through a non-empty path, or from a present value, selects a value. -/
private theorem read_selects : ∀ {start : Option Dynamic.Value} {evaluated : List Dynamic.EvaluatedProjection}
    {result : Option Dynamic.Value}, Dynamic.ProjectionsRead start evaluated result →
    (∃ value, start = some value) ∨ evaluated ≠ [] → ∃ value, result = some value := by
  intro start evaluated result read
  induction read with
  | nil =>
    intro present
    rcases present with ⟨value, rfl⟩ | nonempty
    · exact ⟨value, rfl⟩
    · exact absurd rfl nonempty
  | indexFound _ _ ih => intro _; exact ih (.inl ⟨_, rfl⟩)
  | indexDefault _ _ _ ih => intro _; exact ih (.inl ⟨_, rfl⟩)
  | member _ _ ih => intro _; exact ih (.inl ⟨_, rfl⟩)
  | element _ _ ih => intro _; exact ih (.inl ⟨_, rfl⟩)

/-- A non-empty path of projections evaluates to a non-empty path. -/
private theorem evaluated_nonempty {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {projections : List PlaceProjection}
    {evaluated : List Dynamic.EvaluatedProjection} (projected : projections ≠ [])
    (evaluate : SourceExecutionSize.SourceProjectionsEvaluate program size context scope.evidence scope.source
      environment before projections evaluated after) : evaluated ≠ [] := by
  cases evaluate with
  | nil => exact absurd rfl projected
  | member _ => exact List.cons_ne_nil _ _
  | index _ _ => exact List.cons_ne_nil _ _

/-- One statement followed by the rest of its list, over sized fault
derivations. A faulting head ends the list at its context; a falling-through
head is followed by a fault in the rest. -/
private theorem sequence_fault {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {size : Nat} {reason : Dynamic.SemanticFault} (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (step : ∀ {context environment before middleContext nextEnvironment middle finalContext after}
        {headSize tailSize : Nat}, headSize < size → tailSize < size → context.signatures = program.signatures →
      SourceExecutionSize.StatementExecutes program headSize context scope.evidence scope.source environment before id
        middleContext (.fallthrough nextEnvironment) middle →
      FaultOriginal program tailSize mode middleContext scope.evidence scope.source nextEnvironment middle rest
        finalContext reason after →
      Kept plan closures guard before →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (.fault (.semantic reason)) after)
    (stop : ∀ {context environment before after} {headSize : Nat}, headSize < size →
      context.signatures = program.signatures →
      SourceExecutionSize.StatementFaults program headSize context scope.evidence scope.source environment before id
        reason after →
      Kept plan closures guard before →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        context (.fault (.semantic reason)) after) :
    ∀ {context environment before finalContext after}, context.signatures = program.signatures →
      FaultOriginal program size mode context scope.evidence scope.source environment before (id :: rest)
        finalContext reason after →
      Kept plan closures guard before →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (.fault (.semantic reason)) after := by
  intro context environment before finalContext after signatures original
  cases mode with
  | false =>
    unfold FaultOriginal at original
    cases original with
    | head fault => exact stop CellAwareInvocationAcceptedSizedLifting.below_one signatures fault
    | tail head next =>
      exact step CellAwareInvocationAcceptedSizedLifting.below_left CellAwareInvocationAcceptedSizedLifting.below_right
        signatures head next
  | true =>
    unfold FaultOriginal at original
    cases original with
    | singleton fault => exact stop CellAwareInvocationAcceptedSizedLifting.below_one signatures fault
    | tailExpression contains form _ =>
      obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
      exact absurd form (notTail _)
    | head fault => exact stop CellAwareInvocationAcceptedSizedLifting.below_one signatures fault
    | tail head next =>
      exact step CellAwareInvocationAcceptedSizedLifting.below_left CellAwareInvocationAcceptedSizedLifting.below_right
        signatures head next

/-- The sized Source fault of a `while` loop whose condition `child` admits and
whose body lifts within the bound, with an expressible reason at a context with
the program's signatures, is a staged fault of the loop with the same heap. -/
private theorem while_fault_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard)
    (faultLift : ChildFaultLifts program registry scope child bound plan closures guard) {condition : ExpressionId}
    {body : List StatementId} (test : child condition)
    (inner : ∀ {size : Nat} {context environment before innerContext outcome after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before body
        innerContext outcome after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (CellAwareInvocationAcceptedStatementLifting.control outcome) after)
    (innerFault : ∀ {size : Nat} {context environment before innerContext after} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.StatementsFault program size context scope.evidence scope.source environment before body
        innerContext reason after →
      Kept plan closures guard before →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (.fault (.semantic reason)) after) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.WhileFaults program size context scope.evidence scope.source environment before condition
        body reason after →
      Kept plan closures guard before →
      Staging.Recursive.While program registry scope context environment before condition body
        (.fault (.semantic reason)) after := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context environment before after reason within signatures expressible failed
    intro kept
    cases failed with
    | condition fault =>
      exact .conditionFault (faultLift test
        (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within) signatures expressible fault kept)
    | conditionType => simp [Expressible] at expressible
    | body evaluate fault =>
      have tested := lift test (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within)
        evaluate kept
      exact .bodyFault (lift test (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within)
        evaluate kept).2.2
        (innerFault (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
          signatures expressible fault tested.1)
    | nextFallthrough evaluate executes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      exact .next tested.2.2 ran.2.2
        (ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) signatures expressible fault ran.1)
    | nextContinue evaluate executes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      exact .continueNext tested.2.2 ran.2.2
        (ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) signatures expressible fault ran.1)

/-- A header assignment whose bare target faults: its root is unbound or
dangling. -/
private theorem items_bare_target_fault {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    {rhs : ExpressionId} {rest : List ForItemForm} {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (bare : assignment.target.projections = [])
    (failed : SourceExecutionSize.SourcePlaceFaults program size context scope.evidence scope.source environment
      before assignment.target reason after) :
    Staging.Recursive.ForItems program registry scope context environment before
      (.assignValue assignment operator rhs :: rest) context (.fault (.semantic reason)) after := by
  cases failed with
  | unbound missing => exact .unbound bare missing
  | dangling lookup missing => exact .dangling bare lookup missing
  | projectionExpression _ _ failed =>
    rw [bare] at failed
    cases failed
  | danglingAfterProjections lookup _ evaluated missing =>
    rw [bare] at evaluated
    cases evaluated
    exact .dangling bare lookup missing
  | projectionRead _ _ evaluated _ _ failed =>
    rw [bare] at evaluated
    cases evaluated
    cases failed
  | uninitialized _ _ evaluated _ _ _ projected =>
    rw [bare] at evaluated
    cases evaluated
    exact absurd rfl projected
  | elementPrefix projectionsEq _
  | elementIndex projectionsEq _ _ _
  | elementIndexType projectionsEq _ _ _ _ _
  | elementOutOfBounds projectionsEq _ _ _ _ _ _
  | elementUninitialized projectionsEq _ _ =>
    rw [bare] at projectionsEq
    simp at projectionsEq

/-- The sized Source fault of a supported header vector whose expressions
`child` admits, with an expressible reason at a context with the program's
signatures, is a staged fault of the vector with the same heap, given the value
and fault liftings of `child` within the bound. -/
private theorem items_fault_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard)
    (faultLift : ChildFaultLifts program registry scope child bound plan closures guard) {items : List ForItemForm}
    (shape : CellAwareInvocationAcceptedBodyShape.ItemsShape scope.source child items) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {failedContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ForItemsFault program size context scope.evidence scope.source environment before items
        failedContext reason after →
      Kept plan closures guard before →
      Staging.Recursive.ForItems program registry scope context environment before items failedContext
        (.fault (.semantic reason)) after := by
  induction shape with
  | nil =>
    intro size context environment before after failedContext reason _ _ _ failed
    cases failed
  | absent monomorphic _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    intro kept
    cases failed with
    | head fault =>
      cases fault with
      | polymorphicLet polymorphic _ => exact absurd monomorphic polymorphic
    | tail head fault =>
      cases head with
      | letUninitialized _ extension allocate =>
        exact .absent monomorphic extension allocate
          (tailIH (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
            (extension.context_fields.1.trans signatures) expressible fault (kept.allocates_none allocate))
  | initialized monomorphic value _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    intro kept
    cases failed with
    | head fault =>
      cases fault with
      | polymorphicLet polymorphic _ => exact absurd monomorphic polymorphic
      | letInitializer _ fault =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        exact .initializerFault monomorphic (faultLift value (by omega) signatures expressible fault kept)
    | tail head fault =>
      cases head with
      | letInitialized evaluate _ extension allocate =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        have evaluated := lift value (by omega) evaluate kept
        exact .initialized monomorphic extension evaluated.2.2 allocate
          (tailIH (by omega) (extension.context_fields.1.trans signatures) expressible fault
            (evaluated.1.allocates evaluated.2.1 allocate))
      | letInitializedGeneralized _ _ polymorphic => exact absurd monomorphic polymorphic
  | discarded value _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    intro kept
    cases failed with
    | head fault =>
      cases fault with
      | expression fault =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        exact .expressionFailure (faultLift value (by omega) signatures expressible fault kept)
    | tail head fault =>
      cases head with
      | expression evaluate =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        have evaluated := lift value (by omega) evaluate kept
        exact .expression evaluated.2.2 (tailIH (by omega) signatures expressible fault evaluated.1)
  | assigned assignable value _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    intro kept
    cases failed with
    | head fault =>
      cases fault with
      | assignValue fault =>
        cases fault with
        | target failed => exact items_bare_target_fault assignable.2.1 failed
        | rhs resolve failed =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          exact .assignmentFailure snapshot (faultLift value (by omega) signatures expressible failed kept)
        | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          exact .assignmentOperands snapshot (lift value (by omega) evaluate kept).2.2 currentRead rootType initialValue
            pathRead invalid
        | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          exact .assignmentPanic snapshot (lift value (by omega) evaluate kept).2.2 currentRead rootType initialValue
            pathRead panics
        | structuralUpdate resolve _ _ _ _ failed =>
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          cases snapshot
          cases failed
    | tail head fault =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          have evaluated := lift value (by omega) evaluate kept
          exact .assignment snapshot evaluated.2.2 write
            (tailIH (by omega) signatures expressible fault
              (evaluated.1.assigns (CellAwareInvocationAcceptedSizedLifting.bare_keys snapshot) evaluated.2.1 write))
  | projectedAssigned assignable keys value _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    intro kept
    cases failed with
    | head fault =>
      cases fault with
      | assignValue fault =>
        cases fault with
        | target failed =>
          cases failed with
          | unbound missing => exact .projectedAssignmentRootFault assignable.2.1 (.unbound missing)
          | dangling lookup missing => exact .projectedAssignmentRootFault assignable.2.1 (.dangling lookup missing)
          | projectionExpression lookup read failed =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            exact .projectedAssignmentKeysFault assignable.2.1 (.intro lookup read)
              (projections_fault lift faultLift keys (by omega) signatures expressible failed kept)
          | danglingAfterProjections lookup read evaluate missing =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
            exact .projectedAssignmentGetterFault assignable.2.1 staged (.dangling lookup read ordered missing)
          | projectionRead lookup initialRead evaluate currentRead initialValue failed =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
            exact .projectedAssignmentGetterFault assignable.2.1 staged
              (.projection lookup initialRead ordered currentRead initialValue failed)
          | uninitialized lookup initialRead evaluate currentRead empty notMapping nonempty =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
            exact .projectedAssignmentGetterFault assignable.2.1 staged
              (.uninitialized lookup initialRead ordered currentRead empty notMapping nonempty)
          | elementPrefix projectionsEq _
          | elementIndex projectionsEq _ _ _
          | elementIndexType projectionsEq _ _ _ _ _
          | elementOutOfBounds projectionsEq _ _ _ _ _ _
          | elementUninitialized projectionsEq _ _ =>
            exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
        | rhs resolve failed =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
          have keptTarget := (CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept).1
          exact .projectedAssignmentRhsFault assignable.2.1 staged snapshot
            (faultLift value (by omega) signatures expressible failed keptTarget)
        | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
          have keptTarget := (CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept).1
          exact .projectedAssignmentWriteFault assignable.2.1 staged snapshot
            (lift value (by omega) evaluate keptTarget).2.2
            (.operands currentRead rootType initialValue pathRead invalid)
        | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
          have keptTarget := (CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept).1
          exact .projectedAssignmentWriteFault assignable.2.1 staged snapshot
            (lift value (by omega) evaluate keptTarget).2.2
            (.panic currentRead rootType initialValue pathRead panics)
        | structuralUpdate resolve evaluate currentRead rootType initialValue failed =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
          have keptTarget := (CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept).1
          exact .projectedAssignmentWriteFault assignable.2.1 staged snapshot
            (lift value (by omega) evaluate keptTarget).2.2
            (.structural currentRead rootType initialValue failed)
    | tail head fault =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
          have target := CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept
          have evaluated := lift value (by omega) evaluate target.1
          exact .projectedAssignment assignable.2.1 staged snapshot evaluated.2.2 write
            (tailIH (by omega) signatures expressible fault (evaluated.1.assigns target.2 evaluated.2.1 write))
  | bitNotted assignable _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    intro kept
    cases failed with
    | head fault =>
      cases fault with
      | assignBitNot fault =>
        have unchanged := Staging.Recursive.bitNot_fault_heap assignable.2.1 fault.sound
        subst unchanged
        exact .bitNotFault assignable.2.1 fault.sound
    | tail head fault =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          exact .bitNot snapshot write (tailIH (by omega) signatures expressible fault
            (kept.bitNots (CellAwareInvocationAcceptedSizedLifting.bare_keys snapshot) write))
  | projectedBitNotted assignable keys _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    intro kept
    cases failed with
    | head fault =>
      cases fault with
      | assignBitNot fault =>
        cases fault with
        | target failed =>
          cases failed with
          | unbound missing => exact .projectedBitNotRootFault assignable.2.1 (.unbound missing)
          | dangling lookup missing => exact .projectedBitNotRootFault assignable.2.1 (.dangling lookup missing)
          | projectionExpression lookup read failed =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            exact .projectedBitNotKeysFault assignable.2.1 (.intro lookup read)
              (projections_fault lift faultLift keys (by omega) signatures expressible failed kept)
          | danglingAfterProjections lookup read evaluate missing =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
            exact .projectedBitNotGetterFault assignable.2.1 staged (.dangling lookup read ordered missing)
          | projectionRead lookup initialRead evaluate currentRead initialValue failed =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
            exact .projectedBitNotGetterFault assignable.2.1 staged
              (.projection lookup initialRead ordered currentRead initialValue failed)
          | uninitialized lookup initialRead evaluate currentRead empty notMapping nonempty =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
            exact .projectedBitNotGetterFault assignable.2.1 staged
              (.uninitialized lookup initialRead ordered currentRead empty notMapping nonempty)
          | elementPrefix projectionsEq _
          | elementIndex projectionsEq _ _ _
          | elementIndexType projectionsEq _ _ _ _ _
          | elementOutOfBounds projectionsEq _ _ _ _ _ _
          | elementUninitialized projectionsEq _ _ =>
            exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
        | uninitialized resolve empty =>
          exfalso
          cases resolve with
          | intro _ _ evaluate _ _ selection =>
            obtain ⟨_, present⟩ := read_selects selection (.inr (evaluated_nonempty assignable.2.1 evaluate))
            cases present.symm.trans empty
          | element projectionsEq =>
            exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
        | operand resolve selected invalid =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
          exact .projectedBitNotOperandFault assignable.2.1 staged snapshot selected invalid
    | tail head fault =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
          have target := CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept
          exact .projectedBitNot assignable.2.1 staged snapshot write (tailIH (by omega) signatures expressible fault
            (target.1.bitNots target.2 write))

/-- The sized Source fault of a `for` loop whose condition `child` admits,
whose body lifts within the bound and whose post header is supported, with an
expressible reason at a context with the program's signatures, is a staged
fault of the loop with the same heap. -/
private theorem for_fault_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard)
    (faultLift : ChildFaultLifts program registry scope child bound plan closures guard) {condition : ExpressionId}
    {post : List ForItemForm} {body : List StatementId} (test : child condition)
    (inner : ∀ {size : Nat} {context environment before innerContext outcome after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before body
        innerContext outcome after →
      Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard outcome ∧
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (CellAwareInvocationAcceptedStatementLifting.control outcome) after)
    (innerFault : ∀ {size : Nat} {context environment before innerContext after} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.StatementsFault program size context scope.evidence scope.source environment before body
        innerContext reason after →
      Kept plan closures guard before →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (.fault (.semantic reason)) after)
    (postShape : CellAwareInvocationAcceptedBodyShape.ItemsShape scope.source child post) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ForLoopFaults program size context scope.evidence scope.source environment before
        condition post body reason after →
      Kept plan closures guard before →
      Staging.Recursive.ForLoop program registry scope context environment before condition post body
        (.fault (.semantic reason)) after := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context environment before after reason within signatures expressible failed
    intro kept
    cases failed with
    | condition fault =>
      exact .testFault (faultLift test
        (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within) signatures expressible fault kept)
    | conditionType => simp [Expressible] at expressible
    | body evaluate fault =>
      have tested := lift test (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within)
        evaluate kept
      exact .bodyFailure (lift test (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within)
        evaluate kept).2.2
        (innerFault (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
          signatures expressible fault tested.1)
    | postFallthrough evaluate executes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      exact .postFailure tested.2.2 ran.2.2
        (items_fault_lift lift faultLift postShape (by omega) signatures expressible fault ran.1)
    | postContinue evaluate executes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      exact .continuePostFailure tested.2.2 ran.2.2
        (items_fault_lift lift faultLift postShape (by omega) signatures expressible fault ran.1)
    | nextFallthrough evaluate executes postExecutes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      have posted := CellAwareInvocationAcceptedSizedLifting.items_lift lift postShape (by omega) postExecutes ran.1
      exact .iterate tested.2.2 ran.2.2
        posted.2.1
        (ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) signatures expressible fault posted.1)
    | nextContinue evaluate executes postExecutes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      have tested := lift test (by omega) evaluate kept
      have ran := inner (by omega) executes tested.1
      have posted := CellAwareInvocationAcceptedSizedLifting.items_lift lift postShape (by omega) postExecutes ran.1
      exact .continueIterate tested.2.2 ran.2.2
        posted.2.1
        (ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) signatures expressible fault posted.1)

/-- The sized Source fault of a match whose scrutinee `child` admits and whose selected body's faults lift
within the bound, with an expressible reason at a context with the program's signatures, is a staged fault of
the match with the same heap: a fault of its scrutinee, an invalid pattern, or a fault of its selected body. -/
private theorem match_fault {child : ExpressionId → Prop} {bound : Nat} (unique : NodeOccurrencesUnique scope.source)
    (lift : ChildLifts program registry scope child bound plan closures guard)
    (faultLift : ChildFaultLifts program registry scope child bound plan closures guard) {id : StatementId}
    {node : StatementNode} (found : scope.source.lookupStatement? id = some node) {resolution : MatchResolution}
    (form : node.form = .matchWith resolution) (scrutinee : child resolution.scrutinee)
    {reason : Dynamic.SemanticFault}
    (body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
      ∀ {size : Nat} {context environment before innerContext after}, size ≤ bound →
      context.signatures = program.signatures →
      SourceExecutionSize.StatementsFault program size context scope.evidence scope.source environment before
        statements innerContext reason after →
      Kept plan closures guard before →
      Staging.Recursive.StatementsIn program registry false scope context environment before statements
        innerContext (.fault (.semantic reason)) after)
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} (within : size ≤ bound) (signatures : context.signatures = program.signatures)
    (expressible : Expressible reason)
    (fault : SourceExecutionSize.StatementFaults program size context scope.evidence scope.source environment
      before id reason after) (kept : Kept plan closures guard before) :
    Staging.Recursive.Match program registry scope context environment before resolution
      (.fault (.semantic reason)) after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | matchScrutinee contains formEq failed =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .scrutineeFault (faultLift scrutinee
      (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within) signatures expressible failed kept)
  | matchPattern contains formEq scrutineeContains evaluate allocate invalid =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .patternFault scrutineeContains
      (lift scrutinee (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within) evaluate kept).2.2
      allocate invalid
  | matchArmBody contains formEq scrutineeContains evaluate allocate select bindersEq valuesEq extended allocated
      failed =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    subst bindersEq valuesEq
    obtain ⟨arm, member, same⟩ := (CellAwareInvocationAcceptedStatementLifting.selected_body select).1 _ _ rfl
    have tested :=
      lift scrutinee (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within) evaluate kept
    exact .arm scrutineeContains
      tested.2.2
      allocate select extended allocated
      (body (.inl ⟨arm, member, same⟩)
        (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
        (extended.signatures_eq.trans signatures) failed
        ((tested.1.allocates tested.2.1 allocate).binders (fun on => Value.of_arm select (tested.2.1 on)) allocated))
  | matchDefaultBody contains formEq scrutineeContains evaluate allocate select failed =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    have tested :=
      lift scrutinee (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within) evaluate kept
    exact .default scrutineeContains
      tested.2.2
      allocate select
      (body (.inr ((CellAwareInvocationAcceptedStatementLifting.selected_body select).2 _ rfl))
        (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
        signatures failed (tested.1.allocates tested.2.1 allocate))
  | _ =>
    exfalso
    clear lift faultLift body kept
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

/-- A sized fault execution of a supported statement list with an expressible
reason, at a context with the program's signatures and from a heap that keeps
the stored functions, is a staged fault execution with the same context, reason
and heap, given the value and fault liftings of its expressions below the size. -/
theorem statements_fault (unique : NodeOccurrencesUnique scope.source) {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound plan closures guard)
    (faultLift : ChildFaultLifts program registry scope child bound plan closures guard) {mode : Bool}
    {statements : List StatementId} (shape : Shape scope.source expected child mode statements) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      FaultOriginal program size mode context scope.evidence scope.source environment before statements finalContext
        reason after →
      Kept plan closures guard before →
      Staging.Recursive.StatementsIn program registry mode scope context environment before statements finalContext
        (.fault (.semantic reason)) after := by
  induction shape with
  | @nil mode _ =>
    intro size context environment before after finalContext reason _ _ _ original
    cases mode <;> unfold FaultOriginal at original <;> cases original
  | returned found form value =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after _ _ _ _ _ head _
      obtain ⟨_, _, _, _, _, impossible⟩ := CellAwareInvocationAcceptedSizedLifting.returned_inv unique found form head
      cases impossible
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      obtain ⟨_, childBelow, fault⟩ := return_fault_inv unique found form fault
      exact .returnFault (lookupStatement?_sound found) form
        (faultLift value (by omega) signatures expressible fault kept)
  | returnUnit found form =>
    intro size context environment before after finalContext reason _ signatures _ original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after _ _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := CellAwareInvocationAcceptedSizedLifting.return_unit_inv unique found form head
      cases impossible
    · intro context environment before after _ _ _ fault
      exact (return_unit_fault_inv unique found form fault).elim
  | declared found form monomorphic value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, _, _, childBelow, evaluate, extension, allocate, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.declared_inv unique found form monomorphic head
      cases same
      have evaluated := lift value (by omega) evaluate kept
      exact .letInitialized (lookupStatement?_sound found) form evaluated.2.2
        monomorphic extension allocate
        (tailIH (by omega) (extension.context_fields.1.trans signatures) expressible next
          (evaluated.1.allocates evaluated.2.1 allocate))
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      obtain ⟨_, childBelow, fault⟩ := declared_fault_inv unique found form monomorphic fault
      exact .letFault (lookupStatement?_sound found) form monomorphic
        (faultLift value (by omega) signatures expressible fault kept)
  | uninitialized found form monomorphic _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, extension, allocate, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.uninitialized_inv unique found form head
      cases same
      exact .letUninitialized (lookupStatement?_sound found) form monomorphic extension allocate
        (tailIH (by omega) (extension.context_fields.1.trans signatures) expressible next
          (kept.allocates_none allocate))
    · intro context environment before after _ _ _ fault
      exact (uninitialized_fault_inv unique found form monomorphic fault).elim
  | assigned found form assignable value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        have below := childBelow
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        have evaluated := lift value (by omega) evaluate kept
        exact .assignBare (lookupStatement?_sound found) form snapshot
          (lift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) evaluate kept).2.2
          write (tailIH (by omega) signatures expressible next
            (evaluated.1.assigns (CellAwareInvocationAcceptedSizedLifting.bare_keys snapshot) evaluated.2.1 write))
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      have contains := lookupStatement?_sound found
      obtain ⟨_, childBelow, fault⟩ := assigned_fault_inv unique found form fault
      cases fault with
      | target failed => exact bare_target_fault contains form assignable.2.1 failed
      | rhs resolve failed =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .assignBareFault contains form snapshot
          (faultLift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) signatures expressible failed kept)
      | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .assignBareOperands contains form snapshot
          (lift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) evaluate kept).2.2 currentRead rootType initialValue pathRead invalid
      | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .assignBarePanic contains form snapshot
          (lift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) evaluate kept).2.2 currentRead rootType initialValue pathRead panics
      | structuralUpdate resolve _ _ _ _ failed =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        cases snapshot
        cases failed
  | projectedAssigned found form assignable keys value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
        have target := CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept
        have evaluated := lift value (by omega) evaluate target.1
        exact .assignProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot
          evaluated.2.2 write (tailIH (by omega) signatures expressible next
            (evaluated.1.assigns target.2 evaluated.2.1 write))
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      have contains := lookupStatement?_sound found
      obtain ⟨_, childBelow, fault⟩ := assigned_fault_inv unique found form fault
      cases fault with
      | target failed =>
        cases failed with
        | unbound missing => exact .assignProjectedRootFault contains form assignable.2.1 (.unbound missing)
        | dangling lookup missing =>
          exact .assignProjectedRootFault contains form assignable.2.1 (.dangling lookup missing)
        | projectionExpression lookup read failed =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          exact .assignProjectedKeysFault contains form assignable.2.1 (.intro lookup read)
            (projections_fault lift faultLift keys (by omega) signatures expressible failed kept)
        | danglingAfterProjections lookup read evaluate missing =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
          exact .assignProjectedGetterFault contains form assignable.2.1 staged (.dangling lookup read ordered missing)
        | projectionRead lookup initialRead evaluate currentRead initialValue failed =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
          exact .assignProjectedGetterFault contains form assignable.2.1 staged
            (.projection lookup initialRead ordered currentRead initialValue failed)
        | uninitialized lookup initialRead evaluate currentRead empty notMapping nonempty =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
          exact .assignProjectedGetterFault contains form assignable.2.1 staged
            (.uninitialized lookup initialRead ordered currentRead empty notMapping nonempty)
        | elementPrefix projectionsEq _
        | elementIndex projectionsEq _ _ _
        | elementIndexType projectionsEq _ _ _ _ _
        | elementOutOfBounds projectionsEq _ _ _ _ _ _
        | elementUninitialized projectionsEq _ _ =>
          exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
      | rhs resolve failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
        have keptTarget := (CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept).1
        exact .assignProjectedRhsFault contains form assignable.2.1 staged snapshot
          (faultLift value (by omega) signatures expressible failed keptTarget)
      | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
        have keptTarget := (CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept).1
        exact .assignProjectedWriteFault contains form assignable.2.1 staged snapshot
          (lift value (by omega) evaluate keptTarget).2.2
          (.operands currentRead rootType initialValue pathRead invalid)
      | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
        have keptTarget := (CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept).1
        exact .assignProjectedWriteFault contains form assignable.2.1 staged snapshot
          (lift value (by omega) evaluate keptTarget).2.2
          (.panic currentRead rootType initialValue pathRead panics)
      | structuralUpdate resolve evaluate currentRead rootType initialValue failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
        have keptTarget := (CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept).1
        exact .assignProjectedWriteFault contains form assignable.2.1 staged snapshot
          (lift value (by omega) evaluate keptTarget).2.2
          (.structural currentRead rootType initialValue failed)
  | bitNotted found form assignable _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, _, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .bitNotBare (lookupStatement?_sound found) form snapshot write
          (tailIH (by omega) signatures expressible next
            (kept.bitNots (CellAwareInvocationAcceptedSizedLifting.bare_keys snapshot) write))
    · intro context environment before after _ _ _ fault
      intro _
      obtain ⟨_, _, fault⟩ := bitNotted_fault_inv unique found form fault
      have unchanged := Staging.Recursive.bitNot_fault_heap assignable.2.1 fault.sound
      subst unchanged
      exact .bitNotBareFault (lookupStatement?_sound found) form assignable.2.1 fault.sound
  | projectedBitNotted found form assignable keys _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
        have target := CellAwareInvocationAcceptedSizedLifting.target_kept lift keys (by omega) resolve kept
        exact .bitNotProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot write
          (tailIH (by omega) signatures expressible next (target.1.bitNots target.2 write))
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      have contains := lookupStatement?_sound found
      obtain ⟨_, childBelow, fault⟩ := bitNotted_fault_inv unique found form fault
      cases fault with
      | target failed =>
        cases failed with
        | unbound missing => exact .bitNotProjectedRootFault contains form assignable.2.1 (.unbound missing)
        | dangling lookup missing =>
          exact .bitNotProjectedRootFault contains form assignable.2.1 (.dangling lookup missing)
        | projectionExpression lookup read failed =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          exact .bitNotProjectedKeysFault contains form assignable.2.1 (.intro lookup read)
            (projections_fault lift faultLift keys (by omega) signatures expressible failed kept)
        | danglingAfterProjections lookup read evaluate missing =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
          exact .bitNotProjectedGetterFault contains form assignable.2.1 staged (.dangling lookup read ordered missing)
        | projectionRead lookup initialRead evaluate currentRead initialValue failed =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
          exact .bitNotProjectedGetterFault contains form assignable.2.1 staged
            (.projection lookup initialRead ordered currentRead initialValue failed)
        | uninitialized lookup initialRead evaluate currentRead empty notMapping nonempty =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate kept
          exact .bitNotProjectedGetterFault contains form assignable.2.1 staged
            (.uninitialized lookup initialRead ordered currentRead empty notMapping nonempty)
        | elementPrefix projectionsEq _
        | elementIndex projectionsEq _ _ _
        | elementIndexType projectionsEq _ _ _ _ _
        | elementOutOfBounds projectionsEq _ _ _ _ _ _
        | elementUninitialized projectionsEq _ _ =>
          exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
      | uninitialized resolve empty =>
        exfalso
        cases resolve with
        | intro _ _ evaluate _ _ selection =>
          obtain ⟨_, present⟩ := read_selects selection (.inr (evaluated_nonempty assignable.2.1 evaluate))
          cases present.symm.trans empty
        | element projectionsEq =>
          exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
      | operand resolve selected invalid =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve kept
        exact .bitNotProjectedOperandFault contains form assignable.2.1 staged snapshot selected invalid
  | elementAssigned found form _ single index value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        have target := CellAwareInvocationAcceptedSizedLifting.element_kept lift single index (by omega) resolve kept
        have evaluated := lift value (by omega) evaluate target.1
        exact .assignElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (CellAwareInvocationAcceptedSizedLifting.element_resolved lift single index (by omega) kept
            resolve)
          evaluated.2.2 write (tailIH (by omega) signatures expressible next
            (evaluated.1.assigns target.2 evaluated.2.1 write))
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      have contains := lookupStatement?_sound found
      have element := CellAwareElementTargetLifting.element_place single
      obtain ⟨_, childBelow, fault⟩ := assigned_fault_inv unique found form fault
      cases fault with
      | target failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .assignElementTargetFault contains form element
          (element_fault lift faultLift single index (by omega) signatures expressible failed kept)
      | rhs resolve failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        have target := CellAwareInvocationAcceptedSizedLifting.element_kept lift single index (by omega) resolve kept
        exact .assignElementRhsFault contains form element
          (CellAwareInvocationAcceptedSizedLifting.element_resolved lift single index (by omega) kept
            resolve)
          (faultLift value (by omega) signatures expressible failed target.1)
      | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        have target := CellAwareInvocationAcceptedSizedLifting.element_kept lift single index (by omega) resolve kept
        exact .assignElementWriteFault contains form element
          (CellAwareInvocationAcceptedSizedLifting.element_resolved lift single index (by omega) kept
            resolve)
          (lift value (by omega) evaluate target.1).2.2 (.operands currentRead rootType initialValue pathRead invalid)
      | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        have target := CellAwareInvocationAcceptedSizedLifting.element_kept lift single index (by omega) resolve kept
        exact .assignElementWriteFault contains form element
          (CellAwareInvocationAcceptedSizedLifting.element_resolved lift single index (by omega) kept
            resolve)
          (lift value (by omega) evaluate target.1).2.2 (.panic currentRead rootType initialValue pathRead panics)
      | structuralUpdate resolve evaluate currentRead rootType initialValue failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        have target := CellAwareInvocationAcceptedSizedLifting.element_kept lift single index (by omega) resolve kept
        exact .assignElementWriteFault contains form element
          (CellAwareInvocationAcceptedSizedLifting.element_resolved lift single index (by omega) kept
            resolve)
          (lift value (by omega) evaluate target.1).2.2 (.structural currentRead rootType initialValue failed)
  | elementBitNotted found form _ single index _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        have target := CellAwareInvocationAcceptedSizedLifting.element_kept lift single index (by omega) resolve kept
        exact .bitNotElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (CellAwareInvocationAcceptedSizedLifting.element_resolved lift single index (by omega) kept
            resolve)
          write (tailIH (by omega) signatures expressible next (target.1.bitNots target.2 write))
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      have contains := lookupStatement?_sound found
      have element := CellAwareElementTargetLifting.element_place single
      obtain ⟨_, childBelow, fault⟩ := bitNotted_fault_inv unique found form fault
      cases fault with
      | target failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .bitNotElementTargetFault contains form element
          (element_fault lift faultLift single index (by omega) signatures expressible failed kept)
      | uninitialized resolve empty =>
        exact absurd empty (CellAwareElementTargetLifting.selected_ne_none single resolve.sound)
      | operand resolve selected invalid =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .bitNotElementOperandFault contains form element
          (CellAwareInvocationAcceptedSizedLifting.element_resolved lift single index (by omega) kept
            resolve)
          selected invalid
  | discarded found form value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, childBelow, evaluate, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.discarded_inv unique found form head
      cases same
      have evaluated := lift value (by omega) evaluate kept
      exact .discard (lookupStatement?_sound found) form evaluated.2.2
        (tailIH (by omega) signatures expressible next evaluated.1)
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      obtain ⟨_, childBelow, fault⟩ := expression_fault_inv unique found form fault
      exact .expressionFault (lookupStatement?_sound found) form
        (faultLift value (by omega) signatures expressible fault kept)
  | block found form inner _ innerIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, innerOutcome, innerBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.block_inv unique found form head
      cases innerOutcome with
      | fallthrough innerEnvironment =>
        cases same
        have ran := CellAwareInvocationAcceptedSizedLifting.statements unique lift inner (by omega) executes kept
        exact .blockFallthrough (lookupStatement?_sound found) form
          ran.2.2
          (tailIH (by omega) signatures expressible next ran.1)
      | _ => cases same
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      obtain ⟨_, _, innerBelow, fault⟩ := block_fault_inv unique found form fault
      exact .blockFault (lookupStatement?_sound found) form (innerIH (by omega) signatures expressible fault kept)
  | @conditional mode id rest node condition thenBody elseBody found form test left right _ leftIH rightIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    have branch : ∀ {truth : Bool} {innerSize : Nat} {context environment before innerContext inner after},
        innerSize ≤ bound →
        SourceExecutionSize.StatementsExecute program innerSize context scope.evidence scope.source environment before
          (if truth then thenBody else elseBody.getD []) innerContext inner after →
        Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard inner ∧
        Staging.Recursive.StatementsIn program registry false scope context environment before
          (if truth then thenBody else elseBody.getD []) innerContext
          (CellAwareInvocationAcceptedStatementLifting.control inner) after := by
      intro truth innerSize context environment before innerContext inner after within executes
      cases truth
      · exact CellAwareInvocationAcceptedSizedLifting.statements unique lift right within executes
      · exact CellAwareInvocationAcceptedSizedLifting.statements unique lift left within executes
    have branchFault : ∀ {truth : Bool} {innerSize : Nat} {context environment before innerContext after},
        innerSize ≤ bound → context.signatures = program.signatures →
        SourceExecutionSize.StatementsFault program innerSize context scope.evidence scope.source environment before
          (if truth then thenBody else elseBody.getD []) innerContext reason after →
        Kept plan closures guard before →
        Staging.Recursive.StatementsIn program registry false scope context environment before
          (if truth then thenBody else elseBody.getD []) innerContext (.fault (.semantic reason)) after := by
      intro truth innerSize context environment before innerContext after within signatures failed
      cases truth
      · exact rightIH within signatures expressible failed
      · exact leftIH within signatures expressible failed
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨rfl, _, _, truth, _, _, innerOutcome, testBelow, innerBelow, evaluate, executes, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.conditional_inv unique found form head
      cases innerOutcome with
      | fallthrough innerEnvironment =>
        cases same
        have tested := lift test (by omega) evaluate kept
        have ran := branch (by omega) executes tested.1
        exact .ifFallthrough (lookupStatement?_sound found) form tested.2.2
          ran.2.2 (tailIH (by omega) signatures expressible next ran.1)
      | _ => cases same
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      rcases conditional_fault_inv unique found form fault with
        ⟨_, testBelow, failed⟩ | ⟨_, _, rfl⟩ | ⟨_, _, truth, _, _, testBelow, innerBelow, evaluate, failed⟩
      · exact .ifConditionFault (lookupStatement?_sound found) form
          (faultLift test (by omega) signatures expressible failed kept)
      · simp [Expressible] at expressible
      · have tested := lift test (by omega) evaluate kept
        exact .ifFault (lookupStatement?_sound found) form tested.2.2
          (branchFault (by omega) signatures failed tested.1)
  | @matched mode id rest node resolution found form scrutinee arms fallback _ armsIH fallbackIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    have body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
        ∀ {innerSize : Nat} {context environment before innerContext inner after}, innerSize ≤ bound →
        SourceExecutionSize.StatementsExecute program innerSize context scope.evidence scope.source environment
          before statements innerContext inner after →
        Kept plan closures guard before → Kept plan closures guard after ∧ KeptOutcome plan closures guard inner ∧
        Staging.Recursive.StatementsIn program registry false scope context environment before statements
          innerContext (CellAwareInvocationAcceptedStatementLifting.control inner) after := by
      intro statements selected innerSize context environment before innerContext inner after within executes
      rcases selected with ⟨arm, member, rfl⟩ | same
      · exact CellAwareInvocationAcceptedSizedLifting.statements unique lift (arms arm member) within executes
      · rw [same] at fallback
        exact CellAwareInvocationAcceptedSizedLifting.statements unique lift fallback within executes
    have bodyFault : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
        ∀ {innerSize : Nat} {context environment before innerContext after}, innerSize ≤ bound →
        context.signatures = program.signatures →
        SourceExecutionSize.StatementsFault program innerSize context scope.evidence scope.source environment
          before statements innerContext reason after →
        Kept plan closures guard before →
        Staging.Recursive.StatementsIn program registry false scope context environment before statements
          innerContext (.fault (.semantic reason)) after := by
      intro statements selected innerSize context environment before innerContext after within signatures failed
      rcases selected with ⟨arm, member, rfl⟩ | same
      · exact armsIH arm member within signatures expressible failed
      · rw [same] at fallbackIH
        exact fallbackIH within signatures expressible failed
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨rfl, inner, same, keptMiddle, _, staged⟩ :=
        CellAwareInvocationAcceptedSizedLifting.match_lift unique lift found form scrutinee body (by omega) head kept
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .matchFallthrough (lookupStatement?_sound found) form staged
          (tailIH (by omega) signatures expressible next keptMiddle)
      | _ => cases same
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      exact .matchFault (lookupStatement?_sound found) form
        (match_fault unique lift faultLift found form scrutinee bodyFault (by omega) signatures expressible fault kept)
  | breaking found form =>
    intro size context environment before after finalContext reason _ signatures _ original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after _ _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := CellAwareInvocationAcceptedSizedLifting.break_inv unique found form head
      cases impossible
    · intro context environment before after _ _ _ fault
      exact (jump_fault_inv unique found (.inl form) fault).elim
  | continuing found form =>
    intro size context environment before after finalContext reason _ signatures _ original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after _ _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := CellAwareInvocationAcceptedSizedLifting.continue_inv unique found form head
      cases impossible
    · intro context environment before after _ _ _ fault
      exact (jump_fault_inv unique found (.inr form) fault).elim
  | whileLooped found form test inner _ innerIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, loopOutcome, loopBelow, iterate, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.while_inv unique found form head
      obtain ⟨keptMiddle, _, loop, ended⟩ := CellAwareInvocationAcceptedSizedLifting.while_lift lift test
        (fun within executes => CellAwareInvocationAcceptedSizedLifting.statements unique lift inner within executes)
        (by omega) iterate kept
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        exact .whileFallthrough (lookupStatement?_sound found) form loop
          (tailIH (by omega) signatures expressible next keptMiddle)
      · cases same
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      obtain ⟨_, loopBelow, failed⟩ := while_fault_inv unique found form fault
      exact .whileFault (lookupStatement?_sound found) form
        (while_fault_lift lift faultLift test
          (fun within executes => CellAwareInvocationAcceptedSizedLifting.statements unique lift inner within executes)
          (fun within signatures expressible failed => innerIH within signatures expressible failed)
          (by omega) signatures expressible failed kept)
  | forLooped found form initialItems test inner postItems _ innerIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      intro kept
      obtain ⟨_, _, _, _, _, _, loopOutcome, firstBelow, secondBelow, initialized, iterate, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.for_inv unique found form head
      have initial := CellAwareInvocationAcceptedSizedLifting.items_lift lift initialItems (by omega) initialized kept
      obtain ⟨keptMiddle, _, loop, ended⟩ := CellAwareInvocationAcceptedSizedLifting.for_lift lift test
        (fun within executes => CellAwareInvocationAcceptedSizedLifting.statements unique lift inner within executes)
        postItems (by omega) iterate initial.1
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        exact .forFallthrough (lookupStatement?_sound found) form
          initial.2.1 loop
          (tailIH (by omega) signatures expressible next keptMiddle)
      · cases same
    · intro context environment before after headSize headBelow signatures fault
      intro kept
      rcases for_fault_inv unique found form fault with
        ⟨_, _, initialBelow, failed⟩ | ⟨_, _, _, _, _, firstBelow, secondBelow, initialized, failed⟩
      · exact .forInitializerFault (lookupStatement?_sound found) form
          (items_fault_lift lift faultLift initialItems (by omega) signatures expressible failed kept)
      · obtain ⟨keptInitial, initial, sameSignatures⟩ :=
          CellAwareInvocationAcceptedSizedLifting.items_lift lift initialItems (by omega) initialized kept
        exact .forFault (lookupStatement?_sound found) form initial
          (for_fault_lift lift faultLift test
            (fun within executes => CellAwareInvocationAcceptedSizedLifting.statements unique lift inner within executes)
            (fun within signatures expressible failed => innerIH within signatures expressible failed)
            postItems (by omega) (sameSignatures.trans signatures) expressible failed keptInitial)
  | tail found form _ value =>
    intro size context environment before after finalContext reason within signatures expressible original
    intro kept
    unfold FaultOriginal at original
    cases original with
    | singleton fault =>
      obtain ⟨_, childBelow, fault⟩ := expression_fault_inv unique found form fault
      exact .expressionFault (lookupStatement?_sound found) form
        (faultLift value (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) signatures expressible fault kept)
    | tailExpression contains formEq fault =>
      obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
      rw [form] at formEq
      cases formEq
      exact .expressionFault (lookupStatement?_sound found) form
        (faultLift value (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within)
          signatures expressible fault kept)

/-- Every admitted callee's original body fault is a staged fault execution
at every size: the strong induction on the size across bodies that lifts
their values, given that their direct calls have plain callees. -/
theorem bodies_fault (callees : Callees prepared program registry called)
    (plain : CalleesFault program called) (bound : Nat) :
    BodiesFaultLift program registry called bound prepared.base.plan closures guard := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro instantiation bodyInstance statements admitted instantiates rootsEq
    obtain ⟨child, named, expected, closure, unique, shape⟩ := callees admitted instantiates rootsEq
    refine ⟨child, closure, ?_⟩
    intro size context environment before after finalContext reason below signatures expressible trace
    have sourceEq : child.source = bodyInstance.source := registry.source closure
    have evidenceEq : child.evidence = [] := registry.evidence closure
    have childUnique : NodeOccurrencesUnique child.source := sourceEq ▸ unique
    have childPlain : CalleesPlain child.source := sourceEq ▸ plain admitted instantiates
    have childShape : Shape child.source expected (Nested prepared named child.source called) true statements := by
      rw [sourceEq]
      exact shape
    have values : BodiesLift program registry called size prepared.base.plan closures guard :=
      CellAwareInvocationAcceptedCallLifting.bodies prepared callees
        (fun admitted instantiates indirect => ((plain admitted instantiates).no_indirect indirect).elim) size
    refine statements_fault childUnique
      (CellAwareInvocationAcceptedCallLifting.nested_roots prepared childUnique values
        (fun indirect => (childPlain.no_indirect indirect).elim))
      (nested_fault_roots prepared childUnique childPlain values (ih size below)) childShape (Nat.le_refl size)
      signatures expressible ?_
    show SourceExecutionSize.FunctionStatementsFault program size context child.evidence child.source environment
      before statements finalContext reason after
    rw [sourceEq, evidenceEq]
    exact trace

/-- An ordinary function-body fault of a supported list whose expressions are
nested sites, with an expressible reason at a context with the program's
signatures, is a staged fault execution with the same context, reason and
heap, at any scope with the execution's Source and evidence, given that the
direct calls of the body and of the admitted callees have plain callees, the
static receipts of the admitted callees and, in a family with an indirect
call, the stored functions of its starting heap. -/
theorem body_fault {scope : Staging.Recursive.Scope} {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
    (sourceEq : scope.source = source) (evidenceEq : scope.evidence = evidence)
    (unique : NodeOccurrencesUnique source) (plain : CalleesPlain source)
    (callees : Callees prepared program registry called) (calleesPlain : CalleesFault program called)
    {named : SourceCoreGeneralFunctions.Function} {expected : TypeSystem.Ty} {statements : List StatementId}
    (shape : Shape source expected (Nested prepared named source called) true statements)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (signatures : context.signatures = program.signatures) (expressible : Expressible reason)
    (kept : Kept prepared.base.plan closures (FamilyIndirect program called source) before)
    (trace : Dynamic.FunctionStatementsFault program context evidence source environment before statements
      finalContext reason after) :
    ∃ size, Staging.Recursive.Size.Statements program registry size scope context environment before statements
      finalContext (.fault (.semantic reason)) after := by
  subst sourceEq evidenceEq
  obtain ⟨size, sized⟩ := SourceExecutionSize.FunctionStatementsFault.has_size trace
  have values : BodiesLift program registry called size prepared.base.plan closures
      (FamilyIndirect program called scope.source) :=
    CellAwareInvocationAcceptedCallLifting.bodies prepared callees
      (fun admitted instantiates indirect => ((calleesPlain admitted instantiates).no_indirect indirect).elim) size
  exact Staging.Recursive.Size.Statements.of_trace
    (statements_fault unique (CellAwareInvocationAcceptedCallLifting.nested_roots prepared unique values
        (fun indirect => (plain.no_indirect indirect).elim))
      (nested_fault_roots prepared unique plain values (bodies_fault prepared callees calleesPlain size)) shape
      (Nat.le_refl size) signatures expressible sized kept)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFaultLifting
end
