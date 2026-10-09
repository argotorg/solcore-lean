import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! The accepted indirect call has one actual pair argument. Its two numeric
children use the retained intrinsic evidence and leave the Source heap intact.
Admission follows these finite Source rules at the actual caller state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedArgumentAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedOuterTyping
open CallableIndexedNamedGeneration

variable (fixture : AcceptedFixture)

def argumentValue : Dynamic.Value :=
  .product (.word (Word.ofNatModulo 1)) (.word (Word.ofNatModulo 2))

private theorem requirements_of_owned {node : ExpressionNode} {requirements : List RequirementId}
    (coercions : node.coercions = [])
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements) :
    node.requirements = requirements := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements? at owned
  rw [coercions] at owned
  change (if node.requirements.length < 0 then none else
    if node.requirements = node.requirements.take (node.requirements.length - 0) ++ [] then
      some (node.requirements.take (node.requirements.length - 0)) else none) = some requirements at owned
  simpa using owned

private theorem numeric_evaluates {context : SourceSemantics.Context} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
    {number requirement : Nat} {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .integerLiteral literal (argumentResolution number requirement))
    (coercions : node.coercions = [])
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [⟨requirement⟩])
    (meaning : NumericLiteralDenotes literal number)
    (proves : RequirementProves context ⟨requirement⟩ (ProgramSignatures.builtinIntPredicate wordType)) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id
      (.word (Word.ofNatModulo number)) heap := by
  refine .intro (raw := .word (Word.ofNatModulo number)) (middle := heap) (lookupExpression?_sound found) ?_ ?_
  · rw [form]
    refine .integerLiteral ?_ (.word meaning proves)
    simp [Dynamic.OrdinaryRequirementLayout, argumentResolution, coercions,
      requirements_of_owned coercions owned, coercionRequirementIds]
  · rw [coercions]
    exact .nil

private theorem numeric_outcome {context : SourceSemantics.Context} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
    {number requirement : Nat} {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node) (unique : NodeOccurrencesUnique source)
    (form : node.form = .integerLiteral literal (argumentResolution number requirement))
    (coercions : node.coercions = [])
    (meaning : NumericLiteralDenotes literal number)
    (proves : RequirementProves context ⟨requirement⟩ (ProgramSignatures.builtinIntPredicate wordType))
    (safe : ¬ Dynamic.RequirementUnavailable context evidence ⟨requirement⟩)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    outcome = .value (.word (Word.ofNatModulo number)) ∧ after = before := by
  have sameNode : ∀ other, ContainsExpression source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have nonlocal : ∀ name binder, node.form ≠ .reference name (.local binder) := by
    intros
    rw [form]
    simp
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro other raw path =>
      have same := sameNode _ other
      subst same
      rw [coercions] at path
      cases path
      rw [form] at raw
      cases raw with
      | integerLiteral _ constructed =>
        have expected : Dynamic.ResolvedIntegerLiteralConstructs context literal
            (argumentResolution number requirement) (.word (Word.ofNatModulo number)) := .word meaning proves
        exact ⟨congrArg _ (constructed.functional expected), rfl⟩
    | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
      exact False.elim (nonlocal _ _ (sameNode _ contains ▸ otherForm))
  | @fault _ _ reason failed =>
    have rawFault : Dynamic.ExpressionFormFaults program context evidence source environment before
        node.form node.requirements node.coercions reason after := by
      cases failed with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
      | form contains failed => exact sameNode _ contains ▸ failed
      | coercion contains _ failed =>
        have same := sameNode _ contains
        subst same
        rw [coercions] at failed
        cases failed
      | generalizedLocalRequirement contains otherForm _ _ _ _ _ _ _
      | generalizedLocalCoercion contains otherForm _ _ _ _ _ _ _ =>
        exact False.elim (nonlocal _ _ (sameNode _ contains ▸ otherForm))
    rw [form] at rawFault
    cases rawFault with
    | integerRequirement _ unavailable => exact False.elim (safe unavailable)

theorem left_evaluates {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment heap
      (expressionId fixture.packet 7) (.word (Word.ofNatModulo 1)) heap :=
  numeric_evaluates fixture.parentRows.leftFound fixture.parentRows.leftForm
    fixture.parentRows.leftCoercions fixture.parentRows.leftOwned (numericLiteralValue?_sound rfl)
    (numeric_requirement (context := localContext fixture) fixture.runtime.rows (Or.inr (Or.inl rfl)))

theorem right_evaluates {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment heap
      (expressionId fixture.packet 8) (.word (Word.ofNatModulo 2)) heap :=
  numeric_evaluates fixture.parentRows.rightFound fixture.parentRows.rightForm
    fixture.parentRows.rightCoercions fixture.parentRows.rightOwned (numericLiteralValue?_sound rfl)
    (numeric_requirement (context := localContext fixture) fixture.runtime.rows (Or.inr (Or.inr rfl)))

private theorem numeric_safe {evidence : Dynamic.EvidenceEnvironment} {number requirement : Nat}
    (member : requirement = 1 ∨ requirement = 2) :
    ¬ Dynamic.RequirementUnavailable (localContext fixture) evidence ⟨requirement⟩ := by
  have selected : NumericLiteralEvidenceReceipts.Selected numericRows
      (argumentResolution number requirement) (.builtin .intWord) := by
    rcases member with rfl | rfl
    · exact ⟨wordRequirement 1, by simp [numericRows, wordRequirement, argumentResolution], rfl, rfl⟩
    · exact ⟨wordRequirement 2, by simp [numericRows, wordRequirement, argumentResolution], rfl, rfl⟩
  exact selected.safe (context := localContext fixture) fixture.runtime.rows
    (numeric_runtime_ledger (context := localContext fixture) fixture.runtime.rows) evidence

theorem left_outcome {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 7) outcome after) :
    outcome = .value (.word (Word.ofNatModulo 1)) ∧ after = before :=
  numeric_outcome fixture.parentRows.leftFound fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    fixture.parentRows.leftForm fixture.parentRows.leftCoercions (numericLiteralValue?_sound rfl)
    (numeric_requirement (context := localContext fixture) fixture.runtime.rows (Or.inr (Or.inl rfl)))
    (numeric_safe fixture (number := 1) (Or.inl rfl)) trace

theorem right_outcome {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 8) outcome after) :
    outcome = .value (.word (Word.ofNatModulo 2)) ∧ after = before :=
  numeric_outcome fixture.parentRows.rightFound fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    fixture.parentRows.rightForm fixture.parentRows.rightCoercions (numericLiteralValue?_sound rfl)
    (numeric_requirement (context := localContext fixture) fixture.runtime.rows (Or.inr (Or.inr rfl)))
    (numeric_safe fixture (number := 2) (Or.inr rfl)) trace

/-- The actual two children execute in Source order at the same heap. -/
theorem argument_evaluates {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment heap
      (expressionId fixture.packet 6) argumentValue heap := by
  refine .intro (raw := argumentValue) (middle := heap) (lookupExpression?_sound fixture.graph.argumentFound) ?_ ?_
  · rw [fixture.graph.argumentForm]
    exact .tuple (by simp [Dynamic.OrdinaryRequirementLayout, fixture.parentRows.argumentRequirements,
      fixture.parentRows.argumentCoercions, coercionRequirementIds])
      (.cons (left_evaluates fixture) (.cons (right_evaluates fixture) .nil)) (.cons (.singleton _))
  · rw [fixture.parentRows.argumentCoercions]
    exact .nil

private theorem children_values {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {values : List Dynamic.Value}
    (trace : Dynamic.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 7, expressionId fixture.packet 8] values after) :
    values = [.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 2)] ∧ after = before := by
  cases trace with
  | cons left tail =>
    obtain ⟨sameLeft, sameHeap⟩ := left_outcome fixture (.value left)
    cases sameHeap
    have sameValue := Dynamic.ExpressionOutcome.value.inj sameLeft
    cases sameValue
    cases tail with
    | cons right tail =>
      obtain ⟨sameRight, sameHeap⟩ := right_outcome fixture (.value right)
      cases sameHeap
      have sameValue := Dynamic.ExpressionOutcome.value.inj sameRight
      cases sameValue
      cases tail
      exact ⟨rfl, rfl⟩

private theorem children_no_fault {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ExpressionsFault (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 7, expressionId fixture.packet 8] reason after) : False := by
  cases trace with
  | head failed =>
    have impossible := (left_outcome fixture (.fault failed)).1
    cases impossible
  | tail left failed =>
    have sameHeap := (left_outcome fixture (.value left)).2
    cases sameHeap
    cases failed with
    | head failed =>
      have impossible := (right_outcome fixture (.fault failed)).1
      cases impossible
    | tail _ failed => cases failed

/-- Any actual Source outcome of this pair is the same successful value at
its unchanged heap. Numeric fault exclusion uses the original complete ledger. -/
theorem argument_outcome {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 6) outcome after) :
    outcome = .value argumentValue ∧ after = before := by
  have sameNode : ∀ other, ContainsExpression (source fixture.packet.named) (expressionId fixture.packet 6) other →
      other = fixture.graph.argument := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete
      fixture.runtime.source_runtime.graph.nodeOccurrencesUnique contains).symm.trans fixture.graph.argumentFound)
  have nonlocal : ∀ name binder, fixture.graph.argument.form ≠ .reference name (.local binder) := by
    intros
    rw [fixture.graph.argumentForm]
    simp
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro contains raw path =>
      have same := sameNode _ contains
      subst same
      rw [fixture.parentRows.argumentCoercions] at path
      cases path
      rw [fixture.graph.argumentForm] at raw
      cases raw with
      | tuple _ children pack =>
        obtain ⟨sameValues, sameHeap⟩ := children_values fixture children
        cases sameHeap
        rw [sameValues] at pack
        have expected : Dynamic.ValuesPack [.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 2)]
            argumentValue := .cons (.singleton _)
        exact ⟨congrArg _ (pack.functional expected), rfl⟩
    | generalizedLocal contains form _ _ _ _ _ _ _ =>
      exact False.elim (nonlocal _ _ (sameNode _ contains ▸ form))
  | @fault _ _ reason failed =>
    have rawFault : Dynamic.ExpressionFormFaults (Program.ofChecked fixture.packet.compiled.sourceProgram)
        (localContext fixture) evidence (source fixture.packet.named) environment before
        fixture.graph.argument.form fixture.graph.argument.requirements fixture.graph.argument.coercions reason after := by
      cases failed with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent
          (lookupExpression?_sound fixture.graph.argumentFound))
      | form contains failed => exact sameNode _ contains ▸ failed
      | coercion contains _ failed =>
        have same := sameNode _ contains
        subst same
        rw [fixture.parentRows.argumentCoercions] at failed
        cases failed
      | generalizedLocalRequirement contains form _ _ _ _ _ _ _
      | generalizedLocalCoercion contains form _ _ _ _ _ _ _ =>
        exact False.elim (nonlocal _ _ (sameNode _ contains ▸ form))
    rw [fixture.graph.argumentForm] at rawFault
    cases rawFault with
    | tuple _ failed => exact False.elim (children_no_fault fixture failed)

/-- The genuine physical pair has its raw parameter type in the receiving
closure's context, independently of any native representation. -/
theorem value_typed (context : SourceSemantics.Context) (heap : Dynamic.Heap) :
    Dynamic.ValueHasType context heap argumentValue parameterType :=
  .product (.word _) (.word _)

theorem arguments_typed (context : SourceSemantics.Context) (heap : Dynamic.Heap) :
    Dynamic.ValuesHaveTypes context heap [argumentValue] [parameterType] :=
  .cons (value_typed context heap) .nil

section Admission
universe u
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- The actual pair trace supplies success admission at the actual reached
state. Administrative effects carry every row's own history to that state. -/
theorem post_admission {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge (localContext fixture) first)
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (localContext fixture) evidence (source fixture.packet.named) environment initial.heap
      (expressionId fixture.packet 6) outcome reached.heap)
    (frame : GeneralHeap.AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge (localContext fixture) parameterType outcome last := by
  have same := argument_outcome fixture trace
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (bridge.pool first) (bridge.pool last) admitted.rows frame, ?_⟩
  intro value isValue
  have sameValue := Dynamic.ExpressionOutcome.value.inj (isValue.symm.trans same.1)
  cases sameValue
  exact ⟨value_typed _ _, same.2 ▸ admitted.heap⟩

end Admission

end Tests.SourceCoreChosenOrdinaryAcceptedArgumentAdmission
