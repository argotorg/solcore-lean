import Solcore.SourceSemantics.CoreLowering.CallableCoercionPlanProvenance

/-! Exact growth of the actual specialization worklist and finite preparation
loops. Positions and complete selected records survive later extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparationSteps
open Frontend SourceInference SourceSpecializationWorklist
abbrev Specialized := SourceSpecialization.SpecializedFunction

theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- Growth retains both the vector prefix and the emitter's exact lookup. -/
structure Extends (before after : Plan) : Prop where
  entries : before.specializations <+: after.specializations
  selected : ∀ key value, SourceCompilationPlan.exactSpecialization before key = .ok value →
    SourceCompilationPlan.exactSpecialization after key = .ok value

theorem Extends.refl (plan : Plan) : Extends plan plan :=
  ⟨List.prefix_refl _, fun _ _ given => given⟩

theorem Extends.trans {first middle last : Plan} (left : Extends first middle) (right : Extends middle last) :
    Extends first last := ⟨left.entries.trans right.entries, fun key value given => right.selected key value (left.selected key value given)⟩

theorem Extends.at {before after : Plan} (growth : Extends before after) {index : Nat} {value : Specialized}
    (found : before.specializations[index]? = some value) : after.specializations[index]? = some value := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨Nat.lt_of_lt_of_le bound growth.entries.length_le, (growth.entries.getElem bound).symm.trans same⟩

/-- The real queue appends complete records, including at budget exhaustion. -/
theorem runAux_prefix {program : CheckedProgram} {seeds seen : List SourceSpecialization.SpecializationKey}
    {queue : List Request} {entries : List Specialized} {calls : List CallEdge} {references : List ReferenceEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : runAux program seeds queue seen entries calls references budget = .ok outcome) :
    entries <+: outcome.plan.specializations := by
  induction budget generalizing queue seen entries calls references outcome with
  | zero =>
    unfold runAux at accepted
    obtain ⟨next, _, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; exact List.prefix_refl _
    | some value => rcases value with ⟨request, selected, rest⟩; cases accepted; exact List.prefix_refl _
  | succ budget ih =>
    unfold runAux at accepted
    obtain ⟨next, _, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; exact List.prefix_refl _
    | some value =>
      rcases value with ⟨request, value, rest⟩
      obtain ⟨⟨requests, newCalls, newReferences⟩, _, accepted⟩ := bind_ok accepted
      exact (show entries <+: entries ++ [value] from ⟨[value], rfl⟩).trans (ih accepted)

theorem extend {program : CheckedProgram} {before : Plan} {root : Specialized} {edge : CallEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : extendCompletePlan program before root edge budget = .ok outcome) : Extends before outcome.plan := by
  refine ⟨?_, (CallableCoercionPlanProvenance.extend accepted).2⟩
  unfold extendCompletePlan at accepted
  obtain ⟨checked, _, accepted⟩ := bind_ok accepted
  cases checked
  split at accepted <;> try contradiction
  dsimp only at accepted
  split at accepted
  · simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    exact (show before.specializations <+: before.specializations ++ [root] from ⟨[root], rfl⟩).trans (runAux_prefix accepted)
  · split at accepted <;> try contradiction
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    exact runAux_prefix accepted

/-- Coverage is obtained from each actual loop step, in its original order.
The law does not remove repeated input items. -/
theorem forIn_coverage {α ε : Type} {items : List α} {initial final : Plan}
    {step : α → Plan → Except ε (ForInStep Plan)} {done : α → Plan → Prop}
    (accepted : forIn items initial step = .ok final)
    (monotone : ∀ item before after, Extends before after → done item before → done item after)
    (next : ∀ item ∈ items, ∀ before outcome, step item before = .ok outcome →
      ∃ after, outcome = .yield after ∧ Extends before after ∧ done item after) :
    Extends initial final ∧ ∀ item ∈ items, done item final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst final
    exact ⟨.refl _, by simp⟩
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, executed, finished⟩ := bind_ok accepted
    obtain ⟨after, rfl, growth, doneItem⟩ := next item (by simp) initial outcome executed
    obtain ⟨tailGrowth, doneRest⟩ := ih finished (fun value member => next value (by simp [member]))
    refine ⟨growth.trans tailGrowth, ?_⟩
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact monotone _ _ _ tailGrowth doneItem
    · exact doneRest value member

/-- A visit retains the real selector, dictionary and extension action. Only
static plan lookup is transported to the eventual prepared plan. -/
structure Visit (program : CheckedProgram) (caller : Specialized)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) (node : ExpressionNode)
    (coercion : CoercionStep) (final : Plan) where
  method : ExecutableImplMethods.CheckedMethod
  dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  before : Plan
  inserted : Plan
  budget : Nat
  selected : SourceCompilationPlan.checkedCoercionMethod program caller node available coercion = .ok method
  staged : SourceCompilationPlan.validateStagedCallBoundary caller node [node.id] method.specialized = .ok ()
  materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node coercion method = .ok dictionary
  extended : extendCompletePlan program before method.specialized
    ⟨caller.key, node.id, method.specialized.key⟩ budget = .ok (.complete inserted)
  finalSelected : SourceCompilationPlan.exactSpecialization final method.specialized.key = .ok method.specialized

def Visit.later {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode}
    {coercion : CoercionStep} {before after : Plan}
    (visit : Visit program caller available node coercion before) (growth : Extends before after) :
    Visit program caller available node coercion after :=
  {visit with finalSelected := growth.selected _ _ visit.finalSelected}

/-- This premise is the actual private helper's body by definitional equality;
no replacement helper is evaluated. -/
theorem coercion_accepted {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode}
    {coercion : CoercionStep} {before after : Plan} {budget : Nat}
    (accepted : (do
      let method ← SourceCompilationPlan.checkedCoercionMethod program caller node available coercion
      SourceCompilationPlan.validateStagedCallBoundary caller node [node.id] method.specialized
      discard <| SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node coercion method
      let outcome ← match extendCompletePlan program before method.specialized
          ⟨caller.key, node.id, method.specialized.key⟩ budget with
        | .ok outcome => pure outcome
        | .error error => throw (.coercionMethodWorklist caller.key node.id coercion.requirement error)
      match outcome with
      | .complete extended => pure extended
      | .budgetExhausted _ next pending =>
          throw (.coercionMethodSpecializationBudgetExhausted caller.key node.id coercion.requirement next pending.length)
      : Except SourceTypedRuntime.RuntimeError Plan) = .ok after) :
    Extends before after ∧ Nonempty (Visit program caller available node coercion after) := by
  obtain ⟨method, selected, accepted⟩ := bind_ok accepted
  obtain ⟨returned, staged, accepted⟩ := bind_ok accepted
  cases returned
  obtain ⟨returned, materialized, accepted⟩ := bind_ok accepted
  cases returned
  have materialized : ∃ dictionary, SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node coercion method = .ok dictionary := by
    cases result : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node coercion method with
    | error error => rw [result] at materialized; cases materialized
    | ok value => exact ⟨value, rfl⟩
  obtain ⟨dictionary, materialized⟩ := materialized
  cases extended : extendCompletePlan program before method.specialized ⟨caller.key, node.id, method.specialized.key⟩ budget with
  | error error => rw [extended] at accepted; cases accepted
  | ok outcome =>
    rw [extended] at accepted
    cases outcome with
    | budgetExhausted plan next pending => cases accepted
    | complete inserted =>
      cases accepted
      exact ⟨extend extended, ⟨⟨method, dictionary, before, _, budget, selected, staged, materialized,
        extended, CallableCoercionPlanProvenance.complete_root extended⟩⟩⟩


/-- Only the two forms traversed by the real operator preparation phase. -/
def OperatorForm (node : ExpressionNode) : Prop :=
  match node.form with
  | .unary _ _ | .binary _ _ _ => True
  | _ => False

def operatorOwnedNode (node : ExpressionNode) (requirements : List RequirementId) : ExpressionNode :=
  {node with type := node.rawType, requirements, coercions := []}

/-- The complete actual operator visit survives later worklist growth. The
owned requirements, staged boundary, materialized dictionary and complete
selected body are all retained separately. -/
structure OperatorVisit (program : CheckedProgram) (caller : Specialized)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) (node : ExpressionNode) (final : Plan) where
  requirements : List RequirementId
  owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements
  nonempty : requirements ≠ []
  selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod
  arguments : List ExpressionId
  dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  before : Plan
  inserted : Plan
  budget : Nat
  selected : (match (operatorOwnedNode node requirements).form with
    | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod program caller
        (operatorOwnedNode node requirements) available operator
    | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod program caller
        (operatorOwnedNode node requirements) available operator
    | _ => throw (.unsupportedRequirements requirements)
    : Except SourceTypedRuntime.RuntimeError SourceCompilationPlan.CheckedRuntimeOperatorMethod) = .ok selection
  argumentsSelected : (match (operatorOwnedNode node requirements).form with
    | .unary _ operand => pure [operand]
    | .binary left _ right => pure [left, right]
    | _ => throw (.unsupportedRequirements requirements)
    : Except SourceTypedRuntime.RuntimeError (List ExpressionId)) = .ok arguments
  staged : SourceCompilationPlan.validateStagedCallBoundary caller (operatorOwnedNode node requirements)
    arguments selection.method.specialized = .ok ()
  materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
    (operatorOwnedNode node requirements) selection = .ok dictionary
  extended : extendCompletePlan program before selection.method.specialized
    ⟨caller.key, node.id, selection.method.specialized.key⟩ budget = .ok (.complete inserted)
  finalSelected : SourceCompilationPlan.exactSpecialization final selection.method.specialized.key =
    .ok selection.method.specialized

def OperatorVisit.later {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode} {before after : Plan}
    (visit : OperatorVisit program caller available node before) (growth : Extends before after) :
    OperatorVisit program caller available node after :=
  {visit with finalSelected := growth.selected _ _ visit.finalSelected}

def OperatorCovered (program : CheckedProgram) (caller : Specialized)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) (node : ExpressionNode) (final : Plan) : Prop :=
  ∀ requirements, SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements →
    requirements ≠ [] → OperatorForm node → Nonempty (OperatorVisit program caller available node final)

theorem OperatorCovered.later {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode} {before after : Plan}
    (covered : OperatorCovered program caller available node before) (growth : Extends before after) :
    OperatorCovered program caller available node after := by
  intro requirements owned nonempty form
  obtain ⟨visit⟩ := covered requirements owned nonempty form
  exact ⟨visit.later growth⟩

/-- Successful operator closure preserves the same carriers while the outer
pass moves on to coercions. Its body is only unfolded in this proof premise. -/
theorem operator_accepted_with_visit {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode}
    {before after : Plan} {budget : Nat}
    (accepted : (do
  let requirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  if requirements.isEmpty then
    pure before
  else
    let ownedNode := {
      node with
      type := node.rawType
      requirements
      coercions := []
    }
    let selection ← match ownedNode.form with
      | .unary operator _ =>
          SourceCompilationPlan.checkedUnaryOperatorMethod program caller ownedNode available
            operator
      | .binary _ operator _ =>
          SourceCompilationPlan.checkedBinaryOperatorMethod program caller ownedNode available
            operator
      | _ => throw (.unsupportedRequirements requirements)
    let arguments ← match ownedNode.form with
      | .unary _ operand => pure [operand]
      | .binary left _ right => pure [left, right]
      | _ => throw (.unsupportedRequirements requirements)
    SourceCompilationPlan.validateStagedCallBoundary caller ownedNode arguments
      selection.method.specialized
    discard <| SourceCompilationPlan.operatorMethodRuntimeEvidence program caller ownedNode
      selection
    let outerEdge : SourceSpecializationWorklist.CallEdge := {
      caller := caller.key
      occurrence := node.id
      callee := selection.method.specialized.key
    }
    let outcome ← match SourceSpecializationWorklist.extendCompletePlan program
        before selection.method.specialized outerEdge budget with
      | .ok outcome => pure outcome
      | .error error => throw (.operatorMethodWorklist caller.key node.id
          error)
    match outcome with
    | .complete extended => pure extended
    | .budgetExhausted _ next pending =>
        throw (.operatorMethodSpecializationBudgetExhausted caller.key
          node.id next pending.length)

      : Except SourceTypedRuntime.RuntimeError Plan) = .ok after) :
    Extends before after ∧ OperatorCovered program caller available node after := by
  cases owned : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => simp only [owned, bind, Except.bind, pure, Except.pure] at accepted; cases accepted
  | some requirements =>
    simp only [owned] at accepted
    obtain ⟨actualRequirements, sameRequirements, accepted⟩ := bind_ok accepted
    have sameRequirements : actualRequirements = requirements := (Except.ok.inj sameRequirements).symm
    subst actualRequirements
    cases requirements with
    | nil =>
      simp only [List.isEmpty_nil, ite_true, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      refine ⟨.refl _, ?_⟩
      intro requirements selected nonempty _
      have same := Option.some.inj (selected.symm.trans owned)
      exact False.elim (nonempty same)
    | cons primary remaining =>
      try simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at accepted
      cases form : node.form <;> simp only [form] at accepted <;> try cases accepted
      all_goals
        obtain ⟨selection, selected, accepted⟩ := bind_ok accepted
        obtain ⟨arguments, argumentsSelected, accepted⟩ := bind_ok accepted
        obtain ⟨returned, staged, accepted⟩ := bind_ok accepted
        cases returned
        obtain ⟨returned, materialized, accepted⟩ := bind_ok accepted
        cases returned
        have materialized : ∃ dictionary, SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
            (operatorOwnedNode node (primary :: remaining)) selection = .ok dictionary := by
          have materializedOwned : (discard (SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
              (operatorOwnedNode node (primary :: remaining)) selection) : Except SourceTypedRuntime.RuntimeError PUnit) = .ok PUnit.unit := by
            simpa only [operatorOwnedNode, form] using materialized
          cases result : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
              (operatorOwnedNode node (primary :: remaining)) selection with
          | error error => rw [result] at materializedOwned; cases materializedOwned
          | ok dictionary => exact ⟨dictionary, rfl⟩
        obtain ⟨dictionary, materialized⟩ := materialized
        cases extended : extendCompletePlan program before selection.method.specialized
            ⟨caller.key, node.id, selection.method.specialized.key⟩ budget with
        | error error => rw [extended] at accepted; cases accepted
        | ok outcome =>
          rw [extended] at accepted
          cases outcome with
          | budgetExhausted plan next pending => cases accepted
          | complete inserted =>
            cases accepted
            refine ⟨extend extended, ?_⟩
            intro _ _ _ _
            refine ⟨{
              requirements := primary :: remaining, owned := owned, nonempty := List.cons_ne_nil _ _
              selection := selection, arguments := arguments, dictionary := dictionary
              before := before, inserted := after, budget := budget
              selected := ?_, argumentsSelected := ?_, staged := ?_, materialized := materialized
              extended := extended, finalSelected := CallableCoercionPlanProvenance.complete_root extended }⟩
            · simpa only [operatorOwnedNode, form] using selected
            · simpa only [operatorOwnedNode, form] using argumentsSelected
            · simpa only [operatorOwnedNode, form] using staged

/-- Successful operator closure preserves the same carriers while the outer
pass moves on to coercions. Its body is only unfolded in this proof premise. -/
theorem operator_accepted {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode}
    {before after : Plan} {budget : Nat}
    (accepted : (do
  let requirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  if requirements.isEmpty then
    pure before
  else
    let ownedNode := {
      node with
      type := node.rawType
      requirements
      coercions := []
    }
    let selection ← match ownedNode.form with
      | .unary operator _ =>
          SourceCompilationPlan.checkedUnaryOperatorMethod program caller ownedNode available
            operator
      | .binary _ operator _ =>
          SourceCompilationPlan.checkedBinaryOperatorMethod program caller ownedNode available
            operator
      | _ => throw (.unsupportedRequirements requirements)
    let arguments ← match ownedNode.form with
      | .unary _ operand => pure [operand]
      | .binary left _ right => pure [left, right]
      | _ => throw (.unsupportedRequirements requirements)
    SourceCompilationPlan.validateStagedCallBoundary caller ownedNode arguments
      selection.method.specialized
    discard <| SourceCompilationPlan.operatorMethodRuntimeEvidence program caller ownedNode
      selection
    let outerEdge : SourceSpecializationWorklist.CallEdge := {
      caller := caller.key
      occurrence := node.id
      callee := selection.method.specialized.key
    }
    let outcome ← match SourceSpecializationWorklist.extendCompletePlan program
        before selection.method.specialized outerEdge budget with
      | .ok outcome => pure outcome
      | .error error => throw (.operatorMethodWorklist caller.key node.id
          error)
    match outcome with
    | .complete extended => pure extended
    | .budgetExhausted _ next pending =>
        throw (.operatorMethodSpecializationBudgetExhausted caller.key
          node.id next pending.length)

      : Except SourceTypedRuntime.RuntimeError Plan) = .ok after) : Extends before after :=
  (operator_accepted_with_visit accepted).1

end Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparationSteps
