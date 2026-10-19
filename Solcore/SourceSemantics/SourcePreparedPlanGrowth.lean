import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality

/-! Actual executable-plan growth preserves selected rows and call edges.
All receipts follow accepted helper actions; no independent plan is trusted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.SourcePreparedPlanGrowth
open Frontend SourceInference SourceSpecializationWorklist
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)


structure Growth (before after : Plan) : Prop where
  rows : CoreLowering.CallableCoercionPreparationSteps.Extends before after
  calls : before.callEdges ⊆ after.callEdges

theorem Growth.refl (plan : Plan) : Growth plan plan := ⟨.refl _, fun _ present => present⟩
theorem Growth.trans {first middle last : Plan}
    (left : Growth first middle) (right : Growth middle last) : Growth first last :=
  ⟨left.rows.trans right.rows, fun _ present => right.calls (left.calls present)⟩
theorem Growth.at {before after : Plan} (growth : Growth before after)
    {index : Nat} {value : Specialized} (found : before.specializations[index]? = some value) :
    after.specializations[index]? = some value := growth.rows.at found

theorem runAux_calls_prefix {program : CheckedProgram} {seeds seen : List SourceSpecialization.SpecializationKey}
    {queue : List Request} {entries : List Specialized} {calls : List CallEdge} {references : List ReferenceEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : runAux program seeds queue seen entries calls references budget = .ok outcome) :
    calls <+: outcome.plan.callEdges := by
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
      exact (show calls <+: calls ++ newCalls from ⟨newCalls, rfl⟩).trans (ih accepted)

private def appendEdge (edges : List CallEdge) (edge : CallEdge) : List CallEdge :=
  if edges.contains edge then edges else edges ++ [edge]

private theorem appendEdge_old (edges : List CallEdge) (edge : CallEdge) :
    edges ⊆ appendEdge edges edge := by
  unfold appendEdge
  split
  · exact fun _ present => present
  · exact fun _ present => List.mem_append_left _ present

private theorem appendEdge_new (edges : List CallEdge) (edge : CallEdge) :
    edge ∈ appendEdge edges edge := by
  letI : LawfulBEq CallEdge := by
    exact {
      eq_of_beq := by
        intro left right same
        cases left with
        | mk lc lo lt =>
          cases right with
          | mk rc ro rt =>
            change (lc == rc && (lo == ro && lt == rt)) = true at same
            simp only [Bool.and_eq_true, beq_iff_eq] at same
            rcases same with ⟨rfl,rfl,rfl⟩
            rfl
      rfl := by
        intro edge
        cases edge
        change (_ && (_ && _)) = true
        simp }
  unfold appendEdge
  split
  · rename_i present
    exact List.contains_iff_mem.mp present
  · simp

private theorem appendEdges_members (left right : List CallEdge) :
    left ⊆ right.foldl appendEdge left ∧ right ⊆ right.foldl appendEdge left := by
  induction right generalizing left with
  | nil => exact ⟨fun _ present => present, by simp⟩
  | cons head tail ih =>
    simp only [List.foldl_cons]
    obtain ⟨old, rest⟩ := ih (appendEdge left head)
    refine ⟨fun _ present => old (appendEdge_old left head present), ?_⟩
    intro edge present
    rcases List.mem_cons.mp present with rfl | present
    · exact old (appendEdge_new left _)
    · exact rest present

theorem extend {program : CheckedProgram} {before : Plan} {root : Specialized}
    {edge : CallEdge} {budget : Nat} {outcome : Outcome}
    (accepted : extendCompletePlan program before root edge budget = .ok outcome) :
    Growth before outcome.plan := by
  refine ⟨CoreLowering.CallableCoercionPreparationSteps.extend accepted, ?_⟩
  unfold extendCompletePlan at accepted
  obtain ⟨checked, _, accepted⟩ := bind_ok accepted
  cases checked
  split at accepted <;> try contradiction
  dsimp only at accepted
  split at accepted
  all_goals try (split at accepted <;> try contradiction)
  all_goals
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    have appended := (runAux_calls_prefix accepted).subset
    intro retained present
    apply appended
    apply (appendEdges_members _ calls).1
    apply appendEdge_old
    exact (appendEdges_members [] before.callEdges).2 present

theorem forIn_coverage {α ε : Type} {items : List α} {initial final : Plan}
    {step : α → Plan → Except ε (ForInStep Plan)} {done : α → Plan → Prop}
    (accepted : forIn items initial step = .ok final)
    (monotone : ∀ item before after, Growth before after → done item before → done item after)
    (next : ∀ item ∈ items, ∀ before outcome, step item before = .ok outcome →
      ∃ after, outcome = .yield after ∧ Growth before after ∧ done item after) :
    Growth initial final ∧ ∀ item ∈ items, done item final := by
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
    Growth before after := by
  obtain ⟨method, _, accepted⟩ := bind_ok accepted
  obtain ⟨returned, _, accepted⟩ := bind_ok accepted
  cases returned
  obtain ⟨returned, _, accepted⟩ := bind_ok accepted
  cases returned
  cases extended : extendCompletePlan program before method.specialized
      ⟨caller.key, node.id, method.specialized.key⟩ budget with
  | error error => rw [extended] at accepted; cases accepted
  | ok outcome =>
    rw [extended] at accepted
    cases outcome with
    | budgetExhausted plan next pending => cases accepted
    | complete inserted => cases accepted; exact extend extended

theorem operator_accepted {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {node : ExpressionNode} {before after : Plan} {budget : Nat}
    (accepted : (do
      let requirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
        | some requirements => pure requirements
        | none => throw (.unsupportedRequirements node.requirements)
      if requirements.isEmpty then
        pure before
      else
        let ownedNode := {
          node with type := node.rawType, requirements, coercions := []
        }
        let selection ← match ownedNode.form with
          | .unary operator _ =>
              SourceCompilationPlan.checkedUnaryOperatorMethod program caller ownedNode available operator
          | .binary _ operator _ =>
              SourceCompilationPlan.checkedBinaryOperatorMethod program caller ownedNode available operator
          | _ => throw (.unsupportedRequirements requirements)
        let arguments ← match ownedNode.form with
          | .unary _ operand => pure [operand]
          | .binary left _ right => pure [left, right]
          | _ => throw (.unsupportedRequirements requirements)
        SourceCompilationPlan.validateStagedCallBoundary caller ownedNode arguments
          selection.method.specialized
        discard <| SourceCompilationPlan.operatorMethodRuntimeEvidence program caller ownedNode selection
        let outcome ← match extendCompletePlan program before selection.method.specialized
            ⟨caller.key, node.id, selection.method.specialized.key⟩ budget with
          | .ok outcome => pure outcome
          | .error error => throw (.operatorMethodWorklist caller.key node.id error)
        match outcome with
        | .complete extended => pure extended
        | .budgetExhausted _ next pending =>
            throw (.operatorMethodSpecializationBudgetExhausted caller.key node.id next pending.length)
      : Except SourceTypedRuntime.RuntimeError Plan) = .ok after) :
    Growth before after := by
  cases owned : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none =>
      simp only [owned, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
  | some requirements =>
      simp only [owned] at accepted
      obtain ⟨actualRequirements, sameRequirements, accepted⟩ := bind_ok accepted
      have sameRequirements : actualRequirements = requirements :=
        (Except.ok.inj sameRequirements).symm
      subst actualRequirements
      cases requirements with
      | nil =>
          simp only [List.isEmpty_nil, ite_true, bind, Except.bind, pure,
            Except.pure, Except.ok.injEq] at accepted
          cases accepted
          exact .refl _
      | cons primary remaining =>
          try simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at accepted
          cases form : node.form <;> simp only [form] at accepted <;> try cases accepted
          all_goals
            obtain ⟨selection, selected, accepted⟩ := bind_ok accepted
            obtain ⟨arguments, _, accepted⟩ := bind_ok accepted
            obtain ⟨returned, _, accepted⟩ := bind_ok accepted
            cases returned
            obtain ⟨returned, _, accepted⟩ := bind_ok accepted
            cases returned
            cases extended : extendCompletePlan program before selection.method.specialized
                ⟨caller.key, node.id, selection.method.specialized.key⟩ budget with
            | error error => rw [extended] at accepted; cases accepted
            | ok outcome =>
                rw [extended] at accepted
                cases outcome with
                | budgetExhausted plan next pending => cases accepted
                | complete inserted =>
                    cases accepted
                    exact extend extended

end Solcore.SourceSemantics.SourcePreparedPlanGrowth
