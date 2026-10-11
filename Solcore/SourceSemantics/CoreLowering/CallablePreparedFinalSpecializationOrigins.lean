import Solcore.SourceSemantics.CoreLowering.CallablePreparedSpecializationOrigins
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation

/-!
Successful public executable-plan preparation retains real specialization
receipts for every final row. The canonical input replay supplies the original
rows. Actual checked method selectors supply each detached root, and the real
worklist supplies its newly discovered descendants. No source, guard-frame or
stage equality is an input to this producer.

Private nonrecursive preparation actions are exposed only in proof premises,
following the existing preparation coverage proofs. No replacement compiler
action is defined or evaluated here.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationOrigins

open Frontend SourceInference SourceSpecializationWorklist
open CallablePreparedSpecializationOrigins (Receipt)
open CallableCoercionPreparationSteps (bind_ok)

private theorem forIn_receipts {α ε : Type} {items : List α}
    {initial final : Plan} {step : α → Plan → Except ε (ForInStep Plan)}
    (accepted : forIn items initial step = .ok final)
    (receipts : ∀ row ∈ initial.specializations, Receipt row)
    (next : ∀ item ∈ items, ∀ before outcome,
      step item before = .ok outcome →
      (∀ row ∈ before.specializations, Receipt row) →
      ∃ after, outcome = .yield after ∧
        ∀ row ∈ after.specializations, Receipt row) :
    ∀ row ∈ final.specializations, Receipt row := by
  induction items generalizing initial with
  | nil =>
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
      subst final
      exact receipts
  | cons item rest ih =>
      rw [List.forIn_cons] at accepted
      obtain ⟨outcome, executed, finished⟩ := bind_ok accepted
      obtain ⟨after, rfl, afterReceipts⟩ :=
        next item (by simp) initial outcome executed receipts
      exact ih finished afterReceipts
        (fun value member => next value (by simp [member]))

private theorem coercion_receipts {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {node : ExpressionNode} {coercion : CoercionStep}
    {before after : Plan} {budget : Nat}
    (receipts : ∀ row ∈ before.specializations, Receipt row)
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
    ∀ row ∈ after.specializations, Receipt row := by
  obtain ⟨method, selected, accepted⟩ := bind_ok accepted
  obtain ⟨returned, _, accepted⟩ := bind_ok accepted
  cases returned
  obtain ⟨returned, _, accepted⟩ := bind_ok accepted
  cases returned
  obtain ⟨certificate⟩ := CallableCoercionSourceSelection.of_accepted selected
  have rootReceipt := CallablePreparedSpecializationOrigins.of_method_selection
    certificate.selected.toSelection
  cases extended : extendCompletePlan program before method.specialized
      ⟨caller.key, node.id, method.specialized.key⟩ budget with
  | error error => rw [extended] at accepted; cases accepted
  | ok outcome =>
      rw [extended] at accepted
      cases outcome with
      | budgetExhausted plan next pending => cases accepted
      | complete inserted =>
          cases accepted
          exact CallablePreparedSpecializationOrigins.extend_receipts
            receipts rootReceipt extended

private theorem operator_receipts {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {node : ExpressionNode} {before after : Plan} {budget : Nat}
    (receipts : ∀ row ∈ before.specializations, Receipt row)
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
    ∀ row ∈ after.specializations, Receipt row := by
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
          exact receipts
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
            have rootReceipt : Receipt selection.method.specialized := by
              first
              | (obtain ⟨_, _, _, _, _, ⟨certificate⟩⟩ :=
                    CallablePreparedMethodSelection.unary_of_accepted selected
                 exact CallablePreparedSpecializationOrigins.of_method_selection
                   certificate.selected.toSelection)
              | (obtain ⟨_, _, _, _, _, ⟨certificate⟩⟩ :=
                    CallablePreparedMethodSelection.binary_of_accepted selected
                 exact CallablePreparedSpecializationOrigins.of_method_selection
                   certificate.selected.toSelection)
            cases extended : extendCompletePlan program before selection.method.specialized
                ⟨caller.key, node.id, selection.method.specialized.key⟩ budget with
            | error error => rw [extended] at accepted; cases accepted
            | ok outcome =>
                rw [extended] at accepted
                cases outcome with
                | budgetExhausted plan next pending => cases accepted
                | complete inserted =>
                    cases accepted
                    exact CallablePreparedSpecializationOrigins.extend_receipts
                      receipts rootReceipt extended

private theorem aux_receipts {program : CheckedProgram}
    {budget fuel next : Nat} {before after : Plan}
    (receipts : ∀ row ∈ before.specializations, Receipt row)
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux
      program budget fuel next before = .ok after) :
    ∀ row ∈ after.specializations, Receipt row := by
  induction fuel generalizing next before after with
  | zero =>
      unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
      split at accepted
      · cases accepted; exact receipts
      · cases accepted
  | succ fuel ih =>
      unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
      split at accepted
      · cases accepted; exact receipts
      · rename_i caller found
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨extended, scan, rest⟩ := bind_ok accepted
        obtain ⟨available, _, scan⟩ := bind_ok scan
        obtain ⟨loopFinal, loop, returned⟩ := bind_ok scan
        cases returned
        have scanned : ∀ row ∈ extended.specializations, Receipt row := by
          apply forIn_receipts loop receipts
          intro item member current outcome nodeAccepted currentReceipts
          cases item with
          | statement statement =>
              cases nodeAccepted
              exact ⟨current, rfl, currentReceipts⟩
          | expression node =>
              cases form : node.form <;> simp only [form] at nodeAccepted
              case' call callee arguments resolution => cases resolution
              case' reference name resolution => cases resolution
              all_goals
                first
                | (obtain ⟨opPlan, opAccepted, nodeAccepted⟩ := bind_ok nodeAccepted
                   have opReceipts := operator_receipts currentReceipts opAccepted)
                | (let opPlan := current
                   have opReceipts : ∀ row ∈ opPlan.specializations, Receipt row :=
                     currentReceipts)
              all_goals
                obtain ⟨outputPlan, outputLoop, nodeAccepted⟩ := bind_ok nodeAccepted
                have outputReceipts : ∀ row ∈ outputPlan.specializations, Receipt row :=
                  forIn_receipts (α := CoercionStep) (ε := SourceTypedRuntime.RuntimeError)
                    outputLoop opReceipts (by
                    intro step _ previous outcome accepted previousReceipts
                    obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                    have updatedReceipts : ∀ row ∈ updated.specializations, Receipt row :=
                      coercion_receipts previousReceipts headAccepted
                    cases returned
                    exact ⟨updated, rfl, updatedReceipts⟩)
              all_goals try rw [form] at nodeAccepted
              all_goals try dsimp only at nodeAccepted
              all_goals
                iterate 8 all_goals first
                  | exact ⟨outputPlan, (Except.ok.inj nodeAccepted).symm, outputReceipts⟩
                  | (obtain ⟨argumentPlan, argumentLoop, nodeAccepted⟩ := bind_ok nodeAccepted
                     have argumentReceipts : ∀ row ∈ argumentPlan.specializations, Receipt row :=
                       forIn_receipts (α := CoercionStep) (ε := SourceTypedRuntime.RuntimeError)
                         argumentLoop outputReceipts (by
                         intro step _ previous outcome accepted previousReceipts
                         obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                         have updatedReceipts : ∀ row ∈ updated.specializations, Receipt row :=
                           coercion_receipts previousReceipts headAccepted
                         cases returned
                         exact ⟨updated, rfl, updatedReceipts⟩)
                     exact ⟨argumentPlan, (Except.ok.inj nodeAccepted).symm, argumentReceipts⟩)
                  | (obtain ⟨_, _, nodeAccepted⟩ := bind_ok nodeAccepted)
                  | split at nodeAccepted
                  | contradiction
        exact ih scanned rest

private theorem replay_receipts {program : CheckedProgram} {plan : Plan}
    (accepted : SourceCompilationPlan.validateCanonicalInputPlan program plan = .ok ()) :
    ∀ row ∈ plan.specializations, Receipt row := by
  unfold SourceCompilationPlan.validateCanonicalInputPlan at accepted
  obtain ⟨seeds, _, accepted⟩ := bind_ok accepted
  obtain ⟨outcome, executed, accepted⟩ := bind_ok accepted
  have executed : run program seeds plan.specializations.length = .ok outcome := by
    cases action : run program seeds plan.specializations.length with
    | error error => rw [action] at executed; cases executed
    | ok actual =>
        simp only [action, Except.mapError, Except.ok.injEq] at executed
        cases executed
        rfl
  cases outcome with
  | budgetExhausted previous next pending => cases accepted
  | complete expected =>
      by_cases same : (expected == plan) = true
      · have rows : expected.specializations = plan.specializations := by
          have fields : ((expected.seedKeys == plan.seedKeys) &&
              ((expected.specializations == plan.specializations) &&
                ((expected.callEdges == plan.callEdges) &&
                  (expected.referenceEdges == plan.referenceEdges)))) = true := by
            exact same
          simp only [Bool.and_eq_true] at fields
          exact LawfulBEq.eq_of_beq fields.2.1
        intro row member
        exact CallablePreparedSpecializationOrigins.of_worklist executed row
          (by simpa only [Outcome.plan_complete, rows] using member)
      · simp only [same, throw, throwThe, MonadExceptOf.throw] at accepted
        cases accepted

/-- Public preparation itself authenticates the original replay and every
inserted checked method. Every row in its final plan therefore comes from the
real rigid specializer, including detached roots and their helper frontier. -/
theorem of_preparation {program : CheckedProgram} {before after : Plan}
    {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok after) :
    ∀ row ∈ after.specializations, Receipt row := by
  obtain ⟨prepared, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  exact aux_receipts (replay_receipts canonical) inspected

/-- The default public preparation forwards the same actual producer chain. -/
theorem of_default_preparation {program : CheckedProgram} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidence program before = .ok after) :
    ∀ row ∈ after.specializations, Receipt row :=
  of_preparation accepted

end Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationOrigins
