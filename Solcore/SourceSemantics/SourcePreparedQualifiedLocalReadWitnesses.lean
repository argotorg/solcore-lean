import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadBindings
import Lean

/-! The executable-plan preparation actually resolves and checks the witness
factory for every qualified local reference in each selected original row. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadWitnesses
open Frontend SourceInference SourceSpecializationWorklist TypeSystem
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)

open Lean Meta Elab Tactic in
private def unfoldCheck (hypothesis : Name) : TacticM Unit := withMainContext do
  let declaration ← getLocalDeclFromUserName hypothesis
  let type ← instantiateMVars (← inferType declaration.toExpr)
  let some (_, left, _) := type.eq? | throwError "expected equation: {type}"
  let .const name _ := left.getAppFn | throwError "expected actual definition: {left}"
  let goal ← getMainGoal
  replaceMainGoal [← unfoldLocalDecl goal declaration.fvarId name]

/-- The complete actual resolver and witness equations are retained together. -/
def Covered (program : CheckedProgram) (caller : Specialized) : Prop :=
  ∃ available,
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available ∧
    ∀ node, Node.expression node ∈ caller.function.typedBody.nodes →
      ∀ name localId, node.form = .reference name (.local localId) →
      ∀ binder, SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder →
      binder.schemeRequirements ≠ [] →
      ∃ substitution witnesses, SourceCompilationPlan.localRequirementWitnesses caller available binder node =
        .ok (substitution, witnesses)

private theorem forIn_each {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {property : α → Prop}
    (accepted : forIn items initial step = .ok final)
    (each : ∀ item ∈ items, ∀ before outcome, step item before = .ok outcome →
      ∃ after, outcome = .yield after ∧ property item) :
    ∀ item ∈ items, property item := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, executed, remaining⟩ := bind_ok accepted
    obtain ⟨after, rfl, checked⟩ := each item List.mem_cons_self initial outcome executed
    intro actual member
    rcases List.mem_cons.mp member with rfl | later
    · exact checked
    · exact ih remaining (fun next present => each next (List.mem_cons_of_mem item present)) actual later

/-- The actual frontier scan supplies these receipts even for helper rows
appended during evidence preparation. -/
theorem aux {program : CheckedProgram} {budget fuel next : Nat} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux program budget fuel next before = .ok after) :
    ∀ index caller, next ≤ index → after.specializations[index]? = some caller → Covered program caller := by
  induction fuel generalizing next before after with
  | zero =>
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i ended
      cases accepted
      intro index caller bound found
      have length := List.getElem?_eq_none_iff.mp ended
      have present := (List.getElem?_eq_some_iff.mp found).1
      omega
    · cases accepted
  | succ fuel ih =>
    have growth := (SourcePreparedOpenCallEdges.aux accepted).1
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i ended
      cases accepted
      intro index caller bound found
      have length := List.getElem?_eq_none_iff.mp ended
      have present := (List.getElem?_eq_some_iff.mp found).1
      omega
    · rename_i caller found
      obtain ⟨checked, _metadata, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨extended, scan, remaining⟩ := bind_ok accepted
      intro index actual bound selected
      by_cases current : index = next
      · subst index
        have same := Option.some.inj (selected.symm.trans (growth.at found))
        subst actual
        obtain ⟨available, resolved, scan⟩ := bind_ok scan
        obtain ⟨final, loop, returned⟩ := bind_ok scan
        cases returned
        refine ⟨available, resolved, ?_⟩
        have result := forIn_each (property := fun item =>
          ∀ node, item = Node.expression node → ∀ name localId,
            node.form = .reference name (.local localId) → ∀ binder,
            SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder →
            binder.schemeRequirements ≠ [] → ∃ substitution witnesses,
              SourceCompilationPlan.localRequirementWitnesses caller available binder node = .ok (substitution, witnesses))
          loop ?_
        · intro node member
          exact result _ member node rfl
        intro item _ previous outcome executed
        cases item with
        | statement statement =>
          cases executed
          exact ⟨previous, rfl, fun _ same => by cases same⟩
        | expression node =>
          have originalExecuted := executed
          have yielded : ∃ after, outcome = .yield after := by
            cases form : node.form <;> simp only [form] at executed
            case' call callee arguments resolution => cases resolution
            case' reference name resolution => cases resolution
            all_goals
              iterate 20 all_goals first
                | exact ⟨_, (Except.ok.inj executed).symm⟩
                | (obtain ⟨value, _action, executed⟩ := bind_ok executed)
                | split at executed
                | contradiction
          obtain ⟨after, rfl⟩ := yielded
          refine ⟨after, rfl, ?_⟩
          intro actual same name localId form binder detected qualified
          cases same
          simp only [form] at originalExecuted
          obtain ⟨coercionPlan, _coercions, checked⟩ := bind_ok originalExecuted
          have nonempty : binder.schemeRequirements.isEmpty = false := List.isEmpty_eq_false_iff.mpr qualified
          simp only [detected, nonempty, Bool.false_eq_true, if_false] at checked
          obtain ⟨validated, evidence, _returned⟩ := bind_ok checked
          cases validated
          run_tac unfoldCheck `evidence
          obtain ⟨witnesses, witnessesAccepted, _validated⟩ := bind_ok evidence
          run_tac unfoldCheck `witnessesAccepted
          obtain ⟨covered, _coverage, witnessesAccepted⟩ := bind_ok witnessesAccepted
          cases covered
          obtain ⟨pair, factory, _returned⟩ := bind_ok witnessesAccepted
          exact ⟨pair.1, pair.2, factory⟩
      · exact ih remaining index actual (by omega) selected

/-- Every complete row retained by a successful preparation has been scanned. -/
theorem prepared_selected {program : CheckedProgram} {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok after)
    {caller : Specialized} (member : caller ∈ after.specializations) : Covered program caller := by
  unfold SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget at accepted
  obtain ⟨scanned, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, _canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  exact aux inspected index caller (Nat.zero_le _) found

/-- Compilation supplies the actual witness factory on each retained selected
row; neither a caller-supplied factory result nor evidence coverage is assumed. -/
theorem compiled_selected (compiled : SourceCoreCompiler.Compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations) :
    Covered compiled.program caller := by
  obtain ⟨prepared, accepted, growth, _⟩ := SourcePreparedOpenCallEdges.of_validation compiled.plan_validated
  unfold SourceCompilationPlan.prepareExecutablePlanEvidence
    SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget at accepted
  obtain ⟨scanned, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, _canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp (growth.rows.entries.subset member)
  exact aux inspected index caller (Nat.zero_le _) found

end Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadWitnesses
