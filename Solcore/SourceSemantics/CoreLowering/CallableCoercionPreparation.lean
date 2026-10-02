import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparationSteps

/-! Successful executable-plan preparation supplies actual coercion visits for
all returned carriers, including detached methods and helpers appended during
the scan. Source-view alignment, installed closures and source call execution
remain separate. Fresh trait headers still require their independent origin
profile when an AssembledFrom judgment is requested. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
open Frontend SourceInference SourceSpecializationWorklist CallableCoercionPreparationSteps

/-- Both lists are traversed by the actual preparation pass; this describes
only the indirect-call argument phase, following the output phase. -/
def argumentSteps (node : ExpressionNode) : List CoercionStep :=
  match node.form with
  | .call _ _ (.indirect metadata) => metadata.argumentCoercions
  | _ => []

def NodeCovered (program : CheckedProgram) (caller : Specialized)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) (node : ExpressionNode) (plan : Plan) : Prop :=
  ∀ step ∈ node.coercions ++ argumentSteps node, Nonempty (Visit program caller available node step plan)

def Covered (program : CheckedProgram) (caller : Specialized) (plan : Plan) : Prop :=
  ∃ available, SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available ∧
    ∀ node, .expression node ∈ caller.function.typedBody.nodes → NodeCovered program caller available node plan

theorem NodeCovered.later {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode} {before after : Plan}
    (covered : NodeCovered program caller available node before) (growth : Extends before after) :
    NodeCovered program caller available node after := by
  intro step member
  obtain ⟨visit⟩ := covered step member
  exact ⟨visit.later growth⟩

theorem Covered.later {program : CheckedProgram} {caller : Specialized} {before after : Plan}
    (covered : Covered program caller before) (growth : Extends before after) : Covered program caller after := by
  obtain ⟨available, resolved, covered⟩ := covered
  exact ⟨available, resolved, fun node member => (covered node member).later growth⟩

private theorem ended {entries : List Specialized} {next index : Nat} {caller : Specialized}
    (done : entries[next]? = none) (bound : next ≤ index) (found : entries[index]? = some caller) : False := by
  have size := List.getElem?_eq_none_iff.mp done
  have position := (List.getElem?_eq_some_iff.mp found).1
  omega

/-- The strengthened index invariant covers every returned position at or
beyond `next`. Exact prefix growth makes newly appended methods part of this
same actual traversal. -/
theorem aux {program : CheckedProgram} {budget fuel next : Nat} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux program budget fuel next before = .ok after) :
    Extends before after ∧ ∀ index caller, next ≤ index → after.specializations[index]? = some caller → Covered program caller after := by
  induction fuel generalizing next before after with
  | zero =>
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i done
      cases accepted
      exact ⟨.refl _, fun _ _ bound found => False.elim (ended done bound found)⟩
    · cases accepted
  | succ fuel ih =>
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i done
      cases accepted
      exact ⟨.refl _, fun _ _ bound found => False.elim (ended done bound found)⟩
    · rename_i caller found
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨extended, scan, rest⟩ := bind_ok accepted
      obtain ⟨available, resolved, scan⟩ := bind_ok scan
      obtain ⟨loopFinal, loop, returned⟩ := bind_ok scan
      cases returned
      have scanned : Extends before extended ∧ Covered program caller extended := by
        have result := forIn_coverage
          (done := fun (item : Node) (final : Plan) => ∀ (node : ExpressionNode), item = .expression node → NodeCovered program caller available node final)
          loop (by
            intro item previous final growth done node same
            exact (done node same).later growth) ?_
        · exact ⟨result.1, available, resolved, fun node member => result.2 _ member node rfl⟩
        intro item member current outcome nodeAccepted
        cases item with
        | statement statement =>
          cases nodeAccepted
          exact ⟨current, rfl, .refl _, fun _ same => by cases same⟩
        | expression node =>
          suffices ∃ final, outcome = .yield final ∧ Extends current final ∧ NodeCovered program caller available node final by
            obtain ⟨final, same, growth, covered⟩ := this
            exact ⟨final, same, growth, fun other same => by cases same; exact covered⟩
          cases form : node.form <;> simp only [form] at nodeAccepted
          case' call callee arguments resolution => cases resolution
          case' reference name resolution => cases resolution
          all_goals
            first
            | (obtain ⟨opPlan, opAccepted, nodeAccepted⟩ := bind_ok nodeAccepted
               have opGrowth := operator_accepted opAccepted)
            | (let opPlan := current
               have opGrowth : Extends current opPlan := .refl _)
          all_goals
            obtain ⟨outputPlan, outputLoop, nodeAccepted⟩ := bind_ok nodeAccepted
            have outputCovered := forIn_coverage
              (done := fun step final => Nonempty (Visit program caller available node step final)) outputLoop
              (fun _ _ _ growth ⟨visit⟩ => ⟨visit.later growth⟩) (by
                intro step _ previous outcome accepted
                obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                cases returned
                have head := coercion_accepted headAccepted
                exact ⟨_, rfl, head.1, head.2⟩)
          all_goals try rw [form] at nodeAccepted
          all_goals try dsimp only at nodeAccepted
          all_goals
            iterate 8 all_goals first
              | (have empty : argumentSteps node = [] := by simp only [argumentSteps, form]
                 exact ⟨outputPlan, (Except.ok.inj nodeAccepted).symm, opGrowth.trans outputCovered.1,
                   by simpa only [NodeCovered, empty, List.append_nil] using outputCovered.2⟩)
              | (obtain ⟨argumentPlan, argumentLoop, nodeAccepted⟩ := bind_ok nodeAccepted
                 have argumentCovered := forIn_coverage
                   (done := fun step final => Nonempty (Visit program caller available node step final)) argumentLoop
                   (fun _ _ _ growth ⟨visit⟩ => ⟨visit.later growth⟩) (by
                     intro step _ previous outcome accepted
                     obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                     cases returned
                     have head := coercion_accepted headAccepted
                     exact ⟨_, rfl, head.1, head.2⟩)
                 refine ⟨argumentPlan, (Except.ok.inj nodeAccepted).symm,
                   opGrowth.trans (outputCovered.1.trans argumentCovered.1), ?_⟩
                 intro step member
                 rcases List.mem_append.mp member with member | member
                 · obtain ⟨visit⟩ := outputCovered.2 step member
                   exact ⟨visit.later argumentCovered.1⟩
                 · apply argumentCovered.2 step
                   simpa only [argumentSteps, form] using member)
              | (obtain ⟨_, _, nodeAccepted⟩ := bind_ok nodeAccepted)
              | split at nodeAccepted
              | contradiction
      obtain ⟨tailGrowth, tailCovered⟩ := ih rest
      refine ⟨scanned.1.trans tailGrowth, ?_⟩
      intro index selected bound lookup
      by_cases same : index = next
      · subst index
        have atNext := (scanned.1.trans tailGrowth).at found
        have same := Option.some.inj (lookup.symm.trans atNext)
        subst selected
        exact scanned.2.later tailGrowth
      · exact tailCovered index selected (by omega) lookup

/-- Public preparation success inspects every final carrier, including those
that were absent from the original input vector. -/
theorem of_accepted {program : CheckedProgram} {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok after) :
    Extends before after ∧ ∀ caller ∈ after.specializations, Covered program caller after := by
  obtain ⟨prepared, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, returned⟩ := bind_ok accepted
  cases returned
  obtain ⟨growth, covered⟩ := aux inspected
  refine ⟨growth, ?_⟩
  intro caller member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  exact covered index caller (Nat.zero_le _) found

/-- A supplied emitter dictionary must be the actual caller resolver result.
The full node and step position remain tied to that same final caller. -/
theorem visit {program : CheckedProgram} {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok after)
    {caller : Specialized} (member : caller ∈ after.specializations)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ argumentSteps node)
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available) :
    Nonempty (Visit program caller available node coercion after) := by
  obtain ⟨actual, actualResolved, covered⟩ := (of_accepted accepted).2 caller member
  have same := Except.ok.inj (actualResolved.symm.trans resolved)
  subst actual
  exact covered node nodeMember coercion site

private theorem call_key {plan : Plan} {caller target selected : SourceSpecialization.SpecializationKey} {id : ExpressionId}
    (accepted : SourceCompilationPlan.exactCallKey plan caller id target = .ok selected) : selected = target := by
  unfold SourceCompilationPlan.exactCallKey at accepted
  split at accepted <;> try contradiction
  rename_i edge edges
  cases accepted
  have member : edge ∈ plan.callEdges.filter (fun edge => decide (edge.caller = caller) && decide (edge.occurrence = id) && decide (edge.callee = target)) := by rw [edges]; simp
  have same := (List.mem_filter.mp member).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at same
  exact same.2

/-- The outer preparation supplies the former per-method extension premise.
Both selectors are compared as the same action on complete caller/node data. -/
theorem step_specialized {program : CheckedProgram} {before : Plan} {fuel budget : Nat}
    {project : CallableCoercionSpine.Projector} {context : CallableCoercionSpine.Context}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok context.plan)
    {caller : Specialized} (member : caller ∈ context.plan.specializations)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ argumentSteps node)
    {available : CallableCoercionSpine.RuntimeEvidence}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    {scope : CallableCoercionSpine.Scope} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project context caller available scope node policy input coercion output call) :
    step.specialized = step.method.specialized := by
  obtain ⟨receipt⟩ := visit accepted member nodeMember site resolved
  have sameMethod := Except.ok.inj (receipt.selected.symm.trans step.selectedMethod)
  have retained := receipt.finalSelected
  rw [sameMethod] at retained
  have emitted := step.selected
  rw [call_key step.edge] at emitted
  exact Except.ok.inj (emitted.symm.trans retained)

end Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
