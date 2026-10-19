import Solcore.SourceSemantics.SourcePreparedPlanGrowth
import Solcore.Frontend.SourceCoreCompiler

/-! Successful evidence preparation supplies a real call edge for every open
original declaration call it scans. Intermediate helper plans and their final
edge membership stay explicit. No edge is assumed to belong to the input plan. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourcePreparedOpenCallEdges
open Frontend SourceInference SourceSpecializationWorklist
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)
open SourcePreparedPlanGrowth

/-- The exact boolean condition used by executable-plan preparation. -/
def InstantiationClosed (instantiation : DeclarationInstantiation) : Bool :=
  instantiation.type.freeVariables.isEmpty &&
    (instantiation.parameterSubstitution.all fun entry => entry.2.freeVariables.isEmpty) &&
    instantiation.predicates.all (fun predicate => predicate.subject.freeVariables.isEmpty &&
      predicate.arguments.all fun argument => argument.freeVariables.isEmpty)

structure EdgeAt (caller : Specialized) (node : ExpressionNode)
    (instantiation : DeclarationInstantiation) (final : Plan) where
  stage : Plan
  edge : CallEdge
  present : edge ∈ stage.callEdges
  retained : stage.callEdges ⊆ final.callEdges
  callerEq : edge.caller = caller.key
  occurrenceEq : edge.occurrence = node.id
  declarationEq : edge.callee.declaration = instantiation.declaration

def NodeCovered (caller : Specialized) (node : ExpressionNode) (plan : Plan) : Prop :=
  ∀ callee arguments instantiation,
    node.form = .call callee arguments (.declaration instantiation) →
    InstantiationClosed instantiation = false →
    Nonempty (EdgeAt caller node instantiation plan)

def Covered (caller : Specialized) (plan : Plan) : Prop :=
  ∀ node, .expression node ∈ caller.function.typedBody.nodes → NodeCovered caller node plan

theorem NodeCovered.later {caller : Specialized} {node : ExpressionNode} {before after : Plan}
    (covered : NodeCovered caller node before) (growth : Growth before after) :
    NodeCovered caller node after := by
  intro callee arguments instantiation form opened
  obtain ⟨edge⟩ := covered callee arguments instantiation form opened
  exact ⟨{edge with retained := fun _ present => growth.calls (edge.retained present)}⟩

theorem Covered.later {caller : Specialized} {before after : Plan}
    (covered : Covered caller before) (growth : Growth before after) : Covered caller after :=
  fun node member => (covered node member).later growth

private theorem ended {entries : List Specialized} {next index : Nat} {caller : Specialized}
    (done : entries[next]? = none) (bound : next ≤ index)
    (found : entries[index]? = some caller) : False := by
  have size := List.getElem?_eq_none_iff.mp done
  have position := (List.getElem?_eq_some_iff.mp found).1
  omega

private theorem open_edge {caller : Specialized} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {plan : Plan}
    (nonempty : (plan.callEdges.filter fun edge =>
      decide (edge.caller = caller.key) && decide (edge.occurrence = node.id) &&
        decide (edge.callee.declaration = instantiation.declaration)).isEmpty = false) :
    Nonempty (EdgeAt caller node instantiation plan) := by
  have inhabited : ∃ edge, edge ∈ plan.callEdges.filter (fun edge =>
      decide (edge.caller = caller.key) && decide (edge.occurrence = node.id) &&
        decide (edge.callee.declaration = instantiation.declaration)) := by
    cases selected : plan.callEdges.filter (fun edge =>
      decide (edge.caller = caller.key) && decide (edge.occurrence = node.id) &&
        decide (edge.callee.declaration = instantiation.declaration)) with
    | nil => simp [selected] at nonempty
    | cons edge rest => exact ⟨edge, by simp⟩
  obtain ⟨edge,member⟩ := inhabited
  obtain ⟨present,matched⟩ := List.mem_filter.mp member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at matched
  exact ⟨⟨plan,edge,present,fun _ present => present,matched.1.1,matched.1.2,matched.2⟩⟩

private theorem closed_covered {caller : Specialized} {node : ExpressionNode}
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    {plan : Plan} (form : node.form = .call callee arguments (.declaration instantiation))
    (closed : InstantiationClosed instantiation = true) : NodeCovered caller node plan := by
  intro actualCallee actualArguments actualInstantiation same opened
  have equal := form.symm.trans same
  cases equal
  rw [closed] at opened
  cases opened

/-- Exact row positions survive actual helper extension. Every final row at
or after the scan cursor receives its original open-call edge receipts. -/
theorem aux {program : CheckedProgram} {budget fuel next : Nat} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux program budget fuel next before = .ok after) :
    Growth before after ∧ ∀ index caller, next ≤ index → after.specializations[index]? = some caller → Covered caller after := by
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
      obtain ⟨available, _resolved, scan⟩ := bind_ok scan
      obtain ⟨loopFinal, loop, returned⟩ := bind_ok scan
      cases returned
      have scanned : Growth before extended ∧ Covered caller extended := by
        have result := SourcePreparedPlanGrowth.forIn_coverage
          (done := fun (item : Node) (final : Plan) => ∀ (node : ExpressionNode), item = .expression node → NodeCovered caller node final)
          loop (by
            intro item previous final growth done node same
            exact (done node same).later growth) ?_
        · exact ⟨result.1, fun node member => result.2 _ member node rfl⟩
        intro item member current outcome nodeAccepted
        cases item with
        | statement statement =>
          cases nodeAccepted
          exact ⟨current, rfl, .refl _, fun _ same => by cases same⟩
        | expression node =>
          suffices ∃ final, outcome = .yield final ∧ Growth current final ∧ NodeCovered caller node final by
            obtain ⟨final, same, growth, covered⟩ := this
            exact ⟨final, same, growth, fun other same => by cases same; exact covered⟩
          cases form : node.form <;> simp only [form] at nodeAccepted
          case' call callee arguments resolution => cases resolution
          case' reference name resolution => cases resolution
          all_goals
            first
            | (obtain ⟨opPlan, opAccepted, nodeAccepted⟩ := bind_ok nodeAccepted
               have opGrowth := SourcePreparedPlanGrowth.operator_accepted opAccepted)
            | (let opPlan := current
               have opGrowth : Growth current opPlan := .refl _)
          all_goals
            obtain ⟨outputPlan, outputLoop, nodeAccepted⟩ := bind_ok nodeAccepted
            have outputGrowth := (SourcePreparedPlanGrowth.forIn_coverage
              (done := fun _ _ => True) outputLoop (fun _ _ _ _ _ => True.intro) (by
                intro step _ previous outcome accepted
                obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                cases returned
                exact ⟨_,rfl,SourcePreparedPlanGrowth.coercion_accepted headAccepted,True.intro⟩)).1
          all_goals try rw [form] at nodeAccepted
          all_goals try dsimp only at nodeAccepted
          all_goals
            try (have irrelevant : NodeCovered caller node outputPlan := by
                   intro callee arguments instantiation same _opened
                   simp only [form] at same
                   cases same)
          all_goals
            iterate 8 all_goals first
              | exact ⟨outputPlan,(Except.ok.inj nodeAccepted).symm,opGrowth.trans outputGrowth,irrelevant⟩
              | exact ⟨outputPlan,(Except.ok.inj nodeAccepted).symm,opGrowth.trans outputGrowth,
                  closed_covered form (by assumption)⟩
              | (refine ⟨outputPlan,(Except.ok.inj nodeAccepted).symm,opGrowth.trans outputGrowth,?_⟩
                 intro actualCallee actualArguments actualInstantiation same opened
                 have equal := form.symm.trans same
                 cases equal
                 first
                 | (have closed : InstantiationClosed _ = true := by assumption
                    rw [closed] at opened
                    cases opened)
                 | (apply open_edge
                    exact Bool.eq_false_iff.mpr (by assumption)))
              | (obtain ⟨argumentPlan, argumentLoop, nodeAccepted⟩ := bind_ok nodeAccepted
                 have argumentGrowth := (SourcePreparedPlanGrowth.forIn_coverage
                   (done := fun _ _ => True) argumentLoop (fun _ _ _ _ _ => True.intro) (by
                     intro step _ previous outcome accepted
                     obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                     cases returned
                     exact ⟨_,rfl,SourcePreparedPlanGrowth.coercion_accepted headAccepted,True.intro⟩)).1
                 exact ⟨argumentPlan,(Except.ok.inj nodeAccepted).symm,
                   opGrowth.trans (outputGrowth.trans argumentGrowth),irrelevant.later argumentGrowth⟩)
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

/-- Every final selected row was inspected by the successful preparation,
including methods appended while earlier rows were being checked. -/
theorem of_preparation {program : CheckedProgram} {before after : Plan}
    {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok after) :
    Growth before after ∧ ∀ caller ∈ after.specializations, Covered caller after := by
  obtain ⟨prepared, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, returned⟩ := bind_ok accepted
  cases returned
  obtain ⟨growth, covered⟩ := aux inspected
  refine ⟨growth, ?_⟩
  intro caller member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  exact covered index caller (Nat.zero_le _) found

theorem of_default_preparation {program : CheckedProgram} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidence program before = .ok after) :
    Growth before after ∧ ∀ caller ∈ after.specializations, Covered caller after :=
  of_preparation accepted

/-- Validation retains the actual extended plan. An input call edge is never
silently inferred from an edge introduced by operator or coercion preparation. -/
theorem of_validation {program : CheckedProgram} {input : Plan}
    (accepted : SourceCompilationPlan.validateExecutablePlanEvidence program input = .ok ()) :
    ∃ prepared, SourceCompilationPlan.prepareExecutablePlanEvidence program input = .ok prepared ∧
      Growth input prepared ∧ ∀ caller ∈ prepared.specializations, Covered caller prepared := by
  unfold SourceCompilationPlan.validateExecutablePlanEvidence at accepted
  cases actual : SourceCompilationPlan.prepareExecutablePlanEvidence program input with
  | error error => rw [actual] at accepted; cases accepted
  | ok prepared =>
    have covered := of_default_preparation actual
    exact ⟨prepared,rfl,covered⟩

/-- The public compiled object supplies validation itself. Both the genuine
prepared plan and the selected original row remain visible in the result. -/
theorem compiled_selected (compiled : SourceCoreCompiler.Compiled) :
    ∃ prepared, SourceCompilationPlan.prepareExecutablePlanEvidence compiled.program compiled.plan = .ok prepared ∧
      Growth compiled.plan prepared ∧
      ∀ caller ∈ compiled.plan.specializations, ∀ node,
        .expression node ∈ caller.function.typedBody.nodes →
        ∀ callee arguments instantiation,
          node.form = .call callee arguments (.declaration instantiation) →
          InstantiationClosed instantiation = false →
          Nonempty (EdgeAt caller node instantiation prepared) := by
  obtain ⟨prepared, accepted, growth, covered⟩ := of_validation compiled.plan_validated
  exact ⟨prepared,accepted,growth,fun caller member =>
    covered caller (growth.rows.entries.subset member)⟩

end Solcore.SourceSemantics.SourcePreparedOpenCallEdges
