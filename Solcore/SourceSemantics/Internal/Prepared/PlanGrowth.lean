import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.Frontend.SourceCoreCompiler
import Lean
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.SourceSemantics.Internal.Prepared.StatementReferences

/-!
# Growth of prepared plans

Executable plan growth keeps selected rows and call edges, and evidence preparation gives a real
call edge for each open declaration call it scans. Lexical children of ordinary recursive evaluation
are here too.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedPlanGrowth
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedOpenCallEdges
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceSpecializationLocalLexicalChildren
/-! Ordinary recursive evaluation follows the same source edges as the actual
lexical collector. Lambda bodies enter through their own invocation roots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceSpecializationWorklist
open SourceInference TypeSystem

open Lean Meta Elab Tactic in
private def unfoldActualChildren : TacticM Unit := do
  let original := `Solcore.Frontend.SourceSpecializationWorklist.directLexicalChildren
  let mut found : Option Name := none
  for (name, _) in (← getEnv).constants.toList do
    if privateToUserName? name == some original then
      if found.isSome then throwError "ambiguous lexical child definition: {original}"
      found := some name
  let some name := found | throwError "missing lexical child definition: {original}"
  let definition := mkIdent name
  evalTactic (← `(tactic| unfold localLambdaLexicalChildren $definition:ident))

theorem localLambdaLexicalChildren_statement
    {source : TypedSource} {id : StatementId} {statement : StatementNode} {child : NodeId}
    (found : source.lookupStatement? id = some statement)
    (member : child ∈ statement.form.references) :
    child ∈ localLambdaLexicalChildren source (.statement id) := by
  unfold TypedSource.lookupStatement? at found
  cases looked : source.lookupNode? id.occurrence with
  | none => simp only [looked, reduceCtorEq] at found
  | some node =>
    cases node with
    | expression expression => simp only [looked, reduceCtorEq] at found
    | statement actual =>
      simp only [looked, Option.some.injEq] at found
      subst actual
      run_tac unfoldActualChildren
      simp only [NodeId.occurrenceId, looked]
      exact SourceSpecialization.statementChildNodeIds_of_reference member

theorem localLambdaLexicalChildren_expression
    {source : TypedSource} {id : ExpressionId} {expression : ExpressionNode} {child : NodeId}
    (found : source.lookupExpression? id = some expression)
    (nonLambda : ∀ parameters result body, expression.form ≠ .lambda parameters result body)
    (member : child ∈ expression.form.references) :
    child ∈ localLambdaLexicalChildren source (.expression id) := by
  unfold TypedSource.lookupExpression? at found
  cases looked : source.lookupNode? id.occurrence with
  | none => simp only [looked, reduceCtorEq] at found
  | some node =>
    cases node with
    | statement statement => simp only [looked, reduceCtorEq] at found
    | expression actual =>
      simp only [looked, Option.some.injEq] at found
      subst actual
      cases expression with
      | mk nodeId span type form requirements coercions localStart =>
        cases form <;> try exact False.elim (nonLambda _ _ _ rfl)
        all_goals run_tac unfoldActualChildren
        all_goals
          simpa only [NodeId.occurrenceId, looked,
            SourceSpecialization.expressionChildNodeIds_eq_references] using member

namespace LocalLambdaLexicalPath

theorem statement_child
    {source : TypedSource} {roots : List NodeId} {id : StatementId}
    {statement : StatementNode} {child : NodeId}
    (previous : LocalLambdaLexicalPath source roots (.statement id))
    (found : source.lookupStatement? id = some statement)
    (member : child ∈ statement.form.references) :
    LocalLambdaLexicalPath source roots child :=
  .child previous (localLambdaLexicalChildren_statement found member)

theorem expression_child
    {source : TypedSource} {roots : List NodeId} {id : ExpressionId}
    {expression : ExpressionNode} {child : NodeId}
    (previous : LocalLambdaLexicalPath source roots (.expression id))
    (found : source.lookupExpression? id = some expression)
    (nonLambda : ∀ parameters result body, expression.form ≠ .lambda parameters result body)
    (member : child ∈ expression.form.references) :
    LocalLambdaLexicalPath source roots child :=
  .child previous (localLambdaLexicalChildren_expression found nonLambda member)

end LocalLambdaLexicalPath
end Solcore.Frontend.SourceSpecializationWorklist
end
