import Solcore.SourceSemantics.SourcePreparedCallEdgeOrigins
import Solcore.SourceSemantics.SourcePreparedOpenCallEdges

/-! Actual final call edges retain their canonical input or checked method
preparation ancestry, including genuine supplied-root and later worklist scans. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourcePreparedFinalCallEdgeOrigins
open Frontend SourceInference SourceSpecializationWorklist
open SourcePreparedPlanGrowth SourcePreparedCallEdgeOrigins
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)

private theorem forIn_invariant {α ε : Type} {items : List α}
    {initial final : Plan} {P : Plan → Prop} {step : α → Plan → Except ε (ForInStep Plan)}
    (accepted : forIn items initial step = .ok final)
    (receipts : P initial)
    (next : ∀ item ∈ items, ∀ before outcome,
      step item before = .ok outcome →
      (P before) →
      ∃ after, outcome = .yield after ∧
        P after) :
    P final := by
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

private theorem coercion_origins {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {node : ExpressionNode} {coercion : CoercionStep}
    {input before after : Plan} {budget : Nat}
    (receipts : All program input before)
    (callerMember : caller ∈ before.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (occurrence : CoercionAt node coercion)
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
    Growth before after ∧ All program input after := by
  obtain ⟨method, selected, accepted⟩ := bind_ok accepted
  obtain ⟨returned, boundary, accepted⟩ := bind_ok accepted
  cases returned
  obtain ⟨returned, evidence, accepted⟩ := bind_ok accepted
  cases returned
  cases extended : extendCompletePlan program before method.specialized
      ⟨caller.key, node.id, method.specialized.key⟩ budget with
  | error error => rw [extended] at accepted; cases accepted
  | ok outcome =>
      rw [extended] at accepted
      cases outcome with
      | budgetExhausted plan next pending => cases accepted
      | complete inserted =>
          cases accepted
          let event : Event program := ⟨before, after, caller, callerMember,
            node, nodeMember, available, resolved, method.specialized,
            .coercion occurrence selected boundary evidence, budget, extended⟩
          exact ⟨event.growth, from_extension event receipts⟩

private theorem operator_origins {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {node : ExpressionNode} {input before after : Plan} {budget : Nat}
    (receipts : All program input before)
    (callerMember : caller ∈ before.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
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
    Growth before after ∧ All program input after := by
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
          exact ⟨.refl _, receipts⟩
      | cons primary remaining =>
          try simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at accepted
          cases form : node.form <;> simp only [form] at accepted <;> try cases accepted
          all_goals
            obtain ⟨selection, selected, accepted⟩ := bind_ok accepted
            obtain ⟨arguments, argumentsEq, accepted⟩ := bind_ok accepted
            have argumentsEq := Except.ok.inj argumentsEq
            subst arguments
            obtain ⟨returned, boundary, accepted⟩ := bind_ok accepted
            cases returned
            obtain ⟨returned, evidence, accepted⟩ := bind_ok accepted
            cases returned
            have selectionReceipt : Selection program caller node available selection.method.specialized := by
              first
              | exact .unary owned (by simp) form
                  (by simpa only [form] using selected)
                  (by simpa only [form] using boundary)
                  (by simpa only [form] using evidence)
              | exact .binary owned (by simp) form
                  (by simpa only [form] using selected)
                  (by simpa only [form] using boundary)
                  (by simpa only [form] using evidence)
            cases extended : extendCompletePlan program before selection.method.specialized
                ⟨caller.key, node.id, selection.method.specialized.key⟩ budget with
            | error error => rw [extended] at accepted; cases accepted
            | ok outcome =>
                rw [extended] at accepted
                cases outcome with
                | budgetExhausted plan next pending => cases accepted
                | complete inserted =>
                    cases accepted
                    let event : Event program := ⟨before, after, caller, callerMember,
                      node, nodeMember, available, resolved, selection.method.specialized,
                      selectionReceipt, budget, extended⟩
                    exact ⟨event.growth, from_extension event receipts⟩

private theorem aux_origins {program : CheckedProgram}
    {budget fuel next : Nat} {input before after : Plan}
    (origins : All program input before)
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux
      program budget fuel next before = .ok after) : All program input after := by
  induction fuel generalizing next before after with
  | zero =>
      unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
      split at accepted
      · cases accepted; exact origins
      · cases accepted
  | succ fuel ih =>
      unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
      split at accepted
      · cases accepted; exact origins
      · rename_i caller found
        have callerMember : caller ∈ before.specializations := List.mem_of_getElem? found
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨extended, scan, rest⟩ := bind_ok accepted
        obtain ⟨available, resolved, scan⟩ := bind_ok scan
        obtain ⟨loopFinal, loop, returned⟩ := bind_ok scan
        cases returned
        have scanned : Growth before extended ∧ All program input extended := by
          apply forIn_invariant loop (P := fun current => Growth before current ∧ All program input current)
            ⟨.refl _, origins⟩
          intro item member current outcome nodeAccepted currentOrigins
          cases item with
          | statement statement =>
              cases nodeAccepted
              exact ⟨current, rfl, currentOrigins⟩
          | expression node =>
              have currentMember := currentOrigins.1.rows.entries.subset callerMember
              cases form : node.form <;> simp only [form] at nodeAccepted
              case' call callee arguments resolution => cases resolution
              case' reference name resolution => cases resolution
              all_goals
                first
                | (obtain ⟨opPlan, opAccepted, nodeAccepted⟩ := bind_ok nodeAccepted
                   have opOrigins := operator_origins currentOrigins.2 currentMember member resolved opAccepted
                   have opState : Growth before opPlan ∧ All program input opPlan :=
                     ⟨currentOrigins.1.trans opOrigins.1, opOrigins.2⟩)
                | (let opPlan := current
                   have opState : Growth before opPlan ∧ All program input opPlan := currentOrigins)
              all_goals
                obtain ⟨outputPlan, outputLoop, nodeAccepted⟩ := bind_ok nodeAccepted
                have outputState : Growth before outputPlan ∧ All program input outputPlan :=
                  forIn_invariant (α := CoercionStep) (ε := SourceTypedRuntime.RuntimeError)
                    (P := fun current => Growth before current ∧ All program input current)
                    outputLoop opState (by
                    intro step occurs previous outcome accepted previousState
                    obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                    have updatedState := coercion_origins previousState.2
                      (previousState.1.rows.entries.subset callerMember) member resolved
                      (Or.inl occurs) headAccepted
                    cases returned
                    exact ⟨updated, rfl, previousState.1.trans updatedState.1, updatedState.2⟩)
              all_goals try rw [form] at nodeAccepted
              all_goals try dsimp only at nodeAccepted
              all_goals
                iterate 8 all_goals first
                  | exact ⟨outputPlan, (Except.ok.inj nodeAccepted).symm, outputState⟩
                  | (obtain ⟨argumentPlan, argumentLoop, nodeAccepted⟩ := bind_ok nodeAccepted
                     have argumentState : Growth before argumentPlan ∧ All program input argumentPlan :=
                       forIn_invariant (α := CoercionStep) (ε := SourceTypedRuntime.RuntimeError)
                         (P := fun current => Growth before current ∧ All program input current)
                         argumentLoop outputState (by
                         intro step occurs previous outcome accepted previousState
                         obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                         have occurrence : CoercionAt node step := Or.inr ⟨_, _, _, form, occurs⟩
                         have updatedState := coercion_origins previousState.2
                           (previousState.1.rows.entries.subset callerMember) member resolved
                           occurrence headAccepted
                         cases returned
                         exact ⟨updated, rfl, previousState.1.trans updatedState.1, updatedState.2⟩)
                     exact ⟨argumentPlan, (Except.ok.inj nodeAccepted).symm, argumentState⟩)
                  | (obtain ⟨_, _, nodeAccepted⟩ := bind_ok nodeAccepted)
                  | split at nodeAccepted
                  | contradiction
        exact ih scanned.2 rest

private theorem replay_origins {program : CheckedProgram} {plan : Plan}
    (canonical : SourceCompilationPlan.validateCanonicalInputPlan program plan = .ok ()) :
    All program plan plan := by
  have accepted := canonical
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
      · have fields : ((expected.seedKeys == plan.seedKeys) &&
            ((expected.specializations == plan.specializations) &&
              ((expected.callEdges == plan.callEdges) &&
                (expected.referenceEdges == plan.referenceEdges)))) = true := same
        simp only [Bool.and_eq_true] at fields
        have rows : expected.specializations = plan.specializations :=
          LawfulBEq.eq_of_beq fields.2.1
        letI : LawfulBEq CallEdge := by
          exact {
            eq_of_beq := by
              intro left right equal
              cases left with
              | mk lc lo lt =>
                cases right with
                | mk rc ro rt =>
                  change (lc == rc && (lo == ro && lt == rt)) = true at equal
                  simp only [Bool.and_eq_true, beq_iff_eq] at equal
                  rcases equal with ⟨rfl, rfl, rfl⟩
                  rfl
            rfl := by
              intro edge
              cases edge
              change (_ && (_ && _)) = true
              simp }
        have calls : expected.callEdges = plan.callEdges := LawfulBEq.eq_of_beq fields.2.2.1
        intro edge present
        obtain ⟨row, member, source⟩ := run_call_origins executed
          (show edge ∈ (Outcome.complete expected).plan.callEdges by
            simpa only [Outcome.plan_complete, calls] using present)
        exact .input canonical present row
          (by simpa only [Outcome.plan_complete, rows] using member) source
      · simp only [same, throw, throwThe, MonadExceptOf.throw] at accepted
        cases accepted

/-- Every final edge comes from the authenticated input or from an actual checked
method extension. The latter retains its synthetic outer edge separately from
supplied-root and later ordinary source scans. -/
theorem of_preparation {program : CheckedProgram} {before after : Plan}
    {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok after) : All program before after := by
  obtain ⟨prepared, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  exact aux_origins (replay_origins canonical) inspected

theorem of_default_preparation {program : CheckedProgram} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidence program before = .ok after) :
    All program before after := of_preparation accepted

/-- Original open calls in the actual selected compilation have a final prepared
edge together with its real preparation ancestry. The edge may be introduced by
preparation and is not asserted to be an edge of the input plan. -/
theorem compiled_selected (compiled : SourceCoreCompiler.Compiled) :
    ∃ prepared, SourceCompilationPlan.prepareExecutablePlanEvidence compiled.program compiled.plan = .ok prepared ∧
      Growth compiled.plan prepared ∧ All compiled.program compiled.plan prepared ∧
      ∀ caller ∈ compiled.plan.specializations, ∀ node,
        .expression node ∈ caller.function.typedBody.nodes →
        ∀ callee arguments instantiation,
          node.form = .call callee arguments (.declaration instantiation) →
          SourcePreparedOpenCallEdges.InstantiationClosed instantiation = false →
          ∃ receipt : SourcePreparedOpenCallEdges.EdgeAt caller node instantiation prepared,
            Origin compiled.program compiled.plan prepared receipt.edge := by
  obtain ⟨prepared, accepted, growth, covered⟩ := SourcePreparedOpenCallEdges.compiled_selected compiled
  have origins := of_default_preparation accepted
  refine ⟨prepared, accepted, growth, origins, ?_⟩
  intro caller member node present callee arguments instantiation form opened
  obtain ⟨receipt⟩ := covered caller member node present callee arguments instantiation form opened
  exact ⟨receipt, origins receipt.edge (receipt.retained receipt.present)⟩

end Solcore.SourceSemantics.SourcePreparedFinalCallEdgeOrigins
