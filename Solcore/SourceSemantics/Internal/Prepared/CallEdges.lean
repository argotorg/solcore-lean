import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.Internal.Compiled.InitializerOccurrences
import Solcore.Frontend.SourceInference.Internal.LocalReadScopes
import Solcore.SourceSemantics.Internal.Prepared.PlanGrowth
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOrigins
import Solcore.SourceSemantics.Internal.Compiled.Finalization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.OrdinaryCallsReady
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls

/-!
# Prepared call edges

Final call edges keep their canonical input or checked method ancestry, cataloged calls keep source
ancestry, and open calls use a discovered local instance of the same selected row.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceBodyGeneralizationFrameOrigins
/-! Each active flexible variable comes from an actual outer initialized
binding. Acyclic occurrence paths and unique local identities distinguish
that binding from the initializer currently being checked. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyGeneralizationFrameOrigins
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness

private theorem flatMap_sublist {α β : Type} (values : List α) (f g : α → List β)
    (each : ∀ value, List.Sublist (f value) (g value)) : List.Sublist (values.flatMap f) (values.flatMap g) := by
  induction values with
  | nil => exact .refl _
  | cons head rest ih => exact (each head).append ih

private theorem forItem_ids (item : ForItemForm) :
    List.Sublist ((forItemInitializedLetBindings item).map fun binding => binding.binder.id)
      (forItemDefinedLocalIds item) := by
  cases item <;> try exact .refl _
  rename_i binder initializer
  cases initializer <;> simp [forItemInitializedLetBindings, forItemDefinedLocalIds]

private theorem form_ids (form : StatementForm) :
    List.Sublist ((statementInitializedLetBindings form).map fun binding => binding.binder.id)
      (statementDefinedLocalIds form) := by
  cases form <;> try exact List.nil_sublist _
  case letDecl binder initializer =>
    cases initializer <;> simp [statementInitializedLetBindings, statementDefinedLocalIds]
  case forLoop initial condition post body =>
    simp only [statementInitializedLetBindings, statementDefinedLocalIds, List.map_append, List.map_flatMap]
    exact (flatMap_sublist initial _ _ forItem_ids).append (flatMap_sublist post _ _ forItem_ids)

private theorem initialized_ids (source : TypedSource) :
    List.Sublist ((initializedLetBindings source).map fun binding => binding.binder.id)
      (definedLocalIds source) := by
  unfold initializedLetBindings definedLocalIds
  rw [List.map_flatMap]
  apply List.sublist_append_of_sublist_right
  apply flatMap_sublist
  intro node
  cases node with
  | expression expression => exact List.nil_sublist _
  | statement statement => exact form_ids statement.form


variable {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
  {selected : BodySelection compiled row fuel}
  {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

/-- Recover a raw outer binding from the finalized context and the real
strict containment relation of the current initializer. -/
theorem of_nested {current : InitializedLetBinding}
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (retained : FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution current ∈
      initializedLetBindings selected.body.finalized.typedSource)
    (nested : ∀ outer ∈ frames,
      Descends selected.body.finalized.typedSource outer.initializer current.initializer)
    {metavariable : TypeVarId} (occurs : metavariable ∈ target.typeVariables) :
    ∃ other ∈ initializedLetBindings (evidenceSource selected),
      other.binder ≠ current.binder ∧ metavariable ∈ other.binder.scheme.quantified := by
  rw [actual.variables_eq] at occurs
  obtain ⟨frame, frameMember, quantified⟩ := List.mem_flatMap.mp occurs
  have frameRetained := actual.retained frame frameMember
  have rawRetained := frameRetained
  rw [selected.body.resources.source_eq,
    FlexibleSubstitution.initializedLetBindings_applySubstitution] at rawRetained
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp rawRetained
  refine ⟨original, originalMember, ?_, ?_⟩
  · intro equalBinder
    have unique := (initialized_ids selected.body.finalized.typedSource).nodup
      selected.body.resources.local_identity_ownership.unique
    have ids : frame.binder.id =
        (FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution current).binder.id := by
      rw [← same]
      change original.binder.id = current.binder.id
      exact congrArg TypedBinder.id equalBinder
    have equalBinding := eq_of_mem_of_nodup_map unique frameRetained retained ids
    have path := nested frame frameMember
    rw [equalBinding] at path
    exact selected.body.resources.graph_closed.acyclic _ path
  · rw [← same] at quantified
    exact quantified

/-- Statement scopes are recovered from the same accepted let occurrence
and the context used by its existing typing proof. -/
theorem statement {source : Syntax.Statement} {expectedReturn : Ty}
    (occurrence : BodyInitializerOccurrence selected source)
    (boundary : StatementBoundary selected (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target)
    {metavariable : TypeVarId} (occurs : metavariable ∈ target.typeVariables) :
    ∃ other ∈ initializedLetBindings (evidenceSource selected),
      other.binder ≠ occurrence.receipt.binding.1 ∧ metavariable ∈ other.binder.scheme.quantified := by
  have idEq : occurrence.result.id = occurrence.entry.allocateStatementId.1 :=
    congrArg Detail.StatementResult.id occurrence.receipt.completed
  have entered := occurrence.enter (RecursiveExpressionInvariant.ofStatement boundary.invariant)
    boundary.actual (idEq ▸ boundary.actualCovered)
  have currentMember : occurrence.initializerBinding ∈ frames ++ [occurrence.initializerBinding] := by simp
  have retained := entered.2.1.retained occurrence.initializerBinding currentMember
  have nested := (List.pairwise_append.mp entered.2.1.nested).2.2
  exact of_nested (current := ⟨occurrence.receipt.binding.1, .expression occurrence.receipt.value.id⟩)
    boundary.actual retained
    (fun outer member => nested outer member occurrence.initializerBinding (by simp)) occurs

/-- Header scopes use the actual initialized item and its retained strict
containment relation, including initialization inside loop headers. -/
theorem header {childFuel : Nat} {inferenceContext : SourceInference.Context}
    {item : Syntax.ForItem} {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target)
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel inferenceContext item initial (inferred, final))
    {metavariable : TypeVarId} (occurs : metavariable ∈ target.typeVariables) :
    ∃ other ∈ initializedLetBindings (evidenceSource selected),
      other.binder ≠ receipt.binding.1 ∧ metavariable ∈ other.binder.scheme.quantified := by
  let binding : InitializedLetBinding := ⟨receipt.binding.1, .expression receipt.value.id⟩
  have member : binding ∈ forItemInitializedLetBindings inferred := by
    have itemEq : inferred = .letDecl receipt.binding.1 (some receipt.value.id) := receipt.recorded
    rw [itemEq]
    exact List.mem_singleton_self _
  have nested := boundary.actualBindings binding member
  exact of_nested (current := binding) boundary.actual nested.1 nested.2 occurs

end Solcore.SourceSemantics.SourceBodyGeneralizationFrameOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedCallEdgeOrigins
/-! Final call-edge origins retain the actual checked method action and its
worklist extension. Supplied outer edges remain distinct from source calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourcePreparedCallEdgeOrigins
open Frontend SourceInference SourceSpecializationWorklist
open SourcePreparedPlanGrowth
open CoreLowering.CallableCoercionPreparationSteps (Specialized)

def CoercionAt (node : ExpressionNode) (step : CoercionStep) : Prop :=
  step ∈ node.coercions ∨ ∃ callee arguments metadata,
    node.form = .call callee arguments (.indirect metadata) ∧
      step ∈ metadata.argumentCoercions

inductive Selection (program : CheckedProgram) (caller : Specialized)
    (node : ExpressionNode) (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) :
    Specialized → Prop where
  | coercion {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
      (occurrence : CoercionAt node step)
      (selected : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method)
      (boundary : SourceCompilationPlan.validateStagedCallBoundary caller node [node.id] method.specialized = .ok ())
      (evidence : (discard <| SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method) = .ok ()) :
      Selection program caller node available method.specialized
  | unary {requirements : List RequirementId} {operator : Syntax.UnaryOp} {operand : ExpressionId}
      {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
      (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements)
      (nonempty : requirements ≠ []) (form : node.form = .unary operator operand)
      (selected : SourceCompilationPlan.checkedUnaryOperatorMethod program caller
        { node with type := node.rawType, requirements, coercions := [] } available operator = .ok selection)
      (boundary : SourceCompilationPlan.validateStagedCallBoundary caller
        { node with type := node.rawType, requirements, coercions := [] } [operand]
        selection.method.specialized = .ok ())
      (evidence : (discard <| SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
        { node with type := node.rawType, requirements, coercions := [] } selection) = .ok ()) :
      Selection program caller node available selection.method.specialized
  | binary {requirements : List RequirementId} {operator : Syntax.BinaryOp} {left right : ExpressionId}
      {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
      (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements)
      (nonempty : requirements ≠ []) (form : node.form = .binary left operator right)
      (selected : SourceCompilationPlan.checkedBinaryOperatorMethod program caller
        { node with type := node.rawType, requirements, coercions := [] } available operator = .ok selection)
      (boundary : SourceCompilationPlan.validateStagedCallBoundary caller
        { node with type := node.rawType, requirements, coercions := [] } [left, right]
        selection.method.specialized = .ok ())
      (evidence : (discard <| SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
        { node with type := node.rawType, requirements, coercions := [] } selection) = .ok ()) :
      Selection program caller node available selection.method.specialized

structure Event (program : CheckedProgram) where
  before : Plan
  after : Plan
  caller : Specialized
  callerMember : caller ∈ before.specializations
  node : ExpressionNode
  nodeMember : .expression node ∈ caller.function.typedBody.nodes
  available : SourceTypedRuntime.RuntimeEvidenceEnvironment
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available
  root : Specialized
  selection : Selection program caller node available root
  budget : Nat
  extended : extendCompletePlan program before root ⟨caller.key, node.id, root.key⟩ budget = .ok (.complete after)

def Event.outer {program : CheckedProgram} (event : Event program) : CallEdge :=
  ⟨event.caller.key, event.node.id, event.root.key⟩

theorem Event.growth {program : CheckedProgram} (event : Event program) : Growth event.before event.after :=
  SourcePreparedPlanGrowth.extend event.extended

inductive Origin (program : CheckedProgram) (input final : Plan) (edge : CallEdge) : Prop where
  | input (canonical : SourceCompilationPlan.validateCanonicalInputPlan program input = .ok ())
      (present : edge ∈ input.callEdges)
      (row : Specialized) (member : row ∈ input.specializations)
      (source : CallEdge.SourceOrigin program row.key row.function.typedBody edge)
  | outer (event : Event program) (later : Growth event.after final) (same : edge = event.outer)
  | suppliedRoot (event : Event program) (later : Growth event.after final)
      (source : CallEdge.SourceOrigin program event.root.key event.root.function.typedBody edge)
  | ordinary (event : Event program) (later : Growth event.after final)
      (row : Specialized) (member : row ∈ event.after.specializations)
      (source : CallEdge.SourceOrigin program row.key row.function.typedBody edge)

theorem Origin.later {program : CheckedProgram} {input before after : Plan} {edge : CallEdge}
    (origin : Origin program input before edge) (growth : Growth before after) :
    Origin program input after edge := by
  cases origin with
  | input canonical present row member source => exact .input canonical present row member source
  | outer event later same => exact .outer event (later.trans growth) same
  | suppliedRoot event later source => exact .suppliedRoot event (later.trans growth) source
  | ordinary event later row member source => exact .ordinary event (later.trans growth) row member source

def All (program : CheckedProgram) (input final : Plan) : Prop :=
  ∀ edge ∈ final.callEdges, Origin program input final edge

theorem from_extension {program : CheckedProgram} {input : Plan} (event : Event program)
    (previous : All program input event.before) : All program input event.after := by
  intro edge member
  rcases extendCompletePlan_call_origins event.extended member with inherited | outer | root | ordinary
  · exact (previous edge inherited).later event.growth
  · exact .outer event (.refl _) outer
  · exact .suppliedRoot event (.refl _) root
  · obtain ⟨row, present, source⟩ := ordinary
    exact .ordinary event (.refl _) row present source

end Solcore.SourceSemantics.SourcePreparedCallEdgeOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedFinalCallEdgeOrigins
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedCatalogedCallOrigin
/-! Actual cataloged declaration calls retain source ancestry through every
prepared edge origin. Method extensions cannot impersonate ordinary targets. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourcePreparedCatalogedCallOrigin
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourcePreparedPlanGrowth SourcePreparedCallEdgeOrigins
open CoreLowering
open CallableCoercionPreparationSteps (Specialized bind_ok)

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

/-- The actual specialization constructor uses the checked declaration in its
key. The source owner guard supplies the same declaration. -/
theorem specialization_key_owner {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution} {row : Specialized}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok row) :
    row.key.declaration = row.function.typedBody.owner := by
  have owner := (RecursiveNamedSpecializationBodyFacts.identities accepted).2.1
  unfold SourceSpecialization.specializeFunction at accepted
  iterate 5 have accepted := reject_ok accepted
  iterate 4 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  iterate 4 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction
      (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
      simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
      subst row
      exact owner.symm

/-- All actual method preparation branches retain a method selection, whose
owner is disjoint from the ordinary declaration catalog. -/
theorem selection_key_not_catalog {program : CheckedProgram}
    (catalog : SignatureCatalogWellFormed program.signatures)
    {caller root : Specialized} {node : ExpressionNode}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (selection : Selection program caller node available root) :
    root.key.declaration ∉ program.signatures.functions.map (·.id) := by
  intro present
  obtain ⟨signature, member, same⟩ := List.mem_map.mp present
  have excluded : ∀ (method : ExecutableImplMethods.CheckedMethod),
      CallableCoercionBodyProvenance.Selection program method →
      method.specialized.key.declaration ≠ signature.id := by
    intro method selected
    rw [specialization_key_owner selected.specialized]
    exact CallableOrdinaryMethodCatalogSeparation.method_owner_ne_function catalog member selected
  cases selection with
  | coercion _ selected _ _ =>
      obtain ⟨receipt⟩ := CallableCoercionSourceSelection.of_accepted selected
      exact excluded _ receipt.selected.toSelection same.symm
  | unary _ _ _ selected _ _ =>
      obtain ⟨_, _, _, _, _, ⟨receipt⟩⟩ := CallablePreparedMethodSelection.unary_of_accepted selected
      exact excluded _ receipt.selected.toSelection same.symm
  | binary _ _ _ selected _ _ =>
      obtain ⟨_, _, _, _, _, ⟨receipt⟩⟩ := CallablePreparedMethodSelection.binary_of_accepted selected
      exact excluded _ receipt.selected.toSelection same.symm

private theorem exact_member_eq {plan : Plan} {key : SourceSpecialization.SpecializationKey}
    {selected other : Specialized}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok selected)
    (member : other ∈ plan.specializations) (same : other.key = key) : other = selected := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  rename_i found
  have present : other ∈ plan.specializations.filter (fun row => decide (row.key = key)) :=
    List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using same⟩
  rw [found] at present
  exact List.mem_singleton.mp present

private theorem exact_member {plan : Plan} {key : SourceSpecialization.SpecializationKey}
    {selected : Specialized}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok selected) :
    selected ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  rename_i found
  have present : selected ∈ plan.specializations.filter (fun row => decide (row.key = key)) := by
    rw [found]
    exact List.mem_cons_self
  exact (List.mem_filter.mp present).1

/-- Every real ancestry branch for a cataloged call is source-emitted by the
same complete selected row. Synthetic outer edges are eliminated by the
actual method/ordinary catalog separation. -/
theorem source_origin {program : CheckedProgram} {input final : Plan}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (growth : Growth input final) {caller : Specialized}
    (selected : SourceCompilationPlan.exactSpecialization input caller.key = .ok caller)
    {edge : CallEdge} (origin : Origin program input final edge)
    (sameCaller : edge.caller = caller.key)
    (cataloged : edge.callee.declaration ∈ program.signatures.functions.map (·.id)) :
    CallEdge.SourceOrigin program caller.key caller.function.typedBody edge := by
  have finalSelected := growth.rows.selected caller.key caller selected
  cases origin with
  | input _ _ row member source =>
      have same := exact_member_eq finalSelected (growth.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      subst row
      exact source
  | outer event _ same =>
      have target : event.root.key.declaration ∈ program.signatures.functions.map (·.id) := by
        simpa only [same, Event.outer] using cataloged
      exact False.elim (selection_key_not_catalog catalog event.selection target)
  | suppliedRoot event later source =>
      have root := CallableCoercionPlanProvenance.complete_root event.extended
      have member := exact_member root
      have same := exact_member_eq finalSelected (later.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      rw [same] at source
      exact source
  | ordinary event later row member source =>
      have same := exact_member_eq finalSelected (later.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      subst row
      exact source

end Solcore.SourceSemantics.SourcePreparedCatalogedCallOrigin
end

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedOpenCallOwner
/-! Open source calls use an actually discovered local instance of the same
original selected row. Closed/direct source scans cannot provide that edge. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourcePreparedOpenCallOwner
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourcePreparedOpenCallEdges

private theorem same_expression {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {left right : ExpressionNode} (leftMember : .expression left ∈ source.nodes)
    (rightMember : .expression right ∈ source.nodes) (same : left.id = right.id) : left = right := by
  have leftFound := lookupExpression?_complete unique ⟨leftMember, rfl⟩
  have rightFound := lookupExpression?_complete unique ⟨rightMember, rfl⟩
  rw [same] at leftFound
  exact Option.some.inj (leftFound.symm.trans rightFound)

private theorem direct_closed {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource} {edge : CallEdge}
    (receipt : CallEdge.DirectReceipt program caller source edge) :
    InstantiationClosed receipt.instantiation = true := by
  have closed := receipt.closed
  change (match (match receipt.node.form with
    | .call _ _ (.declaration instantiation) => some instantiation
    | .reference _ (.declaration instantiation) => some instantiation
    | _ => none) with
      | some instantiation => !(((instantiation.type ::
          instantiation.parameterSubstitution.map Prod.snd ++
          instantiation.predicates.flatMap (fun predicate => predicate.subject :: predicate.arguments)).flatMap
            Ty.freeVariables).eraseDups).isEmpty
      | none => false) = false at closed
  rw [receipt.form] at closed
  simp only at closed
  have empty : ((receipt.instantiation.type ::
      receipt.instantiation.parameterSubstitution.map Prod.snd ++
      receipt.instantiation.predicates.flatMap (fun predicate => predicate.subject :: predicate.arguments)).flatMap
        Ty.freeVariables).eraseDups = [] := by
    exact List.isEmpty_iff.mp ((show ∀ value : Bool, (!value) = false → value = true by decide) _ closed)
  have erase_nil : ∀ values : List TypeVarId, values.eraseDups = [] → values = [] := by
    intro values given
    cases values with
    | nil => rfl
    | cons head tail => simp only [List.eraseDups_cons, List.cons_ne_nil] at given
  have empty := erase_nil _ empty
  simp only [List.flatMap_cons, List.append_eq_nil_iff, List.flatMap_append] at empty
  unfold InstantiationClosed
  simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true]
  refine ⟨⟨empty.1.1, ?_⟩, ?_⟩
  · intro entry present
    have all := List.flatMap_eq_nil_iff.mp empty.1.2
    exact all _ (List.mem_map.mpr ⟨entry, present, rfl⟩)
  · intro predicate present
    have all := List.flatMap_eq_nil_iff.mp empty.2
    have subject := all predicate.subject (List.mem_flatMap.mpr ⟨predicate, present, List.mem_cons_self⟩)
    refine ⟨subject, ?_⟩
    intro argument occurs
    exact all argument (List.mem_flatMap.mpr ⟨predicate, present, List.mem_cons_of_mem _ occurs⟩)

structure Contextual (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey) (source : TypedSource)
    (node : ExpressionNode) (edge : CallEdge)
    extends CallEdge.ContextualReceipt program caller source edge where
  sameNode : node.applySubstitution localInstance.substitution = receipt.node

/-- The same original call is in the actual lexical body whose template
ownership checks succeeded for this discovered instance. -/
theorem Contextual.body {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource}
    {node : ExpressionNode} {edge : CallEdge}
    (contextual : Contextual program caller source node edge)
    (unique : NodeOccurrencesUnique source) (present : .expression node ∈ source.nodes) :
    ∃ nodes, localLambdaBodyNodes source contextual.localInstance = .ok nodes ∧
      .expression node ∈ nodes ∧
      LocalTemplateUses (localLambdaBindings source) contextual.localInstance nodes := by
  obtain ⟨original, nodes, accepted, originalMember, transformed⟩ := contextual.toContextualReceipt.original_body
  obtain ⟨checkedNodes, checked, subset, templates⟩ :=
    localLambdaInstances_template_receipts contextual.discovered contextual.localInstance contextual.member
  have same := Except.ok.inj (accepted.symm.trans checked)
  subst checkedNodes
  have sameId := congrArg ExpressionNode.id (transformed.trans contextual.sameNode.symm)
  change original.id = node.id at sameId
  have same := same_expression unique (subset originalMember) present sameId
  subst original
  exact ⟨nodes, accepted, originalMember, templates⟩

/-- This is the actual contextual branch of edge discovery, including the
complete instance, substitution, and same original node. -/
theorem contextual_of_open {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource}
    (unique : NodeOccurrencesUnique source) {node : ExpressionNode}
    (present : .expression node ∈ source.nodes) {callee : ExpressionId}
    {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (opened : InstantiationClosed instantiation = false)
    {edge : CallEdge} (origin : CallEdge.SourceOrigin program caller source edge)
    (occurrence : edge.occurrence = node.id) : Nonempty (Contextual program caller source node edge) := by
  rcases origin.receipts with direct | contextual
  · obtain ⟨receipt, member⟩ := direct
    have same := same_expression unique member present (receipt.emitted.2.1.symm.trans occurrence)
    have forms := receipt.form.symm.trans (same ▸ form)
    have sameInstantiation : receipt.instantiation = instantiation := by cases forms; rfl
    have closed := direct_closed receipt
    rw [sameInstantiation, opened] at closed
    cases closed
  · obtain ⟨contextual⟩ := contextual
    obtain ⟨original, originalMember, transformed⟩ := contextual.original
    have occurrenceEq := congrArg ExpressionNode.id transformed
    change original.id = contextual.receipt.node.id at occurrenceEq
    have same := same_expression unique originalMember present
      (occurrenceEq.trans (contextual.receipt.emitted.2.1.symm.trans occurrence))
    subst original
    exact ⟨⟨contextual, transformed⟩⟩

end Solcore.SourceSemantics.SourcePreparedOpenCallOwner
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceSpecializationLocalLexicalSubstitutionChildren
/-! Actual substituted lookups retain the original lexical child path. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceSpecializationWorklist.LocalLambdaLexicalPath
open SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews

theorem statement_child_of_substitution
    {source : TypedSource} {active : Substitution} {roots : List NodeId}
    {id : StatementId} {statement : StatementNode} {child : NodeId}
    (previous : LocalLambdaLexicalPath source roots (.statement id))
    (found : (source.applySubstitution active).lookupStatement? id = some statement)
    (edge : child ∈ statement.form.references) :
    LocalLambdaLexicalPath source roots child := by
  rw [lookupStatement_apply] at found
  obtain ⟨original, actual, rfl⟩ := Option.map_eq_some_iff.mp found
  exact previous.statement_child actual (by
    simpa only [StatementNode.applySubstitution,
      StatementForm.applySubstitution_references] using edge)

theorem expression_child_of_substitution
    {source : TypedSource} {active : Substitution} {roots : List NodeId}
    {id : ExpressionId} {expression : ExpressionNode} {child : NodeId}
    (previous : LocalLambdaLexicalPath source roots (.expression id))
    (found : (source.applySubstitution active).lookupExpression? id = some expression)
    (nonLambda : ∀ parameters result body, expression.form ≠ .lambda parameters result body)
    (edge : child ∈ expression.form.references) :
    LocalLambdaLexicalPath source roots child := by
  rw [lookupExpression_apply] at found
  obtain ⟨original, actual, rfl⟩ := Option.map_eq_some_iff.mp found
  refine previous.expression_child actual ?_ ?_
  · intro parameters result body form
    apply nonLambda (parameters.map (TypedBinder.applySubstitution active))
      (active.apply result) body
    change original.form.applySubstitution active = _
    rw [form]
    rfl
  · simpa only [ExpressionNode.applySubstitution,
      ExpressionForm.applySubstitution_references] using edge

end Solcore.Frontend.SourceSpecializationWorklist.LocalLambdaLexicalPath
end
