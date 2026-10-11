import Solcore.SourceSemantics.CoreLowering.CallablePreparedOrdinaryRequestOrigins
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection

/-!
Public executable-plan preparation preserves genuine catalog provenance for
all final rows. Ordinary requests retain their function-signature and checked
function membership. Detached coercion and operator roots retain the actual
implementation-method selector instead. New ordinary descendants are supplied
by the real worklist extension. No detached method is treated as an ordinary
catalog function, and no source, stage or execution equality is assumed.

The proof follows the accepted preparation loops. Its action premises are the
actual private helper bodies; it defines no substitute compiler computation.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins

open Frontend SourceInference SourceSpecializationWorklist
open CallableCoercionPreparationSteps (bind_ok)

/-- The exact retained row is either an ordinary catalog specialization or the
specialized result of a genuine implementation-method selector. -/
inductive CatalogOrigin (program : CheckedProgram) :
    SourceSpecialization.SpecializedFunction → Prop where
  | ordinary {row : SourceSpecialization.SpecializedFunction}
      (origin : RecursiveNamedPublicSpecializationMeaning.Origin program row) :
      CatalogOrigin program row
  | method {method : ExecutableImplMethods.CheckedMethod}
      (selected : CallableCoercionBodyProvenance.Selection program method) :
      CatalogOrigin program method.specialized

/-- A worklist extension keeps each original tag and the exact supplied root
while its newly resolved request rows receive ordinary catalog origins. -/
theorem extend_catalog_origins {program : CheckedProgram} {before : Plan}
    {root : SourceSpecialization.SpecializedFunction} {edge : CallEdge}
    {budget : Nat} {outcome : Outcome}
    (origins : ∀ row ∈ before.specializations, CatalogOrigin program row)
    (rootOrigin : CatalogOrigin program root)
    (accepted : extendCompletePlan program before root edge budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, CatalogOrigin program row := by
  intro row member
  rcases CallablePreparedOrdinaryRequestOrigins.extend_origin_cases accepted
      row member with previous | same | ordinary
  · exact origins row previous
  · subst row
    exact rootOrigin
  · exact CatalogOrigin.ordinary ordinary

private theorem forIn_origins {program : CheckedProgram} {α ε : Type} {items : List α}
    {initial final : Plan} {step : α → Plan → Except ε (ForInStep Plan)}
    (accepted : forIn items initial step = .ok final)
    (origins : ∀ row ∈ initial.specializations, CatalogOrigin program row)
    (next : ∀ item ∈ items, ∀ before outcome,
      step item before = .ok outcome →
      (∀ row ∈ before.specializations, CatalogOrigin program row) →
      ∃ after, outcome = .yield after ∧
        ∀ row ∈ after.specializations, CatalogOrigin program row) :
    ∀ row ∈ final.specializations, CatalogOrigin program row := by
  induction items generalizing initial with
  | nil =>
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
      subst final
      exact origins
  | cons item rest ih =>
      rw [List.forIn_cons] at accepted
      obtain ⟨outcome, executed, finished⟩ := bind_ok accepted
      obtain ⟨after, rfl, afterOrigins⟩ :=
        next item (by simp) initial outcome executed origins
      exact ih finished afterOrigins
        (fun value member => next value (by simp [member]))

private theorem coercion_origins {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {node : ExpressionNode} {coercion : CoercionStep}
    {before after : Plan} {budget : Nat}
    (origins : ∀ row ∈ before.specializations, CatalogOrigin program row)
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
    ∀ row ∈ after.specializations, CatalogOrigin program row := by
  obtain ⟨method, selected, accepted⟩ := bind_ok accepted
  obtain ⟨returned, _, accepted⟩ := bind_ok accepted
  cases returned
  obtain ⟨returned, _, accepted⟩ := bind_ok accepted
  cases returned
  obtain ⟨certificate⟩ := CallableCoercionSourceSelection.of_accepted selected
  have rootOrigin : CatalogOrigin program method.specialized :=
    CatalogOrigin.method certificate.selected.toSelection
  cases extended : extendCompletePlan program before method.specialized
      ⟨caller.key, node.id, method.specialized.key⟩ budget with
  | error error => rw [extended] at accepted; cases accepted
  | ok outcome =>
      rw [extended] at accepted
      cases outcome with
      | budgetExhausted plan next pending => cases accepted
      | complete inserted =>
          cases accepted
          exact extend_catalog_origins
            origins rootOrigin extended

private theorem operator_origins {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {node : ExpressionNode} {before after : Plan} {budget : Nat}
    (origins : ∀ row ∈ before.specializations, CatalogOrigin program row)
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
    ∀ row ∈ after.specializations, CatalogOrigin program row := by
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
          exact origins
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
            have rootOrigin : CatalogOrigin program selection.method.specialized := by
              first
              | (obtain ⟨_, _, _, _, _, ⟨certificate⟩⟩ :=
                    CallablePreparedMethodSelection.unary_of_accepted selected
                 exact CatalogOrigin.method certificate.selected.toSelection)
              | (obtain ⟨_, _, _, _, _, ⟨certificate⟩⟩ :=
                    CallablePreparedMethodSelection.binary_of_accepted selected
                 exact CatalogOrigin.method certificate.selected.toSelection)
            cases extended : extendCompletePlan program before selection.method.specialized
                ⟨caller.key, node.id, selection.method.specialized.key⟩ budget with
            | error error => rw [extended] at accepted; cases accepted
            | ok outcome =>
                rw [extended] at accepted
                cases outcome with
                | budgetExhausted plan next pending => cases accepted
                | complete inserted =>
                    cases accepted
                    exact extend_catalog_origins
                      origins rootOrigin extended

private theorem aux_origins {program : CheckedProgram}
    {budget fuel next : Nat} {before after : Plan}
    (origins : ∀ row ∈ before.specializations, CatalogOrigin program row)
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux
      program budget fuel next before = .ok after) :
    ∀ row ∈ after.specializations, CatalogOrigin program row := by
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
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨extended, scan, rest⟩ := bind_ok accepted
        obtain ⟨available, _, scan⟩ := bind_ok scan
        obtain ⟨loopFinal, loop, returned⟩ := bind_ok scan
        cases returned
        have scanned : ∀ row ∈ extended.specializations, CatalogOrigin program row := by
          apply forIn_origins loop origins
          intro item member current outcome nodeAccepted currentOrigins
          cases item with
          | statement statement =>
              cases nodeAccepted
              exact ⟨current, rfl, currentOrigins⟩
          | expression node =>
              cases form : node.form <;> simp only [form] at nodeAccepted
              case' call callee arguments resolution => cases resolution
              case' reference name resolution => cases resolution
              all_goals
                first
                | (obtain ⟨opPlan, opAccepted, nodeAccepted⟩ := bind_ok nodeAccepted
                   have opOrigins := operator_origins currentOrigins opAccepted)
                | (let opPlan := current
                   have opOrigins : ∀ row ∈ opPlan.specializations, CatalogOrigin program row :=
                     currentOrigins)
              all_goals
                obtain ⟨outputPlan, outputLoop, nodeAccepted⟩ := bind_ok nodeAccepted
                have outputOrigins : ∀ row ∈ outputPlan.specializations, CatalogOrigin program row :=
                  forIn_origins (α := CoercionStep) (ε := SourceTypedRuntime.RuntimeError)
                    outputLoop opOrigins (by
                    intro step _ previous outcome accepted previousOrigins
                    obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                    have updatedOrigins : ∀ row ∈ updated.specializations, CatalogOrigin program row :=
                      coercion_origins previousOrigins headAccepted
                    cases returned
                    exact ⟨updated, rfl, updatedOrigins⟩)
              all_goals try rw [form] at nodeAccepted
              all_goals try dsimp only at nodeAccepted
              all_goals
                iterate 8 all_goals first
                  | exact ⟨outputPlan, (Except.ok.inj nodeAccepted).symm, outputOrigins⟩
                  | (obtain ⟨argumentPlan, argumentLoop, nodeAccepted⟩ := bind_ok nodeAccepted
                     have argumentOrigins : ∀ row ∈ argumentPlan.specializations, CatalogOrigin program row :=
                       forIn_origins (α := CoercionStep) (ε := SourceTypedRuntime.RuntimeError)
                         argumentLoop outputOrigins (by
                         intro step _ previous outcome accepted previousOrigins
                         obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                         have updatedOrigins : ∀ row ∈ updated.specializations, CatalogOrigin program row :=
                           coercion_origins previousOrigins headAccepted
                         cases returned
                         exact ⟨updated, rfl, updatedOrigins⟩)
                     exact ⟨argumentPlan, (Except.ok.inj nodeAccepted).symm, argumentOrigins⟩)
                  | (obtain ⟨_, _, nodeAccepted⟩ := bind_ok nodeAccepted)
                  | split at nodeAccepted
                  | contradiction
        exact ih scanned rest

/-- Actual public preparation authenticates the canonical ordinary input and
every inserted checked method. Every final row retains its genuine catalog
branch, including ordinary descendants of detached method roots. -/
theorem of_preparation {program : CheckedProgram} {before after : Plan}
    {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok after) :
    ∀ row ∈ after.specializations, CatalogOrigin program row := by
  obtain ⟨prepared, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  have initial : ∀ row ∈ before.specializations, CatalogOrigin program row := by
    intro row member
    exact CatalogOrigin.ordinary
      (CallablePreparedOrdinaryRequestOrigins.canonical_input_origins canonical
        row member)
  exact aux_origins initial inspected

/-- The default public preparation forwards the same actual producer chain. -/
theorem of_default_preparation {program : CheckedProgram} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidence program before = .ok after) :
    ∀ row ∈ after.specializations, CatalogOrigin program row :=
  of_preparation accepted

end Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins
