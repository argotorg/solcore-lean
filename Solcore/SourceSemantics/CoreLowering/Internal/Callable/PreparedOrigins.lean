import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedMethods
import Solcore.Frontend.SourceSpecializationAcceptance
import Lean
import Solcore.Frontend.SourceCoreCallableIndexedAncestry

/-!
# Prepared origins

Origins of ordinary requests, final catalogs and specializations, and view selection.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedOrdinaryRequestOrigins
/-!
Ordinary requests keep their actual catalog provenance when the real worklist
extends a plan. The general extension theorem separates unchanged rows and the
supplied detached root from rows resolved by ordinary requests. Its ordinary
corollary obtains catalog membership from accepted request and worklist actions.
No detached method is asserted to be an ordinary catalog function.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedOrdinaryRequestOrigins

open Frontend SourceInference TypeSystem SourceSpecializationWorklist

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem next_resolved {program : CheckedProgram}
    {seen : List SourceSpecialization.SpecializationKey}
    {queue rest : List Request} {request : Request}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : nextUnseen program seen queue =
      .ok (some (request, specialized, rest))) :
    resolveRequest program request = .ok specialized := by
  induction queue with
  | nil => cases accepted
  | cons head tail ih =>
      unfold nextUnseen at accepted
      obtain ⟨value, resolved, accepted⟩ := bind_ok accepted
      split at accepted
      · exact ih accepted
      · cases accepted
        exact resolved

private theorem runAux_origin_cases {program : CheckedProgram}
    {seedKeys seen : List SourceSpecialization.SpecializationKey}
    {queue : List Request}
    {entries : List SourceSpecialization.SpecializedFunction}
    {calls : List CallEdge} {references : List ReferenceEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : runAux program seedKeys queue seen entries calls references
      budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations,
      row ∈ entries ∨ RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  induction budget generalizing queue seen entries calls references outcome with
  | zero =>
      unfold runAux at accepted
      obtain ⟨next, _, accepted⟩ := bind_ok accepted
      cases next with
      | none => cases accepted; exact fun row member => Or.inl member
      | some item =>
          rcases item with ⟨request, selected, rest⟩
          cases accepted
          exact fun row member => Or.inl member
  | succ budget ih =>
      unfold runAux at accepted
      obtain ⟨next, found, accepted⟩ := bind_ok accepted
      cases next with
      | none => cases accepted; exact fun row member => Or.inl member
      | some item =>
          rcases item with ⟨request, selected, rest⟩
          obtain ⟨⟨requests, newCalls, newReferences⟩, _, accepted⟩ := bind_ok accepted
          intro row member
          rcases ih (accepted := accepted) row member with previous | origin
          · rcases List.mem_append.mp previous with old | added
            · exact Or.inl old
            · have same : row = selected := by simpa using added
              subst row
              exact Or.inr (RecursiveNamedPublicSpecializationMeaning.resolve_origin
                (next_resolved found))
          · exact Or.inr origin

/-- New retained rows have genuine ordinary request origins. Previously stored
rows and the actual supplied detached root remain separately identified. -/
theorem extend_origin_cases {program : CheckedProgram} {before : Plan}
    {root : SourceSpecialization.SpecializedFunction} {edge : CallEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : extendCompletePlan program before root edge budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations,
      row ∈ before.specializations ∨ row = root ∨
        RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  unfold extendCompletePlan at accepted
  obtain ⟨checked, _, accepted⟩ := bind_ok accepted
  cases checked
  split at accepted <;> try contradiction
  dsimp only at accepted
  split at accepted
  · simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    intro row member
    rcases runAux_origin_cases accepted row member with previous | origin
    · rcases List.mem_append.mp previous with old | added
      · exact Or.inl old
      · have same : row = root := by simpa using added
        exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr origin)
  · split at accepted <;> try contradiction
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    intro row member
    rcases runAux_origin_cases accepted row member with previous | origin
    · exact Or.inl previous
    · exact Or.inr (Or.inr origin)

/-- A genuine ordinary seed run and an actually resolved ordinary root suffice
for catalog provenance of every row retained by their accepted extension. -/
theorem extend_from_worklist_request_origins {program : CheckedProgram}
    {requests : List Request} {initialBudget : Nat} {initial : Outcome}
    {request : Request} {root : SourceSpecialization.SpecializedFunction}
    {edge : CallEdge} {budget : Nat} {outcome : Outcome}
    (initialAccepted : run program requests initialBudget = .ok initial)
    (rootAccepted : resolveRequest program request = .ok root)
    (extended : extendCompletePlan program initial.plan root edge budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations,
      RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  intro row member
  rcases extend_origin_cases extended row member with previous | same | origin
  · exact RecursiveNamedPublicSpecializationMeaning.worklist_origins
      initialAccepted row previous
  · subst row
    exact RecursiveNamedPublicSpecializationMeaning.resolve_origin rootAccepted
  · exact origin

/-- Canonical input validation actually replays ordinary requests and compares
all plan fields. Its retained rows therefore keep complete catalog origins. -/
theorem canonical_input_origins {program : CheckedProgram} {plan : Plan}
    (accepted : SourceCompilationPlan.validateCanonicalInputPlan program plan = .ok ()) :
    ∀ row ∈ plan.specializations,
      RecursiveNamedPublicSpecializationMeaning.Origin program row := by
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
        exact RecursiveNamedPublicSpecializationMeaning.worklist_origins executed
          row (by simpa only [Outcome.plan_complete, rows] using member)
      · simp only [same, throw, throwThe, MonadExceptOf.throw] at accepted
        cases accepted

/-- Successful public evidence preparation authenticates the original input
rows by canonical replay. Detached rows subsequently inserted by scanning are
not included in this conclusion. -/
theorem initial_origins_of_preparation {program : CheckedProgram}
    {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok after) :
    ∀ row ∈ before.specializations,
      RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  obtain ⟨prepared, _, accepted⟩ := bind_ok accepted
  obtain ⟨checked, canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  exact canonical_input_origins canonical

end Solcore.SourceSemantics.CoreLowering.CallablePreparedOrdinaryRequestOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedSpecializationOrigins
/-!
Actual specialization receipts survive ordinary worklist growth and detached
method insertion. Existing request and checked-method origin proofs supply the
receipts; no source equality, stage agreement or execution law is assumed.

An extension's supplied root still needs its genuine producer receipt. The
coercion and operator visit theorems construct that receipt from the actual
method selectors. This module does not yet compose every preparation loop into
a universal final-plan theorem or identify two original method templates.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedSpecializationOrigins

open Frontend SourceInference TypeSystem SourceSpecializationWorklist

abbrev Specialized := SourceSpecialization.SpecializedFunction

/-- A complete source carrier came from the real public rigid specializer. -/
def Receipt (specialized : Specialized) : Prop :=
  ∃ signature generic supplied,
    SourceSpecialization.specializeFunction signature generic supplied =
      .ok specialized

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Forget catalog membership only after the existing exact request-origin
theorem has supplied the actual original function and checker equation. -/
theorem of_request {program : CheckedProgram} {request : Request}
    {specialized : Specialized}
    (accepted : resolveRequest program request = .ok specialized) :
    Receipt specialized := by
  obtain ⟨request, signature, generic, _, _, _, specializedEq⟩ :=
    RecursiveNamedPublicSpecializationMeaning.resolve_origin accepted
  exact ⟨signature, generic, request.parameterSubstitution, specializedEq⟩

/-- The already proved public worklist origin chain covers each retained row,
including the retained prefix at budget exhaustion. -/
theorem of_worklist {program : CheckedProgram} {requests : List Request}
    {budget : Nat} {outcome : Outcome}
    (accepted : run program requests budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, Receipt row := by
  intro row member
  obtain ⟨request, signature, generic, _, _, _, specializedEq⟩ :=
    RecursiveNamedPublicSpecializationMeaning.worklist_origins accepted
      row member
  exact ⟨signature, generic, request.parameterSubstitution, specializedEq⟩

/-- The checked method receipt retains its actual synthetic signature, one
original body-check result, and the exact rigid specialization request. -/
theorem of_method_selection {program : CheckedProgram}
    {method : ExecutableImplMethods.CheckedMethod}
    (selected : CallableCoercionBodyProvenance.Selection program method) :
    Receipt method.specialized :=
  ⟨selected.implementation.functionSignatureOfMethodWithTrait
      selected.trait selected.declaration,
    selected.generic, selected.supplied, selected.specialized⟩

/-- A genuine reached coercion visit supplies its detached root receipt. -/
theorem of_coercion_visit {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {node : ExpressionNode} {coercion : CoercionStep} {final : Plan}
    (visit : CallableCoercionPreparationSteps.Visit program caller available
      node coercion final) :
    Receipt visit.method.specialized := by
  obtain ⟨certificate⟩ := CallableCoercionSourceSelection.of_accepted visit.selected
  exact of_method_selection certificate.selected.toSelection

private theorem operator_selected_receipt {program : CheckedProgram}
    {caller : Specialized} {node : ExpressionNode}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {requirements : List RequirementId}
    {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
    (accepted : (match node.form with
      | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod
          program caller node available operator
      | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod
          program caller node available operator
      | _ => throw (.unsupportedRequirements requirements)
      : Except SourceTypedRuntime.RuntimeError
          SourceCompilationPlan.CheckedRuntimeOperatorMethod) = .ok selection) :
    Receipt selection.method.specialized := by
  cases form : node.form <;> simp only [form] at accepted <;> try cases accepted
  case unary operator operand =>
    obtain ⟨_, _, _, _, _, ⟨certificate⟩⟩ :=
      CallablePreparedMethodSelection.unary_of_accepted accepted
    exact of_method_selection certificate.selected.toSelection
  case binary left operator right =>
    obtain ⟨_, _, _, _, _, ⟨certificate⟩⟩ :=
      CallablePreparedMethodSelection.binary_of_accepted accepted
    exact of_method_selection certificate.selected.toSelection

/-- The reached operator visit keeps its actual owned node and checked
unary/binary selector; either branch supplies its genuine detached root. -/
theorem of_operator_visit {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {node : ExpressionNode} {final : Plan}
    (visit : CallableCoercionPreparationSteps.OperatorVisit program caller
      available node final) :
    Receipt visit.selection.method.specialized :=
  operator_selected_receipt visit.selected

private theorem next_resolved {program : CheckedProgram}
    {seen : List SourceSpecialization.SpecializationKey}
    {queue rest : List Request} {request : Request} {specialized : Specialized}
    (accepted : nextUnseen program seen queue =
      .ok (some (request, specialized, rest))) :
    resolveRequest program request = .ok specialized := by
  induction queue with
  | nil => cases accepted
  | cons head tail ih =>
      unfold nextUnseen at accepted
      obtain ⟨value, resolved, accepted⟩ := bind_ok accepted
      split at accepted
      · exact ih accepted
      · cases accepted
        exact resolved

private theorem runAux_receipts {program : CheckedProgram}
    {seedKeys seen : List SourceSpecialization.SpecializationKey}
    {queue : List Request} {entries : List Specialized}
    {calls : List CallEdge} {references : List ReferenceEdge}
    {budget : Nat} {outcome : Outcome}
    (initial : ∀ row ∈ entries, Receipt row)
    (accepted : runAux program seedKeys queue seen entries calls references
      budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, Receipt row := by
  induction budget generalizing queue seen entries calls references outcome with
  | zero =>
      unfold runAux at accepted
      obtain ⟨next, _, accepted⟩ := bind_ok accepted
      cases next with
      | none => cases accepted; exact initial
      | some item =>
          rcases item with ⟨request, selected, rest⟩
          cases accepted
          exact initial
  | succ budget ih =>
      unfold runAux at accepted
      obtain ⟨next, found, accepted⟩ := bind_ok accepted
      cases next with
      | none => cases accepted; exact initial
      | some item =>
          rcases item with ⟨request, selected, rest⟩
          obtain ⟨⟨requests, newCalls, newReferences⟩, _, accepted⟩ := bind_ok accepted
          apply ih (accepted := accepted)
          intro row member
          rcases List.mem_append.mp member with old | added
          · exact initial row old
          · have same : row = selected := by simpa using added
            subst row
            exact of_request (next_resolved found)

/-- A real extension preserves previously accepted producers and the supplied
root producer. Every newly discovered descendant is actually resolved by the
worklist. Rejected or merely pending candidates are never made retained rows. -/
theorem extend_receipts {program : CheckedProgram} {before : Plan}
    {root : Specialized} {edge : CallEdge} {budget : Nat} {outcome : Outcome}
    (initial : ∀ row ∈ before.specializations, Receipt row)
    (rootReceipt : Receipt root)
    (accepted : extendCompletePlan program before root edge budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, Receipt row := by
  unfold extendCompletePlan at accepted
  obtain ⟨checked, _, accepted⟩ := bind_ok accepted
  cases checked
  split at accepted <;> try contradiction
  dsimp only at accepted
  split at accepted
  · simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    apply runAux_receipts (accepted := accepted)
    intro row member
    rcases List.mem_append.mp member with old | added
    · exact initial row old
    · have same : row = root := by simpa using added
      subst row
      exact rootReceipt
  · split at accepted <;> try contradiction
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    exact runAux_receipts initial accepted

end Solcore.SourceSemantics.CoreLowering.CallablePreparedSpecializationOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationOrigins
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationRanges
/-!
The real executable-plan preparation action supplies a specialization receipt
for each returned row. The actual rigid checker then supplies concrete and
flexible-closed replacements at that row's exact substitution lookup.

The original input plan and inserted methods are authenticated internally.
This result does not identify different original templates or infer source,
stage, guard-frame or execution coherence from a concrete replacement.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationRanges

open Frontend SourceInference TypeSystem SourceSpecializationWorklist

/-- Every actual retained lookup is checked by the genuine rigid specializer;
its accepted replacement contains no flexible variable. -/
theorem of_preparation {program : CheckedProgram} {before after : Plan}
    {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok after) :
    ∀ specialized ∈ after.specializations, ∀ parameter replacement,
      specialized.parameterSubstitution.lookup? parameter = some replacement →
      SourceSpecialization.firstNonConcrete replacement = none ∧
        replacement.freeVariables = [] := by
  intro specialized member parameter replacement found
  obtain ⟨signature, generic, supplied, specializedEq⟩ :=
    CallablePreparedFinalSpecializationOrigins.of_preparation accepted
      specialized member
  exact ⟨SourceSpecializationAcceptance.specializeFunction_parameterReplacement_concrete
      specializedEq parameter replacement found,
    SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
      specializedEq parameter replacement found⟩

/-- Default public preparation keeps the same complete retained-row result. -/
theorem of_default_preparation {program : CheckedProgram} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidence
      program before = .ok after) :
    ∀ specialized ∈ after.specializations, ∀ parameter replacement,
      specialized.parameterSubstitution.lookup? parameter = some replacement →
      SourceSpecialization.firstNonConcrete replacement = none ∧
        replacement.freeVariables = [] :=
  of_preparation accepted

end Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationRanges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedViewSelection
/-! The static view's candidate is selected by the actual native catalog
filter, retaining the complete binding and cumulative substitution key. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedViewSelection
open Frontend SourceInference TypeSystem SourceCoreCallableViews

open Lean Meta Elab Term in
private def actualDefinition (original : Name) : TermElabM Lean.Expr := do
  let mut found : Option Name := none
  for (name, _) in (← getEnv).constants.toList do
    if privateToUserName? name == some original then
      if found.isSome then throwError "ambiguous actual view definition: {original}"
      found := some name
  let some name := found | throwError "missing actual view definition: {original}"
  mkConstWithFreshMVarLevels name

elab "actual_view_select" : term => actualDefinition `Solcore.Frontend.SourceCoreCallableViews.selectInstance
elab "actual_view_insert" : term => actualDefinition `Solcore.Frontend.SourceCoreCallableViews.insert
elab "actual_view_collect" : term => actualDefinition `Solcore.Frontend.SourceCoreCallableViews.collect

open Lean Meta Elab Tactic in
private def unfoldActual (original : Name) (hypothesis : Name) : TacticM Unit := do
  let mut found : Option Name := none
  for (name, _) in (← getEnv).constants.toList do
    if privateToUserName? name == some original then
      if found.isSome then throwError "ambiguous actual view definition: {original}"
      found := some name
  let some name := found | throwError "missing actual view definition: {original}"
  let goal ← getMainGoal
  let declaration ← goal.withContext <| getLocalDeclFromUserName hypothesis
  replaceMainGoal [← unfoldLocalDecl goal declaration.fvarId name]

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item ∈ items, ∀ state outcome, invariant state →
      step item state = .ok outcome → ∃ updated, outcome = .yield updated ∧ invariant updated) :
    invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

structure Selection {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    (catalog : SourceCoreLocalPolymorphism.Catalog) (view : View program plan) where
  binding : SourceCoreLocalPolymorphism.Binding
  located : catalog.binding view.owner view.binding.binder.id = .ok binding
  source : binding.source = view.binding.source
  binder : binding.binder = view.binding.binder
  initializer : binding.initializer = view.binding.initializer
  candidate : SourceCoreLocalPolymorphism.Instance
  selected : view.selectedInstance = some candidate
  rows : binding.instances.filter (fun candidate => decide (candidate.origin.substitution = view.cumulative)) = [candidate]
  owner : candidate.origin.caller = view.owner
  candidateSource : candidate.origin.source = view.binding.source
  candidateBinder : candidate.origin.binder = view.binding.binder
  candidateInitializer : candidate.origin.initializer = view.binding.initializer

private theorem select_correct {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {view result : View program plan}
    (accepted : actual_view_select catalog view = .ok result)
    (generalized : result.wrapsPrincipal = true) : Nonempty (Selection catalog result) := by
  run_tac unfoldActual `Solcore.Frontend.SourceCoreCallableViews.selectInstance `accepted
  split at accepted
  · cases accepted
    simp_all
  · split at accepted
    · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at accepted
    · next binding filtered =>
      try dsimp only [bind, pure, Except.pure, Except.bind] at accepted
      split at accepted
      · simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at accepted
      · next metadata =>
        split at accepted
        · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at accepted
        · next candidate rows =>
          try dsimp only [bind, pure, Except.pure, Except.bind] at accepted
          split at accepted
          · simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at accepted
          · next origin =>
            cases accepted
            have fields : binding.source = view.binding.source ∧ binding.binder = view.binding.binder ∧
                binding.initializer = view.binding.initializer := by simpa [bne, beq_iff_eq, and_assoc] using metadata
            have candidateFields : candidate.origin.caller = view.owner ∧
                candidate.origin.source = view.binding.source ∧ candidate.origin.binder = view.binding.binder ∧
                candidate.origin.initializer = view.binding.initializer := by simpa [bne, beq_iff_eq, and_assoc] using origin
            refine ⟨⟨binding, ?_, fields.1, fields.2.1, fields.2.2, candidate, rfl, rows,
              candidateFields.1, candidateFields.2.1, candidateFields.2.2.1, candidateFields.2.2.2⟩⟩
            change catalog.binding view.owner view.binding.binder.id = .ok binding
            simp only [SourceCoreLocalPolymorphism.Catalog.binding, filtered]
        · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at accepted
    · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at accepted

private def SelectedEntries {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    (catalog : SourceCoreLocalPolymorphism.Catalog) (entries : List (Entry program plan)) : Prop :=
  ∀ entry ∈ entries, entry.view.wrapsPrincipal = true → Nonempty (Selection catalog entry.view)

private theorem insert_preserves {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {limits : Limits} {firstId : Nat}
    {entries result : List (Entry program plan)} {view : View program plan}
    (accepted : actual_view_insert limits firstId entries view = .ok result)
    (previous : SelectedEntries catalog entries)
    (selected : view.wrapsPrincipal = true → Nonempty (Selection catalog view)) :
    SelectedEntries catalog result := by
  run_tac unfoldActual `Solcore.Frontend.SourceCoreCallableViews.insert `accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · try dsimp only at accepted
      split at accepted
      · cases accepted
        intro entry member generalized
        rcases List.mem_append.mp member with old | added
        · exact previous entry old generalized
        · cases List.mem_singleton.mp added
          exact selected generalized
      · cases accepted

private theorem collect_preserves {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {limits : Limits} {firstId : Nat}
    {bindings : List SourceCoreLocalEvidence.Binding} {parent : Option Parent} {nodes : List Node}
    {entries result : List (Entry program plan)}
    (accepted : actual_view_collect limits firstId catalog bindings parent nodes entries = .ok result)
    (previous : SelectedEntries catalog entries) : SelectedEntries catalog result := by
  run_tac unfoldActual `Solcore.Frontend.SourceCoreCallableViews.collect `accepted
  obtain ⟨after, traversed, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant traversed previous
  intro node member before outcome beforeSelected step
  try dsimp only at step
  split at step
  · split at step
    · cases step
      exact ⟨before, rfl, beforeSelected⟩
    · obtain ⟨view, _, step⟩ := bind_ok step
      split at step
      · cases step
      · obtain ⟨selected, chosen, step⟩ := bind_ok step
        obtain ⟨updated, inserted, step⟩ := bind_ok step
        cases step
        exact ⟨updated, rfl, insert_preserves inserted beforeSelected (select_correct chosen)⟩
  · cases step
    exact ⟨before, rfl, beforeSelected⟩

/-- Actual root and contextual preparation retain the same native catalog
selection, including the complete source, binder, initializer and candidate. -/
theorem prepared {checked : Checked} {input : SourceCoreCompatibleFunctions.Prepared checked}
    {limits : Limits} {firstId : Nat} {table : Table input.sourceProgram input.plan}
    (accepted : prepare input limits firstId = .ok table)
    {entry : Entry input.sourceProgram input.plan} (member : entry ∈ table.entries)
    (generalized : entry.view.wrapsPrincipal = true) : Nonempty (Selection input.locals entry.view) := by
  unfold prepare at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · obtain ⟨roots, rootLoop, accepted⟩ := bind_ok accepted
      have rootSelected : SelectedEntries input.locals roots := by
        apply forIn_invariant rootLoop (by simp [SelectedEntries])
        intro caller callerMember before outcome previous step
        obtain ⟨_, _, step⟩ := bind_ok step
        obtain ⟨bindings, _, step⟩ := bind_ok step
        obtain ⟨nodes, _, step⟩ := bind_ok step
        obtain ⟨updated, collected, step⟩ := bind_ok step
        cases step
        exact ⟨updated, rfl, collect_preserves collected previous⟩
      obtain ⟨entries, contextLoop, accepted⟩ := bind_ok accepted
      have allSelected : SelectedEntries input.locals entries := by
        apply forIn_invariant contextLoop rootSelected
        intro parent parentMember before outcome previous step
        obtain ⟨_, _, step⟩ := bind_ok step
        obtain ⟨_, _, step⟩ := bind_ok step
        obtain ⟨bindings, _, step⟩ := bind_ok step
        obtain ⟨updated, collected, step⟩ := bind_ok step
        cases step
        exact ⟨updated, rfl, collect_preserves collected previous⟩
      try dsimp only at accepted
      split at accepted
      · split at accepted
        · cases accepted
          exact allSelected entry member generalized
        · split at accepted <;> cases accepted
      · cases accepted

/-- A read's selected static instance is an actual singleton member of the
binding catalog, with the cumulative substitution key checked by preparation. -/
theorem Selection.candidate_member {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {view : View program plan}
    (selection : Selection catalog view) :
    selection.candidate ∈ selection.binding.instances ∧
      selection.candidate.origin.substitution = view.cumulative := by
  have member : selection.candidate ∈ selection.binding.instances.filter
      (fun candidate => decide (candidate.origin.substitution = view.cumulative)) := by
    rw [selection.rows]
    simp
  exact ⟨(List.mem_filter.mp member).1, of_decide_eq_true (List.mem_filter.mp member).2⟩

/-- The same actual lowered-read receipt selects an entry whose complete native
binding and instance passed preparation. -/
theorem at_receipt {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : Key} {active : Substitution} {read : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : SourceCoreCallableViewLowering.Viewed ancestry.views owner active read lowered)
    (generalized : receipt.entry.view.wrapsPrincipal = true) :
    Nonempty (Selection base.locals receipt.entry.view) := by
  have member : receipt.entry ∈ ancestry.views.entries :=
    List.mem_of_find?_eq_some receipt.found
  exact prepared ancestry.graph.inputs.viewsPrepared member generalized

/-- Any actual member with the checked cumulative key is the same complete
candidate selected for this static view. -/
theorem Selection.same_candidate {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {view : View program plan}
    (selection : Selection catalog view) {candidate : SourceCoreLocalPolymorphism.Instance}
    (member : candidate ∈ selection.binding.instances)
    (key : candidate.origin.substitution = view.cumulative) : candidate = selection.candidate := by
  have present : candidate ∈ selection.binding.instances.filter
      (fun candidate => decide (candidate.origin.substitution = view.cumulative)) :=
    List.mem_filter.mpr ⟨member, by simpa using key⟩
  rw [selection.rows] at present
  exact List.mem_singleton.mp present

end Solcore.SourceSemantics.CoreLowering.CallablePreparedViewSelection
end
