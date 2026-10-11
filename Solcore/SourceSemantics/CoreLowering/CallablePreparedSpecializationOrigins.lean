import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparationSteps

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
