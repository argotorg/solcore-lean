import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOperatorSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodCertificates

/-! Original operator typing and the actual materialized primary requirement
identify an admissible selection goal before any method body is instantiated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionGoal
open Core Frontend SourceInference
open CallablePreparedMethodRuntimeMeaning
open CallablePreparedOperatorSourceBounds
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy lowerBody fuel compilation values source scope id reasonAt lowered)
  (selected : OperatorSource receipt.operator)
  {context : SourceSemantics.Context}

include selected in
private theorem primary_admissible
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ∃ goal, PredicateAdmissible context goal ∧
      RequirementProves context receipt.operator.selection.primaryRequirement goal := by
  generalize _typeEq : receipt.node.type = annotation at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw rawEq _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.operator.found)
    subst actualNode
    have layout := CallableCallRequirementLayouts.ordinary_owned receipt.operator.ordinary
    rcases receipt.operator.form with ⟨operator, operandId, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
    · rw [form] at raw
      cases raw with
      | unary child operatorTyped =>
        cases valid with
        | ordinary _ path requirements =>
          have ownedEq := List.append_cancel_right (layout.symm.trans requirements)
          rw [receipt.metadata.coercions] at path
          generalize targetEq : receipt.node.type = target at path
          cases path
          cases operatorTyped with
          | logicalNot | wordBitNot | integerBitNot => exact False.elim (receipt.operator.nonempty ownedEq)
          | trait dispatch profile proves =>
            cases profile with
            | @intro signature method parameter member name parameters methodUnique inputs results =>
              refine ⟨{ trait := .declaration signature.id, subject := _, arguments := [] }, ⟨child.type_admissible, by simp, signature, member, rfl, ?_⟩, ?_⟩
              · simp [parameters]
              · exact RequirementSequenceProves.head (selected.requirements ▸ ownedEq.symm ▸ proves)
    · rw [form] at raw
      cases raw with
      | binary first second operatorTyped =>
        cases valid with
        | ordinary _ path requirements =>
          have ownedEq := List.append_cancel_right (layout.symm.trans requirements)
          rw [receipt.metadata.coercions] at path
          generalize targetEq : receipt.node.type = target at path
          cases path
          cases operatorTyped with
          | wordArithmetic _ | integerArithmetic _ | wordComparison _ | integerComparison _ | booleanAnd | booleanOr =>
            exact False.elim (receipt.operator.nonempty ownedEq)
          | trait dispatch profile proves =>
            cases profile with
            | @intro signature method parameter member name parameters methodUnique inputs results =>
              refine ⟨{ trait := .declaration signature.id, subject := _, arguments := [] }, ⟨first.type_admissible, by simp, signature, member, rfl, ?_⟩, ?_⟩
              · simp [parameters]
              · exact RequirementSequenceProves.head (selected.requirements ▸ ownedEq.symm ▸ proves)

/-- The real primary evidence and the typed operator share one stable ledger
identity, so the selected head goal inherits complete raw type admission. -/
theorem admissible
    (signatures : context.signatures = receipt.program.signatures)
    (ledger : context.solvedRequirements = receipt.caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ receipt.caller.assumptions → goal ∈ context.assumptions)
    (unique : NodeOccurrencesUnique source)
    (idsUnique : RequirementIdsUnique context)
    (typed : ExpressionHasType source context id receipt.node.type) :
    PredicateAdmissible context selected.certificate.selected.goal := by
  obtain ⟨goal, admitted, proves⟩ := primary_admissible receipt selected unique typed
  have produced := CallableCoercionSourceSelection.requirement_produces signatures ledger assumptions
    receipt.operator.resolved selected.certificate.roots.primarySelected selected.certificate.roots.primaryValid
  have primaryGoal : SourceCompilationPlan.runtimeEvidenceGoal selected.certificate.roots.primary =
      selected.certificate.selected.goal :=
    congrArg SourceCompilationPlan.runtimeEvidenceGoal selected.certificate.selected.primaryShape
  have same := idsUnique.proves_predicate_eq proves produced.requirement_valid
  exact same.trans primaryGoal ▸ admitted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionGoal
