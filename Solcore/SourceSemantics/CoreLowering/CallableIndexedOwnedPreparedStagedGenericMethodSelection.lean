import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionGoal
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionRanges

/-! Method selection with arbitrary actual implementation substitutions.
The retained catalog restricts method assumptions, independently of parameters. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

structure Catalog (program : CheckedProgram) : Prop where
  formed : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → Formation implementation method
  assumptions : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → ∀ trait, trait ∈ program.signatures.traits →
      implementation.methodAssumptions trait method = []

/-- Existing closed catalogs retain their original API and embed directly. -/
theorem Catalog.of_closed {program : CheckedProgram}
    (catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog program) :
    Catalog program := ⟨catalog.formed, catalog.assumptions⟩

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy lowerBody fuel compilation values source scope id reasonAt lowered)

/-- Shared static suffix after the selected raw range is derived. -/
theorem support_of_range     (checked : CallableMethodBodyCoherence.Checked receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures receipt.program.signatures)
      receipt.method.specialized.parameterSubstitution) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionSupport receipt selected := by
  let chosen := selected.certificate.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have assumptions : receipt.method.specialized.assumptions = [] := by
    have fields := CallableCoercionBodyProvenance.specialization_fields chosen.specialized
    rw [fields.2]
    change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
    rw [catalog.assumptions chosen.implementation chosen.implementationMember
      chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
    rfl
  have empty : (bodyInstance receipt.program receipt.method).context.assumptions = [] := assumptions
  have covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method := by
    obtain ⟨headers, resolved, assembled, goals⟩ :=
      CallableCoercionEvidenceOrigins.materialized_operator receipt.operator.materialized
    have dictionary : receipt.operator.dictionary = [] := List.map_eq_nil_iff.mp (goals.trans assumptions)
    have allEmpty := assembled.symm.trans dictionary
    have headersEmpty : headers = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
    rw [headersEmpty] at resolved
    have goalsEmpty : receipt.method.traitPredicates = [] := by
      have lengths := resolved.length_eq
      simpa using lengths
    intro goal member
    rw [goalsEmpty] at member
    cases member
  obtain ⟨definition, _member, _id, instantiated⟩ := chosen.instantiates checked formed.parameters range
  obtain ⟨types, lexical, facts, typing⟩ := instantiated.certificate wellFormed
  exact ⟨formed, range, covered, typing.graph_closed.wellFormed.nodeOccurrencesUnique, empty⟩

/-- Actual original parent typing, current requirement identities and compiler
selection derive the complete raw range before instantiating the Source body. -/
theorem selection_support     (checked : CallableMethodBodyCoherence.Checked receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator)
    {context : SourceSemantics.Context}
    (signatures : context.signatures = receipt.program.signatures)
    (ledger : context.solvedRequirements = receipt.caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ receipt.caller.assumptions → goal ∈ context.assumptions)
    (unique : NodeOccurrencesUnique source)
    (idsUnique : RequirementIdsUnique context)
    (typed : ExpressionHasType source context id receipt.node.type) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionSupport receipt selected := by
  have goalAdmitted := CallableIndexedOwnedPreparedStagedMethodSelectionGoal.admissible
    receipt selected signatures ledger assumptions unique idsUnique typed
  have formed := catalog.formed _ selected.certificate.selected.implementationMember
    _ selected.certificate.selected.methodMember
  have range := CallableIndexedOwnedPreparedStagedMethodSelectionRanges.of_selected
    selected.certificate.selected wellFormed formed signatures goalAdmitted
  exact support_of_range receipt checked wellFormed catalog selected range

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
