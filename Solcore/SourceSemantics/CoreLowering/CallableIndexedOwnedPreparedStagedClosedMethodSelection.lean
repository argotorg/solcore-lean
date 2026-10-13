import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority

/-! A finite closed method catalog discharges method formation and dictionary
selection from actual checker provenance. Caller dictionaries may be nonempty. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedMethodSelection
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

structure Catalog (program : CheckedProgram) : Prop where
  parameters : ∀ implementation, implementation ∈ program.signatures.implementations →
    implementation.parameters = []
  formed : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → Formation implementation method
  assumptions : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → ∀ trait, trait ∈ program.signatures.traits →
      implementation.methodAssumptions trait method = []

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy lowerBody fuel compilation values source scope id reasonAt lowered)

/-- Every field follows from the selected implementation and full materializer,
including empty method dictionaries and original source occurrence uniqueness. -/
theorem selection_support     (checked : CallableMethodBodyCoherence.Checked receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionSupport receipt selected := by
  let chosen := selected.certificate.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have domain := chosen.domain
  have parameters := catalog.parameters chosen.implementation chosen.implementationMember
  have substitution : receipt.method.specialized.parameterSubstitution = [] :=
    List.map_eq_nil_iff.mp (domain.trans parameters)
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures receipt.program.signatures)
      receipt.method.specialized.parameterSubstitution := by
    intro parameter replacement member
    rw [substitution] at member
    cases member
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedMethodSelection
