import Solcore.SourceSemantics.CoreLowering.CallableClosedSchemeSubstitutionAgreement
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedConcreteRangeReceipts
import Solcore.SourceSemantics.Dynamic.Preservation

/-! Original local-reference typing and the actual complete compiler matcher
produce a ground Dynamic instantiation. The current caller dictionary closes
the original ordered requirements, including those erased from native code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalRuntimeInstantiation
open Frontend SourceInference TypeSystem

private theorem empty_orElse {α : Type} (left right : Option α)
    (empty : left.orElse (fun _ => right) = none) : left = none ∧ right = none := by
  cases left with
  | none => exact ⟨rfl, empty⟩
  | some value => cases empty

private theorem concrete_variable (substitution : Substitution) (type : Ty)
    (concrete : SourceSpecialization.firstNonConcrete (substitution.apply type) = none) :
    ∀ metavariable ∈ type.freeVariables,
      SourceSpecialization.firstNonConcrete (substitution.apply (.variable metavariable)) = none := by
  induction type with
  | «variable» candidate =>
    intro metavariable member
    have same : metavariable = candidate := by simpa [Ty.freeVariables] using member
    subst metavariable
    exact concrete
  | parameter | constructor | error => intro metavariable member; simp [Ty.freeVariables] at member
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
    have parts := empty_orElse (SourceSpecialization.firstNonConcrete (substitution.apply left))
      (SourceSpecialization.firstNonConcrete (substitution.apply right)) concrete
    intro metavariable member
    simp at member
    rcases member with member | member
    · exact ihLeft parts.1 metavariable member
    · exact ihRight parts.2 metavariable member
  | proxy inner ih | comptime inner ih => exact ih concrete

/-- Closed matching forces every genuine exact semantic replacement to be
concrete, while original admissibility supplies nominal membership and arity. -/
theorem range_of_match {context : Context} {scheme : Scheme} {actual : Ty}
    {compiled semantic : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual = some compiled)
    (exact : ExactSubstitution semantic scheme.quantified)
    (range : SubstitutionRangeAdmissible context semantic)
    (result : semantic.apply scheme.body = actual) :
    SubstitutionRangeWellFormed context semantic := by
  intro metavariable replacement member
  have lookup := StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup exact.domain_nodup member
  have domain : metavariable ∈ semantic.domain := List.mem_map.mpr ⟨_, member, rfl⟩
  have occurs := CallableClosedSchemeSubstitutionAgreement.quantified_occurs_of_closed_match matched metavariable
    ((exact.mem_domain_iff metavariable).mp domain)
  have concrete := concrete_variable semantic scheme.body
    (result ▸ (SourceSpecialization.matchClosedSchemeInstance?_sound matched).1) metavariable occurs
  simp only [Substitution.apply, lookup, Option.getD_some] at concrete
  have admitted := range metavariable replacement member
  have typed := CallableIndexedOwnedReachedNamedConcreteRangeReceipts.admissible_concrete_at_catalog admitted concrete
  apply Dynamic.TypeWellFormed.transportContext (source := Context.ofSignatures context.signatures) (target := context) ?_ typed
  exact { signatures := rfl
          parameters := by intro parameter impossible; cases impossible
          parameterOwners := by intro parameter impossible; cases impossible
          variables := by intro metavariable impossible; cases impossible
          residualVariables := by intro impossible; cases impossible
          targetBinders := admitted.binders }

theorem of_valid {context : Context} {binder : TypedBinder} {actual : Ty}
    {requirements : List RequirementId} {compiled : Substitution}
    {evidence : Dynamic.EvidenceEnvironment}
    (matched : SourceSpecialization.matchClosedSchemeInstance? binder.scheme actual = some compiled)
    (valid : LocalSchemeInstantiationValid context binder actual requirements)
    (covers : evidence.Covers context) :
    ∃ substitution produced, Dynamic.LocalSchemeRuntimeInstantiation context evidence binder actual
      requirements substitution produced := by
  cases valid with
  | intro formation wellFormed substitution exact range result unique disjoint requirements =>
    obtain ⟨produced, produces⟩ := Dynamic.RequirementSequenceProves.produces_of_covers covers requirements
    exact ⟨substitution, produced, formation, wellFormed, exact,
      range_of_match matched exact range result, result, unique, disjoint, produces⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalRuntimeInstantiation
