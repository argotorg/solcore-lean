import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins

/-! A well-formed signature catalog gives ordinary functions and implementation
methods different source owners. Actual method-selection and specialization
receipts supply those owners; method identity is not inferred from a native
type or from an implementation's shared source owner. -/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallableOrdinaryMethodCatalogSeparation
open Frontend SourceInference

private theorem function_implementation_ids_ne {signatures : ProgramSignatures}
    (catalog : SignatureCatalogWellFormed signatures)
    {signature : ProgramFunctionSignature}
    (functionMember : signature ∈ signatures.functions)
    {implementation : ProgramImplementationSignature}
    (implementationMember : implementation ∈ signatures.implementations) :
    signature.id ≠ implementation.id := by
  have ids := catalog.declaration_ids
  simp only [signatureDeclarationIds] at ids
  have withoutContracts := (List.nodup_append.mp ids).1
  have separated := (List.nodup_append.mp withoutContracts).2.2
  have functionId : signature.id ∈
      signatures.functions.map (fun entry => entry.id) ++
        signatures.dataTypes.map (fun entry => entry.id) ++
        signatures.traits.map (fun entry => entry.id) :=
    List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨signature, functionMember, rfl⟩))
  have implementationId : implementation.id ∈
      signatures.implementations.map (fun entry => entry.id) :=
    List.mem_map.mpr ⟨implementation, implementationMember, rfl⟩
  exact separated signature.id functionId implementation.id implementationId

/-- The real checked method body uses its implementation declaration as owner. -/
theorem method_owner {program : CheckedProgram} {method : ExecutableImplMethods.CheckedMethod}
    (selection : CallableCoercionBodyProvenance.Selection program method) :
    method.specialized.function.typedBody.owner = selection.implementation.id := by
  rw [(CallableCoercionBodyProvenance.specialization_fields selection.specialized).1]
  change selection.generic.typedBody.owner = selection.implementation.id
  exact checkFunctionBody_success_typedBody_owner selection.bodyChecked

/-- A detached method cannot be the source row of a cataloged ordinary owner. -/
theorem method_owner_ne_function {program : CheckedProgram}
    (catalog : SignatureCatalogWellFormed program.signatures)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    {method : ExecutableImplMethods.CheckedMethod}
    (selection : CallableCoercionBodyProvenance.Selection program method) :
    method.specialized.function.typedBody.owner ≠ signature.id := by
  rw [method_owner selection]
  exact Ne.symm (function_implementation_ids_ne catalog member selection.implementationMember)

/-- Actual ordinary and method origins remain distinct after arbitrary local
type substitutions, which preserve their source owners. -/
theorem ordinary_method_owners_ne {program : CheckedProgram}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    {ordinary : SourceSpecialization.SpecializedFunction}
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin program ordinary)
    {method : ExecutableImplMethods.CheckedMethod}
    (selection : CallableCoercionBodyProvenance.Selection program method)
    (ordinaryLocal methodLocal : TypeSystem.Substitution) :
    (ordinary.function.typedBody.applySubstitution ordinaryLocal).owner ≠
      (method.specialized.function.typedBody.applySubstitution methodLocal).owner := by
  obtain ⟨request, signature, generic, signatureMember, _genericMember,
    _resolved, accepted⟩ := origin
  have ordinaryOwner : ordinary.function.typedBody.owner = signature.id := by
    rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1]
    change generic.typedBody.owner = signature.id
    have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
    exact identities.2.1.trans identities.1.symm
  change ordinary.function.typedBody.owner ≠ method.specialized.function.typedBody.owner
  rw [ordinaryOwner]
  exact Ne.symm (method_owner_ne_function wellFormed.signatures signatureMember selection)

/-- A genuine final catalog origin at an ordinary function owner must retain
that ordinary branch. Catalog disjointness rules out the method branch. -/
theorem ordinary_of_catalog_origin {program : CheckedProgram}
    (catalog : SignatureCatalogWellFormed program.signatures)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    {row : SourceSpecialization.SpecializedFunction}
    (origin : CallablePreparedFinalCatalogOrigins.CatalogOrigin program row)
    (owner : row.function.typedBody.owner = signature.id) :
    RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  cases origin with
  | ordinary original => exact original
  | method selected => exact False.elim (method_owner_ne_function catalog member selected owner)

/-- Successful public preparation supplies full ordinary catalog provenance
for every final row at a cataloged function owner, including rows added later
by helper requests during method scanning. -/
theorem of_preparation_at_ordinary_owner {program : CheckedProgram}
    {before after : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok after)
    (catalog : SignatureCatalogWellFormed program.signatures)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions) :
    ∀ row ∈ after.specializations, row.function.typedBody.owner = signature.id →
      RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  intro row retained owner
  exact ordinary_of_catalog_origin catalog member
    (CallablePreparedFinalCatalogOrigins.of_preparation accepted row retained) owner

/-- Default preparation retains the same complete final-row result. -/
theorem of_default_preparation_at_ordinary_owner {program : CheckedProgram}
    {before after : SourceCompilationPlan.Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidence program before = .ok after)
    (catalog : SignatureCatalogWellFormed program.signatures)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions) :
    ∀ row ∈ after.specializations, row.function.typedBody.owner = signature.id →
      RecursiveNamedPublicSpecializationMeaning.Origin program row :=
  of_preparation_at_ordinary_owner accepted catalog member

end Solcore.SourceSemantics.CoreLowering.CallableOrdinaryMethodCatalogSeparation
