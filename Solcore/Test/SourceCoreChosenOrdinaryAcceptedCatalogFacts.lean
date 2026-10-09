import Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeader
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts

/-! The actual accepted Header supplies a singleton catalog. Original matcher
and checker interface receipts determine its raw Source signature fields;
deep body typing, native typing and runtime meaning are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedCatalogFacts
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable {fixture : AcceptedFixture} {header : ActualHeader fixture}

/-- This list retains the Header's genuine selected and cached compiler slot. -/
def headers (header : ActualHeader fixture) :
    RecursiveNamedCatalog.Inventory fixture.packet.compiled.indexed.ancestry
      (.initial fixture.packet.compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed).definitions
      (Program.ofChecked fixture.packet.compiled.sourceProgram) := [header]

theorem header_member : header ∈ headers header := List.mem_singleton_self _

/-- The same accepted hook and target identify the complete original row. -/
theorem header_matches (atHeader : HeaderAt fixture header) :
    CallableNamedMetadata.Matches fixture.packet.named.specialized header.instantiation := by
  have matched := CallableNamedMetadata.matches_of_exact header.target
    (CallableIndexedActualNamedSourceReceipts.header_record fixture.packet.compiled header)
  simpa only [atHeader.named] using matched

/-- The matcher retains length equality even when it permits permutations. -/
theorem substitution_empty (checked : Metadata fixture.packet)
    (atHeader : HeaderAt fixture header) : header.instantiation.parameterSubstitution = [] := by
  have equivalent := (header_matches atHeader).substitution
  rw [checked.substitution] at equivalent
  simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent,
    List.length_nil, List.all_nil, Bool.and_eq_true, beq_iff_eq] at equivalent
  exact List.length_eq_zero_iff.mp equivalent.1.1.symm

theorem header_order (checked : Metadata fixture.packet) (atHeader : HeaderAt fixture header) :
    header.instantiation.parameterSubstitution.map Prod.fst =
      (header.named.specialized.parameterSubstitution.map Prod.fst).reverse := by
  rw [substitution_empty checked atHeader, atHeader.named, checked.substitution]
  rfl

theorem headers_order (checked : Metadata fixture.packet) (atHeader : HeaderAt fixture header) :
    ∀ candidate, candidate ∈ headers header →
      candidate.instantiation.parameterSubstitution.map Prod.fst =
        (candidate.named.specialized.parameterSubstitution.map Prod.fst).reverse := by
  intro candidate member
  have same : candidate = header := List.mem_singleton.mp member
  subst candidate
  exact header_order checked atHeader

/-- These facts concern the actual generic catalog signature and its retained
specialized inferred result. They contain no body typing or execution input. -/
structure SignatureFacts (fixture : AcceptedFixture) (signature : ProgramFunctionSignature) : Prop where
  member : signature ∈ fixture.packet.compiled.sourceProgram.signatures.functions
  declaration : signature.id = fixture.packet.named.specialized.declaration
  parameters : signature.parameterTypes = []
  result : fixture.packet.named.specialized.parameterSubstitution.apply
      (TypeSystem.Ty.productMany signature.returnTypes) =
    fixture.packet.named.specialized.function.inferredBodyType

/-- Original worklist provenance and executable checker header facts supply
raw parameters and result without whole-program body well-formedness. -/
theorem signature_facts (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet) : ∃ signature, SignatureFacts fixture signature := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, accepted⟩ :=
    selected.origin fixture.packet
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
  have catalog := SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked
  rw [← programEq] at catalog
  have genericMember' := genericMember
  rw [programEq] at genericMember'
  obtain ⟨declared, declaredMember, interface⟩ :=
    checkedFunctionHeaderWellFormed_ofCheckProgram fixture.packet.checked genericMember'
  rw [← programEq] at declaredMember interface
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have declaredEq : declared = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
    catalog.function_ids declaredMember signatureMember
    (interface.declaration_eq.symm.trans identities.1.symm)
  subst declared
  have fields := (CallableCoercionBodyProvenance.specialization_fields accepted).1
  have inputs : fixture.packet.named.specialized.function.typedBody.inputs = [] := checked.inputs
  rw [fields] at inputs
  change generic.typedBody.inputs.map
    (SourceSpecialization.applyBinder fixture.packet.named.specialized.parameterSubstitution) = [] at inputs
  have genericInputs := List.map_eq_nil_iff.mp inputs
  obtain ⟨lexical, extension⟩ := interface.inputs_extend
  have length := extension.length_eq
  rw [genericInputs, List.length_nil] at length
  have parameterTypes : signature.parameterTypes = [] := List.length_eq_zero_iff.mp length.symm
  refine ⟨signature, ⟨signatureMember, identities.1.trans identities.2.2.symm, parameterTypes, ?_⟩⟩
  rw [fields]
  change fixture.packet.named.specialized.parameterSubstitution.apply
    (TypeSystem.Ty.productMany signature.returnTypes) =
    fixture.packet.named.specialized.parameterSubstitution.apply generic.inferredBodyType
  rw [interface.result_type]

/-- Actual signature identity is unique in the catalog checked by checkProgram. -/
theorem signature_at (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (atHeader : HeaderAt fixture header) {signature : ProgramFunctionSignature}
    (member : signature ∈ fixture.packet.compiled.sourceProgram.signatures.functions)
    (declaration : header.instantiation.declaration = signature.id) :
    SignatureFacts fixture signature := by
  obtain ⟨actual, facts⟩ := signature_facts selected checked
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
  have catalog := SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked
  rw [← programEq] at catalog
  have namedDeclaration := (header_matches atHeader).declaration
  have same : actual = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
    catalog.function_ids facts.member member (facts.declaration.trans (namedDeclaration.trans declaration))
  exact same ▸ facts

theorem header_bindings_empty (checked : Metadata fixture.packet) (atHeader : HeaderAt fixture header) :
    header.bindings = [] := atHeader.bindings.trans checked.named_inputs

/-- The actual Header keeps the named compiler context's complete ledger. -/
theorem named_ledger (atHeader : HeaderAt fixture header) :
    (CallableIndexedNamedGeneration.context fixture.packet.compiled.indexed fixture.packet.named).solvedRequirements = header.solved :=
  atHeader.ledger.symm

/-- The receiving context may retain lexical and residual variables. Its
genuine signature catalog equality is the only contextual premise here. -/
theorem source_types_at (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (atHeader : HeaderAt fixture header) (currentContext : SourceSemantics.Context)
    (signatures : currentContext.signatures = fixture.packet.compiled.sourceProgram.signatures) :
    RecursiveNamedCallEvidenceHeads.SourceTypes (headers header) currentContext := by
  refine ⟨?_, ?_, ?_⟩
  · intro candidate member signature signatureMember declaration
    have same : candidate = header := List.mem_singleton.mp member
    subst candidate
    have facts := signature_at selected checked atHeader (signatures ▸ signatureMember) declaration
    rw [facts.parameters, header_bindings_empty checked atHeader]
    rfl
  · intro candidate member signature signatureMember declaration
    have same : candidate = header := List.mem_singleton.mp member
    subst candidate
    have facts := signature_at selected checked atHeader (signatures ▸ signatureMember) declaration
    have actualInstantiation := (header_matches atHeader).canonical
      (by rw [checked.substitution, substitution_empty checked atHeader])
    rw [actualInstantiation]
    change fixture.packet.named.specialized.parameterSubstitution.apply
      (TypeSystem.Ty.productMany signature.returnTypes) = header.function.resultType
    exact facts.result.trans (by simpa only [atHeader.named] using header.agreement.result.symm)
  · intro candidate member
    have same : candidate = header := List.mem_singleton.mp member
    subst candidate
    rw [header_bindings_empty checked atHeader]
    rfl

theorem source_types_at_runtime (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (atHeader : HeaderAt fixture header) :
    RecursiveNamedCallEvidenceHeads.SourceTypes (headers header) (runtimeContext fixture.packet) :=
  source_types_at selected checked atHeader _ rfl

end Tests.SourceCoreChosenOrdinaryAcceptedCatalogFacts
