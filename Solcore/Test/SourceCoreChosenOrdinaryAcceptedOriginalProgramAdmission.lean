import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterTyping
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedCatalogFacts
import Solcore.SourceSemantics.SourceInferenceProgramBridge
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationStageFacts
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality

/-! Original program admission from the same accepted fixture. The finite catalog
check compares complete Source records. The original checker, retained typing,
and actual specialization stage analysis supply the independent judgments. -/
set_option autoImplicit false
namespace Tests.SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

/-- These checks concern the original checker output, including its full Source
and ordered recursive evidence. They do not compare emitted native code. -/
structure OriginalCatalog (packet : Packet) : Prop where
  functionsChecked : (packet.program.functions == [packet.named.specialized.function]) = true
  methodsLength : packet.program.methods.length = 0

def originalCatalog (packet : Packet) : Except String (PLift (OriginalCatalog packet)) :=
  if functions : (packet.program.functions == [packet.named.specialized.function]) = true then
    if methods : packet.program.methods.length = 0 then
      .ok ⟨⟨functions, methods⟩⟩
    else .error "original checked program contains implementation methods"
  else .error "original checked function differs from the retained selected Source"

theorem OriginalCatalog.functions {packet : Packet} (given : OriginalCatalog packet) :
    packet.program.functions = [packet.named.specialized.function] :=
  LawfulBEq.eq_of_beq given.functionsChecked

theorem OriginalCatalog.methods {packet : Packet} (given : OriginalCatalog packet) :
    packet.program.methods = [] := List.length_eq_zero_iff.mp given.methodsLength

theorem OriginalCatalog.compiled_functions {packet : Packet} (given : OriginalCatalog packet) :
    packet.compiled.sourceProgram.functions = [packet.named.specialized.function] := by
  rw [(SourceCoreUnifiedPreparationCertificates.prepare_fields packet.compiledAccepted).1]
  exact given.functions

theorem OriginalCatalog.compiled_methods {packet : Packet} (given : OriginalCatalog packet) :
    packet.compiled.sourceProgram.methods = [] := by
  rw [(SourceCoreUnifiedPreparationCertificates.prepare_fields packet.compiledAccepted).1]
  exact given.methods

/-- Original worklist provenance supplies the actual original signature and
specialization equation for this same complete checked function. -/
theorem OriginalCatalog.specialization {packet : Packet} (given : OriginalCatalog packet)
    (selected : OriginalSelection packet) :
    ∃ signature : ProgramFunctionSignature, ∃ supplied : TypeSystem.ParameterSubstitution,
      signature ∈ packet.compiled.sourceProgram.signatures.functions ∧
      SourceSpecialization.specializeFunction signature packet.named.specialized.function supplied =
        .ok packet.named.specialized := by
  obtain ⟨request, signature, generic, member, genericMember, _, accepted⟩ := selected.origin packet
  rw [given.compiled_functions] at genericMember
  have same := List.mem_singleton.mp genericMember
  subst generic
  exact ⟨signature, request.parameterSubstitution, member, accepted⟩

/-- The actual empty specialization and assumptions identify the original rigid
scope; source input binders are a separate field. -/
theorem signature_fields {packet : Packet} (given : Metadata packet)
    {signature : ProgramFunctionSignature} {supplied : TypeSystem.ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature packet.named.specialized.function supplied =
      .ok packet.named.specialized) :
    signature.scheme.parameters = [] ∧ signature.scheme.predicates = [] := by
  have parameters := SourceSpecialization.specializeFunction_parameterDomain accepted
  rw [given.substitution, List.map_nil] at parameters
  have predicates := (CallableCoercionBodyProvenance.specialization_fields accepted).2
  rw [given.assumptions] at predicates
  exact ⟨parameters.symm, List.map_eq_nil_iff.mp predicates.symm⟩

theorem original_context {packet : Packet} (given : Metadata packet)
    {signature : ProgramFunctionSignature} {supplied : TypeSystem.ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature packet.named.specialized.function supplied =
      .ok packet.named.specialized) :
    checkedBodyContext packet.compiled.sourceProgram.signatures signature packet.named.specialized.function =
      runtimeContext packet := by
  obtain ⟨parameters, predicates⟩ := signature_fields given accepted
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have owner : signature.id = (CallableIndexedNamedGeneration.source packet.named).owner :=
    identities.1.trans identities.2.1.symm
  simp only [checkedBodyContext, runtimeContext, parameters, predicates, owner]

/-- All original bodies are typed using the retained finite body proof, at the
original checker's fuel. No global recursive inference theorem is assumed. -/
theorem statements_typed {fixture : AcceptedFixture} (catalog : OriginalCatalog fixture.packet)
    (selected : OriginalSelection fixture.packet) (given : Metadata fixture.packet)
    (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    CheckedProgramBodiesHaveStatementTyping fixture.packet.program 1024 := by
  obtain ⟨signature, supplied, signatureMember, accepted⟩ := catalog.specialization selected
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
  have originalMember : signature ∈ fixture.packet.program.signatures.functions := by
    rwa [programEq] at signatureMember
  have functionMember : fixture.packet.named.specialized.function ∈ fixture.packet.program.functions := by
    rw [catalog.functions]
    exact List.mem_singleton_self _
  obtain ⟨headerSignature, headerMember, header⟩ :=
    checkedFunctionHeaderWellFormed_ofCheckProgram fixture.packet.checked functionMember
  have unique := (SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked).function_ids
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have headerEq : headerSignature = signature := eq_of_mem_of_nodup_map unique
    headerMember originalMember (header.declaration_eq.symm.trans identities.1.symm)
  subst headerSignature
  have inputs : fixture.packet.named.specialized.function.typedBody.inputs = [] := given.inputs
  obtain ⟨_, extension⟩ := header.inputs_extend
  have length := extension.length_eq
  rw [inputs, List.length_nil] at length
  have parameterTypes : signature.parameterTypes = [] := List.length_eq_zero_iff.mp length.symm
  have resultType : TypeSystem.Ty.productMany signature.returnTypes = wordType :=
    header.result_type.symm.trans outer.resultType
  have contextEq : checkedBodyContext fixture.packet.program.signatures signature
      fixture.packet.named.specialized.function = runtimeContext fixture.packet := by
    rw [← programEq]
    exact original_context given accepted
  constructor
  · intro function member candidate candidateMember bodyAccepted
    rw [catalog.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    have candidateEq : candidate = signature := eq_of_mem_of_nodup_map unique
      candidateMember originalMember
      ((checkFunctionBody_success_declaration bodyAccepted).symm.trans identities.1.symm)
    subst candidate
    intro statements roots
    have mapped : statements.map NodeId.statement =
        [statementId fixture.packet 0, statementId fixture.packet 4].map NodeId.statement :=
      roots.symm.trans fixture.graph.roots
    have statementsEq : statements = [statementId fixture.packet 0, statementId fixture.packet 4] :=
      (List.map_inj_right (by intro a b same; cases same; rfl)).mp mapped
    subst statements
    refine ⟨SourceCoreChosenOrdinaryAcceptedOuterTyping.bodyFacts, resultType.symm, ?_⟩
    intro lexicalContext extended
    rw [inputs, parameterTypes] at extended
    cases extended
    refine ⟨SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture, ?_⟩
    rw [contextEq, resultType]
    exact SourceCoreChosenOrdinaryAcceptedOuterTyping.body_typed lambda outer
  · intro method member
    rw [catalog.methods] at member
    cases member

theorem program_well_formed {fixture : AcceptedFixture} (catalog : OriginalCatalog fixture.packet)
    (selected : OriginalSelection fixture.packet) (given : Metadata fixture.packet)
    (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    ProgramWellFormed (Program.ofChecked fixture.packet.compiled.sourceProgram) := by
  rw [(SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1]
  exact programWellFormed_ofCheckProgram_statements fixture.packet.checked
    (statements_typed catalog selected given lambda outer)

/-- The retained successful stage analysis classifies the same original sole
function. Empty method membership closes the remaining original catalog. -/
theorem program_has_stages {fixture : AcceptedFixture} (catalog : OriginalCatalog fixture.packet)
    (selected : OriginalSelection fixture.packet) (given : Metadata fixture.packet)
    (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    Staging.ProgramHasStages (Program.ofChecked fixture.packet.compiled.sourceProgram) := by
  refine ⟨program_well_formed catalog selected given lambda outer, ?_, ?_⟩
  · intro definition member
    obtain ⟨function, functionMember, rfl⟩ := List.mem_map.mp member
    rw [catalog.compiled_functions] at functionMember
    have same := List.mem_singleton.mp functionMember
    subst function
    obtain ⟨_, _, _, accepted⟩ := catalog.specialization selected
    have originalMember : fixture.packet.named.specialized.function ∈ fixture.packet.program.functions := by
      rw [catalog.functions]
      exact List.mem_singleton_self _
    obtain ⟨_, _, bodyAccepted⟩ := checkProgram_success_function_body fixture.packet.checked originalMember
    change Staging.BodyDefinitionHasStages (BodyDefinition.ofChecked fixture.packet.named.specialized.function)
    exact (Staging.bodyDefinitionOfChecked_iff _).2
      (SourceStageAnalysisSoundness.checkFunctionBody_analysis_success_hasStages bodyAccepted
        (RecursiveNamedSpecializationStageFacts.analyzed accepted))
  · intro definition member
    change definition ∈ fixture.packet.compiled.sourceProgram.methods.map MethodDefinition.ofChecked at member
    rw [catalog.compiled_methods] at member
    cases member

end Tests.SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission
