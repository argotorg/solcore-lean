import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.Program

/-!
Conditional bridge from executable whole-program checking results to the
declarative source-program carrier.

The conversions in this module only forget algorithmic bookkeeping.  Checker
success supplies the catalog facts established by executable collection:
declaration identities, canonical generic parameters, rule projection, and
contract-signature semantics.  Separate remaining-condition carriers state
the signature and body judgments that still need declarative proofs; the final
bridges combine both sources without treating the executable frontend as the
definition of semantic validity.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

namespace FunctionDefinition

/-- Forget algorithmic bookkeeping from one checked top-level function. -/
def ofChecked (function : CheckedFunction) : FunctionDefinition := {
  body := BodyDefinition.ofChecked function
}

end FunctionDefinition

namespace MethodDefinition

/-- Forget algorithmic bookkeeping from one checked implementation method
while retaining the stable method identity absent from `CheckedFunction`. -/
def ofChecked (method : CheckedImplementationMethod) : MethodDefinition := {
  id := method.id
  body := BodyDefinition.ofChecked method.checked
}

end MethodDefinition

namespace Program

/-- Project a frontend checked-program carrier into the declarative source
program carrier.  Validity remains a separate proposition. -/
def ofChecked (checked : CheckedProgram) : Program := {
  signatures := checked.signatures
  functions := checked.functions.map FunctionDefinition.ofChecked
  methods := checked.methods.map MethodDefinition.ofChecked
}

end Program

/-- Raw-workspace checker success discharges the cross-category declaration
identity component of semantic signature-catalog well-formedness. -/
theorem signatureDeclarationIds_nodup_ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked) :
    (signatureDeclarationIds checked.signatures).Nodup := by
  simpa [signatureDeclarationIds] using
    Frontend.checkProgram_success_signature_declaration_ids_nodup success

/-- Semantic function-signature obligations not yet discharged by executable
signature collection.  Declaration-owned generic-parameter invariants,
parameter-name uniqueness, and the canonical scheme body are intentionally
absent: successful checking supplies them separately. -/
structure FunctionSignatureRemainingConditions
    (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) : Prop where
  parameter_types : TypesWellFormed
    (signatureContext signatures signature.id signature.scheme.parameters
      signature.scheme.predicates) signature.parameterTypes
  return_types : TypesWellFormed
    (signatureContext signatures signature.id signature.scheme.parameters
      signature.scheme.predicates) signature.returnTypes
  predicates : PredicatesWellFormed
    (signatureContext signatures signature.id signature.scheme.parameters
      signature.scheme.predicates) signature.scheme.predicates

/-- The constructor-payload typing obligation not yet discharged by executable
data-signature collection.  Generic parameters, constructor names, owners, and
source-order positions are supplied separately by checker success. -/
structure DataSignatureRemainingConditions
    (signatures : ProgramSignatures)
    (signature : ProgramDataSignature) : Prop where
  constructor_payloads : ∀ constructor,
    constructor ∈ signature.constructors →
      TypesWellFormed
        (signatureContext signatures signature.id signature.parameters)
        constructor.payloadTypes

/-- Type- and predicate-formation obligations for one trait method.  Method
ownership and duplicate-free parameter names are fixed by executable trait
method collection and therefore supplied separately by checker success. -/
structure TraitMethodSignatureRemainingConditions
    (signatures : ProgramSignatures)
    (trait : ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) : Prop where
  parameter_types : TypesWellFormed
    (signatureContext signatures trait.id trait.parameters
      (trait.wherePredicates ++ method.wherePredicates)) method.parameterTypes
  return_types : TypesWellFormed
    (signatureContext signatures trait.id trait.parameters
      (trait.wherePredicates ++ method.wherePredicates)) method.returnTypes
  predicates : PredicatesWellFormed
    (signatureContext signatures trait.id trait.parameters
      (trait.wherePredicates ++ method.wherePredicates)) method.wherePredicates

/-- Semantic trait-signature obligations beyond its checker-generated generic
parameter row and structural method catalog. -/
structure TraitSignatureRemainingConditions
    (signatures : ProgramSignatures)
    (signature : ProgramTraitSignature) : Prop where
  predicates : PredicatesWellFormed
    (signatureContext signatures signature.id signature.parameters
      signature.wherePredicates) signature.wherePredicates
  methods : ∀ method, method ∈ signature.methods →
    TraitMethodSignatureRemainingConditions signatures signature method

/-- Trait correspondence and type-formation obligations for one implementation
method.  Its owner and duplicate-free parameter names are fixed by executable
implementation-method collection. -/
structure ImplMethodSignatureRemainingConditions
    (signatures : ProgramSignatures)
    (implementation : ProgramImplementationSignature)
    (method : ProgramImplMethodSignature) : Prop where
  trait_method : ∃ trait methodSignature,
    trait ∈ signatures.traits ∧
    implementation.head.trait = .declaration trait.id ∧
    methodSignature ∈ trait.methods ∧
    methodSignature.id = method.traitMethod ∧
    methodSignature.name = method.name ∧
    let substitution : TypeSystem.ParameterSubstitution :=
      trait.parameters.zip
        (implementation.head.subject :: implementation.head.arguments)
    method.parameterTypes =
      methodSignature.parameterTypes.map substitution.apply ∧
    method.returnTypes =
      methodSignature.returnTypes.map substitution.apply ∧
    method.parameterComptime = methodSignature.parameterComptime ∧
    method.returnComptime = methodSignature.returnComptime ∧
    method.wherePredicates = methodSignature.wherePredicates.map
      (ProgramPredicate.applyParameters substitution)
  parameter_types : TypesWellFormed
    (signatureContext signatures implementation.id implementation.parameters
      (implementation.wherePredicates ++ method.wherePredicates))
    method.parameterTypes
  return_types : TypesWellFormed
    (signatureContext signatures implementation.id implementation.parameters
      (implementation.wherePredicates ++ method.wherePredicates))
    method.returnTypes
  predicates : PredicatesWellFormed
    (signatureContext signatures implementation.id implementation.parameters
      (implementation.wherePredicates ++ method.wherePredicates))
    method.wherePredicates

/-- Semantic implementation-signature obligations beyond its checker-generated
generic parameter row, validated head catalog, and structural method catalog. -/
structure ImplementationSignatureRemainingConditions
    (signatures : ProgramSignatures)
    (signature : ProgramImplementationSignature) : Prop where
  head : PredicateWellFormed
    (signatureContext signatures signature.id signature.parameters
      signature.wherePredicates) signature.head
  predicates : PredicatesWellFormed
    (signatureContext signatures signature.id signature.parameters
      signature.wherePredicates) signature.wherePredicates
  methods : ∀ method, method ∈ signature.methods →
    ImplMethodSignatureRemainingConditions signatures signature method
  methods_complete : ∀ trait method,
    trait ∈ signatures.traits →
    signature.head.trait = .declaration trait.id →
    method ∈ trait.methods →
    ∃ implementationMethod ∈ signature.methods,
      implementationMethod.traitMethod = method.id

/-- Catalog conditions not yet implied by raw `checkProgram` success.  The
checker already supplies implementation-rule projection equality, declaration
identity uniqueness, every generic-parameter invariant, data-constructor
structure and identity uniqueness, trait-method structure and identity
uniqueness, implementation-head parameter/catalog validation,
implementation-method structure and identity uniqueness, and complete
contract signature semantics. -/
structure SignatureCatalogRemainingConditions
    (signatures : ProgramSignatures) : Prop where
  functions_semantic : ∀ signature, signature ∈ signatures.functions →
    FunctionSignatureRemainingConditions signatures signature
  data_semantic : ∀ signature, signature ∈ signatures.dataTypes →
    DataSignatureRemainingConditions signatures signature
  traits_semantic : ∀ signature, signature ∈ signatures.traits →
    TraitSignatureRemainingConditions signatures signature
  implementations_semantic :
    ∀ signature, signature ∈ signatures.implementations →
      ImplementationSignatureRemainingConditions signatures signature

/-- Facts supplied solely by a successful raw-workspace checker run. -/
structure CheckedSignatureCatalogFacts
    (signatures : ProgramSignatures) : Prop where
  impl_rules_eq : signatures.implRules =
    signatures.implementations.map ProgramImplementationSignature.implRule
  declaration_ids : (signatureDeclarationIds signatures).Nodup
  function_ids : (signatures.functions.map fun signature => signature.id).Nodup
  data_ids : (signatures.dataTypes.map fun signature => signature.id).Nodup
  trait_ids : (signatures.traits.map fun signature => signature.id).Nodup
  implementation_ids :
    (signatures.implementations.map fun signature => signature.id).Nodup
  contract_ids : (signatures.contracts.map fun signature => signature.id).Nodup
  constructor_ids :
    (signatures.dataTypes.flatMap fun signature =>
      signature.constructors.map fun constructor => constructor.id).Nodup
  trait_method_ids :
    (signatures.traits.flatMap fun signature =>
      signature.methods.map fun method => method.id).Nodup
  implementation_method_ids :
    (signatures.implementations.flatMap fun signature =>
      signature.methods.map fun method => method.id).Nodup
  parameters : ProgramSignatureParametersWellFormed signatures
  function_shapes : ∀ signature, signature ∈ signatures.functions →
    signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes)
  data_structures : ∀ signature, signature ∈ signatures.dataTypes →
    DataSignatureStructuralWellFormed signature
  trait_structures : ∀ signature, signature ∈ signatures.traits →
    TraitSignatureStructuralWellFormed signature
  implementation_structures : ∀ signature,
    signature ∈ signatures.implementations →
      ImplementationSignatureStructuralWellFormed signature
  implementation_heads : ∀ signature,
    signature ∈ signatures.implementations →
      Frontend.ImplementationSignatureHeadValidated signatures.traits signature
  contracts_semantic : ∀ signature, signature ∈ signatures.contracts →
    ContractSignatureWellFormed signatures signature

namespace FunctionSignatureRemainingConditions

/-- Combine the executable collector's parameter witness with the genuinely
remaining function-signature semantics. -/
theorem complete
    {signatures : ProgramSignatures} {signature : ProgramFunctionSignature}
    (remaining : FunctionSignatureRemainingConditions signatures signature)
    (parameters : SignatureParametersWellFormed signature.id
      signature.scheme.parameters)
    (shape : signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes)) :
    FunctionSignatureWellFormed signatures signature := {
  parameters_nodup := parameters.parameters_nodup
  parameters_owned := parameters.parameter_owners
  parameter_positions := by
    simpa [TypeParameterPositionsCanonical] using parameters.parameter_positions
  parameter_names_nodup := shape.1
  parameter_types := remaining.parameter_types
  return_types := remaining.return_types
  predicates := remaining.predicates
  scheme_body := shape.2
}

end FunctionSignatureRemainingConditions

namespace DataSignatureRemainingConditions

/-- Combine canonical declaration parameters with the remaining data
constructor semantics. -/
theorem complete
    {signatures : ProgramSignatures} {signature : ProgramDataSignature}
    (remaining : DataSignatureRemainingConditions signatures signature)
    (parameters : SignatureParametersWellFormed signature.id
      signature.parameters)
    (structural : DataSignatureStructuralWellFormed signature) :
    DataSignatureWellFormed signatures signature := {
  parameters_nodup := parameters.parameters_nodup
  parameters_owned := parameters.parameter_owners
  parameter_positions := by
    simpa [TypeParameterPositionsCanonical] using parameters.parameter_positions
  constructor_names_nodup := structural.constructor_names_nodup
  constructor_owners := structural.constructor_owners
  constructor_positions := structural.constructor_positions
  constructor_payloads := remaining.constructor_payloads
}

end DataSignatureRemainingConditions

namespace TraitSignatureRemainingConditions

/-- Combine canonical declaration parameters with the remaining trait method
catalog semantics. -/
theorem complete
    {signatures : ProgramSignatures} {signature : ProgramTraitSignature}
    (remaining : TraitSignatureRemainingConditions signatures signature)
    (parameters : SignatureParametersWellFormed signature.id
      signature.parameters)
    (structural : TraitSignatureStructuralWellFormed signature) :
    TraitSignatureWellFormed signatures signature := {
  parameters_nodup := parameters.parameters_nodup
  parameters_owned := parameters.parameter_owners
  parameter_positions := by
    simpa [TypeParameterPositionsCanonical] using parameters.parameter_positions
  method_names_nodup := structural.method_names_nodup
  method_positions := structural.method_positions
  predicates := remaining.predicates
  methods := by
    intro method member
    have methodRemaining := remaining.methods method member
    exact {
      owner := structural.method_owners method member
      parameter_names_nodup :=
        structural.method_parameter_names_nodup method member
      parameter_types := methodRemaining.parameter_types
      return_types := methodRemaining.return_types
      predicates := methodRemaining.predicates
    }
}

end TraitSignatureRemainingConditions

namespace ImplMethodSignatureRemainingConditions

/-- Combine checker-fixed method identity structure with the remaining trait
correspondence and type-formation obligations. -/
theorem complete
    {signatures : ProgramSignatures}
    {implementation : ProgramImplementationSignature}
    {method : ProgramImplMethodSignature}
    (remaining : ImplMethodSignatureRemainingConditions signatures
      implementation method)
    (owner : method.id.implementation = implementation.id)
    (parameterNames : method.parameterNames.Nodup) :
    ImplMethodSignatureWellFormed signatures implementation method := {
  owner
  trait_method := remaining.trait_method
  parameter_names_nodup := parameterNames
  parameter_types := remaining.parameter_types
  return_types := remaining.return_types
  predicates := remaining.predicates
}

end ImplMethodSignatureRemainingConditions

namespace ImplementationSignatureHeadValidated

/-- The collector's syntactic parameter-occurrence witness is exactly the
semantic non-phantom-parameter condition. -/
theorem semantic_parameters_in_head
    {signatures : ProgramSignatures}
    {signature : ProgramImplementationSignature}
    (validated : Frontend.ImplementationSignatureHeadValidated
      signatures.traits signature) :
    ∀ parameter, parameter ∈ signature.parameters →
      TypeParameterOccursInPredicate parameter signature.head := by
  intro parameter member
  have occurs := TypedTraitResolution.mem_predicateParameters_iff.mp
    (validated.parameters_in_head parameter member)
  simpa [TypeParameterOccursInPredicate,
    TypedTraitResolution.ParameterOccursInPredicate] using occurs

/-- The selected trait witness, semantic head formation, and the checker's
global trait invariants jointly supply the exact, well-formed substitution
required by the declarative implementation judgment. -/
theorem semantic_trait_catalog
    {signatures : ProgramSignatures}
    {signature : ProgramImplementationSignature}
    (validated : Frontend.ImplementationSignatureHeadValidated
      signatures.traits signature)
    (head : PredicateWellFormed
      (signatureContext signatures signature.id signature.parameters
        signature.wherePredicates) signature.head)
    (traitIds :
      (signatures.traits.map fun trait => trait.id).Nodup)
    (traitParameters : ∀ trait, trait ∈ signatures.traits →
      SignatureParametersWellFormed trait.id trait.parameters) :
    ∃ trait ∈ signatures.traits,
      signature.head.trait = .declaration trait.id ∧
      let substitution : TypeSystem.ParameterSubstitution :=
        trait.parameters.zip
          (signature.head.subject :: signature.head.arguments)
      ParameterSubstitution.Exact substitution trait.parameters ∧
        ParameterSubstitution.RangeWellFormed
          (signatureContext signatures signature.id signature.parameters
            signature.wherePredicates) substitution ∧
        ∀ predicate, predicate ∈ trait.wherePredicates.map
          (ProgramPredicate.applyParameters substitution) →
          predicate ∈ signature.wherePredicates := by
  rcases validated.trait_catalog with
    ⟨trait, traitMember, headTraitEq, requiredPredicates⟩
  refine ⟨trait, traitMember, headTraitEq, ?_⟩
  have headCatalog := head.trait
  rw [headTraitEq] at headCatalog
  rcases headCatalog with
    ⟨headTrait, headTraitMember, headTraitId, headArity⟩
  have headTraitEqSelected : headTrait = trait :=
    Frontend.trait_signature_eq_of_mem_of_id_eq traitIds
      headTraitMember traitMember headTraitId
  subst headTrait
  let substitution : TypeSystem.ParameterSubstitution :=
    trait.parameters.zip
      (signature.head.subject :: signature.head.arguments)
  have exact : ParameterSubstitution.Exact substitution trait.parameters := by
    refine {
      parameters_nodup :=
        (traitParameters trait traitMember).parameters_nodup
      domain_permutation := ?_
    }
    simp only [substitution, ParameterSubstitution.domain]
    have lengthLe : trait.parameters.length ≤
        (signature.head.subject :: signature.head.arguments).length := by
      simp only [List.length_cons]
      omega
    rw [List.map_fst_zip lengthLe]
  have range : ParameterSubstitution.RangeWellFormed
      (signatureContext signatures signature.id signature.parameters
        signature.wherePredicates) substitution := by
    intro parameter replacement member
    have replacementMember := (List.of_mem_zip member).2
    simp only [List.mem_cons] at replacementMember
    rcases replacementMember with rfl | replacementMember
    · exact head.subject
    · exact head.arguments replacement replacementMember
  exact ⟨exact, range, requiredPredicates⟩

end ImplementationSignatureHeadValidated

namespace ImplementationSignatureRemainingConditions

/-- Combine canonical declaration parameters with the remaining
implementation-head and method-catalog semantics. -/
theorem complete
    {signatures : ProgramSignatures}
    {signature : ProgramImplementationSignature}
    (remaining : ImplementationSignatureRemainingConditions signatures signature)
    (parameters : SignatureParametersWellFormed signature.id
      signature.parameters)
    (structural : ImplementationSignatureStructuralWellFormed signature)
    (validated : Frontend.ImplementationSignatureHeadValidated
      signatures.traits signature)
    (traitIds :
      (signatures.traits.map fun trait => trait.id).Nodup)
    (traitParameters : ∀ trait, trait ∈ signatures.traits →
      SignatureParametersWellFormed trait.id trait.parameters)
    (ruleProjection : signature.implRule ∈ signatures.implRules) :
    ImplementationSignatureWellFormed signatures signature := {
  parameters_nodup := parameters.parameters_nodup
  parameters_owned := parameters.parameter_owners
  parameter_positions := by
    simpa [TypeParameterPositionsCanonical] using parameters.parameter_positions
  parameters_in_head :=
    ImplementationSignatureHeadValidated.semantic_parameters_in_head validated
  method_names_nodup := structural.method_names_nodup
  method_positions := structural.method_positions
  head := remaining.head
  predicates := remaining.predicates
  rule_projection := ruleProjection
  trait_catalog :=
    ImplementationSignatureHeadValidated.semantic_trait_catalog validated
      remaining.head traitIds traitParameters
  methods := by
    intro method member
    exact (remaining.methods method member).complete
      (structural.method_owners method member)
      (structural.method_parameter_names_nodup method member)
  methods_complete := remaining.methods_complete
}

end ImplementationSignatureRemainingConditions

/-- Recover every catalog fact that follows from the actual raw-workspace
checker pipeline, without asking callers to restate any semantic premise. -/
theorem checkedSignatureCatalogFacts_ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked) :
    CheckedSignatureCatalogFacts checked.signatures := by
  obtain ⟨loaded, loadedSuccess, checkedSuccess⟩ :=
    Frontend.checkProgram_success_load success
  have environmentIds := Frontend.loadProgram_success_declarations_nodup
    loadedSuccess
  have signaturesSuccess := Frontend.checkLoadedProgram_success_signatures
    checkedSuccess
  have parameters :=
    Frontend.checkProgram_success_signature_parameters_wellFormed success
  refine {
    impl_rules_eq :=
      Frontend.buildProgramSignatures_success_implRules_eq signaturesSuccess
    declaration_ids := signatureDeclarationIds_nodup_ofCheckProgram success
    function_ids :=
      Frontend.buildProgramSignatures_success_function_ids_nodup
        environmentIds signaturesSuccess
    data_ids := Frontend.buildProgramSignatures_success_data_ids_nodup
      environmentIds signaturesSuccess
    trait_ids := Frontend.buildProgramSignatures_success_trait_ids_nodup
      environmentIds signaturesSuccess
    implementation_ids :=
      Frontend.buildProgramSignatures_success_implementation_ids_nodup
        environmentIds signaturesSuccess
    contract_ids := Frontend.buildProgramSignatures_success_contract_ids_nodup
      environmentIds signaturesSuccess
    constructor_ids := Frontend.checkProgram_success_constructor_ids_nodup success
    trait_method_ids :=
      Frontend.checkProgram_success_trait_method_ids_nodup success
    implementation_method_ids :=
      Frontend.checkProgram_success_implementation_method_ids_nodup success
    parameters
    function_shapes := by
      intro signature member
      exact Frontend.checkProgram_success_function_signature_shape success member
    data_structures := by
      intro signature member
      exact Frontend.checkProgram_success_data_signature_structure success member
    trait_structures := by
      intro signature member
      exact Frontend.checkProgram_success_trait_signature_structure success member
    implementation_structures := by
      intro signature member
      exact Frontend.checkProgram_success_implementation_signature_structure
        success member
    implementation_heads := by
      intro signature member
      exact Frontend.checkProgram_success_implementation_head_validated
        success member
    contracts_semantic := ?_
  }
  intro signature member
  have canonical := parameters.contracts signature member
  exact {
    parameters_nodup := canonical.parameters_nodup
    parameters_owned := canonical.parameter_owners
    parameter_positions := by
      simpa [TypeParameterPositionsCanonical] using
        canonical.parameter_positions
  }

namespace SignatureCatalogRemainingConditions

/-- Merge checker-derived facts with precisely the catalog obligations that
remain declarative. -/
theorem complete
    {signatures : ProgramSignatures}
    (remaining : SignatureCatalogRemainingConditions signatures)
    (checked : CheckedSignatureCatalogFacts signatures) :
    SignatureCatalogWellFormed signatures := by
  refine {
    impl_rules_eq := checked.impl_rules_eq
    declaration_ids := checked.declaration_ids
    function_ids := checked.function_ids
    data_ids := checked.data_ids
    trait_ids := checked.trait_ids
    implementation_ids := checked.implementation_ids
    contract_ids := checked.contract_ids
    constructor_ids := checked.constructor_ids
    trait_method_ids := checked.trait_method_ids
    implementation_method_ids := checked.implementation_method_ids
    function_parameters := ?_
    data_parameters := ?_
    trait_parameters := ?_
    implementation_parameters := ?_
    contract_parameters := ?_
    functions_semantic := ?_
    data_semantic := ?_
    traits_semantic := ?_
    implementations_semantic := ?_
    contracts_semantic := checked.contracts_semantic
  }
  · intro signature member
    have parameters := checked.parameters.functions signature member
    exact ⟨parameters.parameters_nodup, parameters.parameter_owners⟩
  · intro signature member
    have parameters := checked.parameters.dataTypes signature member
    exact ⟨parameters.parameters_nodup, parameters.parameter_owners⟩
  · intro signature member
    have parameters := checked.parameters.traits signature member
    exact ⟨parameters.parameters_nodup, parameters.parameter_owners⟩
  · intro signature member
    have parameters := checked.parameters.implementations signature member
    exact ⟨parameters.parameters_nodup, parameters.parameter_owners⟩
  · intro signature member
    have parameters := checked.parameters.contracts signature member
    exact ⟨parameters.parameters_nodup, parameters.parameter_owners⟩
  · intro signature member
    exact (remaining.functions_semantic signature member).complete
      (checked.parameters.functions signature member)
      (checked.function_shapes signature member)
  · intro signature member
    exact (remaining.data_semantic signature member).complete
      (checked.parameters.dataTypes signature member)
      (checked.data_structures signature member)
  · intro signature member
    exact (remaining.traits_semantic signature member).complete
      (checked.parameters.traits signature member)
      (checked.trait_structures signature member)
  · intro signature member
    apply (remaining.implementations_semantic signature member).complete
      (checked.parameters.implementations signature member)
      (checked.implementation_structures signature member)
      (checked.implementation_heads signature member)
      checked.trait_ids checked.parameters.traits
    rw [checked.impl_rules_eq]
    exact List.mem_map.mpr ⟨signature, member, rfl⟩

end SignatureCatalogRemainingConditions

namespace SignatureCatalogWellFormed

/-- Raw checker success plus only the still-declarative catalog premises yields
the complete semantic signature catalog invariant. -/
theorem ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    (remaining : SignatureCatalogRemainingConditions checked.signatures) :
    SignatureCatalogWellFormed checked.signatures :=
  remaining.complete (checkedSignatureCatalogFacts_ofCheckProgram success)

end SignatureCatalogWellFormed

/-- The remaining proof obligations for promoting a forgeable checked-program
carrier to a declaratively well-formed source program.  Exact ID alignment
rules out missing and extra bodies; semantic body validity is deliberately an
explicit premise rather than being identified with checker success. -/
structure CheckedProgramWellFormedConditions
    (checked : CheckedProgram) : Prop where
  signatures : SignatureCatalogWellFormed checked.signatures
  function_ids : checked.functions.map (fun function => function.declaration) =
    checked.signatures.functions.map (fun signature => signature.id)
  method_ids : checked.methods.map (fun method => method.id) =
    (checked.signatures.implementations.flatMap fun implementation =>
      implementation.methods.map fun method => method.id)
  functions_valid : ∀ function, function ∈ checked.functions →
    FunctionDefinition.Valid checked.signatures
      (FunctionDefinition.ofChecked function)
  methods_valid : ∀ method, method ∈ checked.methods →
    MethodDefinition.Valid checked.signatures
      (MethodDefinition.ofChecked method)

namespace CheckedProgramWellFormedConditions

/-- Successful executable checking discharges the exact function/method
identity alignment obligations.  The catalog invariant and semantic validity
of each body remain explicit because they are not yet consequences of checker
success. -/
theorem ofCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = Except.ok checked)
    (signatures : SignatureCatalogWellFormed checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    CheckedProgramWellFormedConditions checked := by
  obtain ⟨functionIds, methodIds⟩ :=
    Frontend.checkLoadedProgram_success_ids success
  exact {
    signatures
    function_ids := functionIds
    method_ids := methodIds
    functions_valid := functionsValid
    methods_valid := methodsValid
  }

/-- Raw checker success fills the body identity alignment and every automatic
catalog field; callers provide only the residual catalog semantics and body
validity. -/
theorem ofCheckProgramWithRemainingCatalog
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = Except.ok checked)
    (remaining : SignatureCatalogRemainingConditions checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    CheckedProgramWellFormedConditions checked := by
  obtain ⟨functionIds, methodIds⟩ := Frontend.checkProgram_success_ids success
  exact {
    signatures := SignatureCatalogWellFormed.ofCheckProgram success remaining
    function_ids := functionIds
    method_ids := methodIds
    functions_valid := functionsValid
    methods_valid := methodsValid
  }

/-- Successful checking from a raw workspace likewise discharges exact body
identity alignment; callers retain only the semantic catalog/body premises. -/
theorem ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = Except.ok checked)
    (signatures : SignatureCatalogWellFormed checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    CheckedProgramWellFormedConditions checked := by
  obtain ⟨functionIds, methodIds⟩ := Frontend.checkProgram_success_ids success
  exact {
    signatures
    function_ids := functionIds
    method_ids := methodIds
    functions_valid := functionsValid
    methods_valid := methodsValid
  }

/-- Assemble whole-program declarative well-formedness from the explicit
checker-to-semantics bridge obligations. -/
theorem programWellFormed
    {checked : CheckedProgram}
    (conditions : CheckedProgramWellFormedConditions checked) :
    ProgramWellFormed (Program.ofChecked checked) := by
  constructor
  · exact conditions.signatures
  · simp only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked]
    rw [conditions.function_ids]
    exact conditions.signatures.function_ids
  · simp only [Program.ofChecked, List.map_map, Function.comp_def,
      MethodDefinition.ofChecked]
    rw [conditions.method_ids]
    exact conditions.signatures.implementation_method_ids
  · intro definition definitionMem
    simp only [Program.ofChecked, List.mem_map] at definitionMem
    rcases definitionMem with ⟨function, functionMem, rfl⟩
    exact conditions.functions_valid function functionMem
  · intro definition definitionMem
    simp only [Program.ofChecked, List.mem_map] at definitionMem
    rcases definitionMem with ⟨method, methodMem, rfl⟩
    exact conditions.methods_valid method methodMem
  · intro signature signatureMem
    have signatureIdMem : signature.id ∈
        checked.signatures.functions.map (fun candidate => candidate.id) :=
      List.mem_map.mpr ⟨signature, signatureMem, rfl⟩
    rw [← conditions.function_ids] at signatureIdMem
    rcases List.mem_map.mp signatureIdMem with
      ⟨function, functionMem, declarationEq⟩
    refine ⟨FunctionDefinition.ofChecked function, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨function, functionMem, rfl⟩
    · simpa [FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using
        declarationEq
  · intro implementation implementationMem method methodMem
    have methodIdMem : method.id ∈
        (checked.signatures.implementations.flatMap fun candidate =>
          candidate.methods.map fun candidateMethod => candidateMethod.id) := by
      apply List.mem_flatMap.mpr
      exact ⟨implementation, implementationMem,
        List.mem_map.mpr ⟨method, methodMem, rfl⟩⟩
    rw [← conditions.method_ids] at methodIdMem
    rcases List.mem_map.mp methodIdMem with
      ⟨checkedMethod, checkedMethodMem, idEq⟩
    refine ⟨MethodDefinition.ofChecked checkedMethod, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨checkedMethod, checkedMethodMem, rfl⟩
    · simpa [MethodDefinition.ofChecked] using idEq

/-- Promote a successful loaded-program check directly to declarative
whole-program well-formedness once the remaining semantic premises are
supplied.  Function and method identity alignment is recovered from checker
success rather than repeated by callers. -/
theorem programWellFormedOfCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = Except.ok checked)
    (signatures : SignatureCatalogWellFormed checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    ProgramWellFormed (Program.ofChecked checked) :=
  (CheckedProgramWellFormedConditions.ofCheckLoadedProgram success signatures
    functionsValid methodsValid).programWellFormed

/-- Promote raw-workspace checker success directly to declarative
whole-program well-formedness once the remaining semantic premises are
supplied. -/
theorem programWellFormedOfCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = Except.ok checked)
    (signatures : SignatureCatalogWellFormed checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    ProgramWellFormed (Program.ofChecked checked) :=
  (CheckedProgramWellFormedConditions.ofCheckProgram success signatures
    functionsValid methodsValid).programWellFormed

/-- End-to-end declarative program admission from raw checker success, the
remaining signature-catalog semantics, and semantic body validity. -/
theorem programWellFormedOfCheckProgramWithRemainingCatalog
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = Except.ok checked)
    (remaining : SignatureCatalogRemainingConditions checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    ProgramWellFormed (Program.ofChecked checked) :=
  (CheckedProgramWellFormedConditions.ofCheckProgramWithRemainingCatalog
    success remaining functionsValid methodsValid).programWellFormed

end CheckedProgramWellFormedConditions

end Solcore.SourceSemantics
