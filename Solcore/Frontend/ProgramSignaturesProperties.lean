import Solcore.Frontend.ProgramSignatures

/-!
Properties guaranteed directly by successful whole-program signature collection.
-/

set_option autoImplicit false

namespace Solcore.Frontend

namespace ProgramFunctionSignature

/-- All three parameter projections retain the exact source parameter
cardinality. -/
@[simp] theorem parameterNames_length (signature : ProgramFunctionSignature) :
    signature.parameterNames.length = signature.parameters.length := by
  simp [parameterNames]

@[simp] theorem parameterTypes_length (signature : ProgramFunctionSignature) :
    signature.parameterTypes.length = signature.parameters.length := by
  simp [parameterTypes]

@[simp] theorem parameterComptime_length
    (signature : ProgramFunctionSignature) :
    signature.parameterComptime.length = signature.parameters.length := by
  simp [parameterComptime]

end ProgramFunctionSignature

/-- A collected function has duplicate-free source parameter names and a
scheme body assembled exactly from its stored parameter and return types. -/
theorem buildProgramSignatures_success_function_shape
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ signatures.functions) :
    signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes) :=
  buildProgramSignatures_success_function_shape_state success signature member

/-- Successful collection rejects duplicate source parameter names for every
function signature retained in the catalog. -/
theorem buildProgramSignatures_success_function_parameter_names_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ signatures.functions) :
    signature.parameterNames.Nodup :=
  (buildProgramSignatures_success_function_shape success member).1

/-- Successful collection records the canonical function type as the body of
every constrained function scheme. -/
theorem buildProgramSignatures_success_function_scheme_body
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ signatures.functions) :
    signature.scheme.body = .function
      (TypeSystem.Ty.productMany signature.parameterTypes)
      (TypeSystem.Ty.productMany signature.returnTypes) :=
  (buildProgramSignatures_success_function_shape success member).2

namespace DataSignatureStructuralWellFormed

/-- Stable constructor identities are unique within one structurally valid
data signature because their source-order indices are distinct. -/
theorem constructor_ids_nodup
    {signature : ProgramDataSignature}
    (shape : DataSignatureStructuralWellFormed signature) :
    (signature.constructors.map fun constructor => constructor.id).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map,
    List.pairwise_iff_getElem]
  intro leftIndex rightIndex leftBound rightBound before equal
  have leftPosition := shape.constructor_positions
    ⟨leftIndex, leftBound⟩
  have rightPosition := shape.constructor_positions
    ⟨rightIndex, rightBound⟩
  simp only [List.get_eq_getElem] at leftPosition rightPosition
  have indexEqual := congrArg ProgramDataConstructorId.constructorIndex equal
  rw [leftPosition, rightPosition] at indexEqual
  omega

end DataSignatureStructuralWellFormed

/-- Successful collection retains duplicate-free constructor names and the
canonical declaration-owned constructor identity allocation for every data
signature. -/
theorem buildProgramSignatures_success_data_structure
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramDataSignature}
    (member : signature ∈ signatures.dataTypes) :
    DataSignatureStructuralWellFormed signature :=
  buildProgramSignatures_success_data_structure_state success signature member

/-- Successful collection rejects duplicate constructor names within every
data declaration. -/
theorem buildProgramSignatures_success_data_constructor_names_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramDataSignature}
    (member : signature ∈ signatures.dataTypes) :
    (signature.constructors.map fun constructor => constructor.name).Nodup :=
  (buildProgramSignatures_success_data_structure success member).constructor_names_nodup

/-- Every collected constructor identity records the declaration that owns
its data signature. -/
theorem buildProgramSignatures_success_data_constructor_owners
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramDataSignature}
    (member : signature ∈ signatures.dataTypes) :
    ∀ constructor, constructor ∈ signature.constructors →
      constructor.id.dataType = signature.id :=
  (buildProgramSignatures_success_data_structure success member).constructor_owners

/-- Every collected constructor identity uses its zero-based source position
within the owning declaration. -/
theorem buildProgramSignatures_success_data_constructor_positions
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramDataSignature}
    (member : signature ∈ signatures.dataTypes) :
    ∀ index : Fin signature.constructors.length,
      (signature.constructors.get index).id.constructorIndex = index.val :=
  (buildProgramSignatures_success_data_structure success member).constructor_positions

namespace TraitSignatureStructuralWellFormed

/-- Stable method identities are unique within one structurally valid trait
signature because their source-order indices are distinct. -/
theorem method_ids_nodup
    {signature : ProgramTraitSignature}
    (shape : TraitSignatureStructuralWellFormed signature) :
    (signature.methods.map fun method => method.id).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map,
    List.pairwise_iff_getElem]
  intro leftIndex rightIndex leftBound rightBound before equal
  have leftPosition := shape.method_positions ⟨leftIndex, leftBound⟩
  have rightPosition := shape.method_positions ⟨rightIndex, rightBound⟩
  simp only [List.get_eq_getElem] at leftPosition rightPosition
  have indexEqual := congrArg ProgramTraitMethodId.methodIndex equal
  rw [leftPosition, rightPosition] at indexEqual
  omega

end TraitSignatureStructuralWellFormed

/-- Successful collection retains duplicate-free method names, canonical
trait ownership and source-order IDs, and duplicate-free local parameter
names for every trait method. -/
theorem buildProgramSignatures_success_trait_structure
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramTraitSignature}
    (member : signature ∈ signatures.traits) :
    TraitSignatureStructuralWellFormed signature :=
  buildProgramSignatures_success_trait_structure_state success signature member

/-- Successful collection rejects duplicate method names within every trait. -/
theorem buildProgramSignatures_success_trait_method_names_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramTraitSignature}
    (member : signature ∈ signatures.traits) :
    (signature.methods.map fun method => method.name).Nodup :=
  (buildProgramSignatures_success_trait_structure success member).method_names_nodup

/-- Every collected trait method identity records the declaration that owns
its trait signature. -/
theorem buildProgramSignatures_success_trait_method_owners
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramTraitSignature}
    (member : signature ∈ signatures.traits) :
    ∀ method, method ∈ signature.methods → method.id.trait = signature.id :=
  (buildProgramSignatures_success_trait_structure success member).method_owners

/-- Every collected trait method identity uses its zero-based source position
within the owning declaration. -/
theorem buildProgramSignatures_success_trait_method_positions
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramTraitSignature}
    (member : signature ∈ signatures.traits) :
    ∀ index : Fin signature.methods.length,
      (signature.methods.get index).id.methodIndex = index.val :=
  (buildProgramSignatures_success_trait_structure success member).method_positions

/-- Every collected trait method retains duplicate-free source parameter
names from ordinary method-shape resolution. -/
theorem buildProgramSignatures_success_trait_method_parameter_names_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramTraitSignature}
    (member : signature ∈ signatures.traits) :
    ∀ method, method ∈ signature.methods → method.parameterNames.Nodup :=
  (buildProgramSignatures_success_trait_structure success member)
    |>.method_parameter_names_nodup

/-- A successfully built signature catalog stores exactly the rules projected from
its implementation signatures. -/
theorem buildProgramSignatures_success_implRules_eq
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    signatures.implRules =
      signatures.implementations.map ProgramImplementationSignature.implRule := by
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    rfl
  · simp at success

/-- Membership in the collected rule list has an exact implementation-signature
origin. -/
theorem buildProgramSignatures_success_implRule_mem_iff
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {rule : ProgramImplRule} :
    rule ∈ signatures.implRules ↔
      ∃ implementation, implementation ∈ signatures.implementations ∧
        implementation.implRule = rule := by
  rw [buildProgramSignatures_success_implRules_eq success]
  simp

/-- Successful collection establishes the canonical rigid-parameter contract
simultaneously for functions, data types, traits, implementations, and
contracts. -/
theorem buildProgramSignatures_success_parameters_wellFormed
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    ProgramSignatureParametersWellFormed signatures :=
  buildProgramSignatures_success_parameter_state success

/-- A collected function's rigid generic parameters are unique, owned by the
function declaration, and numbered in source order. -/
theorem buildProgramSignatures_success_function_parameters
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ signatures.functions) :
    SignatureParametersWellFormed signature.id signature.scheme.parameters :=
  (buildProgramSignatures_success_parameters_wellFormed success).functions
    signature member

/-- A collected data type's rigid generic parameters are unique, owned by the
data declaration, and numbered in source order. -/
theorem buildProgramSignatures_success_data_parameters
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramDataSignature}
    (member : signature ∈ signatures.dataTypes) :
    SignatureParametersWellFormed signature.id signature.parameters :=
  (buildProgramSignatures_success_parameters_wellFormed success).dataTypes
    signature member

/-- A collected trait's rigid generic parameters are unique, owned by the
trait declaration, and numbered in source order. -/
theorem buildProgramSignatures_success_trait_parameters
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramTraitSignature}
    (member : signature ∈ signatures.traits) :
    SignatureParametersWellFormed signature.id signature.parameters :=
  (buildProgramSignatures_success_parameters_wellFormed success).traits
    signature member

/-- A collected implementation's rigid generic parameters are unique, owned
by the implementation declaration, and numbered in source order. -/
theorem buildProgramSignatures_success_implementation_parameters
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramImplementationSignature}
    (member : signature ∈ signatures.implementations) :
    SignatureParametersWellFormed signature.id signature.parameters :=
  (buildProgramSignatures_success_parameters_wellFormed success).implementations
    signature member

/-- A collected contract's rigid generic parameters are unique, owned by the
contract declaration, and numbered in source order. -/
theorem buildProgramSignatures_success_contract_parameters
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {signature : ProgramContractSignature}
    (member : signature ∈ signatures.contracts) :
    SignatureParametersWellFormed signature.id signature.parameters :=
  (buildProgramSignatures_success_parameters_wellFormed success).contracts
    signature member

/-- Function declaration identities are unique after successful signature
collection from an environment with unique declaration identities. -/
theorem buildProgramSignatures_success_function_ids_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (environmentIds :
      (environment.declarations.map fun declaration => declaration.id).Nodup)
    (success : buildProgramSignatures environment = .ok signatures) :
    (signatures.functions.map fun signature => signature.id).Nodup := by
  have all := buildProgramSignatures_success_declaration_ids_nodup
    environmentIds success
  have withoutContracts := (List.nodup_append.mp all).1
  have withoutImplementations := (List.nodup_append.mp withoutContracts).1
  have functionsAndData :=
    (List.nodup_append.mp withoutImplementations).1
  exact (List.nodup_append.mp functionsAndData).1

/-- Data declaration identities are unique after successful signature
collection from an environment with unique declaration identities. -/
theorem buildProgramSignatures_success_data_ids_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (environmentIds :
      (environment.declarations.map fun declaration => declaration.id).Nodup)
    (success : buildProgramSignatures environment = .ok signatures) :
    (signatures.dataTypes.map fun signature => signature.id).Nodup := by
  have all := buildProgramSignatures_success_declaration_ids_nodup
    environmentIds success
  have withoutContracts := (List.nodup_append.mp all).1
  have withoutImplementations := (List.nodup_append.mp withoutContracts).1
  have functionsAndData :=
    (List.nodup_append.mp withoutImplementations).1
  exact (List.nodup_append.mp functionsAndData).2.1

/-- Distinct owning declaration identities plus each data signature's local
source-order allocation make constructor identities unique across the whole
catalog. -/
theorem data_constructor_ids_nodup_of_structural
    {dataTypes : List ProgramDataSignature}
    (dataIds : (dataTypes.map fun signature => signature.id).Nodup)
    (shapes : ∀ signature, signature ∈ dataTypes →
      DataSignatureStructuralWellFormed signature) :
    (dataTypes.flatMap fun signature =>
      signature.constructors.map fun constructor => constructor.id).Nodup := by
  induction dataTypes with
  | nil => simp
  | cons dataType rest induction =>
      simp only [List.map_cons, List.nodup_cons] at dataIds
      have dataTypeShape := shapes dataType (by simp)
      have restShapes : ∀ signature, signature ∈ rest →
          DataSignatureStructuralWellFormed signature := by
        intro signature member
        exact shapes signature (by simp [member])
      simp only [List.flatMap_cons, List.nodup_append]
      refine ⟨dataTypeShape.constructor_ids_nodup,
        induction dataIds.2 restShapes, ?_⟩
      intro left leftMember right rightMember equal
      rcases List.mem_map.mp leftMember with
        ⟨leftConstructor, leftConstructorMember, rfl⟩
      rcases List.mem_flatMap.mp rightMember with
        ⟨rightDataType, rightDataTypeMember, rightMember⟩
      rcases List.mem_map.mp rightMember with
        ⟨rightConstructor, rightConstructorMember, rfl⟩
      apply dataIds.1
      apply List.mem_map.mpr
      refine ⟨rightDataType, rightDataTypeMember, ?_⟩
      calc
        rightDataType.id = rightConstructor.id.dataType :=
          (restShapes rightDataType rightDataTypeMember).constructor_owners
            rightConstructor rightConstructorMember |>.symm
        _ = leftConstructor.id.dataType := by
          exact congrArg ProgramDataConstructorId.dataType equal.symm
        _ = dataType.id :=
          dataTypeShape.constructor_owners leftConstructor
            leftConstructorMember

/-- Successful collection from an identity-unique environment assigns one
globally unique stable identity to every data constructor. -/
theorem buildProgramSignatures_success_constructor_ids_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (environmentIds :
      (environment.declarations.map fun declaration => declaration.id).Nodup)
    (success : buildProgramSignatures environment = .ok signatures) :
    (signatures.dataTypes.flatMap fun signature =>
      signature.constructors.map fun constructor => constructor.id).Nodup := by
  apply data_constructor_ids_nodup_of_structural
    (buildProgramSignatures_success_data_ids_nodup environmentIds success)
  intro signature member
  exact buildProgramSignatures_success_data_structure success member

/-- Trait declaration identities are unique after successful signature
collection from an environment with unique declaration identities. -/
theorem buildProgramSignatures_success_trait_ids_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (environmentIds :
      (environment.declarations.map fun declaration => declaration.id).Nodup)
    (success : buildProgramSignatures environment = .ok signatures) :
    (signatures.traits.map fun signature => signature.id).Nodup := by
  have all := buildProgramSignatures_success_declaration_ids_nodup
    environmentIds success
  have withoutContracts := (List.nodup_append.mp all).1
  have withoutImplementations := (List.nodup_append.mp withoutContracts).1
  exact (List.nodup_append.mp withoutImplementations).2.1

/-- Distinct owning trait identities plus each trait's local source-order
allocation make trait-method identities unique across a complete catalog. -/
theorem trait_method_ids_nodup_of_structural
    {traits : List ProgramTraitSignature}
    (traitIds : (traits.map fun signature => signature.id).Nodup)
    (shapes : ∀ signature, signature ∈ traits →
      TraitSignatureStructuralWellFormed signature) :
    (traits.flatMap fun signature =>
      signature.methods.map fun method => method.id).Nodup := by
  induction traits with
  | nil => simp
  | cons trait rest induction =>
      simp only [List.map_cons, List.nodup_cons] at traitIds
      have traitShape := shapes trait (by simp)
      have restShapes : ∀ signature, signature ∈ rest →
          TraitSignatureStructuralWellFormed signature := by
        intro signature member
        exact shapes signature (by simp [member])
      simp only [List.flatMap_cons, List.nodup_append]
      refine ⟨traitShape.method_ids_nodup,
        induction traitIds.2 restShapes, ?_⟩
      intro left leftMember right rightMember equal
      rcases List.mem_map.mp leftMember with
        ⟨leftMethod, leftMethodMember, rfl⟩
      rcases List.mem_flatMap.mp rightMember with
        ⟨rightTrait, rightTraitMember, rightMember⟩
      rcases List.mem_map.mp rightMember with
        ⟨rightMethod, rightMethodMember, rfl⟩
      apply traitIds.1
      apply List.mem_map.mpr
      refine ⟨rightTrait, rightTraitMember, ?_⟩
      calc
        rightTrait.id = rightMethod.id.trait :=
          (restShapes rightTrait rightTraitMember).method_owners
            rightMethod rightMethodMember |>.symm
        _ = leftMethod.id.trait := by
          exact congrArg ProgramTraitMethodId.trait equal.symm
        _ = trait.id :=
          traitShape.method_owners leftMethod leftMethodMember

/-- Successful collection from an identity-unique environment assigns one
globally unique stable identity to every trait method. -/
theorem buildProgramSignatures_success_trait_method_ids_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (environmentIds :
      (environment.declarations.map fun declaration => declaration.id).Nodup)
    (success : buildProgramSignatures environment = .ok signatures) :
    (signatures.traits.flatMap fun signature =>
      signature.methods.map fun method => method.id).Nodup := by
  apply trait_method_ids_nodup_of_structural
    (buildProgramSignatures_success_trait_ids_nodup environmentIds success)
  intro signature member
  exact buildProgramSignatures_success_trait_structure success member

/-- Implementation declaration identities are unique after successful
signature collection from an environment with unique declaration identities. -/
theorem buildProgramSignatures_success_implementation_ids_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (environmentIds :
      (environment.declarations.map fun declaration => declaration.id).Nodup)
    (success : buildProgramSignatures environment = .ok signatures) :
    (signatures.implementations.map fun signature => signature.id).Nodup := by
  have all := buildProgramSignatures_success_declaration_ids_nodup
    environmentIds success
  have withoutContracts := (List.nodup_append.mp all).1
  exact (List.nodup_append.mp withoutContracts).2.1

/-- Contract declaration identities are unique after successful signature
collection from an environment with unique declaration identities. -/
theorem buildProgramSignatures_success_contract_ids_nodup
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (environmentIds :
      (environment.declarations.map fun declaration => declaration.id).Nodup)
    (success : buildProgramSignatures environment = .ok signatures) :
    (signatures.contracts.map fun signature => signature.id).Nodup := by
  have all := buildProgramSignatures_success_declaration_ids_nodup
    environmentIds success
  exact (List.nodup_append.mp all).2.1

end Solcore.Frontend
