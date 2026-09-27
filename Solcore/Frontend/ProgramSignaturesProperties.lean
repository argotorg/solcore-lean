import Solcore.Frontend.ProgramSignatures

/-!
Properties guaranteed directly by successful whole-program signature collection.
-/

set_option autoImplicit false

namespace Solcore.Frontend

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
