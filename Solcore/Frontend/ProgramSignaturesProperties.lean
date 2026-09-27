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
