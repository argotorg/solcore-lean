import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.Program
import Solcore.SourceSemantics.SubstitutionProperties

/-!
Conditional bridge from executable whole-program checking results to the
declarative source-program carrier.

The conversions in this module only forget algorithmic bookkeeping.  Checker
success supplies declaration identities, canonical generic parameters,
resolved signature formation, rule projection, and contract-signature
semantics.  Semantic body validity remains a separate premise because the
executable frontend is not itself the definition of source typing.
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

/-- Declaration context used by the semantic header recovered from one
successful executable body check. -/
def checkedBodyContext (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) (checked : CheckedFunction) :
    Context :=
  declarationContext signatures signature.id signature.scheme.parameters
    signature.scheme.predicates checked.solvedRequirements

/-- Every interface-level component of `BodyDefinitionHasType` which follows
from signature formation and executable body-check provenance alone.  Graph,
requirement-ledger, and deep statement typing remain deliberately separate. -/
structure CheckedBodyHeaderWellFormed
    (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature)
    (checked : CheckedFunction) : Prop where
  declaration_eq : checked.declaration = signature.id
  source_owner : checked.typedBody.owner = checked.declaration
  parameter_binders : TypeParameterBindersWellFormed
    (checkedBodyContext signatures signature checked)
  parameter_types : TypesWellFormed
    (checkedBodyContext signatures signature checked) signature.parameterTypes
  return_types : TypesWellFormed
    (checkedBodyContext signatures signature checked) signature.returnTypes
  callable_type : checked.type = .function
    (TypeSystem.Ty.productMany signature.parameterTypes)
    (TypeSystem.Ty.productMany signature.returnTypes)
  result_type : checked.inferredBodyType =
    TypeSystem.Ty.productMany signature.returnTypes
  return_comptime : checked.returnComptime = signature.returnComptime
  input_names : checked.typedBody.inputs.map (fun binder => binder.name) =
    signature.parameterNames
  input_comptime : checked.typedBody.inputs.map (fun binder => binder.comptime) =
    signature.parameterComptime
  inputs_extend : ∃ lexicalContext,
    MonoBindersExtend signature.id
      (checkedBodyContext signatures signature checked)
      checked.typedBody.inputs signature.parameterTypes lexicalContext

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

/-- Formation validation is independent of declaration assumptions, so its
closed type witness embeds into every semantic signature context with the same
catalog, owner, and rigid parameter row. -/
theorem SignatureTypeFormationValidated.typeWellScoped
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {type : TypeSystem.Ty}
    (validated : Frontend.SignatureTypeFormationValidated signatures owner
      parameters type)
    (assumptions : List ProgramPredicate) :
    TypeWellScoped
      (signatureContext signatures owner parameters assumptions) [] type := by
  refine Frontend.SignatureTypeFormationValidated.rec
    (motive_1 := fun type _ => TypeWellScoped
      (signatureContext signatures owner parameters assumptions) [] type)
    (motive_2 := fun types _ => TypesWellScoped
      (signatureContext signatures owner parameters assumptions) [] types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ validated
  · intro parameter bound owned
    exact .parameter
      (by simpa [signatureContext, Context.withAssumptions,
        Context.forDeclaration] using bound)
      (by simp [signatureContext, Context.withAssumptions,
        Context.forDeclaration, owned])
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    exact .nominal dataType arguments cataloged arity argumentsInduction
  · intro contract arguments cataloged arity _ argumentsInduction
    exact .contractNominal contract arguments cataloged arity argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

/-- Source-order type-row formation embeds into the corresponding semantic
scope using the type conversion above. -/
theorem SignatureTypesFormationValidated.typesWellScoped
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {types : List TypeSystem.Ty}
    (validated : Frontend.SignatureTypesFormationValidated signatures owner
      parameters types)
    (assumptions : List ProgramPredicate) :
    TypesWellScoped
      (signatureContext signatures owner parameters assumptions) [] types := by
  cases validated with
  | nil => exact .nil
  | cons headValidated tailValidated =>
      exact .cons
        (SignatureTypeFormationValidated.typeWellScoped
          headValidated assumptions)
        (SignatureTypesFormationValidated.typesWellScoped
          tailValidated assumptions)

private theorem signatureContext_typeParameterBinders
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    (canonical : SignatureParametersWellFormed owner parameters)
    (assumptions : List ProgramPredicate) :
    TypeParameterBindersWellFormed
      (signatureContext signatures owner parameters assumptions) := by
  constructor
  · simpa [signatureContext, Context.withAssumptions,
      Context.forDeclaration] using canonical.parameters_nodup
  · intro parameter member
    have parameterMember : parameter ∈ parameters := by
      simpa [signatureContext, Context.withAssumptions,
        Context.forDeclaration] using member
    have owned := canonical.parameter_owners parameter parameterMember
    simp [signatureContext, Context.withAssumptions,
      Context.forDeclaration, owned]

namespace SignatureParametersWellFormed

/-- Canonical declaration parameters remain valid after installing solved
requirements and opening the residual body-inference scope. -/
theorem declarationContextBinders
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    (canonical : SignatureParametersWellFormed owner parameters)
    (assumptions : List ProgramPredicate)
    (requirements : List SolvedRequirement) :
    TypeParameterBindersWellFormed
      (declarationContext signatures owner parameters assumptions
        requirements) := by
  exact StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
    rfl rfl (signatureContext_typeParameterBinders
      (signatures := signatures) canonical assumptions)

end SignatureParametersWellFormed

namespace SignatureTypeFormationValidated

/-- Close a validated frontend type with the signature collector's canonical
rigid binder witness. -/
theorem typeWellFormed
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {type : TypeSystem.Ty}
    (validated : Frontend.SignatureTypeFormationValidated signatures owner
      parameters type)
    (canonical : SignatureParametersWellFormed owner parameters)
    (assumptions : List ProgramPredicate) :
    TypeWellFormed
      (signatureContext signatures owner parameters assumptions) type := {
  binders := signatureContext_typeParameterBinders canonical assumptions
  typeWellScoped := SignatureTypeFormationValidated.typeWellScoped
    validated assumptions
}

end SignatureTypeFormationValidated

namespace SignatureTypesFormationValidated

/-- Pointwise closed formation for a validated source-order type row. -/
theorem typesWellFormed
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {types : List TypeSystem.Ty}
    (validated : Frontend.SignatureTypesFormationValidated signatures owner
      parameters types)
    (canonical : SignatureParametersWellFormed owner parameters)
    (assumptions : List ProgramPredicate) :
    TypesWellFormed
      (signatureContext signatures owner parameters assumptions) types := by
  intro type member
  exact {
    binders := signatureContext_typeParameterBinders canonical assumptions
    typeWellScoped :=
      (SignatureTypesFormationValidated.typesWellScoped validated assumptions)
        |>.member member
  }

/-- Validated signature types remain well formed after installing the solved
requirement ledger and opening the declaration's residual inference scope. -/
theorem declarationTypesWellFormed
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {types : List TypeSystem.Ty}
    (validated : Frontend.SignatureTypesFormationValidated signatures owner
      parameters types)
    (canonical : SignatureParametersWellFormed owner parameters)
    (assumptions : List ProgramPredicate)
    (requirements : List SolvedRequirement) :
    TypesWellFormed
      (declarationContext signatures owner parameters assumptions requirements)
      types := by
  exact StructuralSubstitution.TypesWellFormed.transportContext
    (source := signatureContext signatures owner parameters assumptions)
    (target := declarationContext signatures owner parameters assumptions
      requirements)
    rfl rfl rfl
    (Solcore.SourceSemantics.SignatureTypesFormationValidated.typesWellFormed
      validated canonical assumptions)

end SignatureTypesFormationValidated

namespace SignaturePredicateFormationValidated

/-- Frontend predicate formation is exactly the algorithm-independent
predicate judgment after closing its declaration binders. -/
theorem predicateWellFormed
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {predicate : ProgramPredicate}
    (validated : Frontend.SignaturePredicateFormationValidated signatures owner
      parameters predicate)
    (canonical : SignatureParametersWellFormed owner parameters)
    (assumptions : List ProgramPredicate) :
    PredicateWellFormed
      (signatureContext signatures owner parameters assumptions) predicate := {
  subject := SignatureTypeFormationValidated.typeWellFormed validated.subject
    canonical assumptions
  arguments := by
    intro argument member
    exact SignatureTypesFormationValidated.typesWellFormed validated.arguments
      canonical assumptions argument member
  trait := validated.trait
}

end SignaturePredicateFormationValidated

namespace SignaturePredicatesFormationValidated

/-- Pointwise conversion of a validated predicate row. -/
theorem predicatesWellFormed
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {predicates : List ProgramPredicate}
    (validated : Frontend.SignaturePredicatesFormationValidated signatures owner
      parameters predicates)
    (canonical : SignatureParametersWellFormed owner parameters)
    (assumptions : List ProgramPredicate) :
    PredicatesWellFormed
      (signatureContext signatures owner parameters assumptions) predicates := by
  intro predicate member
  exact SignaturePredicateFormationValidated.predicateWellFormed
    (validated predicate member) canonical assumptions

end SignaturePredicatesFormationValidated

/-- Closed semantic return formation is sufficient to remove the final
inference substitution from a successful checked body's reported result. -/
theorem checkFunctionBody_success_result_type_eq
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    {context : Context}
    (returnTypes : TypesWellFormed context signature.returnTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.inferredBodyType = TypeSystem.Ty.productMany signature.returnTypes := by
  rw [Frontend.SourceInference.checkFunctionBody_success_inferredBodyType success]
  exact StructuralSubstitution.TypeWellScoped.applySubstitution_eq_self
    checked.substitution
    (StructuralSubstitution.TypesWellScoped.productMany
      (StructuralSubstitution.TypesWellFormed.toTypesWellScoped returnTypes))

/-- Closed parameter formation and successful body checking construct the
exact semantic lexical context obtained by installing the finalized input
binders.  This theorem is independent of frontend formation witnesses, so it
also applies to synthetic implementation-method signatures. -/
theorem checkFunctionBody_success_inputs_extend
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    {context : Context}
    (locals_empty : context.locals = [])
    (local_requirements_empty : context.localSchemeRequirements = [])
    (parameterTypes : TypesWellFormed context signature.parameterTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ∃ lexicalContext,
      MonoBindersExtend signature.id context checked.typedBody.inputs
        signature.parameterTypes lexicalContext := by
  have typesFixed :
      signature.parameterTypes.map checked.substitution.apply =
        signature.parameterTypes :=
    StructuralSubstitution.TypesWellScoped.applySubstitution_eq_self
      checked.substitution
      (StructuralSubstitution.TypesWellFormed.toTypesWellScoped parameterTypes)
  have inputsEq :=
    Frontend.SourceInference.checkFunctionBody_success_typedBody_inputs_eq_initial_of_types_fixed
      typesFixed success
  obtain ⟨lexicalContext, extension⟩ := MonoBindersExtend.initialInputs
    signature.id context signature.parameterNames signature.parameterTypes
      signature.parameterComptime
      (signature.parameterNames_length.trans
        signature.parameterTypes_length.symm)
      locals_empty local_requirements_empty parameterTypes
  rw [inputsEq]
  exact ⟨lexicalContext, extension⟩

namespace CheckedBodyHeaderWellFormed

/-- Recover the complete checker-derived body header from canonical generic
parameters, closed signature types, callable shape, and one exact body-check
success equation.  The theorem also applies to synthetic method signatures. -/
theorem ofCheckFunctionBody
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (parameters : SignatureParametersWellFormed signature.id
      signature.scheme.parameters)
    (parameterTypes : TypesWellFormed
      (signatureContext signatures signature.id signature.scheme.parameters
        signature.scheme.predicates) signature.parameterTypes)
    (returnTypes : TypesWellFormed
      (signatureContext signatures signature.id signature.scheme.parameters
        signature.scheme.predicates) signature.returnTypes)
    (schemeBody : signature.scheme.body = .function
      (TypeSystem.Ty.productMany signature.parameterTypes)
      (TypeSystem.Ty.productMany signature.returnTypes))
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    CheckedBodyHeaderWellFormed signatures signature checked := by
  have parameterTypesBody : TypesWellFormed
      (checkedBodyContext signatures signature checked)
      signature.parameterTypes :=
    StructuralSubstitution.TypesWellFormed.transportContext
      (source := signatureContext signatures signature.id
        signature.scheme.parameters signature.scheme.predicates)
      (target := checkedBodyContext signatures signature checked)
      rfl rfl rfl parameterTypes
  have returnTypesBody : TypesWellFormed
      (checkedBodyContext signatures signature checked)
      signature.returnTypes :=
    StructuralSubstitution.TypesWellFormed.transportContext
      (source := signatureContext signatures signature.id
        signature.scheme.parameters signature.scheme.predicates)
      (target := checkedBodyContext signatures signature checked)
      rfl rfl rfl returnTypes
  refine {
    declaration_eq := checkFunctionBody_success_declaration success
    source_owner := ?_
    parameter_binders := ?_
    parameter_types := parameterTypesBody
    return_types := returnTypesBody
    callable_type := ?_
    result_type := checkFunctionBody_success_result_type_eq returnTypes success
    return_comptime := checkFunctionBody_success_returnComptime success
    input_names := checkFunctionBody_success_typedBody_inputNames success
    input_comptime := checkFunctionBody_success_typedBody_inputComptime success
    inputs_extend := ?_
  }
  · exact (checkFunctionBody_success_typedBody_owner success).trans
      (checkFunctionBody_success_declaration success).symm
  · exact
      Solcore.SourceSemantics.SignatureParametersWellFormed.declarationContextBinders
        parameters signature.scheme.predicates checked.solvedRequirements
  · exact (checkFunctionBody_success_type success).trans schemeBody
  · exact checkFunctionBody_success_inputs_extend
      (context := checkedBodyContext signatures signature checked)
      (by rfl)
      (by rfl)
      parameterTypesBody success

/-- Implementation-method signature semantics supply the same body header for
the synthetic ordinary-function view used by executable checking.  This local
bridge is intentionally parametric in the selected trait; callers relating it
to a program catalog retain the corresponding `trait?` lookup equation. -/
theorem ofCheckImplementationMethod
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {implementation : ProgramImplementationSignature}
    {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (implementationWellFormed : ImplementationSignatureWellFormed signatures
      implementation)
    (methodWellFormed : ImplMethodSignatureWellFormed signatures implementation
      method)
    (success : checkFunctionBody environment signatures
      (implementation.functionSignatureOfMethodWithTrait trait method) fuel =
        .ok checked) :
    CheckedBodyHeaderWellFormed signatures
      (implementation.functionSignatureOfMethodWithTrait trait method)
      checked := by
  let signature := implementation.functionSignatureOfMethodWithTrait trait method
  let parameters : SignatureParametersWellFormed implementation.id
      implementation.parameters := {
    parameters_nodup := implementationWellFormed.parameters_nodup
    parameter_owners := implementationWellFormed.parameters_owned
    parameter_positions := implementationWellFormed.parameter_positions
  }
  have parameterTypes : TypesWellFormed
      (signatureContext signatures signature.id signature.scheme.parameters
        signature.scheme.predicates) signature.parameterTypes := by
    change TypesWellFormed
      (signatureContext signatures implementation.id implementation.parameters
        (implementation.methodAssumptions trait method)) method.parameterTypes
    exact StructuralSubstitution.TypesWellFormed.transportContext
      (source := signatureContext signatures implementation.id
        implementation.parameters
        (implementation.wherePredicates ++ method.wherePredicates))
      (target := signatureContext signatures implementation.id
        implementation.parameters (implementation.methodAssumptions trait method))
      rfl rfl rfl methodWellFormed.parameter_types
  have returnTypes : TypesWellFormed
      (signatureContext signatures signature.id signature.scheme.parameters
        signature.scheme.predicates) signature.returnTypes := by
    change TypesWellFormed
      (signatureContext signatures implementation.id implementation.parameters
        (implementation.methodAssumptions trait method)) method.returnTypes
    exact StructuralSubstitution.TypesWellFormed.transportContext
      (source := signatureContext signatures implementation.id
        implementation.parameters
        (implementation.wherePredicates ++ method.wherePredicates))
      (target := signatureContext signatures implementation.id
        implementation.parameters (implementation.methodAssumptions trait method))
      rfl rfl rfl methodWellFormed.return_types
  apply ofCheckFunctionBody parameters parameterTypes returnTypes
  · rfl
  · exact success

end CheckedBodyHeaderWellFormed

/-- Catalog facts retained by successful checking.  Loaded-program checking
requires a separate declaration-identity uniqueness premise because its input
carrier is intentionally forgeable; raw checking obtains that premise from
the loader. -/
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
  formation : Frontend.ProgramSignatureFormationValidated signatures
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
  implementation_method_catalogs : ∀ signature,
    signature ∈ signatures.implementations →
      Frontend.ImplementationSignatureMethodCatalogValidated
        signatures.traits signature
  contracts_semantic : ∀ signature, signature ∈ signatures.contracts →
    ContractSignatureWellFormed signatures signature

namespace ProgramSignatureFormationValidated

/-- Combine executable formation, canonical parameters, and callable shape
into the declarative function-signature judgment. -/
theorem functionWellFormed
    {signatures : ProgramSignatures} {signature : ProgramFunctionSignature}
    (validated : Frontend.ProgramSignatureFormationValidated signatures)
    (member : signature ∈ signatures.functions)
    (parameters : SignatureParametersWellFormed signature.id
      signature.scheme.parameters)
    (shape : signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes)) :
    FunctionSignatureWellFormed signatures signature := by
  rcases validated.functions signature member with
    ⟨parameterTypes, returnTypes, predicates⟩
  exact {
    parameters_nodup := parameters.parameters_nodup
    parameters_owned := parameters.parameter_owners
    parameter_positions := by
      simpa [TypeParameterPositionsCanonical] using parameters.parameter_positions
    parameter_names_nodup := shape.1
    parameter_types := SignatureTypesFormationValidated.typesWellFormed
      parameterTypes parameters signature.scheme.predicates
    return_types := SignatureTypesFormationValidated.typesWellFormed
      returnTypes parameters signature.scheme.predicates
    predicates := SignaturePredicatesFormationValidated.predicatesWellFormed
      predicates parameters signature.scheme.predicates
    scheme_body := shape.2
  }

/-- Combine executable constructor-payload formation with the collector's
canonical data-signature structure. -/
theorem dataWellFormed
    {signatures : ProgramSignatures} {signature : ProgramDataSignature}
    (validated : Frontend.ProgramSignatureFormationValidated signatures)
    (member : signature ∈ signatures.dataTypes)
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
  constructor_payloads := by
    intro constructor constructorMember
    exact SignatureTypesFormationValidated.typesWellFormed
      (validated.dataTypes signature member constructor constructorMember)
      parameters []
}

/-- Combine executable trait and method formation with the collector's
canonical trait-method structure. -/
theorem traitWellFormed
    {signatures : ProgramSignatures} {signature : ProgramTraitSignature}
    (validated : Frontend.ProgramSignatureFormationValidated signatures)
    (member : signature ∈ signatures.traits)
    (parameters : SignatureParametersWellFormed signature.id
      signature.parameters)
    (structural : TraitSignatureStructuralWellFormed signature) :
    TraitSignatureWellFormed signatures signature := by
  rcases validated.traits signature member with ⟨predicates, methods⟩
  exact {
    parameters_nodup := parameters.parameters_nodup
    parameters_owned := parameters.parameter_owners
    parameter_positions := by
      simpa [TypeParameterPositionsCanonical] using parameters.parameter_positions
    method_names_nodup := structural.method_names_nodup
    method_positions := structural.method_positions
    predicates := SignaturePredicatesFormationValidated.predicatesWellFormed
      predicates parameters signature.wherePredicates
    methods := by
      intro method methodMember
      rcases methods method methodMember with
        ⟨parameterTypes, returnTypes, methodPredicates⟩
      let assumptions := signature.wherePredicates ++ method.wherePredicates
      exact {
        owner := structural.method_owners method methodMember
        parameter_names_nodup :=
          structural.method_parameter_names_nodup method methodMember
        parameter_types := SignatureTypesFormationValidated.typesWellFormed
          parameterTypes parameters assumptions
        return_types := SignatureTypesFormationValidated.typesWellFormed
          returnTypes parameters assumptions
        predicates := SignaturePredicatesFormationValidated.predicatesWellFormed
          methodPredicates parameters assumptions
      }
  }

end ProgramSignatureFormationValidated

namespace ImplementationSignatureMethodCatalogValidated

/-- The executable method-catalog witness directly supplies the declarative
trait correspondence for every retained implementation method. -/
theorem semantic_method
    {signatures : ProgramSignatures}
    {implementation : ProgramImplementationSignature}
    (validated : Frontend.ImplementationSignatureMethodCatalogValidated
      signatures.traits implementation)
    {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    ∃ trait methodSignature,
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
        (ProgramPredicate.applyParameters substitution) := by
  rcases validated.trait_catalog with
    ⟨trait, traitMember, headTrait, correspondence, completeness⟩
  obtain ⟨traitMethod, traitMethodMember, traitMethodId, traitMethodName,
    parameterTypes, returnTypes, parameterComptime, returnComptime,
    predicates⟩ := correspondence method member
  exact ⟨trait, traitMethod, traitMember, headTrait, traitMethodMember,
    traitMethodId, traitMethodName, parameterTypes, returnTypes,
    parameterComptime, returnComptime, predicates⟩

/-- Selected-trait completeness transports to the declarative judgment's
arbitrary equal-headed trait entry using global trait identity uniqueness. -/
theorem semantic_methods_complete
    {signatures : ProgramSignatures}
    {implementation : ProgramImplementationSignature}
    (validated : Frontend.ImplementationSignatureMethodCatalogValidated
      signatures.traits implementation)
    (traitIds : (signatures.traits.map fun trait => trait.id).Nodup)
    {trait : ProgramTraitSignature} (traitMember : trait ∈ signatures.traits)
    (headTrait : implementation.head.trait = .declaration trait.id)
    {method : ProgramTraitMethodSignature} (methodMember : method ∈ trait.methods) :
    ∃ implementationMethod ∈ implementation.methods,
      implementationMethod.traitMethod = method.id := by
  rcases validated.trait_catalog with
    ⟨selected, selectedMember, selectedHead, correspondence, completeness⟩
  have selectedId : selected.id = trait.id := by
    have equal := selectedHead.symm.trans headTrait
    injection equal
  have selectedEq : selected = trait :=
    Frontend.trait_signature_eq_of_mem_of_id_eq traitIds
      selectedMember traitMember selectedId
  subst trait
  exact completeness method methodMember

end ImplementationSignatureMethodCatalogValidated

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

namespace ProgramSignatureFormationValidated

/-- Combine checker-derived formation and catalog facts into the declarative
implementation judgment.  Every implementation method inherits formation
from its corresponding well-formed trait method through the exact,
well-formed head substitution. -/
theorem implementationWellFormed
    {signatures : ProgramSignatures}
    {signature : ProgramImplementationSignature}
    (formation : Frontend.ProgramSignatureFormationValidated signatures)
    (member : signature ∈ signatures.implementations)
    (parameters : SignatureParametersWellFormed signature.id
      signature.parameters)
    (structural : ImplementationSignatureStructuralWellFormed signature)
    (validated : Frontend.ImplementationSignatureHeadValidated
      signatures.traits signature)
    (methodCatalog : Frontend.ImplementationSignatureMethodCatalogValidated
      signatures.traits signature)
    (traitIds :
      (signatures.traits.map fun trait => trait.id).Nodup)
    (traitParameters : ∀ trait, trait ∈ signatures.traits →
      SignatureParametersWellFormed trait.id trait.parameters)
    (traitSemantics : ∀ trait, trait ∈ signatures.traits →
      TraitSignatureWellFormed signatures trait)
    (ruleProjection : signature.implRule ∈ signatures.implRules) :
    ImplementationSignatureWellFormed signatures signature := by
  rcases formation.implementations signature member with
    ⟨headFormation, predicateFormation⟩
  have headWellFormed :=
    SignaturePredicateFormationValidated.predicateWellFormed headFormation
      parameters signature.wherePredicates
  have predicatesWellFormed :=
    SignaturePredicatesFormationValidated.predicatesWellFormed
      predicateFormation parameters signature.wherePredicates
  rcases ImplementationSignatureHeadValidated.semantic_trait_catalog validated
      headWellFormed traitIds traitParameters with
    ⟨trait, traitMember, headTrait, substitutionExact, substitutionRange,
      requiredPredicates⟩
  let substitution : TypeSystem.ParameterSubstitution :=
    trait.parameters.zip
      (signature.head.subject :: signature.head.arguments)
  change ParameterSubstitution.Exact substitution trait.parameters at substitutionExact
  change ParameterSubstitution.RangeWellFormed
    (signatureContext signatures signature.id signature.parameters
      signature.wherePredicates) substitution at substitutionRange
  refine {
    parameters_nodup := parameters.parameters_nodup
    parameters_owned := parameters.parameter_owners
    parameter_positions := by
      simpa [TypeParameterPositionsCanonical] using
        parameters.parameter_positions
    parameters_in_head :=
      ImplementationSignatureHeadValidated.semantic_parameters_in_head validated
    method_names_nodup := structural.method_names_nodup
    method_positions := structural.method_positions
    head := headWellFormed
    predicates := predicatesWellFormed
    rule_projection := ruleProjection
    trait_catalog := ⟨trait, traitMember, headTrait, substitutionExact,
      substitutionRange, requiredPredicates⟩
    methods := ?_
    methods_complete := ?_
  }
  · intro method member
    rcases ImplementationSignatureMethodCatalogValidated.semantic_method
        methodCatalog member with
      ⟨selectedTrait, traitMethod, selectedTraitMember, selectedHeadTrait,
        traitMethodMember, traitMethodId, traitMethodName, parameterTypes,
        returnTypes, parameterComptime, returnComptime, methodPredicates⟩
    have selectedTraitId : selectedTrait.id = trait.id := by
      have equal := selectedHeadTrait.symm.trans headTrait
      injection equal
    have selectedTraitEq : selectedTrait = trait :=
      Frontend.trait_signature_eq_of_mem_of_id_eq traitIds
        selectedTraitMember traitMember selectedTraitId
    subst selectedTrait
    have traitMethodWellFormed :=
      (traitSemantics trait traitMember).methods traitMethod traitMethodMember
    let targetContext :=
      signatureContext signatures signature.id signature.parameters
        (signature.wherePredicates ++ method.wherePredicates)
    have targetBinders : TypeParameterBindersWellFormed targetContext := by
      constructor
      · simpa [targetContext, signatureContext, Context.withAssumptions,
          Context.forDeclaration] using parameters.parameters_nodup
      · intro parameter parameterMember
        have member : parameter ∈ signature.parameters := by
          simpa [targetContext, signatureContext, Context.withAssumptions,
            Context.forDeclaration] using parameterMember
        have owner := parameters.parameter_owners parameter member
        simp [targetContext, signatureContext, Context.withAssumptions,
          Context.forDeclaration, owner]
    have targetRange : ParameterSubstitution.RangeWellFormed
        targetContext substitution :=
      StructuralSubstitution.ParameterSubstitution.RangeWellFormed.transportContext
        (source := signatureContext signatures signature.id
          signature.parameters signature.wherePredicates)
        (target := targetContext) rfl rfl rfl substitutionRange
    have parameterTypesWellFormed : TypesWellFormed targetContext
        (traitMethod.parameterTypes.map substitution.apply) :=
      StructuralSubstitution.TypesWellFormed.applyParametersTo substitution
        (source := signatureContext signatures trait.id trait.parameters
          (trait.wherePredicates ++ traitMethod.wherePredicates))
        (target := targetContext) substitutionExact targetRange rfl targetBinders
        traitMethodWellFormed.parameter_types
    have returnTypesWellFormed : TypesWellFormed targetContext
        (traitMethod.returnTypes.map substitution.apply) :=
      StructuralSubstitution.TypesWellFormed.applyParametersTo substitution
        (source := signatureContext signatures trait.id trait.parameters
          (trait.wherePredicates ++ traitMethod.wherePredicates))
        (target := targetContext) substitutionExact targetRange rfl targetBinders
        traitMethodWellFormed.return_types
    have predicatesWellFormed : PredicatesWellFormed targetContext
        (traitMethod.wherePredicates.map
          (ProgramPredicate.applyParameters substitution)) :=
      StructuralSubstitution.PredicatesWellFormed.applyParametersTo substitution
        (source := signatureContext signatures trait.id trait.parameters
          (trait.wherePredicates ++ traitMethod.wherePredicates))
        (target := targetContext) substitutionExact targetRange rfl targetBinders
        traitMethodWellFormed.predicates
    refine {
      owner := structural.method_owners method member
      trait_method :=
        ImplementationSignatureMethodCatalogValidated.semantic_method
          methodCatalog member
      parameter_names_nodup :=
        structural.method_parameter_names_nodup method member
      parameter_types := ?_
      return_types := ?_
      predicates := ?_
    }
    · change TypesWellFormed targetContext method.parameterTypes
      rw [parameterTypes]
      exact parameterTypesWellFormed
    · change TypesWellFormed targetContext method.returnTypes
      rw [returnTypes]
      exact returnTypesWellFormed
    · change PredicatesWellFormed targetContext method.wherePredicates
      rw [methodPredicates]
      exact predicatesWellFormed
  · intro catalogTrait method catalogTraitMember catalogHeadTrait methodMember
    exact
      ImplementationSignatureMethodCatalogValidated.semantic_methods_complete
        methodCatalog traitIds catalogTraitMember catalogHeadTrait methodMember

end ProgramSignatureFormationValidated

/-- Recover every catalog fact from successful checking of a loaded carrier
whose declaration environment has unique stable identities. -/
theorem checkedSignatureCatalogFacts_ofCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = .ok checked)
    (environmentIds :
      (loaded.environment.declarations.map fun declaration => declaration.id).Nodup) :
    CheckedSignatureCatalogFacts checked.signatures := by
  have signaturesSuccess := Frontend.checkLoadedProgram_success_signatures
    success
  have parameters :=
    Frontend.checkLoadedProgram_success_signature_parameters_wellFormed success
  refine {
    impl_rules_eq :=
      Frontend.buildProgramSignatures_success_implRules_eq signaturesSuccess
    declaration_ids := by
      simpa [signatureDeclarationIds] using
        Frontend.buildProgramSignatures_success_declaration_ids_nodup
          environmentIds signaturesSuccess
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
    constructor_ids :=
      Frontend.buildProgramSignatures_success_constructor_ids_nodup
        environmentIds signaturesSuccess
    trait_method_ids :=
      Frontend.buildProgramSignatures_success_trait_method_ids_nodup
        environmentIds signaturesSuccess
    implementation_method_ids :=
      Frontend.buildProgramSignatures_success_implementation_method_ids_nodup
        environmentIds signaturesSuccess
    parameters
    formation := Frontend.checkLoadedProgram_success_signature_formation success
    function_shapes := by
      intro signature member
      exact Frontend.checkLoadedProgram_success_function_signature_shape
        success member
    data_structures := by
      intro signature member
      exact Frontend.checkLoadedProgram_success_data_signature_structure
        success member
    trait_structures := by
      intro signature member
      exact Frontend.checkLoadedProgram_success_trait_signature_structure
        success member
    implementation_structures := by
      intro signature member
      exact Frontend.checkLoadedProgram_success_implementation_signature_structure
        success member
    implementation_heads := by
      intro signature member
      exact Frontend.checkLoadedProgram_success_implementation_head_validated
        success member
    implementation_method_catalogs := by
      intro signature member
      exact
        Frontend.checkLoadedProgram_success_implementation_method_catalog_validated
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

/-- Raw-workspace checking supplies loaded-environment identity uniqueness, so
all catalog facts follow from checker success alone. -/
theorem checkedSignatureCatalogFacts_ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked) :
    CheckedSignatureCatalogFacts checked.signatures := by
  obtain ⟨loaded, loadedSuccess, checkedSuccess⟩ :=
    Frontend.checkProgram_success_load success
  exact checkedSignatureCatalogFacts_ofCheckLoadedProgram checkedSuccess
    (Frontend.loadProgram_success_declarations_nodup loadedSuccess)

namespace CheckedSignatureCatalogFacts

/-- Forget executable bookkeeping from a complete set of checked catalog
facts, including resolved type and predicate formation. -/
theorem complete
    {signatures : ProgramSignatures}
    (checked : CheckedSignatureCatalogFacts signatures) :
    SignatureCatalogWellFormed signatures := by
  have traitSemantics : ∀ trait, trait ∈ signatures.traits →
      TraitSignatureWellFormed signatures trait := by
    intro trait member
    exact ProgramSignatureFormationValidated.traitWellFormed checked.formation
      member
      (checked.parameters.traits trait member)
      (checked.trait_structures trait member)
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
    exact ProgramSignatureFormationValidated.functionWellFormed
      checked.formation member
      (checked.parameters.functions signature member)
      (checked.function_shapes signature member)
  · intro signature member
    exact ProgramSignatureFormationValidated.dataWellFormed checked.formation
      member
      (checked.parameters.dataTypes signature member)
      (checked.data_structures signature member)
  · intro signature member
    exact traitSemantics signature member
  · intro signature member
    apply ProgramSignatureFormationValidated.implementationWellFormed
      checked.formation member
      (checked.parameters.implementations signature member)
      (checked.implementation_structures signature member)
      (checked.implementation_heads signature member)
      (checked.implementation_method_catalogs signature member)
      checked.trait_ids checked.parameters.traits traitSemantics
    rw [checked.impl_rules_eq]
    exact List.mem_map.mpr ⟨signature, member, rfl⟩

end CheckedSignatureCatalogFacts

namespace SignatureCatalogWellFormed

/-- Loaded-program checker success yields the semantic catalog invariant when
the forgeable input environment has unique declaration identities. -/
theorem ofCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = .ok checked)
    (environmentIds :
      (loaded.environment.declarations.map fun declaration => declaration.id).Nodup) :
    SignatureCatalogWellFormed checked.signatures :=
  (checkedSignatureCatalogFacts_ofCheckLoadedProgram success environmentIds).complete

/-- Raw checker success alone yields the complete semantic signature catalog
invariant. -/
theorem ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked) :
    SignatureCatalogWellFormed checked.signatures :=
  (checkedSignatureCatalogFacts_ofCheckProgram success).complete

end SignatureCatalogWellFormed

/-- Loaded checker success automatically validates every interface-level
semantic field of any retained top-level function body. -/
theorem checkedFunctionHeaderWellFormed_ofCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = .ok checked)
    {function : CheckedFunction}
    (member : function ∈ checked.functions) :
    ∃ signature, signature ∈ checked.signatures.functions ∧
      CheckedBodyHeaderWellFormed checked.signatures signature function := by
  obtain ⟨signature, signatureMember, bodySuccess⟩ :=
    Frontend.checkLoadedProgram_success_function_body success member
  have formation := Frontend.checkLoadedProgram_success_signature_formation
    success
  rcases formation.functions signature signatureMember with
    ⟨parameterFormation, returnFormation, _⟩
  have parameters :=
    (Frontend.checkLoadedProgram_success_signature_parameters_wellFormed
      success).functions signature signatureMember
  have parameterTypes :=
    Solcore.SourceSemantics.SignatureTypesFormationValidated.typesWellFormed
      parameterFormation parameters signature.scheme.predicates
  have returnTypes :=
    Solcore.SourceSemantics.SignatureTypesFormationValidated.typesWellFormed
      returnFormation parameters signature.scheme.predicates
  have schemeBody :=
    (Frontend.checkLoadedProgram_success_function_signature_shape success
      signatureMember).2
  exact ⟨signature, signatureMember,
    CheckedBodyHeaderWellFormed.ofCheckFunctionBody parameters parameterTypes
      returnTypes schemeBody bodySuccess⟩

/-- Raw checker success carries the same complete function-body header
certificate through validation and loading. -/
theorem checkedFunctionHeaderWellFormed_ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    {function : CheckedFunction}
    (member : function ∈ checked.functions) :
    ∃ signature, signature ∈ checked.signatures.functions ∧
      CheckedBodyHeaderWellFormed checked.signatures signature function := by
  obtain ⟨_, _, checkedSuccess⟩ := Frontend.checkProgram_success_load success
  exact checkedFunctionHeaderWellFormed_ofCheckLoadedProgram checkedSuccess member

/-- Loaded checker success validates the complete interface-level body header
of every implementation method once the forgeable environment's declaration
identities are known to be unique. -/
theorem checkedMethodHeaderWellFormed_ofCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = .ok checked)
    (environmentIds :
      (loaded.environment.declarations.map fun declaration => declaration.id).Nodup)
    {checkedMethod : CheckedImplementationMethod}
    (member : checkedMethod ∈ checked.methods) :
    ∃ implementation method trait,
      implementation ∈ checked.signatures.implementations ∧
        method ∈ implementation.methods ∧
          checked.signatures.trait? method.traitMethod.trait = some trait ∧
            checkedMethod.id = method.id ∧
              CheckedBodyHeaderWellFormed checked.signatures
                (implementation.functionSignatureOfMethodWithTrait trait method)
                checkedMethod.checked := by
  obtain ⟨implementation, method, trait, implementationMember, methodMember,
    traitLookup, methodId, bodySuccess⟩ :=
    Frontend.checkLoadedProgram_success_method_body success member
  have catalog := SignatureCatalogWellFormed.ofCheckLoadedProgram success
    environmentIds
  have implementationWellFormed :=
    catalog.implementations_semantic implementation implementationMember
  have methodWellFormed := implementationWellFormed.methods method methodMember
  exact ⟨implementation, method, trait, implementationMember, methodMember,
    traitLookup, methodId,
    CheckedBodyHeaderWellFormed.ofCheckImplementationMethod
      implementationWellFormed methodWellFormed bodySuccess⟩

/-- Raw checker success supplies environment identity uniqueness itself, so
every retained implementation method has a complete semantic body header. -/
theorem checkedMethodHeaderWellFormed_ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    {checkedMethod : CheckedImplementationMethod}
    (member : checkedMethod ∈ checked.methods) :
    ∃ implementation method trait,
      implementation ∈ checked.signatures.implementations ∧
        method ∈ implementation.methods ∧
          checked.signatures.trait? method.traitMethod.trait = some trait ∧
            checkedMethod.id = method.id ∧
              CheckedBodyHeaderWellFormed checked.signatures
                (implementation.functionSignatureOfMethodWithTrait trait method)
                checkedMethod.checked := by
  obtain ⟨loaded, loadedSuccess, checkedSuccess⟩ :=
    Frontend.checkProgram_success_load success
  exact checkedMethodHeaderWellFormed_ofCheckLoadedProgram checkedSuccess
    (Frontend.loadProgram_success_declarations_nodup loadedSuccess) member

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

/-- Successful loaded-program checking discharges catalog formation and exact
body identity alignment once declaration identity uniqueness is supplied.
Semantic body validity remains explicit. -/
theorem ofCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = Except.ok checked)
    (environmentIds :
      (loaded.environment.declarations.map fun declaration => declaration.id).Nodup)
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
    signatures := SignatureCatalogWellFormed.ofCheckLoadedProgram success
      environmentIds
    function_ids := functionIds
    method_ids := methodIds
    functions_valid := functionsValid
    methods_valid := methodsValid
  }

/-- Successful raw-workspace checking discharges the complete signature
catalog and exact body identity alignment.  Only semantic body validity remains
explicit. -/
theorem ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = Except.ok checked)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    CheckedProgramWellFormedConditions checked := by
  obtain ⟨functionIds, methodIds⟩ := Frontend.checkProgram_success_ids success
  exact {
    signatures := SignatureCatalogWellFormed.ofCheckProgram success
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
whole-program well-formedness once declaration identity uniqueness and body
validity are supplied. -/
theorem programWellFormedOfCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = Except.ok checked)
    (environmentIds :
      (loaded.environment.declarations.map fun declaration => declaration.id).Nodup)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    ProgramWellFormed (Program.ofChecked checked) :=
  (CheckedProgramWellFormedConditions.ofCheckLoadedProgram success environmentIds
    functionsValid methodsValid).programWellFormed

/-- Promote raw-workspace checker success directly to declarative
whole-program well-formedness once semantic body validity is supplied. -/
theorem programWellFormedOfCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = Except.ok checked)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    ProgramWellFormed (Program.ofChecked checked) :=
  (CheckedProgramWellFormedConditions.ofCheckProgram success functionsValid
    methodsValid).programWellFormed

end CheckedProgramWellFormedConditions

end Solcore.SourceSemantics
