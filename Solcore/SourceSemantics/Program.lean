import Solcore.SourceSemantics.Graph
import Solcore.SourceSemantics.Ownership
import Solcore.SourceSemantics.Static

/-!
Declarative resolved-source declaration bodies and whole programs.

The carriers in this file are forgeable semantic inputs.  Their validity is
defined entirely by the judgments below, not by possession of a frontend
checker result.  Implementation methods are first-class bodies as well as
top-level functions, so trait evidence has a source body to invoke.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A resolved body together with all retained metadata needed by static and
dynamic source semantics. -/
structure BodyDefinition where
  owner : Resolved.DeclarationId
  type : TypeSystem.Ty
  resultType : TypeSystem.Ty
  returnComptime : Bool := false
  solvedRequirements : List SolvedRequirement
  source : TypedSource
  deriving Repr

namespace BodyDefinition

/-- Forget the algorithmic substitution from a forgeable checked-function
carrier while retaining all proof-relevant resolved source data. -/
def ofChecked (function : CheckedFunction) : BodyDefinition := {
  owner := function.declaration
  type := function.type
  resultType := function.inferredBodyType
  returnComptime := function.returnComptime
  solvedRequirements := function.solvedRequirements
  source := function.typedBody
}

end BodyDefinition

/-- A top-level function definition. -/
structure FunctionDefinition where
  body : BodyDefinition
  deriving Repr

/-- A cataloged implementation method with an independently validated body. -/
structure MethodDefinition where
  id : ProgramImplMethodId
  body : BodyDefinition
  deriving Repr

/-- Semantic whole-program body catalog. -/
structure Program where
  signatures : ProgramSignatures
  functions : List FunctionDefinition
  methods : List MethodDefinition
  deriving Repr

/-- Base assumptions for one generic declaration body. -/
def declarationContext (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (assumptions : List ProgramPredicate)
    (requirements : List SolvedRequirement) : Context :=
  (((((Context.ofSignatures signatures).forDeclaration owner parameters)
    |>.withAssumptions assumptions)
    |>.withSolvedRequirements requirements)
    |>.withResidualTypeVariables)

/-- One solved row is valid for a whole source either as ordinary evidence in
the declaration context or as an assumption template with a primary use
scoped by its owning generalized initializer.  `RequirementOwnership`
separately makes the primary use unique at the body boundary. -/
inductive ScopedRequirementEntryValid (context : Context)
    (source : TypedSource) (row : SolvedRequirement) : Prop where
  | ordinary
      (not_template : row.id ∉ sourceLocalSchemeTemplateIds source)
      (valid : SolvedRequirementValid context row) :
      ScopedRequirementEntryValid context source row
  | template
      (scopeProof : LocalSchemeTemplateRowScoped source row) :
      ScopedRequirementEntryValid context source row

/-- A whole-body requirement ledger separates declaration-wide evidence from
qualified local-scheme templates.  Template identities are source-unique,
each ledger row obeys its corresponding validation mode, and every declared
template owner has a retained row. -/
structure ScopedRequirementLedgerWellFormed (context : Context)
    (source : TypedSource) : Prop where
  idsUnique : RequirementIdsUnique context
  templateOwnership : LocalSchemeTemplateOwnership source
  entriesValid :
    ∀ row, row ∈ context.solvedRequirements →
      ScopedRequirementEntryValid context source row
  templatesComplete :
    ∀ owner, ContainsLocalSchemeTemplate source owner →
      ∃ row, row ∈ context.solvedRequirements ∧
        row.id = owner.requirement.templateRequirement

/-- The part of a solved-requirement ledger that must survive at runtime.
Stable identity uniqueness supports dispatch agreement.  Only
implementation-backed rows need independent semantic validity: assumption
rows are justified by the evidence environment at their use site, while
qualified local-scheme templates are validated at the static body boundary. -/
structure RuntimeRequirementLedgerValid (context : Context) : Prop where
  idsUnique : RequirementIdsUnique context
  implementationEntries :
    ∀ row evidence, row ∈ context.solvedRequirements →
      row.evidence = .implementation evidence →
        SolvedRequirementValid context row

namespace ScopedRequirementLedgerWellFormed

/-- A non-template ledger row retains ordinary declaration-context evidence
validity. -/
theorem ordinary_valid
    {context : Context} {source : TypedSource}
    (wellFormed : ScopedRequirementLedgerWellFormed context source)
    {row : SolvedRequirement}
    (member : row ∈ context.solvedRequirements)
    (notTemplate : row.id ∉ sourceLocalSchemeTemplateIds source) :
    SolvedRequirementValid context row := by
  cases wellFormed.entriesValid row member with
  | ordinary _ valid => exact valid
  | template scopeProof =>
      exact False.elim (notTemplate scopeProof.template_id_mem)

/-- A ledger row whose identity is owned by a local template has an exact
initializer-scoped primary use. -/
theorem template_scoped
    {context : Context} {source : TypedSource}
    (wellFormed : ScopedRequirementLedgerWellFormed context source)
    {row : SolvedRequirement}
    (member : row ∈ context.solvedRequirements)
    (templateId : row.id ∈ sourceLocalSchemeTemplateIds source) :
    LocalSchemeTemplateRowScoped source row := by
  cases wellFormed.entriesValid row member with
  | ordinary notTemplate _ => exact False.elim (notTemplate templateId)
  | template scopeProof => exact scopeProof

/-- Recover the exact scoped ledger row promised for one source template
owner. -/
theorem template_row
    {context : Context} {source : TypedSource}
    (wellFormed : ScopedRequirementLedgerWellFormed context source)
    {owner : LocalSchemeTemplateOwner}
    (contains : ContainsLocalSchemeTemplate source owner) :
    ∃ row, row ∈ context.solvedRequirements ∧
      row.id = owner.requirement.templateRequirement ∧
      LocalSchemeTemplateRowScoped source row := by
  rcases wellFormed.templatesComplete owner contains with
    ⟨row, member, idEq⟩
  have templateId : row.id ∈ sourceLocalSchemeTemplateIds source := by
    rw [idEq]
    exact sourceLocalSchemeTemplateIds_mem_iff.mpr
      ⟨owner, contains, rfl⟩
  exact ⟨row, member, idEq, wellFormed.template_scoped member templateId⟩

/-- An ordinary well-formed ledger is a scoped ledger whenever the source
declares no qualified local templates. -/
theorem ofRequirementLedger
    {context : Context} {source : TypedSource}
    (wellFormed : RequirementLedgerWellFormed context)
    (templatesEmpty : sourceLocalSchemeTemplateIds source = []) :
    ScopedRequirementLedgerWellFormed context source := by
  constructor
  · exact wellFormed.idsUnique
  · constructor
    simp [templatesEmpty]
  · intro row member
    exact ScopedRequirementEntryValid.ordinary (by simp [templatesEmpty])
      (wellFormed.entriesValid row member)
  · intro owner contains
    have member : owner.requirement.templateRequirement ∈
        sourceLocalSchemeTemplateIds source :=
      sourceLocalSchemeTemplateIds_mem_iff.mpr ⟨owner, contains, rfl⟩
    simp [templatesEmpty] at member

/-- Forget source-scoped template bookkeeping after static validation while
retaining exactly the requirement facts needed by execution and flexible
closure materialization. -/
theorem toRuntime
    {context : Context} {source : TypedSource}
    (wellFormed : ScopedRequirementLedgerWellFormed context source) :
    RuntimeRequirementLedgerValid context := by
  refine {
    idsUnique := wellFormed.idsUnique
    implementationEntries := ?_
  }
  intro row evidence member implementationEq
  cases wellFormed.entriesValid row member with
  | ordinary _ valid => exact valid
  | template rowScoped =>
      rcases rowScoped.exact_owner with
        ⟨owner, occurrence, contains, idEq, predicateEq, evidenceEq,
          occurs, scope⟩
      have impossible :
          PredicateEvidence.assumption owner.requirement.predicate =
            .implementation evidence :=
        evidenceEq.symm.trans implementationEq
      cases impossible

end ScopedRequirementLedgerWellFormed

namespace RuntimeRequirementLedgerValid

/-- Entering a generalized local initializer preserves the runtime ledger.
The ledger rows and their stable identities are unchanged, while retained
implementation evidence remains valid after the initializer's qualified
predicates are appended to the available assumptions. -/
theorem localSchemeInitializer
    {context : Context} {binder : TypedBinder}
    (valid : RuntimeRequirementLedgerValid context) :
    RuntimeRequirementLedgerValid
      (localSchemeInitializerContext context binder) := by
  refine {
    idsUnique := ?_
    implementationEntries := ?_
  }
  · simpa [RequirementIdsUnique, localSchemeInitializerContext,
      Context.withTypeVariables, Context.withAssumptions] using valid.idsUnique
  · intro row evidence member implementationEq
    have sourceMember : row ∈ context.solvedRequirements := by
      simpa [localSchemeInitializerContext, Context.withTypeVariables,
        Context.withAssumptions] using member
    cases valid.implementationEntries row evidence sourceMember
        implementationEq with
    | intro evidenceValid =>
        exact .intro (evidenceValid.weakenAssumptions (by
          intro predicate predicateMember
          change predicate ∈ context.assumptions ++ _
          exact List.mem_append_left _ predicateMember))

end RuntimeRequirementLedgerValid

/-- Pointwise closed type well-formedness. -/
def TypesWellFormed (context : Context) (types : List TypeSystem.Ty) : Prop :=
  ∀ type, type ∈ types → TypeWellFormed context type

/-- Stable type-parameter indices agree with their source-order positions. -/
def TypeParameterPositionsCanonical
    (parameters : List TypeSystem.TypeParameterId) : Prop :=
  ∀ index : Fin parameters.length,
    (parameters.get index).index = index.val

/-- All source declaration categories share the same resolved identity space.
This combined projection prevents a forged catalog from assigning one
declaration identity to (for example) both a function and a trait. -/
def signatureDeclarationIds (signatures : ProgramSignatures) :
    List Resolved.DeclarationId :=
  signatures.functions.map (fun signature => signature.id) ++
    signatures.dataTypes.map (fun signature => signature.id) ++
    signatures.traits.map (fun signature => signature.id) ++
    signatures.implementations.map (fun signature => signature.id)

/-- The declarative type context used to validate one catalog signature. -/
def signatureContext (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (assumptions : List ProgramPredicate := []) : Context :=
  ((Context.ofSignatures signatures).forDeclaration owner parameters)
    |>.withAssumptions assumptions

/-- A top-level function signature is internally closed and its redundant
callable projections agree exactly. -/
structure FunctionSignatureWellFormed (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) : Prop where
  parameters_nodup : signature.scheme.parameters.Nodup
  parameters_owned : ∀ parameter, parameter ∈ signature.scheme.parameters →
    parameter.owner = signature.id
  parameter_positions :
    TypeParameterPositionsCanonical signature.scheme.parameters
  parameter_names_nodup : signature.parameterNames.Nodup
  parameter_types : TypesWellFormed
    (signatureContext signatures signature.id signature.scheme.parameters
      signature.scheme.predicates) signature.parameterTypes
  return_types : TypesWellFormed
    (signatureContext signatures signature.id signature.scheme.parameters
      signature.scheme.predicates) signature.returnTypes
  predicates : PredicatesWellFormed
    (signatureContext signatures signature.id signature.scheme.parameters
      signature.scheme.predicates) signature.scheme.predicates
  scheme_body : signature.scheme.body = .function
    (TypeSystem.Ty.productMany signature.parameterTypes)
    (TypeSystem.Ty.productMany signature.returnTypes)

/-- A nominal data signature binds all constructor payload types in the data
declaration's rigid parameter scope. -/
structure DataSignatureWellFormed (signatures : ProgramSignatures)
    (signature : ProgramDataSignature) : Prop where
  parameters_nodup : signature.parameters.Nodup
  parameters_owned : ∀ parameter, parameter ∈ signature.parameters →
    parameter.owner = signature.id
  parameter_positions : TypeParameterPositionsCanonical signature.parameters
  constructor_names_nodup :
    (signature.constructors.map fun constructor => constructor.name).Nodup
  constructor_owners : ∀ constructor, constructor ∈ signature.constructors →
    constructor.id.dataType = signature.id
  constructor_positions : ∀ index : Fin signature.constructors.length,
    (signature.constructors.get index).id.constructorIndex = index.val
  constructor_payloads : ∀ constructor,
    constructor ∈ signature.constructors →
      TypesWellFormed
        (signatureContext signatures signature.id signature.parameters)
        constructor.payloadTypes

/-- One trait method is closed in the enclosing trait's rigid scope. -/
structure TraitMethodSignatureWellFormed (signatures : ProgramSignatures)
    (trait : ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) : Prop where
  owner : method.id.trait = trait.id
  parameter_names_nodup : method.parameterNames.Nodup
  parameter_types : TypesWellFormed
    (signatureContext signatures trait.id trait.parameters
      (trait.wherePredicates ++ method.wherePredicates)) method.parameterTypes
  return_types : TypesWellFormed
    (signatureContext signatures trait.id trait.parameters
      (trait.wherePredicates ++ method.wherePredicates)) method.returnTypes
  predicates : PredicatesWellFormed
    (signatureContext signatures trait.id trait.parameters
      (trait.wherePredicates ++ method.wherePredicates)) method.wherePredicates

/-- A trait signature validates its declaration predicates and every method. -/
structure TraitSignatureWellFormed (signatures : ProgramSignatures)
    (signature : ProgramTraitSignature) : Prop where
  parameters_nodup : signature.parameters.Nodup
  parameters_owned : ∀ parameter, parameter ∈ signature.parameters →
    parameter.owner = signature.id
  parameter_positions : TypeParameterPositionsCanonical signature.parameters
  method_names_nodup : (signature.methods.map fun method => method.name).Nodup
  method_positions : ∀ index : Fin signature.methods.length,
    (signature.methods.get index).id.methodIndex = index.val
  predicates : PredicatesWellFormed
    (signatureContext signatures signature.id signature.parameters
      signature.wherePredicates) signature.wherePredicates
  methods : ∀ method, method ∈ signature.methods →
    TraitMethodSignatureWellFormed signatures signature method

/-- One implementation method has a closed signature in the implementation's
rigid scope and names a cataloged method of the implemented trait. -/
structure ImplMethodSignatureWellFormed (signatures : ProgramSignatures)
    (implementation : ProgramImplementationSignature)
    (method : ProgramImplMethodSignature) : Prop where
  owner : method.id.implementation = implementation.id
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
  parameter_names_nodup : method.parameterNames.Nodup
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

/-- A source implementation is a closed trait rule with a complete,
name-unique method signature catalog. -/
structure ImplementationSignatureWellFormed (signatures : ProgramSignatures)
    (signature : ProgramImplementationSignature) : Prop where
  parameters_nodup : signature.parameters.Nodup
  parameters_owned : ∀ parameter, parameter ∈ signature.parameters →
    parameter.owner = signature.id
  parameter_positions : TypeParameterPositionsCanonical signature.parameters
  parameters_in_head : ∀ parameter, parameter ∈ signature.parameters →
    TypeParameterOccursInPredicate parameter signature.head
  method_names_nodup : (signature.methods.map fun method => method.name).Nodup
  method_positions : ∀ index : Fin signature.methods.length,
    (signature.methods.get index).id.methodIndex = index.val
  head : PredicateWellFormed
    (signatureContext signatures signature.id signature.parameters
      signature.wherePredicates) signature.head
  predicates : PredicatesWellFormed
    (signatureContext signatures signature.id signature.parameters
      signature.wherePredicates) signature.wherePredicates
  rule_projection : signature.implRule ∈ signatures.implRules
  trait_catalog : ∃ trait ∈ signatures.traits,
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
        predicate ∈ signature.wherePredicates
  methods : ∀ method, method ∈ signature.methods →
    ImplMethodSignatureWellFormed signatures signature method
  methods_complete : ∀ trait method,
    trait ∈ signatures.traits →
    signature.head.trait = .declaration trait.id →
    method ∈ trait.methods →
    ∃ implementationMethod ∈ signature.methods,
      implementationMethod.traitMethod = method.id

/-- A generic body implements one exact callable signature. -/
inductive BodyDefinitionHasType
    (signatures : ProgramSignatures)
    (parameters : List TypeSystem.TypeParameterId)
    (assumptions : List ProgramPredicate)
    (parameterNames : List String)
    (parameterTypes : List TypeSystem.Ty)
    (parameterComptime : List Bool)
    (returnTypes : List TypeSystem.Ty)
    (returnComptime : Bool)
    (definition : BodyDefinition)
    (facts : BodyFacts) : Prop where
  | intro
      {lexicalContext : Context}
      (source_owner : definition.source.owner = definition.owner)
      (parameter_binders : TypeParameterBindersWellFormed
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements))
      (parameter_types_well_formed : TypesWellFormed
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements) parameterTypes)
      (return_types_well_formed : TypesWellFormed
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements) returnTypes)
      (callable_type_eq : definition.type = .function
        (TypeSystem.Ty.productMany parameterTypes)
        (TypeSystem.Ty.productMany returnTypes))
      (result_type_eq :
        definition.resultType = TypeSystem.Ty.productMany returnTypes)
      (return_comptime_eq : definition.returnComptime = returnComptime)
      (input_names_eq :
        definition.source.inputs.map (fun binder => binder.name) = parameterNames)
      (input_comptime_eq :
        definition.source.inputs.map (fun binder => binder.comptime) =
          parameterComptime)
      (inputs_extend : MonoBindersExtend definition.owner
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements)
        definition.source.inputs parameterTypes lexicalContext)
      (graph_closed : OccurrenceGraphClosed definition.source)
      (local_ownership : LocalIdentityOwnership definition.source)
      (requirement_ledger : ScopedRequirementLedgerWellFormed
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements) definition.source)
      (requirement_ownership : RequirementOwnership
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements) definition.source)
      (body_type : BodyHasType definition.source lexicalContext
        (TypeSystem.Ty.productMany returnTypes) facts)
      (body_annotation_eq : facts.type = TypeSystem.Ty.productMany returnTypes) :
      BodyDefinitionHasType signatures parameters assumptions parameterNames
        parameterTypes parameterComptime returnTypes returnComptime definition facts

/-- Exact generic trait assumptions available to an implementation method. -/
def methodAssumptions (trait : ProgramTraitSignature)
    (implementation : ProgramImplementationSignature)
    (method : ProgramImplMethodSignature) : List ProgramPredicate :=
  implementation.methodAssumptions trait method

namespace FunctionDefinition

/-- One function definition implements one catalog entry. -/
inductive Valid (signatures : ProgramSignatures)
    (definition : FunctionDefinition) : Prop where
  | intro
      {signature : ProgramFunctionSignature} {facts : BodyFacts}
      (signature_mem : signature ∈ signatures.functions)
      (owner_eq : definition.body.owner = signature.id)
      (body_valid : BodyDefinitionHasType signatures signature.scheme.parameters
        signature.scheme.predicates signature.parameterNames
        signature.parameterTypes signature.parameterComptime signature.returnTypes
        signature.returnComptime definition.body facts) :
      Valid signatures definition

end FunctionDefinition

namespace MethodDefinition

/-- One implementation-method body implements its cataloged method and is
typed under trait-, implementation-, and method-level generic assumptions. -/
inductive Valid (signatures : ProgramSignatures)
    (definition : MethodDefinition) : Prop where
  | intro
      {implementation : ProgramImplementationSignature}
      {method : ProgramImplMethodSignature}
      {trait : ProgramTraitSignature}
      {trait_method : ProgramTraitMethodSignature}
      {facts : BodyFacts}
      (implementation_mem : implementation ∈ signatures.implementations)
      (method_mem : method ∈ implementation.methods)
      (method_id_eq : definition.id = method.id)
      (method_owner : method.id.implementation = implementation.id)
      (trait_mem : trait ∈ signatures.traits)
      (trait_method_mem : trait_method ∈ trait.methods)
      (trait_method_id_eq : method.traitMethod = trait_method.id)
      (trait_owner : trait_method.id.trait = trait.id)
      (owner_eq : definition.body.owner = implementation.id)
      (body_valid : BodyDefinitionHasType signatures implementation.parameters
        (methodAssumptions trait implementation method)
        method.parameterNames method.parameterTypes method.parameterComptime
        method.returnTypes method.returnComptime definition.body facts) :
      Valid signatures definition

end MethodDefinition

/-- Stable identity uniqueness and ownership for the whole signature catalog. -/
structure SignatureCatalogWellFormed (signatures : ProgramSignatures) : Prop where
  impl_rules_eq : signatures.implRules =
    signatures.implementations.map ProgramImplementationSignature.implRule
  declaration_ids : (signatureDeclarationIds signatures).Nodup
  function_ids : (signatures.functions.map fun signature => signature.id).Nodup
  data_ids : (signatures.dataTypes.map fun signature => signature.id).Nodup
  trait_ids : (signatures.traits.map fun signature => signature.id).Nodup
  implementation_ids :
    (signatures.implementations.map fun signature => signature.id).Nodup
  constructor_ids :
    (signatures.dataTypes.flatMap fun signature =>
      signature.constructors.map fun constructor => constructor.id).Nodup
  trait_method_ids :
    (signatures.traits.flatMap fun signature =>
      signature.methods.map fun method => method.id).Nodup
  implementation_method_ids :
    (signatures.implementations.flatMap fun signature =>
      signature.methods.map fun method => method.id).Nodup
  function_parameters : ∀ signature, signature ∈ signatures.functions →
    signature.scheme.parameters.Nodup ∧
      ∀ parameter, parameter ∈ signature.scheme.parameters →
        parameter.owner = signature.id
  data_parameters : ∀ signature, signature ∈ signatures.dataTypes →
    signature.parameters.Nodup ∧
      ∀ parameter, parameter ∈ signature.parameters →
        parameter.owner = signature.id
  trait_parameters : ∀ signature, signature ∈ signatures.traits →
    signature.parameters.Nodup ∧
      ∀ parameter, parameter ∈ signature.parameters →
        parameter.owner = signature.id
  implementation_parameters :
    ∀ signature, signature ∈ signatures.implementations →
      signature.parameters.Nodup ∧
        ∀ parameter, parameter ∈ signature.parameters →
          parameter.owner = signature.id
  functions_semantic : ∀ signature, signature ∈ signatures.functions →
    FunctionSignatureWellFormed signatures signature
  data_semantic : ∀ signature, signature ∈ signatures.dataTypes →
    DataSignatureWellFormed signatures signature
  traits_semantic : ∀ signature, signature ∈ signatures.traits →
    TraitSignatureWellFormed signatures signature
  implementations_semantic :
    ∀ signature, signature ∈ signatures.implementations →
      ImplementationSignatureWellFormed signatures signature

/-- Every cataloged function and implementation method has exactly one valid
semantic body, with no extra body identities. -/
structure ProgramWellFormed (program : Program) : Prop where
  signatures : SignatureCatalogWellFormed program.signatures
  function_ids : (program.functions.map fun definition =>
    definition.body.owner).Nodup
  method_ids : (program.methods.map fun definition => definition.id).Nodup
  functions_valid : ∀ definition, definition ∈ program.functions →
    FunctionDefinition.Valid program.signatures definition
  methods_valid : ∀ definition, definition ∈ program.methods →
    MethodDefinition.Valid program.signatures definition
  functions_complete : ∀ signature, signature ∈ program.signatures.functions →
    ∃ definition ∈ program.functions, definition.body.owner = signature.id
  methods_complete :
    ∀ implementation, implementation ∈ program.signatures.implementations →
      ∀ method, method ∈ implementation.methods →
        ∃ definition ∈ program.methods, definition.id = method.id

end Solcore.SourceSemantics
