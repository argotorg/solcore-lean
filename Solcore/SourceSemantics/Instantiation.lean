import Solcore.SourceSemantics.Context
import Solcore.Frontend.SourceInference.TypedIR

/-!
Declarative instantiation relations for source schemes and resolved
declarations.

These propositions specify what a valid instantiation is.  In particular they
do not call the source inference implementation and place no freshness policy
on the replacement types.  Fresh-variable allocation is an algorithmic choice,
whereas the relations below allow every exact substitution.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open TypeSystem

/-- A flexible-variable substitution covers precisely the listed binders,
with every binder occurring exactly once.  Substitution order is irrelevant. -/
structure ExactSubstitution
    (substitution : TypeSystem.Substitution)
    (variables : List TypeSystem.TypeVarId) : Prop where
  variables_nodup : variables.Nodup
  domain_permutation : substitution.domain.Perm variables

namespace ExactSubstitution

theorem empty : ExactSubstitution [] [] := by
  constructor <;> simp [TypeSystem.Substitution.domain]

theorem singleton (metavariable : TypeSystem.TypeVarId)
    (replacement : TypeSystem.Ty) :
    ExactSubstitution [(metavariable, replacement)] [metavariable] := by
  constructor <;> simp [TypeSystem.Substitution.domain]

theorem domain_nodup {substitution : TypeSystem.Substitution}
    {variables : List TypeSystem.TypeVarId}
    (exact : ExactSubstitution substitution variables) :
    substitution.domain.Nodup :=
  exact.domain_permutation.nodup_iff.mpr exact.variables_nodup

theorem mem_domain_iff {substitution : TypeSystem.Substitution}
    {variables : List TypeSystem.TypeVarId}
    (exact : ExactSubstitution substitution variables)
    (metavariable : TypeSystem.TypeVarId) :
    metavariable ∈ substitution.domain ↔ metavariable ∈ variables :=
  exact.domain_permutation.mem_iff

end ExactSubstitution

/-- `type` is an arbitrary exact instance of the quantified scheme. -/
inductive SchemeInstantiates (scheme : TypeSystem.Scheme)
    (type : TypeSystem.Ty) : Prop where
  | intro (substitution : TypeSystem.Substitution)
      (exact : ExactSubstitution substitution scheme.quantified)
      (result : substitution.apply scheme.body = type) :
      SchemeInstantiates scheme type

namespace SchemeInstantiates

private theorem empty_apply (type : TypeSystem.Ty) :
    TypeSystem.Substitution.apply [] type = type := by
  induction type <;>
    simp_all [TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?]

theorem mono (type : TypeSystem.Ty) :
    SchemeInstantiates (.mono type) type := by
  refine ⟨[], ExactSubstitution.empty, ?_⟩
  exact empty_apply type

theorem has_exact_substitution {scheme : TypeSystem.Scheme}
    {type : TypeSystem.Ty} (instantiates : SchemeInstantiates scheme type) :
    ∃ substitution,
      ExactSubstitution substitution scheme.quantified ∧
        substitution.apply scheme.body = type := by
  cases instantiates with
  | intro substitution exact result =>
      exact ⟨substitution, exact, result⟩

end SchemeInstantiates

namespace ParameterSubstitution

/-- Rigid-parameter domain of a source declaration substitution. -/
def domain (substitution : TypeSystem.ParameterSubstitution) :
    List TypeSystem.TypeParameterId :=
  substitution.map Prod.fst

/-- A rigid-parameter substitution covers precisely the declaration's
parameters, with every parameter occurring exactly once. -/
structure Exact (substitution : TypeSystem.ParameterSubstitution)
    (parameters : List TypeSystem.TypeParameterId) : Prop where
  parameters_nodup : parameters.Nodup
  domain_permutation : domain substitution |>.Perm parameters

/-- Recover replacement types in declaration-parameter order.  `Exact`
guarantees that the fallback branch is unreachable. -/
def orderedArguments (substitution : TypeSystem.ParameterSubstitution)
    (parameters : List TypeSystem.TypeParameterId) : List TypeSystem.Ty :=
  parameters.map fun parameter =>
    (TypeSystem.ParameterSubstitution.lookup? substitution parameter).getD
      (.parameter parameter)

theorem exact_empty : Exact [] [] := by
  constructor <;> simp [domain]

theorem exact_singleton (parameter : TypeSystem.TypeParameterId)
    (replacement : TypeSystem.Ty) :
    Exact [(parameter, replacement)] [parameter] := by
  constructor <;> simp [domain]

theorem Exact.domain_nodup {substitution : TypeSystem.ParameterSubstitution}
    {parameters : List TypeSystem.TypeParameterId}
    (exact : Exact substitution parameters) :
    (domain substitution).Nodup :=
  exact.domain_permutation.nodup_iff.mpr exact.parameters_nodup

theorem Exact.mem_domain_iff {substitution : TypeSystem.ParameterSubstitution}
    {parameters : List TypeSystem.TypeParameterId}
    (exact : Exact substitution parameters)
    (parameter : TypeSystem.TypeParameterId) :
    parameter ∈ domain substitution ↔ parameter ∈ parameters :=
  exact.domain_permutation.mem_iff

end ParameterSubstitution

namespace DeclarationInstantiation

/-- A typed-IR function occurrence is exactly an instance of one cataloged
function signature.  Staging metadata is copied, not inferred from types. -/
inductive Valid (context : Context)
    (instantiation : Frontend.SourceInference.DeclarationInstantiation) : Prop where
  | intro (signature : Frontend.ProgramFunctionSignature)
      (signature_mem : signature ∈ context.signatures.functions)
      (declaration_eq : instantiation.declaration = signature.id)
      (substitution_exact :
        ParameterSubstitution.Exact instantiation.parameterSubstitution
          signature.scheme.parameters)
      (type_eq :
        instantiation.type =
          TypeSystem.ParameterSubstitution.apply instantiation.parameterSubstitution
            signature.scheme.body)
      (predicates_eq :
        instantiation.predicates = signature.scheme.predicates.map
          (Frontend.ProgramPredicate.applyParameters
            instantiation.parameterSubstitution))
      (parameterComptime_eq :
        instantiation.parameterComptime = signature.parameterComptime)
      (returnComptime_eq :
        instantiation.returnComptime = signature.returnComptime) :
      Valid context instantiation

theorem Valid.signature_id {context : Context}
    {instantiation : Frontend.SourceInference.DeclarationInstantiation}
    (valid : Valid context instantiation) :
    ∃ signature ∈ context.signatures.functions,
      signature.id = instantiation.declaration := by
  cases valid with
  | intro signature signature_mem declaration_eq =>
      exact ⟨signature, signature_mem, declaration_eq.symm⟩

end DeclarationInstantiation

namespace DataConstructorInstantiation

/-- A typed-IR constructor occurrence is exactly an instance of one constructor
from one cataloged data declaration. -/
inductive Valid (context : Context)
    (instantiation : Frontend.SourceInference.DataConstructorInstantiation) : Prop where
  | intro (dataType : Frontend.ProgramDataSignature)
      (signature : Frontend.ProgramDataConstructorSignature)
      (dataType_mem : dataType ∈ context.signatures.dataTypes)
      (signature_mem : signature ∈ dataType.constructors)
      (signature_owner : signature.id.dataType = dataType.id)
      (constructor_eq : instantiation.constructor = signature.id)
      (substitution_exact :
        ParameterSubstitution.Exact instantiation.parameterSubstitution
          dataType.parameters)
      (payloadTypes_eq :
        instantiation.payloadTypes = signature.payloadTypes.map
          (TypeSystem.ParameterSubstitution.apply instantiation.parameterSubstitution))
      (resultType_eq :
        instantiation.resultType = TypeSystem.Ty.nominal dataType.id
          (ParameterSubstitution.orderedArguments
            instantiation.parameterSubstitution dataType.parameters)) :
      Valid context instantiation

theorem Valid.signature_id {context : Context}
    {instantiation : Frontend.SourceInference.DataConstructorInstantiation}
    (valid : Valid context instantiation) :
    ∃ dataType ∈ context.signatures.dataTypes,
      ∃ signature ∈ dataType.constructors,
        signature.id = instantiation.constructor := by
  cases valid with
  | intro dataType signature dataType_mem signature_mem _ constructor_eq =>
      exact ⟨dataType, dataType_mem, signature, signature_mem,
        constructor_eq.symm⟩

end DataConstructorInstantiation

private def exampleVariable : TypeSystem.TypeVarId := ⟨0⟩

example : SchemeInstantiates
    { quantified := [exampleVariable], body := .variable exampleVariable }
    .word := by
  refine ⟨[(exampleVariable, .word)], ?_, rfl⟩
  exact ExactSubstitution.singleton exampleVariable .word

example (parameter : TypeSystem.TypeParameterId) :
    ParameterSubstitution.Exact [(parameter, .bool)] [parameter] :=
  ParameterSubstitution.exact_singleton parameter .bool

end Solcore.SourceSemantics
