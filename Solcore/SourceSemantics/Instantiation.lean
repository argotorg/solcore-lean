import Solcore.SourceSemantics.Types
import Solcore.Frontend.SourceInference.TypedIR
import Solcore.Frontend.SourceInference.Types

/-!
# Instantiation and structural substitution

Exact substitutions, scheme instantiation and the substitution of typed source. Main declarations:
`ExactSubstitution`, `SchemeInstantiates`, `SchemeInstantiatesAt`, `SubstitutionRangeWellFormed`,
`StructuralSubstitution.applyScheme`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Instantiation
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

/-- Every replacement in a flexible substitution is a closed, meaningful
type in the use-site context.  Exact domains alone do not prevent a forged
substitution from hiding free metavariables or recovery types in an unused
range entry. -/
def SubstitutionRangeWellFormed (context : Context)
    (substitution : TypeSystem.Substitution) : Prop :=
  ∀ metavariable replacement,
    (metavariable, replacement) ∈ substitution →
      TypeWellFormed context replacement

/-- Every replacement in a flexible substitution is meaningful at the use
site.  Unlike `SubstitutionRangeWellFormed`, this permits both the lexical
variables installed while checking a generalized initializer and body-wide
residual inference variables retained by the frontend. -/
def SubstitutionRangeAdmissible (context : Context)
    (substitution : TypeSystem.Substitution) : Prop :=
  ∀ metavariable replacement,
    (metavariable, replacement) ∈ substitution →
      TypeAdmissible context replacement

theorem SubstitutionRangeWellFormed.toAdmissible
    {context : Context} {substitution : TypeSystem.Substitution}
    (range : SubstitutionRangeWellFormed context substitution) :
    SubstitutionRangeAdmissible context substitution := by
  intro metavariable replacement member
  exact TypeAdmissible.ofWellFormed (range metavariable replacement member)

/-- Flexible range validity recovers the closed range judgment when both the
lexical and residual flexible-variable scopes are closed. -/
theorem SubstitutionRangeAdmissible.toWellFormed
    {context : Context} {substitution : TypeSystem.Substitution}
    (range : SubstitutionRangeAdmissible context substitution)
    (typeVariables_eq : context.typeVariables = [])
    (residualTypeVariables_eq : context.residualTypeVariables = false) :
    SubstitutionRangeWellFormed context substitution := by
  intro metavariable replacement member
  exact (range metavariable replacement member).toWellFormed typeVariables_eq
    residualTypeVariables_eq

/-- `type` is an arbitrary exact instance of the quantified scheme. -/
inductive SchemeInstantiates (scheme : TypeSystem.Scheme)
    (type : TypeSystem.Ty) : Prop where
  | intro (substitution : TypeSystem.Substitution)
      (exact : ExactSubstitution substitution scheme.quantified)
      (result : substitution.apply scheme.body = type) :
      SchemeInstantiates scheme type

namespace SchemeInstantiates

theorem empty_apply (type : TypeSystem.Ty) :
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

/-- The executable TypeSystem matcher emits a witness for the declarative
rank-1 instantiation relation. -/
theorem of_matchInstance?
    {scheme : TypeSystem.Scheme} {type : TypeSystem.Ty}
    {substitution : TypeSystem.Substitution}
    (matched : scheme.matchInstance? type = some substitution) :
    SchemeInstantiates scheme type := by
  obtain ⟨quantifiedUnique, domainExact, applies⟩ :=
    TypeSystem.Scheme.matchInstance?_sound matched
  exact .intro substitution {
    variables_nodup := quantifiedUnique
    domain_permutation := by rw [domainExact]
  } applies

end SchemeInstantiates

/-- A use-site-valid scheme instance.  Besides exact domain coverage, every
replacement is meaningful in the caller's rigid and admissible flexible scope,
and the quantified scheme itself is well formed there.  This closes the
otherwise invisible range entries of unused quantified variables. -/
inductive SchemeInstantiatesAt (context : Context)
    (scheme : TypeSystem.Scheme) (type : TypeSystem.Ty) : Prop where
  | intro
      (scheme_well_formed : SchemeWellFormed context scheme)
      (substitution : TypeSystem.Substitution)
      (exact : ExactSubstitution substitution scheme.quantified)
      (range_well_formed :
        SubstitutionRangeAdmissible context substitution)
      (result : substitution.apply scheme.body = type) :
      SchemeInstantiatesAt context scheme type

namespace SchemeInstantiatesAt

theorem toSchemeInstantiates
    {context : Context} {scheme : TypeSystem.Scheme} {type : TypeSystem.Ty}
    (instantiates : SchemeInstantiatesAt context scheme type) :
    SchemeInstantiates scheme type := by
  cases instantiates with
  | intro _ substitution exact _ result =>
      exact .intro substitution exact result

/-- A successful executable match becomes a use-site-valid instance once the
scheme and every recovered replacement are admissible in that context. -/
theorem of_matchInstance?
    {context : Context} {scheme : TypeSystem.Scheme} {type : TypeSystem.Ty}
    {substitution : TypeSystem.Substitution}
    (schemeWellFormed : SchemeWellFormed context scheme)
    (rangeAdmissible : SubstitutionRangeAdmissible context substitution)
    (matched : scheme.matchInstance? type = some substitution) :
    SchemeInstantiatesAt context scheme type := by
  obtain ⟨quantifiedUnique, domainExact, applies⟩ :=
    TypeSystem.Scheme.matchInstance?_sound matched
  exact .intro schemeWellFormed substitution {
    variables_nodup := quantifiedUnique
    domain_permutation := by rw [domainExact]
  } rangeAdmissible applies

/-- Canonical frontend instantiation is a valid semantic scheme instance in
a body whose residual inference-variable scope remains open.  The executable
allocator chooses fresh flexible variables; residual scope admits precisely
those generated range entries at their retained occurrence. -/
theorem of_instantiateWithSubstitution
    {context : Context} {scheme : TypeSystem.Scheme}
    (schemeWellFormed : SchemeWellFormed context scheme)
    (residual : context.residualTypeVariables = true)
    (next : Nat) :
    SchemeInstantiatesAt context scheme
      (scheme.instantiateWithSubstitution next).body := by
  refine .intro schemeWellFormed
    (scheme.instantiateWithSubstitution next).substitution {
      variables_nodup := schemeWellFormed.quantified_nodup
      domain_permutation :=
        scheme.instantiateWithSubstitution_substitution_domain_permutation next
          schemeWellFormed.quantified_nodup
    } ?_ rfl
  intro metavariable replacement member
  obtain ⟨fresh, rfl, _, _⟩ :=
    scheme.instantiateWithSubstitution_substitution_range_fresh next member
  exact TypeAdmissible.variableOfResidual schemeWellFormed.binders residual fresh

/-- Admissible flexible variables may occur in a monomorphic local while the
initializer of an enclosing generalized binding is checked or while a body
retains residual inference variables. -/
theorem monoAdmissible {context : Context} {type : TypeSystem.Ty}
    (admissible : TypeAdmissible context type) :
    SchemeInstantiatesAt context (.mono type) type := by
  refine .intro (SchemeWellFormed.monoAdmissible admissible) []
    ExactSubstitution.empty ?_ ?_
  · intro metavariable replacement member
    simp at member
  · exact SchemeInstantiates.empty_apply type

theorem mono {context : Context} {type : TypeSystem.Ty}
    (wellFormed : TypeWellFormed context type) :
    SchemeInstantiatesAt context (.mono type) type :=
  monoAdmissible (TypeAdmissible.ofWellFormed wellFormed)

end SchemeInstantiatesAt

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

/-- Every rigid-parameter replacement is closed and meaningful in the
use-site context.  This is deliberately separate from `Exact`, whose domain
property is context independent. -/
def RangeWellFormed (context : Context)
    (substitution : TypeSystem.ParameterSubstitution) : Prop :=
  ∀ parameter replacement,
    (parameter, replacement) ∈ substitution →
      TypeWellFormed context replacement

/-- Rigid-parameter replacements at a retained source occurrence may mention
lexical generalized-initializer variables or body-wide residual variables. -/
def RangeAdmissible (context : Context)
    (substitution : TypeSystem.ParameterSubstitution) : Prop :=
  ∀ parameter replacement,
    (parameter, replacement) ∈ substitution →
      TypeAdmissible context replacement

theorem RangeWellFormed.toAdmissible
    {context : Context} {substitution : TypeSystem.ParameterSubstitution}
    (range : RangeWellFormed context substitution) :
    RangeAdmissible context substitution := by
  intro parameter replacement member
  exact TypeAdmissible.ofWellFormed (range parameter replacement member)

/-- Admissible rigid-substitution ranges become closed when both flexible
scopes of the use-site context are closed. -/
theorem RangeAdmissible.toWellFormed
    {context : Context} {substitution : TypeSystem.ParameterSubstitution}
    (range : RangeAdmissible context substitution)
    (typeVariables_eq : context.typeVariables = [])
    (residualTypeVariables_eq : context.residualTypeVariables = false) :
    RangeWellFormed context substitution := by
  intro parameter replacement member
  exact (range parameter replacement member).toWellFormed typeVariables_eq
    residualTypeVariables_eq

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

/-- Zipping a duplicate-free rigid-parameter row with an equally sized
argument row covers that parameter row exactly once. -/
theorem exact_zip {parameters : List TypeSystem.TypeParameterId}
    {arguments : List TypeSystem.Ty}
    (parameters_nodup : parameters.Nodup)
    (length_eq : arguments.length = parameters.length) :
    Exact (parameters.zip arguments) parameters := by
  refine {
    parameters_nodup
    domain_permutation := ?_
  }
  unfold domain
  have length_le : parameters.length ≤ arguments.length := by omega
  rw [List.map_fst_zip length_le]

/-- Lookup through an exact positional zip recovers the argument row in
declaration-parameter order. -/
theorem orderedArguments_zip {parameters : List TypeSystem.TypeParameterId}
    {arguments : List TypeSystem.Ty}
    (parameters_nodup : parameters.Nodup)
    (length_eq : arguments.length = parameters.length) :
    orderedArguments (parameters.zip arguments) parameters = arguments := by
  induction parameters generalizing arguments with
  | nil =>
      cases arguments with
      | nil => rfl
      | cons argument arguments => simp at length_eq
  | cons parameter parameters induction =>
      cases arguments with
      | nil => simp at length_eq
      | cons argument arguments =>
          simp only [List.length_cons, Nat.succ.injEq] at length_eq
          simp only [List.nodup_cons] at parameters_nodup
          rcases parameters_nodup with
            ⟨parameter_fresh, parameters_nodup⟩
          unfold orderedArguments
          simp only [List.zip_cons_cons, List.map_cons]
          simp only [List.cons.injEq]
          constructor
          · simp [TypeSystem.ParameterSubstitution.lookup?]
          · calc
              parameters.map (fun candidate =>
                  (TypeSystem.ParameterSubstitution.lookup?
                    ((parameter, argument) :: parameters.zip arguments)
                    candidate).getD (.parameter candidate)) =
                  parameters.map (fun candidate =>
                    (TypeSystem.ParameterSubstitution.lookup?
                      (parameters.zip arguments) candidate).getD
                        (.parameter candidate)) := by
                    apply List.map_congr_left
                    intro candidate candidate_mem
                    have different : parameter ≠ candidate := by
                      intro same
                      apply parameter_fresh
                      simpa [same] using candidate_mem
                    simp [TypeSystem.ParameterSubstitution.lookup?, different]
              _ = arguments := induction parameters_nodup length_eq

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
function signature with a closed replacement range.  Staging metadata is
copied, not inferred from types. -/
inductive Valid (context : Context)
    (instantiation : Frontend.SourceInference.DeclarationInstantiation) : Prop where
  | intro (signature : Frontend.ProgramFunctionSignature)
      (signature_mem : signature ∈ context.signatures.functions)
      (declaration_eq : instantiation.declaration = signature.id)
      (substitution_exact :
        ParameterSubstitution.Exact instantiation.parameterSubstitution
          signature.scheme.parameters)
      (substitution_range :
        ParameterSubstitution.RangeWellFormed context
          instantiation.parameterSubstitution)
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

/-- Static use-site validity for a retained function instantiation.  This has
the same catalog and exactness conditions as `Valid`, but its replacement
range may mention lexical generalized-initializer variables or body-wide
residual variables. -/
inductive Admissible (context : Context)
    (instantiation : Frontend.SourceInference.DeclarationInstantiation) : Prop where
  | intro (signature : Frontend.ProgramFunctionSignature)
      (signature_mem : signature ∈ context.signatures.functions)
      (declaration_eq : instantiation.declaration = signature.id)
      (substitution_exact :
        ParameterSubstitution.Exact instantiation.parameterSubstitution
          signature.scheme.parameters)
      (substitution_range :
        ParameterSubstitution.RangeAdmissible context
          instantiation.parameterSubstitution)
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
      Admissible context instantiation

theorem Valid.toAdmissible {context : Context}
    {instantiation : Frontend.SourceInference.DeclarationInstantiation}
    (valid : Valid context instantiation) : Admissible context instantiation := by
  cases valid with
  | intro signature signature_mem declaration_eq substitution_exact
      substitution_range type_eq predicates_eq parameterComptime_eq
      returnComptime_eq =>
      exact .intro signature signature_mem declaration_eq substitution_exact
        substitution_range.toAdmissible type_eq predicates_eq
        parameterComptime_eq returnComptime_eq

/-- Static instantiation validity recovers the closed runtime judgment when
both use-site flexible scopes are closed. -/
theorem Admissible.toValid {context : Context}
    {instantiation : Frontend.SourceInference.DeclarationInstantiation}
    (valid : Admissible context instantiation)
    (typeVariables_eq : context.typeVariables = [])
    (residualTypeVariables_eq : context.residualTypeVariables = false) :
    Valid context instantiation := by
  cases valid with
  | intro signature signature_mem declaration_eq substitution_exact
      substitution_range type_eq predicates_eq parameterComptime_eq
      returnComptime_eq =>
      exact .intro signature signature_mem declaration_eq substitution_exact
        (substitution_range.toWellFormed typeVariables_eq
          residualTypeVariables_eq) type_eq predicates_eq
        parameterComptime_eq returnComptime_eq

theorem Valid.signature_id {context : Context}
    {instantiation : Frontend.SourceInference.DeclarationInstantiation}
    (valid : Valid context instantiation) :
    ∃ signature ∈ context.signatures.functions,
      signature.id = instantiation.declaration := by
  cases valid with
  | intro signature signature_mem declaration_eq =>
      exact ⟨signature, signature_mem, declaration_eq.symm⟩

theorem Admissible.signature_id {context : Context}
    {instantiation : Frontend.SourceInference.DeclarationInstantiation}
    (valid : Admissible context instantiation) :
    ∃ signature ∈ context.signatures.functions,
      signature.id = instantiation.declaration := by
  cases valid with
  | intro signature signature_mem declaration_eq =>
      exact ⟨signature, signature_mem, declaration_eq.symm⟩

end DeclarationInstantiation

namespace DataConstructorInstantiation

/-- A typed-IR constructor occurrence is exactly an instance of one constructor
from one cataloged data declaration with a closed replacement range. -/
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
      (substitution_range :
        ParameterSubstitution.RangeWellFormed context
          instantiation.parameterSubstitution)
      (payloadTypes_eq :
        instantiation.payloadTypes = signature.payloadTypes.map
          (TypeSystem.ParameterSubstitution.apply instantiation.parameterSubstitution))
      (resultType_eq :
        instantiation.resultType = TypeSystem.Ty.nominal dataType.id
          (ParameterSubstitution.orderedArguments
            instantiation.parameterSubstitution dataType.parameters)) :
      Valid context instantiation

/-- Static use-site validity for a retained data-constructor instantiation,
permitting rigid parameters to be replaced by lexical initializer variables or
body-wide residual variables. -/
inductive Admissible (context : Context)
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
      (substitution_range :
        ParameterSubstitution.RangeAdmissible context
          instantiation.parameterSubstitution)
      (payloadTypes_eq :
        instantiation.payloadTypes = signature.payloadTypes.map
          (TypeSystem.ParameterSubstitution.apply instantiation.parameterSubstitution))
      (resultType_eq :
        instantiation.resultType = TypeSystem.Ty.nominal dataType.id
          (ParameterSubstitution.orderedArguments
            instantiation.parameterSubstitution dataType.parameters)) :
      Admissible context instantiation

theorem Valid.toAdmissible {context : Context}
    {instantiation : Frontend.SourceInference.DataConstructorInstantiation}
    (valid : Valid context instantiation) : Admissible context instantiation := by
  cases valid with
  | intro dataType signature dataType_mem signature_mem signature_owner
      constructor_eq substitution_exact substitution_range payloadTypes_eq
      resultType_eq =>
      exact .intro dataType signature dataType_mem signature_mem signature_owner
        constructor_eq substitution_exact substitution_range.toAdmissible
        payloadTypes_eq resultType_eq

/-- Static constructor-instantiation validity recovers the closed runtime
judgment when both use-site flexible scopes are closed. -/
theorem Admissible.toValid {context : Context}
    {instantiation : Frontend.SourceInference.DataConstructorInstantiation}
    (valid : Admissible context instantiation)
    (typeVariables_eq : context.typeVariables = [])
    (residualTypeVariables_eq : context.residualTypeVariables = false) :
    Valid context instantiation := by
  cases valid with
  | intro dataType signature dataType_mem signature_mem signature_owner
      constructor_eq substitution_exact substitution_range payloadTypes_eq
      resultType_eq =>
      exact .intro dataType signature dataType_mem signature_mem signature_owner
        constructor_eq substitution_exact
        (substitution_range.toWellFormed typeVariables_eq
          residualTypeVariables_eq) payloadTypes_eq
        resultType_eq

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

theorem Admissible.signature_id {context : Context}
    {instantiation : Frontend.SourceInference.DataConstructorInstantiation}
    (valid : Admissible context instantiation) :
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
end

section
-- leanmerge: from Solcore.SourceSemantics.Substitution
/-!
Structural rigid-parameter substitution for the declarative source carrier.

This module intentionally lives below the frontend specialization pass.  Its
functions are the syntax-directed action of a substitution on retained source
metadata; they perform no discovery, checking, stage analysis, worklist
construction, or execution.  Dynamic instantiation can therefore cite this
normative operation without making an executable compiler pass authoritative.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.StructuralSubstitution

open Frontend
open Frontend.SourceInference
open TypeSystem

def applyScheme (substitution : ParameterSubstitution) (scheme : Scheme) : Scheme :=
  { scheme with body := substitution.apply scheme.body }

def applyBinder (substitution : ParameterSubstitution)
    (binder : TypedBinder) : TypedBinder :=
  { binder with
    scheme := applyScheme substitution binder.scheme
    schemeRequirements := binder.schemeRequirements.map
      (LocalSchemeRequirement.applyParameters substitution) }

def applyDeclarationInstantiation (substitution : ParameterSubstitution)
    (instantiation : DeclarationInstantiation) : DeclarationInstantiation :=
  { instantiation with
    parameterSubstitution := instantiation.parameterSubstitution.map fun entry =>
      (entry.1, substitution.apply entry.2)
    type := substitution.apply instantiation.type
    predicates := instantiation.predicates.map
      (ProgramPredicate.applyParameters substitution) }

def applyReferenceResolution (substitution : ParameterSubstitution) :
    ReferenceResolution → ReferenceResolution
  | .local binder => .local binder
  | .declaration instantiation =>
      .declaration (applyDeclarationInstantiation substitution instantiation)
  | .builtinFunction function => .builtinFunction function
  | .builtinBoolean value => .builtinBoolean value

def applyIndirectCallResolution (substitution : ParameterSubstitution)
    (metadata : IndirectCallResolution) : IndirectCallResolution := {
  argumentCount := metadata.argumentCount
  argumentTypeBeforeCoercion :=
    substitution.apply metadata.argumentTypeBeforeCoercion
  argumentTypeAfterCoercion :=
    substitution.apply metadata.argumentTypeAfterCoercion
  argumentCoercions := metadata.argumentCoercions.map fun step => {
    step with
    source := substitution.apply step.source
    target := substitution.apply step.target
  }
}

def applyCallResolution (substitution : ParameterSubstitution) :
    CallResolution → CallResolution
  | .indirect metadata =>
      .indirect (applyIndirectCallResolution substitution metadata)
  | .declaration instantiation =>
      .declaration (applyDeclarationInstantiation substitution instantiation)
  | .builtinFunction function => .builtinFunction function

def applyIntegerLiteralResolution (substitution : ParameterSubstitution)
    (resolution : IntegerLiteralResolution) : IntegerLiteralResolution := {
  resolution with targetType := substitution.apply resolution.targetType
}

def applyDataConstructorInstantiation (substitution : ParameterSubstitution)
    (instantiation : DataConstructorInstantiation) :
    DataConstructorInstantiation := {
  instantiation with
  parameterSubstitution := instantiation.parameterSubstitution.map fun entry =>
    (entry.1, substitution.apply entry.2)
  payloadTypes := instantiation.payloadTypes.map substitution.apply
  resultType := substitution.apply instantiation.resultType
}

def applyMatchPatternInstruction (substitution : ParameterSubstitution) :
    MatchPatternInstruction → MatchPatternInstruction
  | .wildcard => .wildcard
  | .integerLiteral source resolution =>
      .integerLiteral source
        (applyIntegerLiteralResolution substitution resolution)
  | .binder binder => .binder (applyBinder substitution binder)
  | .constructor instantiation argumentCount =>
      .constructor (applyDataConstructorInstantiation substitution instantiation)
        argumentCount
  | .tuple elementCount => .tuple elementCount

def applyMatchPatternResolution (substitution : ParameterSubstitution) :
    MatchPatternResolution → MatchPatternResolution
  | .wildcard => .wildcard
  | .integerLiteral source resolution =>
      .integerLiteral source
        (applyIntegerLiteralResolution substitution resolution)
  | .binder binder => .binder (applyBinder substitution binder)
  | .constructor instantiation arguments =>
      .constructor (applyDataConstructorInstantiation substitution instantiation)
        (arguments.map (applyMatchPatternInstruction substitution))
  | .tuple elements =>
      .tuple (elements.map (applyMatchPatternInstruction substitution))

def applyTypedMatchPattern (substitution : ParameterSubstitution)
    (pattern : TypedMatchPattern) : TypedMatchPattern := {
  pattern with
  type := substitution.apply pattern.type
  resolution := applyMatchPatternResolution substitution pattern.resolution
}

def applyTypedMatchCase (substitution : ParameterSubstitution)
    (matchCase : TypedMatchCase) : TypedMatchCase := {
  matchCase with pattern := applyTypedMatchPattern substitution matchCase.pattern
}

def applyMatchResolution (substitution : ParameterSubstitution)
    (resolution : MatchResolution) : MatchResolution := {
  resolution with
  cases := resolution.cases.map (applyTypedMatchCase substitution)
}

def applyExpressionForm (substitution : ParameterSubstitution) :
    ExpressionForm → ExpressionForm
  | .literal literal => .literal literal
  | .integerLiteral source resolution =>
      .integerLiteral source
        (applyIntegerLiteralResolution substitution resolution)
  | .reference name resolution =>
      .reference name (applyReferenceResolution substitution resolution)
  | .group inner => .group inner
  | .tuple elements => .tuple elements
  | .unary operator operand => .unary operator operand
  | .binary left operator right => .binary left operator right
  | .conditional condition thenBranch elseBranch =>
      .conditional condition thenBranch elseBranch
  | .lambda parameters returnType body =>
      .lambda (parameters.map (applyBinder substitution))
        (substitution.apply returnType) body
  | .call callee arguments resolution =>
      .call callee arguments (applyCallResolution substitution resolution)
  | .constructor instantiation arguments =>
      .constructor (applyDataConstructorInstantiation substitution instantiation)
        arguments
  | .member base name memberIndex => .member base name memberIndex
  | .proxy inner => .proxy (substitution.apply inner)
  | .index base index => .index base index

def applyPlaceResolution (substitution : ParameterSubstitution)
    (place : PlaceResolution) : PlaceResolution := {
  place with type := substitution.apply place.type
}

def applyAssignmentResolution (substitution : ParameterSubstitution)
    (assignment : AssignmentResolution) : AssignmentResolution := {
  assignment with target := applyPlaceResolution substitution assignment.target
}

def applyForItemForm (substitution : ParameterSubstitution) :
    ForItemForm → ForItemForm
  | .letDecl binder initializer =>
      .letDecl (applyBinder substitution binder) initializer
  | .expression expression => .expression expression
  | .assignValue assignment operator value =>
      .assignValue (applyAssignmentResolution substitution assignment)
        operator value
  | .assignBitNot assignment =>
      .assignBitNot (applyAssignmentResolution substitution assignment)

def applyCoercionStep (substitution : ParameterSubstitution)
    (step : CoercionStep) : CoercionStep := {
  step with
  source := substitution.apply step.source
  target := substitution.apply step.target
}

def applyExpressionNode (substitution : ParameterSubstitution)
    (node : ExpressionNode) : ExpressionNode := {
  node with
  type := substitution.apply node.type
  form := applyExpressionForm substitution node.form
  coercions := node.coercions.map (applyCoercionStep substitution)
}

def applyStatementForm (substitution : ParameterSubstitution) :
    StatementForm → StatementForm
  | .letDecl binder initializer =>
      .letDecl (applyBinder substitution binder) initializer
  | .returnStmt value => .returnStmt value
  | .expression expression trailingSemicolon =>
      .expression expression trailingSemicolon
  | .assignValue assignment operator value =>
      .assignValue (applyAssignmentResolution substitution assignment)
        operator value
  | .assignBitNot assignment =>
      .assignBitNot (applyAssignmentResolution substitution assignment)
  | .ifThen condition thenBody elseBody =>
      .ifThen condition thenBody elseBody
  | .block body => .block body
  | .matchWith resolution =>
      .matchWith (applyMatchResolution substitution resolution)
  | .forLoop initializer condition post body =>
      .forLoop (initializer.map (applyForItemForm substitution)) condition
        (post.map (applyForItemForm substitution)) body
  | .whileLoop condition body => .whileLoop condition body
  | .breakStmt => .breakStmt
  | .continueStmt => .continueStmt

def applyStatementNode (substitution : ParameterSubstitution)
    (node : StatementNode) : StatementNode := {
  node with
  type := substitution.apply node.type
  form := applyStatementForm substitution node.form
}

def applyNode (substitution : ParameterSubstitution) : Node → Node
  | .expression node => .expression (applyExpressionNode substitution node)
  | .statement node => .statement (applyStatementNode substitution node)

/-- Apply a rigid substitution to every retained semantic type without
changing ownership, occurrence identities, graph edges, or roots. -/
def applyTypedSource (substitution : ParameterSubstitution)
    (source : TypedSource) : TypedSource := {
  source with
  inputs := source.inputs.map (applyBinder substitution)
  nodes := source.nodes.map (applyNode substitution)
}

mutual

  def applyEvidence (substitution : ParameterSubstitution) :
      TypedTraitResolution.Evidence → TypedTraitResolution.Evidence
    | .byImpl goal implementation premises =>
        .byImpl (ProgramPredicate.applyParameters substitution goal)
          implementation (applyEvidences substitution premises)

  def applyEvidences (substitution : ParameterSubstitution) :
      List TypedTraitResolution.Evidence → List TypedTraitResolution.Evidence
    | [] => []
    | evidence :: rest =>
        applyEvidence substitution evidence :: applyEvidences substitution rest

end

def applyPredicateEvidence (substitution : ParameterSubstitution) :
    PredicateEvidence → PredicateEvidence
  | .assumption predicate =>
      .assumption (ProgramPredicate.applyParameters substitution predicate)
  | .implementation evidence =>
      .implementation (applyEvidence substitution evidence)

def applySolvedRequirement (substitution : ParameterSubstitution)
    (requirement : SolvedRequirement) : SolvedRequirement := {
  requirement with
  predicate := ProgramPredicate.applyParameters substitution
    requirement.predicate
  evidence := applyPredicateEvidence substitution requirement.evidence
}

end Solcore.SourceSemantics.StructuralSubstitution

/-!
## Flexible local-scheme substitution

Unlike `StructuralSubstitution`, this namespace acts on flexible inference
variables.  Its context operation is intended for closing the temporary
flexible-variable scope of a generalized local initializer.  Exact domain and
range conditions remain separate propositions in `Instantiation`; the
functions below are only the total structural action.
-/

namespace Solcore.SourceSemantics.FlexibleSubstitution

open Frontend
open Frontend.SourceInference
open TypeSystem

mutual

  /-- Apply a flexible substitution throughout retained implementation
  evidence without changing the selected implementation identities. -/
  def applyEvidence (substitution : Substitution) :
      TypedTraitResolution.Evidence → TypedTraitResolution.Evidence
    | .byImpl goal implementation premises =>
        .byImpl (TypedTraitResolution.applySubstitution substitution goal)
          implementation (applyEvidences substitution premises)

  /-- Pointwise flexible substitution of retained implementation premises. -/
  def applyEvidences (substitution : Substitution) :
      List TypedTraitResolution.Evidence → List TypedTraitResolution.Evidence
    | [] => []
    | evidence :: rest =>
        applyEvidence substitution evidence :: applyEvidences substitution rest

end

/-- Apply a flexible substitution to either retained evidence representation. -/
def applyPredicateEvidence (substitution : Substitution) :
    PredicateEvidence → PredicateEvidence
  | .assumption predicate =>
      .assumption (TypedTraitResolution.applySubstitution substitution predicate)
  | .implementation evidence =>
      .implementation (applyEvidence substitution evidence)

/-- Close every flexible type position in a solved row while preserving its
stable requirement identity. -/
def applySolvedRequirement (substitution : Substitution)
    (requirement : SolvedRequirement) : SolvedRequirement := {
  requirement with
  predicate := TypedTraitResolution.applySubstitution substitution
    requirement.predicate
  evidence := applyPredicateEvidence substitution requirement.evidence
}

/-- Capture-avoiding flexible substitution of a lexical scheme scope. -/
def applyLocals (substitution : Substitution)
    (locals : Resolved.LocalScope Scheme) : Resolved.LocalScope Scheme :=
  locals.map fun entry => (entry.1, entry.2.apply substitution)

/-- Restrict a flexible substitution before entering the scheme associated
with one stable local identity.  Malformed, unpaired requirement scopes remain
total by falling back to the original substitution. -/
def forLocal (substitution : Substitution)
    (locals : Resolved.LocalScope Scheme) (id : Resolved.LocalId) :
    Substitution :=
  match locals.lookup? id with
  | some scheme => substitution.without scheme.quantified
  | none => substitution

/-- Substitute qualified-local metadata with the same capture avoidance as
its corresponding lexical scheme.  First-match lookup deliberately agrees
with the lookup semantics of `Context.LocalLookup`. -/
def applyLocalSchemeRequirements (substitution : Substitution)
    (locals : Resolved.LocalScope Scheme)
    (requirements : Resolved.LocalScope (List LocalSchemeRequirement)) :
    Resolved.LocalScope (List LocalSchemeRequirement) :=
  requirements.map fun entry =>
    let localSubstitution := forLocal substitution locals entry.1
    (entry.1,
      entry.2.map (LocalSchemeRequirement.applySubstitution localSubstitution))

/-- Apply a flexible substitution to a source-semantics context while retaining
the indicated inner lexical variables.  Rigid declaration binders and the
residual-variable policy are independent of this operation.  Exactness and
range well-formedness are stated separately by `ContextCloses`.

This total structural action maps every solved row, including rows in an
arbitrary malformed `Context`.  Soundness consumers must therefore carry the
appropriate well-formed-context or requirement-ledger premise; `closeContext`
alone does not establish that mapped evidence remains valid. -/
def applyContext (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context) : Context := {
  signatures := context.signatures
  currentDeclaration := context.currentDeclaration
  typeParameters := context.typeParameters
  typeVariables := retainedVariables
  residualTypeVariables := context.residualTypeVariables
  locals := applyLocals substitution context.locals
  localSchemeRequirements :=
    applyLocalSchemeRequirements substitution context.locals
      context.localSchemeRequirements
  assumptions := context.assumptions.map
    (TypedTraitResolution.applySubstitution substitution)
  solvedRequirements := context.solvedRequirements.map
    (applySolvedRequirement substitution)
}

/-- Close every lexical flexible variable in a source-semantics context. -/
def closeContext (substitution : Substitution) (context : Context) : Context :=
  applyContext substitution [] context

/-- A structural flexible substitution closes exactly an outer prefix of the
lexical metavariable scope while leaving a fresh inner suffix available. -/
structure ContextCloses (substitution : Substitution)
    (closedVariables : List TypeVarId) (source target : Context) : Prop where
  variables_eq :
    source.typeVariables = closedVariables ++ target.typeVariables
  exact : SourceSemantics.ExactSubstitution substitution closedVariables
  retained_fresh :
    ∀ metavariable, metavariable ∈ target.typeVariables →
      metavariable ∉ substitution.domain
  range : SourceSemantics.SubstitutionRangeWellFormed target substitution
  target_eq : applyContext substitution target.typeVariables source = target

end Solcore.SourceSemantics.FlexibleSubstitution
end
