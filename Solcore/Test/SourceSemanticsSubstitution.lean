import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.Graph

/-!
Focused public checks for rigid substitution through implementation matching,
semantic evidence, and solved-requirement ledgers.
-/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsSubstitution

open Frontend
open Frontend.SourceInference
open TypeSystem
open SourceSemantics
open SourceSemantics.StructuralSubstitution

/-- An already matched implementation head remains matched after applying an
outer declaration-parameter substitution to its goal and premises. -/
example (outer : ParameterSubstitution) (rule : ProgramImplRule)
    (goal : ProgramPredicate) (premises : List ProgramPredicate)
    (matched : ImplHeadInstantiates rule goal premises) :
    ImplHeadInstantiates rule
      (ProgramPredicate.applyParameters outer goal)
      (premises.map (ProgramPredicate.applyParameters outer)) :=
  StructuralSubstitution.ImplHeadInstantiates.applyParameters outer matched

/-- Nested semantic evidence is closed by the same structural action. -/
example (outer : ParameterSubstitution)
    (assumptions : List ProgramPredicate) (rules : List ProgramImplRule)
    (goal : ProgramPredicate) (evidence : TraitEvidence)
    (valid : EvidenceValid assumptions rules goal evidence) :
    EvidenceValid
      (assumptions.map (ProgramPredicate.applyParameters outer)) rules
      (ProgramPredicate.applyParameters outer goal)
      (applyTraitEvidence outer evidence) :=
  StructuralSubstitution.EvidenceValid.applyParameters outer valid

/-- A well-formed solved-requirement ledger supplies the evidence premise for
transporting the complete source typing derivation. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (ledger : RequirementLedgerWellFormed context) :
    ContextSubstitutionValid substitution context :=
  ContextSubstitutionValid.ofRequirementLedger exact range ledger

/-- The external substitution premise is needed only for implementation
evidence.  Assumption evidence is transported from its lexical validity by
`RequirementProves.applyParameters`. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context)
    (valid : ContextSubstitutionValid substitution context)
    (requirement : SolvedRequirement)
    (evidence : TypedTraitResolution.Evidence)
    (member : requirement ∈ context.solvedRequirements)
    (implementation : requirement.evidence = .implementation evidence) :
    SolvedRequirementValid (applyContext substitution context)
      (applySolvedRequirement substitution requirement) :=
  valid.implementationRequirements requirement evidence member implementation

/-- A ledger consisting only of assumption rows needs no evidence-transport
premise beyond exactness and range well-formedness.  The local proof supplies
the assumption membership used by rigid substitution. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (assumptionRows : ∀ requirement,
      requirement ∈ context.solvedRequirements →
        ∃ predicate, requirement.evidence = .assumption predicate)
    (id : RequirementId) (predicate : ProgramPredicate)
    (proves : RequirementProves context id predicate) :
    RequirementProves (applyContext substitution context) id
      (ProgramPredicate.applyParameters substitution predicate) := by
  apply RequirementProves.applyParameters
      ({ exact, range, implementationRequirements := ?_ } :
        ContextSubstitutionValid substitution context)
    proves
  intro requirement evidence member implementation
  rcases assumptionRows requirement member with ⟨assumption, assumptionEq⟩
  rw [assumptionEq] at implementation
  cases implementation

/-- One rigid declaration instantiation preserves the shared local-scheme
type/predicate witness and its ordered actual requirement identities. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context)
    (resolution : ReferenceResolution) (type : Ty)
    (requirements : List RequirementId)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : ReferenceUseValid context resolution type requirements) :
    ReferenceUseValid (applyContext substitution context)
      (applyReferenceResolution substitution resolution)
      (substitution.apply type) requirements :=
  ReferenceUseValid.applyParameters catalog contextValid valid

/-- Rigid substitution cannot change the occurrence graph of a generic body. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (closed : OccurrenceGraphClosed source) :
    OccurrenceGraphClosed (applyTypedSource substitution source) :=
  StructuralSubstitution.OccurrenceGraphClosed.applyParameters substitution
    closed

/-- Template-owner uniqueness is invariant under rigid declaration
instantiation. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (ownership : LocalSchemeTemplateOwnership source) :
    LocalSchemeTemplateOwnership (applyTypedSource substitution source) :=
  LocalSchemeTemplateOwnership.applyParameters substitution ownership

/-- Exact template-row ownership maps its predicate while retaining the
stable template identity. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (row : SolvedRequirement)
    (owned : LocalSchemeTemplateRowOwned source row) :
    LocalSchemeTemplateRowOwned (applyTypedSource substitution source)
      (applySolvedRequirement substitution row) :=
  LocalSchemeTemplateRowOwned.applyParameters substitution owned

/-- Rigid instantiation preserves the initializer subtree in which a template
owner may be used. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (owner : LocalSchemeTemplateOwner) (occurrence : NodeId)
    (scope : owner.Scopes source occurrence) :
    (applyLocalSchemeTemplateOwner substitution owner).Scopes
      (applyTypedSource substitution source) occurrence :=
  LocalSchemeTemplateOwner.Scopes.applyParameters substitution scope

/-- The occurrence-aware primary-requirement inventory forgets to the legacy
flat identity inventory exactly. -/
example (source : TypedSource) :
    (primaryRequirementOccurrences source).map
        (fun occurrence => occurrence.requirement) =
      primaryRequirementIds source :=
  primaryRequirementOccurrenceIds_eq source

/-- Rigid substitution preserves exact primary requirement attachment sites. -/
example (substitution : ParameterSubstitution) (source : TypedSource) :
    primaryRequirementOccurrences (applyTypedSource substitution source) =
      primaryRequirementOccurrences source :=
  primaryRequirementOccurrences_applyTypedSource substitution source

/-- The relational view of an exact primary attachment transports without
changing either stable identity. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (occurrence : NodeId) (requirement : RequirementId)
    (occurs : PrimaryRequirementOccursAt source occurrence requirement) :
    PrimaryRequirementOccursAt (applyTypedSource substitution source)
      occurrence requirement := by
  simpa using occurs

/-- The declaration-level API closes the evidence side condition internally:
an exact, range-valid rigid substitution transports both input binders and the
complete generic body typing derivation. -/
example (signatures : ProgramSignatures)
    (parameters : List TypeParameterId)
    (assumptions : List ProgramPredicate)
    (parameterNames : List String) (parameterTypes : List Ty)
    (parameterComptime : List Bool) (returnTypes : List Ty)
    (returnComptime : Bool) (definition : BodyDefinition) (facts : BodyFacts)
    (substitution : ParameterSubstitution)
    (catalog : SignatureCatalogWellFormed signatures)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements)) substitution)
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    ∃ lexicalContext,
      MonoBindersExtend definition.source.owner
        (applyContext substitution
          (declarationContext signatures definition.owner parameters assumptions
            definition.solvedRequirements))
        (definition.source.inputs.map (applyBinder substitution))
        (parameterTypes.map substitution.apply) lexicalContext ∧
      BodyHasType (applyTypedSource substitution definition.source)
        lexicalContext (substitution.apply definition.resultType)
        (applyBodyFacts substitution facts) :=
  BodyDefinitionHasType.instantiate substitution catalog exact range typing

end Solcore.Test.SourceSemanticsSubstitution
