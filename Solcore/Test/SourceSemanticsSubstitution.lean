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

/-- Rigid substitution cannot change the occurrence graph of a generic body. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (closed : OccurrenceGraphClosed source) :
    OccurrenceGraphClosed (applyTypedSource substitution source) :=
  StructuralSubstitution.OccurrenceGraphClosed.applyParameters substitution
    closed

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
