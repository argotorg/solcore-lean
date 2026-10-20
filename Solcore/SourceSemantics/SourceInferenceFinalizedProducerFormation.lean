import Solcore.SourceSemantics.SourceInferenceNormalizedCoercionIssued

/-! Producer formation from the actual selected finalizer's validated type
rows and substitution. These facts precede expression/body typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

/-- The static declaration fields shared by an initializer and its successful
whole-body finalizer. Lexical variables and local qualified assumptions may
grow when entering a generalized initializer. -/
structure ProducerScope (whole : SourceInference.Context)
    (semantic : SourceSemantics.Context) : Prop where
  binders : TypeParameterBindersWellFormed semantic
  signatures : semantic.signatures = whole.signatures
  parameters : semantic.typeParameters = whole.typeParameters
  owner : semantic.currentDeclaration = some whole.scope.genericOwner
  residual : semantic.residualTypeVariables = true
  catalog : SignatureCatalogWellFormed semantic.signatures

namespace FinalInferenceResources
variable {whole : SourceInference.Context} {wholeReturn : Ty}
    {evidence : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {semantic : SourceSemantics.Context}

theorem producerRange (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic) :
    SubstitutionRangeAdmissible semantic finalized.substitution :=
  InferenceSubstitutionRangeFormationValidated.rangeAdmissible resources.range_formation
    scope.binders scope.signatures scope.parameters scope.owner scope.residual

/-- The real raw node-type validation and final range validation form the
operand's final type without a semantic typing judgment for that node. -/
theorem retainedProducerType
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {node : ExpressionNode}
    (member : Node.expression node ∈ (evidence.toTypedSource roots).nodes) :
    TypeAdmissible semantic (finalized.substitution.apply node.type) :=
  type_applySubstitution_residual scope.residual (resources.producerRange scope)
    (InferenceTypeFormationValidated.typeAdmissible
      (resources.expressionTypeFormationValidated member)
      scope.binders scope.signatures scope.parameters scope.owner scope.residual)

theorem retainedResolvedProducerType
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {node : ExpressionNode} {state : State}
    (member : Node.expression node ∈ (evidence.toTypedSource roots).nodes)
    (continuation : finalized.substitution.SemanticallyExtends state.inference.substitution) :
    TypeAdmissible semantic (finalized.substitution.apply (state.resolve node.type)) :=
  (continuation node.type).symm ▸ resources.retainedProducerType scope member

/-- Signature obligations follow their accepted declaration attempt. Their
normalization uses the actual selected finalizer's validated range. -/
theorem functionProducer
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {context : SourceInference.Context} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State} {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    (member : signature ∈ semantic.signatures.functions)
    (accepted : Detail.tryFunctionCandidate context arguments integerOrigins call expected state signature =
      .ok (some result)) :
    RequirementPredicatesCorrespond result.state.requirements
      (signature.scheme.instantiate state.inference.next).predicates result.signatureRequirements ∧
      ∀ predicate ∈ (signature.scheme.instantiate state.inference.next).predicates,
        PredicateAdmissible semantic
          (TypedTraitResolution.applySubstitution finalized.substitution predicate) := by
  have actual := candidate_signature_issuance scope.catalog scope.binders scope.residual member accepted
  exact ⟨actual.1, fun predicate member =>
    predicate_applySubstitution_residual scope.residual (resources.producerRange scope) (actual.2 predicate member)⟩

/-- The literal requirement refers to its actual allocator variable. Its
final type is obtained from the finalizer's checked literal-origin ledger. -/
theorem integerLiteralProducer
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {origin : IntegerLiteralOrigin} (member : origin ∈ evidence.integerLiterals) :
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution finalized.substitution
      (ProgramSignatures.builtinIntPredicate (.variable origin.metavariable))) := by
  apply builtin_integer_predicate
  change TypeAdmissible semantic (finalized.substitution.apply (.variable origin.metavariable))
  rcases resources.integer_literal_target_supported origin member with word | integer
  · rw [word]; exact .word scope.binders
  · rw [integer]; exact .integer scope.binders

theorem integerPatternProducer
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {origin : IntegerPatternOrigin} (member : origin ∈ evidence.integerPatterns) :
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution finalized.substitution
      (ProgramSignatures.builtinIntPredicate (.variable origin.metavariable))) := by
  apply builtin_integer_predicate
  change TypeAdmissible semantic (finalized.substitution.apply (.variable origin.metavariable))
  rcases resources.integer_pattern_target_supported origin member with word | integer
  · rw [word]; exact .word scope.binders
  · rw [integer]; exact .integer scope.binders

/-- A real retained operand supplies the normalized type required by actual
operator-profile issuance. No operator-expression typing is assumed. -/
theorem operatorProducer
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {context : SourceInference.Context} {state : State} {node : ExpressionNode}
    {trait : Resolved.DeclarationId} {traitName methodName : String}
    {parameters returns : List Ty} {predicates : List ProgramPredicate}
    (member : Node.expression node ∈ (evidence.toTypedSource roots).nodes)
    (continuation : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (signatures : context.signatures = whole.signatures)
    (traitNameEq : (context.signatures.trait? trait).map (·.name) = some traitName)
    (accepted : Detail.operatorTraitPredicates context trait methodName (state.resolve node.type)
      parameters returns = .ok predicates) :
    ∀ predicate ∈ predicates, PredicateAdmissible semantic
      (TypedTraitResolution.applySubstitution finalized.substitution predicate) :=
  operator_issuance_normalized scope.catalog (scope.signatures.trans signatures.symm)
    traitNameEq (resources.retainedResolvedProducerType scope member continuation) accepted

end FinalInferenceResources
end Solcore.SourceSemantics.SourceInferenceSoundness
