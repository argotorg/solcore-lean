import Solcore.TypeSystem.CorrelatedParameterInstances
import Solcore.Frontend.SourceSpecialization

/-!
Equal local instances of one original typed source retain equal rigid source
instances when the rigid replacement ranges contain no flexible variables.
This proof follows the actual full carrier, including qualified local predicates,
ordered coercion paths and flat match instructions. It neither identifies the
original template nor assumes local substitutions are injective.
-/

set_option autoImplicit false
namespace Solcore.Frontend.CorrelatedTypedSourceInstances
open SourceInference SourceSpecialization TypeSystem

private theorem recover_map {α β γ : Type} (original : List α)
    (left right : α → β) (leftFinal rightFinal : β → γ)
    (recover : ∀ item, leftFinal (left item) = rightFinal (right item) →
      left item = right item)
    (same : (original.map left).map leftFinal =
      (original.map right).map rightFinal) :
    original.map left = original.map right := by
  revert same
  induction original with
  | nil => intro _same; rfl
  | cons item rest ih =>
      intro same
      obtain ⟨firstSame, restSame⟩ := List.cons.inj same
      have first := recover item firstSame
      have tail := ih restSame
      simp only [List.map_cons]
      rw [first, tail]

section
variable {left right : ParameterSubstitution}
variable (leftClosed : ∀ parameter replacement,
  left.lookup? parameter = some replacement → replacement.freeVariables = [])
variable (rightClosed : ∀ parameter replacement,
  right.lookup? parameter = some replacement → replacement.freeVariables = [])

include leftClosed rightClosed

private theorem recover_type (original : Ty) (leftLocal rightLocal : Substitution)
    (same : leftLocal.apply (left.apply original) =
      rightLocal.apply (right.apply original)) :
    left.apply original = right.apply original :=
  CorrelatedParameterInstances.apply_parameters_eq_of_equal_local_instances
    original left right leftLocal rightLocal leftClosed rightClosed same

private theorem recover_types (original : List Ty)
    (leftLocal rightLocal : Substitution)
    (same : (original.map left.apply).map leftLocal.apply =
      (original.map right.apply).map rightLocal.apply) :
    original.map left.apply = original.map right.apply :=
  CorrelatedParameterInstances.apply_parameters_list_eq_of_equal_local_instances
    original left right leftLocal rightLocal leftClosed rightClosed same

private theorem recover_predicate (original : ProgramPredicate)
    (leftLocal rightLocal : Substitution)
    (same : TypedTraitResolution.applySubstitution leftLocal
        (ProgramPredicate.applyParameters left original) =
      TypedTraitResolution.applySubstitution rightLocal
        (ProgramPredicate.applyParameters right original)) :
    ProgramPredicate.applyParameters left original =
      ProgramPredicate.applyParameters right original := by
  have subjectSame := recover_type leftClosed rightClosed original.subject
    leftLocal rightLocal (congrArg (fun predicate => predicate.subject) same)
  have argumentsSame := recover_types leftClosed rightClosed original.arguments
    leftLocal rightLocal (congrArg (fun predicate => predicate.arguments) same)
  dsimp only [ProgramPredicate.applyParameters]
  rw [subjectSame, argumentsSame]

private theorem recover_requirement (original : LocalSchemeRequirement)
    (leftLocal rightLocal : Substitution)
    (same : LocalSchemeRequirement.applySubstitution leftLocal
        (LocalSchemeRequirement.applyParameters left original) =
      LocalSchemeRequirement.applySubstitution rightLocal
        (LocalSchemeRequirement.applyParameters right original)) :
    LocalSchemeRequirement.applyParameters left original =
      LocalSchemeRequirement.applyParameters right original := by
  have predicateSame := recover_predicate leftClosed rightClosed original.predicate
    leftLocal rightLocal (congrArg LocalSchemeRequirement.predicate same)
  dsimp only [LocalSchemeRequirement.applyParameters]
  rw [predicateSame]

private theorem recover_binder (original : TypedBinder)
    (leftLocal rightLocal : Substitution)
    (same : (applyBinder left original).applySubstitution leftLocal =
      (applyBinder right original).applySubstitution rightLocal) :
    applyBinder left original = applyBinder right original := by
  have bodySame := recover_type leftClosed rightClosed original.scheme.body
    ((leftLocal.without original.scheme.quantified).without original.scheme.quantified)
    ((rightLocal.without original.scheme.quantified).without original.scheme.quantified)
    (congrArg (fun binder => binder.scheme.body) same)
  have schemeSame : applyScheme left original.scheme =
      applyScheme right original.scheme := by
    dsimp only [applyScheme]
    rw [bodySame]
  have requirementsSame :
      original.schemeRequirements.map (LocalSchemeRequirement.applyParameters left) =
      original.schemeRequirements.map (LocalSchemeRequirement.applyParameters right) :=
    recover_map original.schemeRequirements _ _ _ _
      (fun item itemSame => recover_requirement leftClosed rightClosed item
        (leftLocal.without original.scheme.quantified)
        (rightLocal.without original.scheme.quantified) itemSame)
      (congrArg TypedBinder.schemeRequirements same)
  dsimp only [applyBinder]
  rw [schemeSame, requirementsSame]

private theorem recover_parameters (original : ParameterSubstitution)
    (leftLocal rightLocal : Substitution)
    (same : (original.map (fun item => (item.1, left.apply item.2))).map
        (fun item => (item.1, leftLocal.apply item.2)) =
      (original.map (fun item => (item.1, right.apply item.2))).map
        (fun item => (item.1, rightLocal.apply item.2))) :
    original.map (fun item => (item.1, left.apply item.2)) =
      original.map (fun item => (item.1, right.apply item.2)) := by
  apply recover_map original _ _ _ _ _ same
  intro item itemSame
  have typeSame := recover_type leftClosed rightClosed item.2 leftLocal rightLocal
    (congrArg Prod.snd itemSame)
  exact congrArg (fun type => (item.1, type)) typeSame

private theorem recover_instantiation (original : DeclarationInstantiation)
    (leftLocal rightLocal : Substitution)
    (same : (applyInstantiation left original).applySubstitution leftLocal =
      (applyInstantiation right original).applySubstitution rightLocal) :
    applyInstantiation left original = applyInstantiation right original := by
  have parametersSame := recover_parameters leftClosed rightClosed
    original.parameterSubstitution leftLocal rightLocal
    (congrArg DeclarationInstantiation.parameterSubstitution same)
  have typeSame := recover_type leftClosed rightClosed original.type
    leftLocal rightLocal (congrArg DeclarationInstantiation.type same)
  have predicatesSame :
      original.predicates.map (ProgramPredicate.applyParameters left) =
      original.predicates.map (ProgramPredicate.applyParameters right) :=
    recover_map original.predicates _ _ _ _
      (fun item itemSame => recover_predicate leftClosed rightClosed item
        leftLocal rightLocal itemSame)
      (congrArg DeclarationInstantiation.predicates same)
  dsimp only [applyInstantiation]
  rw [parametersSame, typeSame, predicatesSame]

private theorem recover_coercion (original : CoercionStep)
    (leftLocal rightLocal : Substitution)
    (same : (applyCoercionStep left original).applySubstitution leftLocal =
      (applyCoercionStep right original).applySubstitution rightLocal) :
    applyCoercionStep left original = applyCoercionStep right original := by
  have sourceSame := recover_type leftClosed rightClosed original.source
    leftLocal rightLocal (congrArg CoercionStep.source same)
  have targetSame := recover_type leftClosed rightClosed original.target
    leftLocal rightLocal (congrArg CoercionStep.target same)
  dsimp only [applyCoercionStep]
  rw [sourceSame, targetSame]

private theorem recover_indirect (original : IndirectCallResolution)
    (leftLocal rightLocal : Substitution)
    (same : (applyIndirectCallResolution left original).applySubstitution leftLocal =
      (applyIndirectCallResolution right original).applySubstitution rightLocal) :
    applyIndirectCallResolution left original =
      applyIndirectCallResolution right original := by
  have beforeSame := recover_type leftClosed rightClosed
    original.argumentTypeBeforeCoercion leftLocal rightLocal
    (congrArg IndirectCallResolution.argumentTypeBeforeCoercion same)
  have afterSame := recover_type leftClosed rightClosed
    original.argumentTypeAfterCoercion leftLocal rightLocal
    (congrArg IndirectCallResolution.argumentTypeAfterCoercion same)
  have coercionsSame : original.argumentCoercions.map (applyCoercionStep left) =
      original.argumentCoercions.map (applyCoercionStep right) :=
    recover_map original.argumentCoercions _ _ _ _
      (fun item itemSame => recover_coercion leftClosed rightClosed item
        leftLocal rightLocal itemSame)
      (congrArg IndirectCallResolution.argumentCoercions same)
  change { original with
      argumentTypeBeforeCoercion := left.apply original.argumentTypeBeforeCoercion
      argumentTypeAfterCoercion := left.apply original.argumentTypeAfterCoercion
      argumentCoercions := original.argumentCoercions.map (applyCoercionStep left) } =
    { original with
      argumentTypeBeforeCoercion := right.apply original.argumentTypeBeforeCoercion
      argumentTypeAfterCoercion := right.apply original.argumentTypeAfterCoercion
      argumentCoercions := original.argumentCoercions.map (applyCoercionStep right) }
  rw [beforeSame, afterSame, coercionsSame]

private theorem recover_reference (original : ReferenceResolution)
    (leftLocal rightLocal : Substitution)
    (same : (applyReferenceResolution left original).applySubstitution leftLocal =
      (applyReferenceResolution right original).applySubstitution rightLocal) :
    applyReferenceResolution left original =
      applyReferenceResolution right original := by
  cases original with
  | «local» binder => rfl
  | declaration instantiation =>
      exact congrArg ReferenceResolution.declaration
        (recover_instantiation leftClosed rightClosed instantiation leftLocal rightLocal
          (ReferenceResolution.declaration.inj same))
  | builtinFunction function => rfl
  | builtinBoolean value => rfl

private theorem recover_call (original : CallResolution)
    (leftLocal rightLocal : Substitution)
    (same : (applyCallResolution left original).applySubstitution leftLocal =
      (applyCallResolution right original).applySubstitution rightLocal) :
    applyCallResolution left original = applyCallResolution right original := by
  cases original with
  | indirect metadata =>
      exact congrArg CallResolution.indirect
        (recover_indirect leftClosed rightClosed metadata leftLocal rightLocal
          (CallResolution.indirect.inj same))
  | declaration instantiation =>
      exact congrArg CallResolution.declaration
        (recover_instantiation leftClosed rightClosed instantiation leftLocal rightLocal
          (CallResolution.declaration.inj same))
  | builtinFunction function => rfl

private theorem recover_integer (original : IntegerLiteralResolution)
    (leftLocal rightLocal : Substitution)
    (same : (applyIntegerLiteralResolution left original).applySubstitution leftLocal =
      (applyIntegerLiteralResolution right original).applySubstitution rightLocal) :
    applyIntegerLiteralResolution left original =
      applyIntegerLiteralResolution right original := by
  have targetSame := recover_type leftClosed rightClosed original.targetType
    leftLocal rightLocal (congrArg IntegerLiteralResolution.targetType same)
  dsimp only [applyIntegerLiteralResolution]
  rw [targetSame]

private theorem recover_constructor (original : DataConstructorInstantiation)
    (leftLocal rightLocal : Substitution)
    (same : (applyDataConstructorInstantiation left original).applySubstitution leftLocal =
      (applyDataConstructorInstantiation right original).applySubstitution rightLocal) :
    applyDataConstructorInstantiation left original =
      applyDataConstructorInstantiation right original := by
  have parametersSame := recover_parameters leftClosed rightClosed
    original.parameterSubstitution leftLocal rightLocal
    (congrArg DataConstructorInstantiation.parameterSubstitution same)
  have payloadSame := recover_types leftClosed rightClosed original.payloadTypes
    leftLocal rightLocal (congrArg DataConstructorInstantiation.payloadTypes same)
  have resultSame := recover_type leftClosed rightClosed original.resultType
    leftLocal rightLocal (congrArg DataConstructorInstantiation.resultType same)
  dsimp only [applyDataConstructorInstantiation]
  rw [parametersSame, payloadSame, resultSame]

private theorem recover_instruction (original : MatchPatternInstruction)
    (leftLocal rightLocal : Substitution)
    (same : (applyMatchPatternInstruction left original).applySubstitution leftLocal =
      (applyMatchPatternInstruction right original).applySubstitution rightLocal) :
    applyMatchPatternInstruction left original =
      applyMatchPatternInstruction right original := by
  cases original with
  | wildcard => rfl
  | integerLiteral value resolution =>
      exact congrArg (MatchPatternInstruction.integerLiteral value)
        (recover_integer leftClosed rightClosed resolution leftLocal rightLocal
          (MatchPatternInstruction.integerLiteral.inj same).2)
  | binder binder =>
      exact congrArg MatchPatternInstruction.binder
        (recover_binder leftClosed rightClosed binder leftLocal rightLocal
          (MatchPatternInstruction.binder.inj same))
  | constructor instantiation count =>
      have recovered := recover_constructor leftClosed rightClosed instantiation
        leftLocal rightLocal (MatchPatternInstruction.constructor.inj same).1
      exact congrArg (fun selected => MatchPatternInstruction.constructor selected count) recovered
  | tuple count => rfl

private theorem recover_pattern_resolution (original : MatchPatternResolution)
    (leftLocal rightLocal : Substitution)
    (same : (applyMatchPatternResolution left original).applySubstitution leftLocal =
      (applyMatchPatternResolution right original).applySubstitution rightLocal) :
    applyMatchPatternResolution left original =
      applyMatchPatternResolution right original := by
  cases original with
  | wildcard => rfl
  | integerLiteral value resolution =>
      exact congrArg (MatchPatternResolution.integerLiteral value)
        (recover_integer leftClosed rightClosed resolution leftLocal rightLocal
          (MatchPatternResolution.integerLiteral.inj same).2)
  | binder binder =>
      exact congrArg MatchPatternResolution.binder
        (recover_binder leftClosed rightClosed binder leftLocal rightLocal
          (MatchPatternResolution.binder.inj same))
  | constructor instantiation arguments =>
      obtain ⟨instantiationSame, argumentsSame⟩ := MatchPatternResolution.constructor.inj same
      have recovered := recover_constructor leftClosed rightClosed instantiation
        leftLocal rightLocal instantiationSame
      have recoveredArguments : arguments.map (applyMatchPatternInstruction left) =
          arguments.map (applyMatchPatternInstruction right) :=
        recover_map arguments _ _ _ _
          (fun item itemSame => recover_instruction leftClosed rightClosed item
            leftLocal rightLocal itemSame) argumentsSame
      dsimp only [applyMatchPatternResolution]
      rw [recovered, recoveredArguments]
  | tuple elements =>
      exact congrArg MatchPatternResolution.tuple
        (recover_map elements _ _ _ _
          (fun item itemSame => recover_instruction leftClosed rightClosed item
            leftLocal rightLocal itemSame) (MatchPatternResolution.tuple.inj same))

private theorem recover_pattern (original : TypedMatchPattern)
    (leftLocal rightLocal : Substitution)
    (same : (applyTypedMatchPattern left original).applySubstitution leftLocal =
      (applyTypedMatchPattern right original).applySubstitution rightLocal) :
    applyTypedMatchPattern left original = applyTypedMatchPattern right original := by
  have typeSame := recover_type leftClosed rightClosed original.type
    leftLocal rightLocal (congrArg TypedMatchPattern.type same)
  have resolutionSame := recover_pattern_resolution leftClosed rightClosed original.resolution
    leftLocal rightLocal (congrArg TypedMatchPattern.resolution same)
  dsimp only [applyTypedMatchPattern]
  rw [typeSame, resolutionSame]

private theorem recover_case (original : TypedMatchCase)
    (leftLocal rightLocal : Substitution)
    (same : (applyTypedMatchCase left original).applySubstitution leftLocal =
      (applyTypedMatchCase right original).applySubstitution rightLocal) :
    applyTypedMatchCase left original = applyTypedMatchCase right original := by
  have patternSame := recover_pattern leftClosed rightClosed original.pattern
    leftLocal rightLocal (congrArg TypedMatchCase.pattern same)
  dsimp only [applyTypedMatchCase]
  rw [patternSame]

private theorem recover_match (original : MatchResolution)
    (leftLocal rightLocal : Substitution)
    (same : (applyMatchResolution left original).applySubstitution leftLocal =
      (applyMatchResolution right original).applySubstitution rightLocal) :
    applyMatchResolution left original = applyMatchResolution right original := by
  have casesSame : original.cases.map (applyTypedMatchCase left) =
      original.cases.map (applyTypedMatchCase right) :=
    recover_map original.cases _ _ _ _
      (fun item itemSame => recover_case leftClosed rightClosed item leftLocal rightLocal itemSame)
      (congrArg MatchResolution.cases same)
  dsimp only [applyMatchResolution]
  rw [casesSame]

private theorem recover_expression_form (original : ExpressionForm)
    (leftLocal rightLocal : Substitution)
    (same : (applyExpressionForm left original).applySubstitution leftLocal =
      (applyExpressionForm right original).applySubstitution rightLocal) :
    applyExpressionForm left original = applyExpressionForm right original := by
  cases original with
  | literal value => rfl
  | integerLiteral value resolution =>
      exact congrArg (ExpressionForm.integerLiteral value)
        (recover_integer leftClosed rightClosed resolution leftLocal rightLocal
          (ExpressionForm.integerLiteral.inj same).2)
  | reference name resolution =>
      exact congrArg (ExpressionForm.reference name)
        (recover_reference leftClosed rightClosed resolution leftLocal rightLocal
          (ExpressionForm.reference.inj same).2)
  | group inner => rfl
  | tuple elements => rfl
  | unary operator operand => rfl
  | binary first operator second => rfl
  | conditional condition first second => rfl
  | lambda parameters result body =>
      have fields := ExpressionForm.lambda.inj same
      have parametersSame : parameters.map (applyBinder left) =
          parameters.map (applyBinder right) :=
        recover_map parameters _ _ _ _
          (fun item itemSame => recover_binder leftClosed rightClosed item leftLocal rightLocal itemSame)
          fields.1
      have resultSame := recover_type leftClosed rightClosed result leftLocal rightLocal fields.2.1
      dsimp only [applyExpressionForm]
      rw [parametersSame, resultSame]
  | call callee arguments resolution =>
      exact congrArg (ExpressionForm.call callee arguments)
        (recover_call leftClosed rightClosed resolution leftLocal rightLocal
          (ExpressionForm.call.inj same).2.2)
  | constructor instantiation arguments =>
      have instantiationSame := recover_constructor leftClosed rightClosed instantiation
        leftLocal rightLocal (ExpressionForm.constructor.inj same).1
      exact congrArg (fun selected => ExpressionForm.constructor selected arguments) instantiationSame
  | member base name index => rfl
  | proxy type =>
      exact congrArg ExpressionForm.proxy
        (recover_type leftClosed rightClosed type leftLocal rightLocal (ExpressionForm.proxy.inj same))
  | index base key => rfl

private theorem recover_place (original : PlaceResolution)
    (leftLocal rightLocal : Substitution)
    (same : (applyPlaceResolution left original).applySubstitution leftLocal =
      (applyPlaceResolution right original).applySubstitution rightLocal) :
    applyPlaceResolution left original = applyPlaceResolution right original := by
  have typeSame := recover_type leftClosed rightClosed original.type
    leftLocal rightLocal (congrArg PlaceResolution.type same)
  dsimp only [applyPlaceResolution]
  rw [typeSame]

private theorem recover_assignment (original : AssignmentResolution)
    (leftLocal rightLocal : Substitution)
    (same : (applyAssignmentResolution left original).applySubstitution leftLocal =
      (applyAssignmentResolution right original).applySubstitution rightLocal) :
    applyAssignmentResolution left original = applyAssignmentResolution right original := by
  have targetSame := recover_place leftClosed rightClosed original.target
    leftLocal rightLocal (congrArg AssignmentResolution.target same)
  dsimp only [applyAssignmentResolution]
  rw [targetSame]

private theorem recover_for_item (original : ForItemForm)
    (leftLocal rightLocal : Substitution)
    (same : (applyForItemForm left original).applySubstitution leftLocal =
      (applyForItemForm right original).applySubstitution rightLocal) :
    applyForItemForm left original = applyForItemForm right original := by
  cases original with
  | letDecl binder initializer =>
      exact congrArg (fun selected => ForItemForm.letDecl selected initializer)
        (recover_binder leftClosed rightClosed binder leftLocal rightLocal
          (ForItemForm.letDecl.inj same).1)
  | expression id => rfl
  | assignValue assignment operator value =>
      exact congrArg (fun selected => ForItemForm.assignValue selected operator value)
        (recover_assignment leftClosed rightClosed assignment leftLocal rightLocal
          (ForItemForm.assignValue.inj same).1)
  | assignBitNot assignment =>
      exact congrArg ForItemForm.assignBitNot
        (recover_assignment leftClosed rightClosed assignment leftLocal rightLocal
          (ForItemForm.assignBitNot.inj same))

private theorem recover_statement_form (original : StatementForm)
    (leftLocal rightLocal : Substitution)
    (same : (applyStatementForm left original).applySubstitution leftLocal =
      (applyStatementForm right original).applySubstitution rightLocal) :
    applyStatementForm left original = applyStatementForm right original := by
  cases original with
  | letDecl binder initializer =>
      exact congrArg (fun selected => StatementForm.letDecl selected initializer)
        (recover_binder leftClosed rightClosed binder leftLocal rightLocal
          (StatementForm.letDecl.inj same).1)
  | returnStmt value => rfl
  | expression id trailing => rfl
  | assignValue assignment operator value =>
      exact congrArg (fun selected => StatementForm.assignValue selected operator value)
        (recover_assignment leftClosed rightClosed assignment leftLocal rightLocal
          (StatementForm.assignValue.inj same).1)
  | assignBitNot assignment =>
      exact congrArg StatementForm.assignBitNot
        (recover_assignment leftClosed rightClosed assignment leftLocal rightLocal
          (StatementForm.assignBitNot.inj same))
  | ifThen condition first second => rfl
  | block body => rfl
  | matchWith resolution =>
      exact congrArg StatementForm.matchWith
        (recover_match leftClosed rightClosed resolution leftLocal rightLocal
          (StatementForm.matchWith.inj same))
  | forLoop initial condition post body =>
      have fields := StatementForm.forLoop.inj same
      have initialSame : initial.map (applyForItemForm left) =
          initial.map (applyForItemForm right) :=
        recover_map initial _ _ _ _
          (fun item itemSame => recover_for_item leftClosed rightClosed item
            leftLocal rightLocal itemSame) fields.1
      have postSame : post.map (applyForItemForm left) =
          post.map (applyForItemForm right) :=
        recover_map post _ _ _ _
          (fun item itemSame => recover_for_item leftClosed rightClosed item
            leftLocal rightLocal itemSame) fields.2.2.1
      dsimp only [applyStatementForm]
      rw [initialSame, postSame]
  | whileLoop condition body => rfl
  | breakStmt => rfl
  | continueStmt => rfl

private theorem recover_expression (original : ExpressionNode)
    (leftLocal rightLocal : Substitution)
    (same : (applyExpressionNode left original).applySubstitution leftLocal =
      (applyExpressionNode right original).applySubstitution rightLocal) :
    applyExpressionNode left original = applyExpressionNode right original := by
  have typeSame := recover_type leftClosed rightClosed original.type
    leftLocal rightLocal (congrArg ExpressionNode.type same)
  have formSame := recover_expression_form leftClosed rightClosed original.form
    leftLocal rightLocal (congrArg ExpressionNode.form same)
  have coercionsSame : original.coercions.map (applyCoercionStep left) =
      original.coercions.map (applyCoercionStep right) :=
    recover_map original.coercions _ _ _ _
      (fun item itemSame => recover_coercion leftClosed rightClosed item leftLocal rightLocal itemSame)
      (congrArg ExpressionNode.coercions same)
  dsimp only [applyExpressionNode]
  rw [typeSame, formSame, coercionsSame]

private theorem recover_statement (original : StatementNode)
    (leftLocal rightLocal : Substitution)
    (same : (applyStatementNode left original).applySubstitution leftLocal =
      (applyStatementNode right original).applySubstitution rightLocal) :
    applyStatementNode left original = applyStatementNode right original := by
  have typeSame := recover_type leftClosed rightClosed original.type
    leftLocal rightLocal (congrArg StatementNode.type same)
  have formSame := recover_statement_form leftClosed rightClosed original.form
    leftLocal rightLocal (congrArg StatementNode.form same)
  dsimp only [applyStatementNode]
  rw [typeSame, formSame]

private theorem recover_node (original : Node)
    (leftLocal rightLocal : Substitution)
    (same : (applyNode left original).applySubstitution leftLocal =
      (applyNode right original).applySubstitution rightLocal) :
    applyNode left original = applyNode right original := by
  cases original with
  | expression node =>
      exact congrArg Node.expression
        (recover_expression leftClosed rightClosed node leftLocal rightLocal (Node.expression.inj same))
  | statement node =>
      exact congrArg Node.statement
        (recover_statement leftClosed rightClosed node leftLocal rightLocal (Node.statement.inj same))

/-- Equality of final local source instances recovers every field of their
rigid instances of the same original source. Quantified local scheme variables
retain their actual restricted flexible substitutions. Node order, duplicate
entries, identities, spans and all non-type metadata remain literal. -/
theorem apply_source_eq_of_equal_local_instances (original : TypedSource)
    (leftLocal rightLocal : Substitution)
    (same : (applyTypedSource left original).applySubstitution leftLocal =
      (applyTypedSource right original).applySubstitution rightLocal) :
    applyTypedSource left original = applyTypedSource right original := by
  have inputsSame : original.inputs.map (applyBinder left) =
      original.inputs.map (applyBinder right) :=
    recover_map original.inputs _ _ _ _
      (fun item itemSame => recover_binder leftClosed rightClosed item leftLocal rightLocal itemSame)
      (congrArg TypedSource.inputs same)
  have nodesSame : original.nodes.map (applyNode left) =
      original.nodes.map (applyNode right) :=
    recover_map original.nodes _ _ _ _
      (fun item itemSame => recover_node leftClosed rightClosed item leftLocal rightLocal itemSame)
      (congrArg TypedSource.nodes same)
  dsimp only [applyTypedSource]
  rw [inputsSame, nodesSame]

end
end Solcore.Frontend.CorrelatedTypedSourceInstances

