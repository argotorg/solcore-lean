import Solcore.Frontend.SourceSpecialization
import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition

/-! Agreement on the types inspected by the actual residual validator determines
the flexible substitution action on that node. Binder metadata uses the same
quantifier mask as TypedBinder.applySubstitution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceResidualNodeSubstitutionAgreement
open Frontend SourceInference TypeSystem
open CoreLowering.CallableAncestryProfiles.SourceComposition

private def Agree (left right : Substitution) (types : List Ty) : Prop :=
  ∀ type ∈ types, left.apply type = right.apply type

private theorem Agree.mono {left right : Substitution} {small large : List Ty}
    (same : Agree left right large) (subset : ∀ type ∈ small, type ∈ large) :
    Agree left right small := fun type member => same type (subset type member)

private theorem Agree.head {left right : Substitution} {type : Ty} {types : List Ty}
    (same : Agree left right (type :: types)) : left.apply type = right.apply type :=
  same type (by simp)

private theorem Agree.tail {left right : Substitution} {type : Ty} {types : List Ty}
    (same : Agree left right (type :: types)) : Agree left right types :=
  same.mono (by intro type member; exact List.mem_cons_of_mem _ member)

private theorem Agree.left {left right : Substitution} {xs ys : List Ty}
    (same : Agree left right (xs ++ ys)) : Agree left right xs :=
  same.mono (by intro type member; exact List.mem_append_left _ member)

private theorem Agree.right {left right : Substitution} {xs ys : List Ty}
    (same : Agree left right (xs ++ ys)) : Agree left right ys :=
  same.mono (by intro type member; exact List.mem_append_right _ member)

private theorem Agree.flatMap {α : Type} {left right : Substitution}
    {xs : List α} {types : α → List Ty}
    (same : Agree left right (xs.flatMap types)) {x : α} (member : x ∈ xs) :
    Agree left right (types x) :=
  same.mono (by intro type present; exact List.mem_flatMap.mpr ⟨x, member, present⟩)

private theorem Agree.map {left right : Substitution} {types : List Ty}
    (same : Agree left right types) : types.map left.apply = types.map right.apply :=
  List.map_congr_left same

-- These structural views are definitionally the validator's private collectors.
-- The public endpoint below checks their exact agreement with its public aliases.
private def predicateTypes (predicate : ProgramPredicate) : List Ty :=
  predicate.subject :: predicate.arguments

private def declarationTypes (instantiation : DeclarationInstantiation) : List Ty :=
  instantiation.parameterSubstitution.map Prod.snd ++
    instantiation.type :: instantiation.predicates.flatMap predicateTypes

private def constructorTypes (instantiation : DataConstructorInstantiation) : List Ty :=
  instantiation.parameterSubstitution.map Prod.snd ++
    instantiation.resultType :: instantiation.payloadTypes

private def coercionTypes (steps : List CoercionStep) : List Ty :=
  steps.flatMap fun step => [step.source, step.target]

private def referenceTypes : ReferenceResolution → List Ty
  | .local _
  | .builtinFunction _
  | .builtinBoolean _ => []
  | .declaration instantiation => declarationTypes instantiation

private def callTypes : CallResolution → List Ty
  | .indirect metadata =>
    metadata.argumentTypeBeforeCoercion :: metadata.argumentTypeAfterCoercion ::
      coercionTypes metadata.argumentCoercions
  | .declaration instantiation => declarationTypes instantiation
  | .builtinFunction _ => []

private def expressionTypes : ExpressionForm → List Ty
  | .reference _ resolution => referenceTypes resolution
  | .integerLiteral _ resolution => [resolution.targetType]
  | .lambda _ returnType _ => [returnType]
  | .call _ _ resolution => callTypes resolution
  | .constructor instantiation _ => constructorTypes instantiation
  | .proxy inner => [inner]
  | .literal _
  | .group _
  | .tuple _
  | .unary _ _
  | .binary _ _ _
  | .conditional _ _ _
  | .member _ _ _
  | .index _ _ => []

private def expressionBinders : ExpressionForm → List TypedBinder
  | .lambda parameters _ _ => parameters
  | _ => []

private def instructionTypes : MatchPatternInstruction → List Ty
  | .wildcard
  | .tuple _ => []
  | .integerLiteral _ resolution => [resolution.targetType]
  | .binder binder => [binder.scheme.body]
  | .constructor instantiation _ => constructorTypes instantiation

private def patternTypes : MatchPatternResolution → List Ty
  | .wildcard => []
  | .integerLiteral _ resolution => [resolution.targetType]
  | .binder binder => [binder.scheme.body]
  | .constructor instantiation instructions =>
      constructorTypes instantiation ++ instructions.flatMap instructionTypes
  | .tuple instructions => instructions.flatMap instructionTypes

private def instructionBinders (instructions : List MatchPatternInstruction) : List TypedBinder :=
  instructions.filterMap fun
    | .binder binder => some binder
    | _ => none

private def patternBinders : MatchPatternResolution → List TypedBinder
  | .binder binder => [binder]
  | .constructor _ instructions | .tuple instructions => instructionBinders instructions
  | _ => []

private def forTypes : ForItemForm → List Ty
  | .letDecl binder _ => [binder.scheme.body]
  | .assignValue assignment _ _ | .assignBitNot assignment => [assignment.target.type]
  | .expression _ => []

private def forBinders (items : List ForItemForm) : List TypedBinder :=
  items.filterMap fun
    | .letDecl binder _ => some binder
    | _ => none

private def statementTypes : StatementForm → List Ty
  | .letDecl _ _ => []
  | .returnStmt _
  | .expression _ _
  | .ifThen _ _ _
  | .block _
  | .whileLoop _ _
  | .breakStmt
  | .continueStmt => []
  | .assignValue assignment _ _ | .assignBitNot assignment => [assignment.target.type]
  | .forLoop initializer _ post _ => (initializer ++ post).flatMap forTypes
  | .matchWith resolution =>
    resolution.cases.flatMap fun arm =>
      arm.pattern.type :: patternTypes arm.pattern.resolution

private def statementBinders : StatementForm → List TypedBinder
  | .letDecl binder _ => [binder]
  | .forLoop initializer _ post _ => forBinders (initializer ++ post)
  | .matchWith resolution => resolution.cases.flatMap fun arm => patternBinders arm.pattern.resolution
  | _ => []

private theorem predicate_congr {left right : Substitution} {predicate : ProgramPredicate}
    (same : Agree left right (predicateTypes predicate)) :
    TypedTraitResolution.applySubstitution left predicate =
      TypedTraitResolution.applySubstitution right predicate := by
  have subject := same.head
  have arguments := same.tail.map
  simp only [TypedTraitResolution.applySubstitution, subject, arguments]

/-- The actual binder action is determined by its masked body and predicate types. -/
theorem binder_congr {left right : Substitution} {binder : TypedBinder}
    (same : ∀ type ∈ SourceSpecialization.residualBinderTypes binder,
      (left.without binder.scheme.quantified).apply type =
        (right.without binder.scheme.quantified).apply type) :
    binder.applySubstitution left = binder.applySubstitution right := by
  change Agree (left.without binder.scheme.quantified)
    (right.without binder.scheme.quantified)
    (binder.scheme.body :: binder.schemeRequirements.flatMap fun row =>
      predicateTypes row.predicate) at same
  have body := same.head
  have requirements :
      binder.schemeRequirements.map (LocalSchemeRequirement.applySubstitution (left.without binder.scheme.quantified)) =
      binder.schemeRequirements.map (LocalSchemeRequirement.applySubstitution (right.without binder.scheme.quantified)) := by
    apply List.map_congr_left
    intro row member
    have predicate := predicate_congr (same.tail.flatMap member)
    simp only [LocalSchemeRequirement.applySubstitution, predicate]
  simp only [TypedBinder.applySubstitution, Scheme.apply, mask_twice, body, requirements]

private theorem parameters_congr {left right : Substitution} {parameters : ParameterSubstitution}
    (same : Agree left right (parameters.map Prod.snd)) :
    parameters.map (fun entry => (entry.1, left.apply entry.2)) =
      parameters.map (fun entry => (entry.1, right.apply entry.2)) := by
  apply List.map_congr_left
  intro entry member
  have value := same entry.2 (List.mem_map.mpr ⟨entry, member, rfl⟩)
  simp only [value]

private theorem declaration_congr {left right : Substitution} {value : DeclarationInstantiation}
    (same : Agree left right (declarationTypes value)) :
    value.applySubstitution left = value.applySubstitution right := by
  have parameters := parameters_congr same.left
  have type := same.right.head
  have predicates :
      value.predicates.map (TypedTraitResolution.applySubstitution left) =
      value.predicates.map (TypedTraitResolution.applySubstitution right) :=
    List.map_congr_left (fun _ member => predicate_congr (same.right.tail.flatMap member))
  unfold DeclarationInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map
      (fun (entry : TypeParameterId × Ty) => (entry.1, left.apply entry.2))
    type := left.apply value.type
    predicates := value.predicates.map (TypedTraitResolution.applySubstitution left) } =
    { value with
    parameterSubstitution := value.parameterSubstitution.map
      (fun (entry : TypeParameterId × Ty) => (entry.1, right.apply entry.2))
    type := right.apply value.type
    predicates := value.predicates.map (TypedTraitResolution.applySubstitution right) }
  rw [parameters, type, predicates]

private theorem constructor_congr {left right : Substitution} {value : DataConstructorInstantiation}
    (same : Agree left right (constructorTypes value)) :
    value.applySubstitution left = value.applySubstitution right := by
  have parameters := parameters_congr same.left
  have result := same.right.head
  have payloads := same.right.tail.map
  unfold DataConstructorInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map
      (fun (entry : TypeParameterId × Ty) => (entry.1, left.apply entry.2))
    payloadTypes := value.payloadTypes.map left.apply
    resultType := left.apply value.resultType } =
    { value with
    parameterSubstitution := value.parameterSubstitution.map
      (fun (entry : TypeParameterId × Ty) => (entry.1, right.apply entry.2))
    payloadTypes := value.payloadTypes.map right.apply
    resultType := right.apply value.resultType }
  rw [parameters, result, payloads]

private theorem coercions_congr {left right : Substitution} {steps : List CoercionStep}
    (same : Agree left right (coercionTypes steps)) :
    steps.map (CoercionStep.applySubstitution left) =
      steps.map (CoercionStep.applySubstitution right) := by
  apply List.map_congr_left
  intro step member
  have source := (same.flatMap member).head
  have target := (same.flatMap member).tail.head
  simp only [CoercionStep.applySubstitution, source, target]

private theorem integer_congr {left right : Substitution} {resolution : IntegerLiteralResolution}
    (same : left.apply resolution.targetType = right.apply resolution.targetType) :
    resolution.applySubstitution left = resolution.applySubstitution right := by
  simp only [IntegerLiteralResolution.applySubstitution, same]

private theorem reference_congr {left right : Substitution} {resolution : ReferenceResolution}
    (same : Agree left right (referenceTypes resolution)) :
    resolution.applySubstitution left = resolution.applySubstitution right := by
  cases resolution with
  | declaration value =>
    exact congrArg ReferenceResolution.declaration (declaration_congr same)
  | «local» | builtinFunction | builtinBoolean => rfl

private theorem call_congr {left right : Substitution} {resolution : CallResolution}
    (same : Agree left right (callTypes resolution)) :
    resolution.applySubstitution left = resolution.applySubstitution right := by
  cases resolution with
  | declaration value => exact congrArg CallResolution.declaration (declaration_congr same)
  | builtinFunction => rfl
  | indirect metadata =>
    have before := same.head
    have after := same.tail.head
    have coercions := coercions_congr same.tail.tail
    simp only [CallResolution.applySubstitution, IndirectCallResolution.applySubstitution,
      before, after, coercions]

private theorem expression_congr {left right : Substitution} {form : ExpressionForm}
    (same : Agree left right (expressionTypes form))
    (binders : ∀ binder ∈ expressionBinders form,
      binder.applySubstitution left = binder.applySubstitution right) :
    form.applySubstitution left = form.applySubstitution right := by
  cases form with
  | integerLiteral _ resolution => exact congrArg _ (integer_congr same.head)
  | reference _ resolution => exact congrArg _ (reference_congr same)
  | lambda parameters returnType body =>
    have parameters : parameters.map (TypedBinder.applySubstitution left) =
        parameters.map (TypedBinder.applySubstitution right) := List.map_congr_left binders
    have returnType := same.head
    simp only [ExpressionForm.applySubstitution, parameters, returnType]
  | call _ _ resolution => exact congrArg _ (call_congr same)
  | constructor instantiation arguments =>
    exact congrArg (fun value => ExpressionForm.constructor value arguments) (constructor_congr same)
  | proxy _ => exact congrArg _ same.head
  | literal | group | tuple | unary | binary | conditional | member | index => rfl

private theorem instruction_congr {left right : Substitution} {instruction : MatchPatternInstruction}
    (same : Agree left right (instructionTypes instruction))
    (binders : ∀ binder ∈ instructionBinders [instruction],
      binder.applySubstitution left = binder.applySubstitution right) :
    instruction.applySubstitution left = instruction.applySubstitution right := by
  cases instruction with
  | wildcard | tuple => rfl
  | integerLiteral source resolution => exact congrArg _ (integer_congr same.head)
  | binder binder =>
    exact congrArg MatchPatternInstruction.binder
      (binders binder (by simp [instructionBinders]))
  | constructor instantiation count =>
    exact congrArg (fun value => MatchPatternInstruction.constructor value count)
      (constructor_congr same)

private theorem instructions_congr {left right : Substitution}
    {instructions : List MatchPatternInstruction}
    (same : Agree left right (instructions.flatMap instructionTypes))
    (binders : ∀ binder ∈ instructionBinders instructions,
      binder.applySubstitution left = binder.applySubstitution right) :
    instructions.map (MatchPatternInstruction.applySubstitution left) =
      instructions.map (MatchPatternInstruction.applySubstitution right) := by
  apply List.map_congr_left
  intro instruction member
  apply instruction_congr (same.flatMap member)
  intro binder bound
  apply binders binder
  obtain ⟨selected, selectedMember, equality⟩ := List.mem_filterMap.mp bound
  have selectedEq : selected = instruction := List.mem_singleton.mp selectedMember
  exact List.mem_filterMap.mpr ⟨instruction, member, selectedEq ▸ equality⟩

private theorem pattern_congr {left right : Substitution} {pattern : MatchPatternResolution}
    (same : Agree left right (patternTypes pattern))
    (binders : ∀ binder ∈ patternBinders pattern,
      binder.applySubstitution left = binder.applySubstitution right) :
    pattern.applySubstitution left = pattern.applySubstitution right := by
  cases pattern with
  | wildcard => rfl
  | integerLiteral source resolution => exact congrArg _ (integer_congr same.head)
  | binder binder =>
    exact congrArg MatchPatternResolution.binder (binders binder (by simp [patternBinders]))
  | constructor instantiation instructions =>
    have constructor := constructor_congr same.left
    have instructions := instructions_congr same.right binders
    simp only [MatchPatternResolution.applySubstitution, constructor, instructions]
  | tuple instructions =>
    exact congrArg MatchPatternResolution.tuple (instructions_congr same binders)

private theorem assignment_congr {left right : Substitution} {assignment : AssignmentResolution}
    (same : left.apply assignment.target.type = right.apply assignment.target.type) :
    assignment.applySubstitution left = assignment.applySubstitution right := by
  simp only [AssignmentResolution.applySubstitution, PlaceResolution.applySubstitution, same]

private theorem forItem_congr {left right : Substitution} {item : ForItemForm}
    (same : Agree left right (forTypes item))
    (binders : ∀ binder ∈ forBinders [item],
      binder.applySubstitution left = binder.applySubstitution right) :
    item.applySubstitution left = item.applySubstitution right := by
  cases item with
  | letDecl binder initializer =>
    exact congrArg (fun value => ForItemForm.letDecl value initializer)
      (binders binder (by simp [forBinders]))
  | expression => rfl
  | assignValue assignment operator value =>
    exact congrArg (fun target => ForItemForm.assignValue target operator value)
      (assignment_congr same.head)
  | assignBitNot assignment => exact congrArg ForItemForm.assignBitNot (assignment_congr same.head)

private theorem forItems_congr {left right : Substitution} {items : List ForItemForm}
    (same : Agree left right (items.flatMap forTypes))
    (binders : ∀ binder ∈ forBinders items,
      binder.applySubstitution left = binder.applySubstitution right) :
    items.map (ForItemForm.applySubstitution left) =
      items.map (ForItemForm.applySubstitution right) := by
  apply List.map_congr_left
  intro item member
  apply forItem_congr (same.flatMap member)
  intro binder bound
  apply binders binder
  obtain ⟨selected, selectedMember, equality⟩ := List.mem_filterMap.mp bound
  have selectedEq : selected = item := List.mem_singleton.mp selectedMember
  exact List.mem_filterMap.mpr ⟨item, member, selectedEq ▸ equality⟩

private theorem match_congr {left right : Substitution} {resolution : MatchResolution}
    (same : Agree left right (resolution.cases.flatMap fun arm =>
      arm.pattern.type :: patternTypes arm.pattern.resolution))
    (binders : ∀ binder ∈ resolution.cases.flatMap (fun arm => patternBinders arm.pattern.resolution),
      binder.applySubstitution left = binder.applySubstitution right) :
    resolution.applySubstitution left = resolution.applySubstitution right := by
  have arms : resolution.cases.map (TypedMatchCase.applySubstitution left) =
      resolution.cases.map (TypedMatchCase.applySubstitution right) := by
    apply List.map_congr_left
    intro arm member
    have type := (same.flatMap member).head
    have pattern := pattern_congr (same.flatMap member).tail
      (fun binder bound => binders binder (List.mem_flatMap.mpr ⟨arm, member, bound⟩))
    simp only [TypedMatchCase.applySubstitution, TypedMatchPattern.applySubstitution, type, pattern]
  simp only [MatchResolution.applySubstitution, arms]

private theorem statement_congr {left right : Substitution} {form : StatementForm}
    (same : Agree left right (statementTypes form))
    (binders : ∀ binder ∈ statementBinders form,
      binder.applySubstitution left = binder.applySubstitution right) :
    form.applySubstitution left = form.applySubstitution right := by
  cases form with
  | letDecl binder initializer =>
    exact congrArg (fun value => StatementForm.letDecl value initializer)
      (binders binder (by simp [statementBinders]))
  | assignValue assignment operator value =>
    exact congrArg (fun target => StatementForm.assignValue target operator value)
      (assignment_congr same.head)
  | assignBitNot assignment => exact congrArg StatementForm.assignBitNot (assignment_congr same.head)
  | matchWith resolution => exact congrArg StatementForm.matchWith (match_congr same binders)
  | forLoop initializer condition post body =>
    have allTypes : Agree left right
        (initializer.flatMap forTypes ++ post.flatMap forTypes) := by
      simpa only [statementTypes, List.flatMap_append] using same
    have initialBinders : ∀ binder ∈ forBinders initializer,
        binder.applySubstitution left = binder.applySubstitution right := by
      intro binder member
      apply binders binder
      simpa only [statementBinders, forBinders, List.filterMap_append] using
        List.mem_append_left (forBinders post) member
    have postBinders : ∀ binder ∈ forBinders post,
        binder.applySubstitution left = binder.applySubstitution right := by
      intro binder member
      apply binders binder
      simpa only [statementBinders, forBinders, List.filterMap_append] using
        List.mem_append_right (forBinders initializer) member
    have initializer := forItems_congr allTypes.left initialBinders
    have post := forItems_congr allTypes.right postBinders
    simp only [StatementForm.applySubstitution, initializer, post]
  | returnStmt | expression | ifThen | block | whileLoop | breakStmt | continueStmt => rfl

/-- Equality is required only at the actual residual validator's inspected
types. No global lookup agreement is needed; each embedded binder retains its
own mask, including its local scheme requirements. -/
theorem node_congr {left right : Substitution} {node : Node}
    (same : ∀ type ∈ SourceSpecialization.residualNodeTypes node,
      left.apply type = right.apply type)
    (masked : ∀ binder ∈ SourceSpecialization.residualNodeBinders node,
      ∀ type ∈ SourceSpecialization.residualBinderTypes binder,
      (left.without binder.scheme.quantified).apply type =
        (right.without binder.scheme.quantified).apply type) :
    node.applySubstitution left = node.applySubstitution right := by
  have binders : ∀ binder ∈ SourceSpecialization.residualNodeBinders node,
      binder.applySubstitution left = binder.applySubstitution right :=
    fun binder member => binder_congr (masked binder member)
  cases node with
  | expression value =>
    change Agree left right (value.type :: expressionTypes value.form ++
      coercionTypes value.coercions) at same
    change ∀ binder ∈ expressionBinders value.form,
      binder.applySubstitution left = binder.applySubstitution right at binders
    have type := same.head
    have form := expression_congr same.tail.left binders
    have coercions := coercions_congr same.tail.right
    simp only [Node.applySubstitution, ExpressionNode.applySubstitution, type, form, coercions]
  | statement value =>
    change Agree left right (value.type :: statementTypes value.form) at same
    change ∀ binder ∈ statementBinders value.form,
      binder.applySubstitution left = binder.applySubstitution right at binders
    have type := same.head
    have form := statement_congr same.tail binders
    simp only [Node.applySubstitution, StatementNode.applySubstitution, type, form]

end Solcore.SourceSemantics.SourceResidualNodeSubstitutionAgreement
