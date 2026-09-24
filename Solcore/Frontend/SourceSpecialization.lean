import Solcore.Frontend.SourceInference.Types
import Solcore.Frontend.SourceStageAnalysis

/-!
Closing specialization for checked generic source functions.

The resolved signature supplies the authoritative declaration-parameter order,
including parameters which do not occur in the function type or body.  The
result keeps source/declaration identities intact while closing every semantic
type retained by source inference.  Top-level types are fully ground; a
generalized initialized `let` may retain its quantified variables only inside
a direct lambda initializer, where they have an explicit lexical scope.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceSpecialization

open SourceInference TypeSystem

/-- Why a purported concrete type is not closed. -/
inductive NonConcreteType where
  | flexible (id : TypeVarId)
  | rigid (id : TypeParameterId)
  | error
  deriving Repr, DecidableEq

/-- Rejections at the generic-function specialization boundary. -/
inductive Error where
  | declarationMismatch
      (signature function : Resolved.DeclarationId)
  | typedBodyOwnerMismatch
      (expected actual : Resolved.DeclarationId)
  | signatureTypeMismatch (signature function : Ty)
  | parameterComptimeMismatch
      (signature typedBody : List Bool)
  | returnComptimeMismatch
      (signature function : Bool)
  | declaredParameterOwnerMismatch
      (expected : Resolved.DeclarationId) (parameter : TypeParameterId)
  | duplicateDeclaredParameter (parameter : TypeParameterId)
  | suppliedParameterOwnerMismatch
      (expected : Resolved.DeclarationId) (parameter : TypeParameterId)
  | duplicateSuppliedParameter (parameter : TypeParameterId)
  | unknownSuppliedParameter (parameter : TypeParameterId)
  | missingSuppliedParameter (parameter : TypeParameterId)
  | observedParameterOwnerMismatch
      (expected : Resolved.DeclarationId) (parameter : TypeParameterId)
  | undeclaredObservedParameter (parameter : TypeParameterId)
  | nonConcreteArgument
      (parameter : TypeParameterId) (reason : NonConcreteType)
  | polymorphicBinder (binder : Resolved.LocalId) (variables : List TypeVarId)
  | evidenceGoalMismatch (id : RequirementId)
      (predicate goal : ProgramPredicate)
  | stageAnalysis (error : SourceStageAnalysis.Error)
  | residualType (reason : NonConcreteType)
  deriving Repr, DecidableEq

/-- Worklist identity for one declaration specialized at concrete arguments in
authoritative signature order. -/
structure SpecializationKey where
  declaration : Resolved.DeclarationId
  arguments : List Ty
  deriving Repr, BEq, DecidableEq

/-- A declaration-order specialization together with the checked source
carrier.  `assumptions` are the signature's specialized where predicates; the
checked function retains all original owner and occurrence identities.
Top-level types are closed, while a direct generalized lambda initializer may
retain the variables quantified by its owning local scheme. -/
structure SpecializedFunction where
  key : SpecializationKey
  declaration : Resolved.DeclarationId
  parameterSubstitution : ParameterSubstitution
  assumptions : List ProgramPredicate
  function : CheckedFunction
  /-- Scope-aware source-stage facts for this exact specialization. -/
  stageAnalysis : SourceStageAnalysis.Analysis
  deriving Repr, BEq

def applyScheme (substitution : ParameterSubstitution) (scheme : Scheme) : Scheme :=
  { scheme with body := substitution.apply scheme.body }

def applyBinder (substitution : ParameterSubstitution)
    (binder : TypedBinder) : TypedBinder :=
  { binder with scheme := applyScheme substitution binder.scheme }

def applyInstantiation (substitution : ParameterSubstitution)
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
      .declaration (applyInstantiation substitution instantiation)
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
      .declaration (applyInstantiation substitution instantiation)
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
  | .binder selectedBinder => .binder (applyBinder substitution selectedBinder)
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
  | .binder selectedBinder => .binder (applyBinder substitution selectedBinder)
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
    (arm : TypedMatchCase) : TypedMatchCase := {
  arm with pattern := applyTypedMatchPattern substitution arm.pattern
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
  | .letDecl selectedBinder initializer =>
      .letDecl (applyBinder substitution selectedBinder) initializer
  | .expression expressionId => .expression expressionId
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

/-- Apply a declaration-parameter substitution without changing source graph
ownership, roots, or occurrence identities. -/
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

/-- Apply rigid specialization to every retained type in a checked function.
The inference substitution is provenance, but its range is specialized as well
so it cannot retain a hidden rigid or flexible type. -/
def applyCheckedFunction (substitution : ParameterSubstitution)
    (function : CheckedFunction) : CheckedFunction := {
  function with
  type := substitution.apply function.type
  inferredBodyType := substitution.apply function.inferredBodyType
  substitution := function.substitution.map fun entry =>
    (entry.1, substitution.apply entry.2)
  solvedRequirements := function.solvedRequirements.map
    (applySolvedRequirement substitution)
  typedBody := applyTypedSource substitution function.typedBody
}

private def firstDuplicate : List TypeParameterId → Option TypeParameterId
  | [] => none
  | parameter :: rest =>
      if rest.contains parameter then some parameter else firstDuplicate rest

private def firstNonConcrete : Ty → Option NonConcreteType
  | .variable id => some (.flexible id)
  | .parameter id => some (.rigid id)
  | .constructor _ => none
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right =>
      (firstNonConcrete left).orElse fun _ => firstNonConcrete right
  | .proxy inner
  | .comptime inner => firstNonConcrete inner
  | .error => some .error

private def predicateTypes (predicate : ProgramPredicate) : List Ty :=
  predicate.subject :: predicate.arguments

mutual

  private def evidenceTypes :
      TypedTraitResolution.Evidence → List Ty
    | .byImpl goal _ premises =>
        predicateTypes goal ++ evidencesTypes premises

  private def evidencesTypes :
      List TypedTraitResolution.Evidence → List Ty
    | [] => []
    | evidence :: rest => evidenceTypes evidence ++ evidencesTypes rest

end

private def predicateEvidenceTypes : PredicateEvidence → List Ty
  | .assumption predicate => predicateTypes predicate
  | .implementation evidence => evidenceTypes evidence

private def requirementTypes (requirement : SolvedRequirement) : List Ty :=
  predicateTypes requirement.predicate ++
    predicateEvidenceTypes requirement.evidence

private def instantiationTypes
    (instantiation : DeclarationInstantiation) : List Ty :=
  instantiation.parameterSubstitution.map Prod.snd ++
    instantiation.type :: instantiation.predicates.flatMap predicateTypes

private def referenceTypes : ReferenceResolution → List Ty
  | .local _
  | .builtinFunction _
  | .builtinBoolean _ => []
  | .declaration instantiation => instantiationTypes instantiation

private def callResolutionTypes : CallResolution → List Ty
  | .indirect metadata =>
      metadata.argumentTypeBeforeCoercion ::
        metadata.argumentTypeAfterCoercion ::
        metadata.argumentCoercions.flatMap fun step =>
          [step.source, step.target]
  | .declaration instantiation => instantiationTypes instantiation
  | .builtinFunction _ => []

private def dataInstantiationTypes
    (instantiation : DataConstructorInstantiation) : List Ty :=
  instantiation.parameterSubstitution.map Prod.snd ++
    instantiation.resultType :: instantiation.payloadTypes

private def matchInstructionTypes : MatchPatternInstruction → List Ty
  | .wildcard
  | .tuple _ => []
  | .integerLiteral _ resolution => [resolution.targetType]
  | .binder selectedBinder => [selectedBinder.scheme.body]
  | .constructor instantiation _ => dataInstantiationTypes instantiation

private def matchResolutionTypes : MatchPatternResolution → List Ty
  | .wildcard => []
  | .integerLiteral _ resolution => [resolution.targetType]
  | .binder selectedBinder => [selectedBinder.scheme.body]
  | .constructor instantiation arguments =>
      dataInstantiationTypes instantiation ++
        arguments.flatMap matchInstructionTypes
  | .tuple elements => elements.flatMap matchInstructionTypes

private def expressionFormTypes : ExpressionForm → List Ty
  | .reference _ resolution => referenceTypes resolution
  | .integerLiteral _ resolution => [resolution.targetType]
  | .lambda _ returnType _ => [returnType]
  | .call _ _ resolution => callResolutionTypes resolution
  | .constructor instantiation _ => dataInstantiationTypes instantiation
  | .proxy inner => [inner]
  | .literal _
  | .group _
  | .tuple _
  | .unary _ _
  | .binary _ _ _
  | .conditional _ _ _
  | .member _ _ _
  | .index _ _ => []

private def forItemTypes : ForItemForm → List Ty
  | .letDecl selectedBinder _ => [selectedBinder.scheme.body]
  | .assignValue assignment _ _
  | .assignBitNot assignment => [assignment.target.type]
  | .expression _ => []

private def statementFormTypes : StatementForm → List Ty
  | .letDecl _ _ => []
  | .returnStmt _
  | .expression _ _
  | .ifThen _ _ _
  | .block _
  | .whileLoop _ _
  | .breakStmt
  | .continueStmt => []
  | .assignValue assignment _ _
  | .assignBitNot assignment => [assignment.target.type]
  | .forLoop initializer _ post _ =>
      (initializer ++ post).flatMap forItemTypes
  | .matchWith resolution =>
      resolution.cases.flatMap fun arm =>
        arm.pattern.type :: matchResolutionTypes arm.pattern.resolution

private def nodeTypes : Node → List Ty
  | .expression node =>
      node.type :: expressionFormTypes node.form ++
        node.coercions.flatMap fun step => [step.source, step.target]
  | .statement node => node.type :: statementFormTypes node.form

private def typedSourceTypes (source : TypedSource) : List Ty :=
  source.nodes.flatMap nodeTypes

private def expressionFormBinders : ExpressionForm → List TypedBinder
  | .lambda parameters _ _ => parameters
  | _ => []

private def statementFormBinders : StatementForm → List TypedBinder
  | .letDecl binder _ => [binder]
  | .forLoop initializer _ post _ =>
      (initializer ++ post).filterMap fun
        | .letDecl selectedBinder _ => some selectedBinder
        | _ => none
  | .matchWith resolution =>
      resolution.cases.flatMap fun arm =>
        let instructionBinders := fun (instructions : List MatchPatternInstruction) =>
          instructions.filterMap fun
            | .binder selectedBinder => some selectedBinder
            | _ => none
        match arm.pattern.resolution with
        | .binder selectedBinder => [selectedBinder]
        | .constructor _ instructions
        | .tuple instructions => instructionBinders instructions
        | _ => []
  | _ => []

private def nodeBinders : Node → List TypedBinder
  | .expression node => expressionFormBinders node.form
  | .statement node => statementFormBinders node.form

private def typedSourceBinders (source : TypedSource) : List TypedBinder :=
  source.inputs ++ source.nodes.flatMap nodeBinders

private def checkedFunctionTypes (function : CheckedFunction) : List Ty :=
  [function.type, function.inferredBodyType] ++
    function.substitution.map Prod.snd ++
    function.solvedRequirements.flatMap requirementTypes ++
    typedSourceTypes function.typedBody

private def checkedFunctionParameterTypes (function : CheckedFunction) : List Ty :=
  checkedFunctionTypes function ++
    (typedSourceBinders function.typedBody).map (·.scheme.body)

private def insertParameter (parameters : List TypeParameterId)
    (parameter : TypeParameterId) : List TypeParameterId :=
  if parameters.contains parameter then parameters else parameters ++ [parameter]

private def typeParameters (parameters : List TypeParameterId) :
    Ty → List TypeParameterId
  | .parameter parameter => insertParameter parameters parameter
  | .variable _
  | .constructor _
  | .error => parameters
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right =>
      typeParameters (typeParameters parameters left) right
  | .proxy inner
  | .comptime inner => typeParameters parameters inner

private def parametersInTypes (types : List Ty) : List TypeParameterId :=
  types.foldl typeParameters []

private def validateDeclaredParameters (owner : Resolved.DeclarationId)
    (parameters : List TypeParameterId) : Except Error Unit := do
  match parameters.find? fun parameter => decide (parameter.owner != owner) with
  | some parameter => throw (.declaredParameterOwnerMismatch owner parameter)
  | none => pure ()
  match firstDuplicate parameters with
  | some parameter => throw (.duplicateDeclaredParameter parameter)
  | none => pure ()

private def validateSuppliedParameters (owner : Resolved.DeclarationId)
    (declared : List TypeParameterId) (supplied : ParameterSubstitution) :
    Except Error Unit := do
  let keys := supplied.map Prod.fst
  match keys.find? fun parameter => decide (parameter.owner != owner) with
  | some parameter => throw (.suppliedParameterOwnerMismatch owner parameter)
  | none => pure ()
  match firstDuplicate keys with
  | some parameter => throw (.duplicateSuppliedParameter parameter)
  | none => pure ()
  match keys.find? fun parameter => !(declared.contains parameter) with
  | some parameter => throw (.unknownSuppliedParameter parameter)
  | none => pure ()
  match declared.find? fun parameter => !(keys.contains parameter) with
  | some parameter => throw (.missingSuppliedParameter parameter)
  | none => pure ()

private def canonicalSubstitution :
    List TypeParameterId → ParameterSubstitution →
      Except Error ParameterSubstitution
  | [], _ => .ok []
  | parameter :: rest, supplied =>
      match supplied.lookup? parameter with
      | none => .error (.missingSuppliedParameter parameter)
      | some type => do
          match firstNonConcrete type with
          | some reason => throw (.nonConcreteArgument parameter reason)
          | none => pure ()
          pure ((parameter, type) ::
            (← canonicalSubstitution rest supplied))

private def validateObservedParameters (owner : Resolved.DeclarationId)
    (declared : List TypeParameterId) (types : List Ty) :
    Except Error Unit := do
  let observed := parametersInTypes types
  match observed.find? fun parameter => decide (parameter.owner != owner) with
  | some parameter => throw (.observedParameterOwnerMismatch owner parameter)
  | none => pure ()
  match observed.find? fun parameter => !(declared.contains parameter) with
  | some parameter => throw (.undeclaredObservedParameter parameter)
  | none => pure ()

private def validateConcreteTypes (types : List Ty) : Except Error Unit :=
  match types.findSome? firstNonConcrete with
  | some reason => .error (.residualType reason)
  | none => .ok ()

private def firstNonLexical
    (lexical : List TypeVarId) : Ty → Option NonConcreteType
  | .variable id =>
      if lexical.contains id then none else some (.flexible id)
  | .constructor _ => none
  | .parameter id => some (.rigid id)
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right =>
      (firstNonLexical lexical left).orElse fun _ =>
        firstNonLexical lexical right
  | .proxy inner
  | .comptime inner => firstNonLexical lexical inner
  | .error => some .error

private def appendVariables (left right : List TypeVarId) : List TypeVarId :=
  right.foldl (fun variables metavariable =>
    if variables.contains metavariable then variables
    else variables ++ [metavariable])
    left

private def validateLexicalTypes (lexical : List TypeVarId)
    (types : List Ty) : Except Error Unit :=
  match types.findSome? (firstNonLexical lexical) with
  | some reason => .error (.residualType reason)
  | none => pure ()

private def validateLexicalScheme (lexical : List TypeVarId)
    (scheme : Scheme) : Except Error Unit :=
  validateLexicalTypes (appendVariables lexical scheme.quantified) [scheme.body]

private def validateLexicalBinderSchemes (lexical : List TypeVarId) :
    List TypedBinder → Except Error Unit
  | [] => .ok ()
  | binder :: rest => do
      validateLexicalScheme lexical binder.scheme
      validateLexicalBinderSchemes lexical rest

/-- Whether an initializer edge points directly to a lambda node.  Grouping,
proxying, or calling a lambda does not satisfy the restricted polymorphic-let
profile. -/
def isDirectLambdaInitializer (source : TypedSource)
    (initializer : ExpressionId) : Bool :=
  match source.lookupExpression? initializer with
  | some { form := .lambda _ _ _, .. } => true
  | _ => false

private def polymorphicLetAllowed (source : TypedSource)
    (binder : TypedBinder) (initializer : Option ExpressionId) : Bool :=
  !binder.scheme.quantified.isEmpty &&
    initializer.any (isDirectLambdaInitializer source)

private def patternInstructionBinders :
    MatchPatternInstruction → List TypedBinder
  | .binder binder => [binder]
  | _ => []

private def patternResolutionBinders :
    MatchPatternResolution → List TypedBinder
  | .binder binder => [binder]
  | .constructor _ instructions
  | .tuple instructions => instructions.flatMap patternInstructionBinders
  | _ => []

private def unsupportedPolymorphicBindersInNode
    (source : TypedSource) : Node → List TypedBinder
  | .expression node =>
      match node.form with
      | .lambda parameters _ _ =>
          parameters.filter fun binder => !binder.scheme.quantified.isEmpty
      | _ => []
  | .statement node =>
      match node.form with
      | .letDecl binder initializer =>
          if binder.scheme.quantified.isEmpty ||
              polymorphicLetAllowed source binder initializer then
            []
          else
            [binder]
      | .forLoop initializer _ post _ =>
          (initializer ++ post).filterMap fun
            | .letDecl binder _ =>
                if binder.scheme.quantified.isEmpty then none else some binder
            | _ => none
      | .matchWith resolution =>
          resolution.cases.flatMap fun arm =>
            (patternResolutionBinders arm.pattern.resolution).filter fun binder =>
              !binder.scheme.quantified.isEmpty
      | _ => []

/-- Only ordinary initialized lets whose initializer node is directly a lambda
may remain quantified.  This positional rejection runs before residual-type
checking so unsupported quantified binders retain the precise legacy error. -/
private def validatePolymorphicBinderPositions (source : TypedSource) :
    Except Error Unit := do
  let unsupportedInputs := source.inputs.filter fun binder =>
    !binder.scheme.quantified.isEmpty
  let unsupportedNodes := source.nodes.flatMap
    (unsupportedPolymorphicBindersInNode source)
  match (unsupportedInputs ++ unsupportedNodes).head? with
  | some binder =>
      throw (.polymorphicBinder binder.id binder.scheme.quantified)
  | none => pure ()

private structure ResidualScopeTask where
  node : NodeId
  variables : List TypeVarId

private structure ResidualScope where
  node : NodeId
  variables : List TypeVarId

private def expressionTasks (variables : List TypeVarId)
    (expressions : List ExpressionId) : List ResidualScopeTask :=
  expressions.map fun expression => { node := .expression expression, variables }

private def statementTasks (variables : List TypeVarId)
    (statements : List StatementId) : List ResidualScopeTask :=
  statements.map fun statement => { node := .statement statement, variables }

private def projectionTasks (variables : List TypeVarId)
    (projections : List PlaceProjection) : List ResidualScopeTask :=
  projections.filterMap fun
    | .index key => some { node := .expression key, variables }
    | .member _ _ => none

private def assignmentTasks (variables : List TypeVarId)
    (assignment : AssignmentResolution) : List ResidualScopeTask :=
  projectionTasks variables assignment.target.projections

private def forItemTasks (variables : List TypeVarId) :
    ForItemForm → List ResidualScopeTask
  | .letDecl _ initializer =>
      initializer.toList.map fun expression =>
        { node := .expression expression, variables }
  | .expression expression =>
      [{ node := .expression expression, variables }]
  | .assignValue assignment _ value =>
      assignmentTasks variables assignment ++
        [{ node := .expression value, variables }]
  | .assignBitNot assignment => assignmentTasks variables assignment

private def expressionChildTasks (variables : List TypeVarId)
    (node : ExpressionNode) : List ResidualScopeTask :=
  match node.form with
  | .literal _
  | .integerLiteral _ _
  | .reference _ _
  | .proxy _ => []
  | .group inner
  | .unary _ inner
  | .member inner _ _ => expressionTasks variables [inner]
  | .tuple elements => expressionTasks variables elements
  | .binary left _ right
  | .index left right => expressionTasks variables [left, right]
  | .conditional condition thenBranch elseBranch =>
      expressionTasks variables [condition, thenBranch, elseBranch]
  | .lambda _ _ body => statementTasks variables body
  | .call callee arguments _ =>
      expressionTasks variables (callee :: arguments)
  | .constructor _ arguments => expressionTasks variables arguments

private def statementChildTasks (source : TypedSource)
    (variables : List TypeVarId) (node : StatementNode) :
    List ResidualScopeTask :=
  match node.form with
  | .letDecl binder initializer =>
      let initializerVariables :=
        if polymorphicLetAllowed source binder initializer then
          appendVariables variables binder.scheme.quantified
        else
          variables
      initializer.toList.map fun expression =>
        { node := .expression expression, variables := initializerVariables }
  | .returnStmt value => expressionTasks variables value.toList
  | .expression expression _ => expressionTasks variables [expression]
  | .assignValue assignment _ value =>
      assignmentTasks variables assignment ++ expressionTasks variables [value]
  | .assignBitNot assignment => assignmentTasks variables assignment
  | .ifThen condition thenBody elseBody =>
      expressionTasks variables [condition] ++
        statementTasks variables thenBody ++
        statementTasks variables (elseBody.getD [])
  | .block body => statementTasks variables body
  | .matchWith resolution =>
      expressionTasks variables [resolution.scrutinee] ++
        (resolution.cases.flatMap fun arm =>
          statementTasks variables arm.body) ++
        statementTasks variables (resolution.defaultBody.getD [])
  | .forLoop initializer condition post body =>
      initializer.flatMap (forItemTasks variables) ++
        expressionTasks variables [condition] ++
        statementTasks variables body ++
        post.flatMap (forItemTasks variables)
  | .whileLoop condition body =>
      expressionTasks variables [condition] ++ statementTasks variables body
  | .breakStmt
  | .continueStmt => []

private def residualChildTasks (source : TypedSource)
    (task : ResidualScopeTask) : List ResidualScopeTask :=
  match source.lookupNode? task.node.occurrenceId with
  | some (.expression node) => expressionChildTasks task.variables node
  | some (.statement node) => statementChildTasks source task.variables node
  | none => []

private def collectResidualScopes (source : TypedSource) :
    Nat → List ResidualScopeTask → List ResidualScope → List ResidualScope
  | 0, _, scopes => scopes
  | _ + 1, [], scopes => scopes
  | fuel + 1, task :: rest, scopes =>
      if scopes.any fun scope => decide (scope.node = task.node) then
        collectResidualScopes source fuel rest scopes
      else
        let scopes := scopes ++ [{
          node := task.node
          variables := task.variables
        }]
        collectResidualScopes source fuel
          (residualChildTasks source task ++ rest) scopes

private def residualScopes (source : TypedSource) : List ResidualScope :=
  let roots := source.roots.map fun node =>
    { node, variables := [] : ResidualScopeTask }
  collectResidualScopes source (source.nodes.length + 1) roots []

private def residualVariablesFor (scopes : List ResidualScope)
    (node : NodeId) : List TypeVarId :=
  ((scopes.find? fun scope => decide (scope.node = node)).map
    (·.variables)).getD []

private def validateNodeBinderSchemes (source : TypedSource)
    (lexical : List TypeVarId) : Node → Except Error Unit
  | .expression node =>
      match node.form with
      | .lambda parameters _ _ =>
          validateLexicalBinderSchemes lexical parameters
      | _ => pure ()
  | .statement node =>
      match node.form with
      | .letDecl binder initializer =>
          let binderLexical :=
            if polymorphicLetAllowed source binder initializer then
              appendVariables lexical binder.scheme.quantified
            else
              lexical
          validateLexicalScheme binderLexical binder.scheme
      | _ =>
          validateLexicalBinderSchemes lexical
            (statementFormBinders node.form)

private def validateScopedNodes (source : TypedSource)
    (scopes : List ResidualScope) : List Node → Except Error Unit
  | [] => pure ()
  | node :: rest => do
      let lexical := residualVariablesFor scopes node.id
      validateLexicalTypes lexical (nodeTypes node)
      validateNodeBinderSchemes source lexical node
      validateScopedNodes source scopes rest

private def validateTypedSourceResiduals (source : TypedSource) :
    Except Error Unit := do
  validatePolymorphicBinderPositions source
  validateLexicalBinderSchemes [] source.inputs
  validateScopedNodes source (residualScopes source) source.nodes

private def supportedPolymorphicVariables
    (source : TypedSource) : List TypeVarId :=
  source.nodes.foldl (fun variables node =>
    match node with
    | .statement { form := .letDecl binder initializer, .. } =>
        if polymorphicLetAllowed source binder initializer then
          appendVariables variables binder.scheme.quantified
        else
          variables
    | _ => variables) []

private def validateEvidenceGoals :
    List SolvedRequirement → Except Error Unit
  | [] => .ok ()
  | requirement :: rest => do
      let goal := requirement.evidence.goal
      if goal != requirement.predicate then
        throw (.evidenceGoalMismatch requirement.id requirement.predicate goal)
      validateEvidenceGoals rest

/-- Close one checked generic function using an exact declaration-order
substitution.  Validation precedes all rewriting, and every supplied type must
already be ground. -/
def specializeFunction (signature : ProgramFunctionSignature)
    (function : CheckedFunction) (supplied : ParameterSubstitution) :
    Except Error SpecializedFunction := do
  if signature.id != function.declaration then
    throw (.declarationMismatch signature.id function.declaration)
  if function.typedBody.owner != function.declaration then
    throw (.typedBodyOwnerMismatch function.declaration function.typedBody.owner)
  if signature.scheme.body != function.type then
    throw (.signatureTypeMismatch signature.scheme.body function.type)
  let bodyParameterComptime :=
    function.typedBody.inputs.map (·.comptime)
  if signature.parameterComptime != bodyParameterComptime then
    throw (.parameterComptimeMismatch
      signature.parameterComptime bodyParameterComptime)
  if signature.returnComptime != function.returnComptime then
    throw (.returnComptimeMismatch
      signature.returnComptime function.returnComptime)
  validateEvidenceGoals function.solvedRequirements
  let declared := signature.scheme.parameters
  validateDeclaredParameters signature.id declared
  validateSuppliedParameters signature.id declared supplied
  validateObservedParameters signature.id declared
    (signature.scheme.predicates.flatMap predicateTypes ++
      checkedFunctionParameterTypes function)
  let canonical ← canonicalSubstitution declared supplied
  let assumptions := signature.scheme.predicates.map
    (ProgramPredicate.applyParameters canonical)
  let specialized := applyCheckedFunction canonical function
  validateTypedSourceResiduals specialized.typedBody
  let lexicalVariables :=
    supportedPolymorphicVariables specialized.typedBody
  validateConcreteTypes (assumptions.flatMap predicateTypes ++
    [specialized.type, specialized.inferredBodyType] ++
    specialized.solvedRequirements.flatMap requirementTypes)
  validateLexicalTypes lexicalVariables
    (specialized.substitution.map Prod.snd)
  let stagesAfter ← match SourceStageAnalysis.analyzeFunction specialized with
    | .ok analysis => pure analysis
    | .error error => throw (.stageAnalysis error)
  pure {
    key := {
      declaration := function.declaration
      arguments := canonical.map Prod.snd
    }
    declaration := function.declaration
    parameterSubstitution := canonical
    assumptions
    function := specialized
    stageAnalysis := stagesAfter
  }

end Solcore.Frontend.SourceSpecialization

/-!
## Consolidated module: `Solcore.Frontend.SourceSpecializationProperties`
-/

/-! Identity-preservation laws for checked source specialization. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceSpecialization

open SourceInference TypeSystem

@[simp] theorem applyIntegerLiteralResolution_rawValue
    (substitution : ParameterSubstitution)
    (resolution : IntegerLiteralResolution) :
    (applyIntegerLiteralResolution substitution resolution).rawValue =
      resolution.rawValue := by
  rfl

@[simp] theorem applyIntegerLiteralResolution_targetType
    (substitution : ParameterSubstitution)
    (resolution : IntegerLiteralResolution) :
    (applyIntegerLiteralResolution substitution resolution).targetType =
      substitution.apply resolution.targetType := by
  rfl

@[simp] theorem applyIntegerLiteralResolution_requirement
    (substitution : ParameterSubstitution)
    (resolution : IntegerLiteralResolution) :
    (applyIntegerLiteralResolution substitution resolution).requirement =
      resolution.requirement := by
  rfl

theorem applyIntegerLiteralResolution_predicate
    (substitution : ParameterSubstitution)
    (resolution : IntegerLiteralResolution) :
    (applyIntegerLiteralResolution substitution resolution).predicate =
      ProgramPredicate.applyParameters substitution resolution.predicate := by
  rfl

@[simp] theorem applyScheme_quantified
    (substitution : ParameterSubstitution) (scheme : Scheme) :
    (applyScheme substitution scheme).quantified = scheme.quantified := by
  rfl

@[simp] theorem applyScheme_body
    (substitution : ParameterSubstitution) (scheme : Scheme) :
    (applyScheme substitution scheme).body = substitution.apply scheme.body := by
  rfl

@[simp] theorem applyInstantiation_declaration
    (substitution : ParameterSubstitution)
    (instantiation : DeclarationInstantiation) :
    (applyInstantiation substitution instantiation).declaration =
      instantiation.declaration := by
  rfl

@[simp] theorem applyInstantiation_parameterKeys
    (substitution : ParameterSubstitution)
    (instantiation : DeclarationInstantiation) :
    (applyInstantiation substitution instantiation).parameterSubstitution.map
        Prod.fst =
      instantiation.parameterSubstitution.map Prod.fst := by
  simp [applyInstantiation]

@[simp] theorem applyCoercionStep_requirement
    (substitution : ParameterSubstitution) (step : CoercionStep) :
    (applyCoercionStep substitution step).requirement = step.requirement := by
  rfl

@[simp] theorem applyCoercionStep_methodRequirements
    (substitution : ParameterSubstitution) (step : CoercionStep) :
    (applyCoercionStep substitution step).methodRequirements =
      step.methodRequirements := by
  rfl

@[simp] theorem applyCoercionStep_requirements
    (substitution : ParameterSubstitution) (step : CoercionStep) :
    (applyCoercionStep substitution step).requirements = step.requirements := by
  rfl

@[simp] theorem applyNode_id (substitution : ParameterSubstitution)
    (node : Node) :
    (applyNode substitution node).id = node.id := by
  cases node <;> rfl

@[simp] theorem applyTypedSource_owner
    (substitution : ParameterSubstitution) (source : TypedSource) :
    (applyTypedSource substitution source).owner = source.owner := by
  rfl

@[simp] theorem applyTypedSource_roots
    (substitution : ParameterSubstitution) (source : TypedSource) :
    (applyTypedSource substitution source).roots = source.roots := by
  rfl

@[simp] theorem applyTypedSource_nodeIds
    (substitution : ParameterSubstitution) (source : TypedSource) :
    (applyTypedSource substitution source).nodes.map Node.id =
      source.nodes.map Node.id := by
  simp [applyTypedSource]

@[simp] theorem applySolvedRequirement_id
    (substitution : ParameterSubstitution)
    (requirement : SolvedRequirement) :
    (applySolvedRequirement substitution requirement).id = requirement.id := by
  rfl

theorem applyPredicateEvidence_goal (substitution : ParameterSubstitution)
    (evidence : PredicateEvidence) :
    (applyPredicateEvidence substitution evidence).goal =
      ProgramPredicate.applyParameters substitution evidence.goal := by
  cases evidence with
  | assumption predicate => rfl
  | implementation evidence =>
      cases evidence
      rfl

theorem applySolvedRequirement_goal_alignment
    (substitution : ParameterSubstitution)
    (requirement : SolvedRequirement)
    (aligned : requirement.evidence.goal = requirement.predicate) :
    (applySolvedRequirement substitution requirement).evidence.goal =
      (applySolvedRequirement substitution requirement).predicate := by
  change (applyPredicateEvidence substitution requirement.evidence).goal =
    ProgramPredicate.applyParameters substitution requirement.predicate
  rw [applyPredicateEvidence_goal, aligned]

@[simp] theorem applyCheckedFunction_declaration
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).declaration =
      function.declaration := by
  rfl

@[simp] theorem applyCheckedFunction_bodyOwner
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).typedBody.owner =
      function.typedBody.owner := by
  rfl

@[simp] theorem applyCheckedFunction_bodyRoots
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).typedBody.roots =
      function.typedBody.roots := by
  rfl

@[simp] theorem applyCheckedFunction_requirementIds
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).solvedRequirements.map
        (·.id) =
      function.solvedRequirements.map (·.id) := by
  simp [applyCheckedFunction]

@[simp] theorem applyCheckedFunction_nodeIds
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).typedBody.nodes.map Node.id =
      function.typedBody.nodes.map Node.id := by
  simp [applyCheckedFunction]

end Solcore.Frontend.SourceSpecialization
