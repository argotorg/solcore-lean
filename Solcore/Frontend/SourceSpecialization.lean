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
  | qualifiedBinderPosition (binder : Resolved.LocalId)
  | duplicateLocalSchemeRequirement (requirement : RequirementId)
  | missingLocalSchemeRequirement
      (binder : Resolved.LocalId) (requirement : RequirementId)
  | duplicateSolvedLocalSchemeRequirement
      (binder : Resolved.LocalId) (requirement : RequirementId) (count : Nat)
  | localSchemeRequirementPredicateMismatch
      (binder : Resolved.LocalId) (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | localSchemeRequirementEvidenceMismatch
      (binder : Resolved.LocalId) (requirement : RequirementId)
      (predicate : ProgramPredicate)
  | localSchemeRequirementNotGeneralized
      (binder : Resolved.LocalId) (requirement : RequirementId)
      (predicate : ProgramPredicate)
  | orphanOpenLocalSchemeAssumption
      (requirement : RequirementId) (predicate : ProgramPredicate)
  | conflictingResidualScope
      (node : NodeId) (first second : List TypeVarId)
  | residualScopeTraversalLimit (node : NodeId)
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
  { binder with
    scheme := applyScheme substitution binder.scheme
    schemeRequirements := binder.schemeRequirements.map
      (LocalSchemeRequirement.applyParameters substitution) }

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

def firstNonConcrete : Ty → Option NonConcreteType
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
    (typedSourceBinders function.typedBody).flatMap fun binder =>
      binder.scheme.body :: binder.schemeRequirements.flatMap fun requirement =>
        predicateTypes requirement.predicate

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

private def validateLexicalBinder (lexical : List TypeVarId)
    (binder : TypedBinder) : Except Error Unit :=
  let binderLexical := appendVariables lexical binder.scheme.quantified
  validateLexicalTypes binderLexical
    (binder.scheme.body :: binder.schemeRequirements.flatMap fun requirement =>
      predicateTypes requirement.predicate)

private def validateLexicalBinderSchemes (lexical : List TypeVarId) :
    List TypedBinder → Except Error Unit
  | [] => .ok ()
  | binder :: rest => do
      validateLexicalBinder lexical binder
      validateLexicalBinderSchemes lexical rest

/-- Whether an initializer edge points directly to a lambda node.  Grouping,
proxying, or calling a lambda does not satisfy the restricted polymorphic-let
profile. -/
def isDirectLambdaInitializer (source : TypedSource)
    (initializer : ExpressionId) : Bool :=
  match source.lookupExpression? initializer with
  | some { form := .lambda _ _ _, .. } => true
  | _ => false

/-- Recover a complete ground substitution for one use of a polymorphic local
scheme.  Phantom or otherwise undetermined quantified variables are rejected,
as are occurrences which still contain inference metavariables. -/
def matchClosedSchemeInstance? (scheme : Scheme) (actual : Ty) :
    Option Substitution := do
  if (firstNonConcrete actual).isSome then none else pure ()
  scheme.matchInstance? actual

/-- Successful closed matching exposes both the specialization policy and the
complete rank-1 instantiation certificate supplied by `TypeSystem`. -/
theorem matchClosedSchemeInstance?_sound
    {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (matched : matchClosedSchemeInstance? scheme actual = some substitution) :
    firstNonConcrete actual = none ∧
      scheme.quantified.Nodup ∧
      substitution.domain = scheme.quantified ∧
      substitution.apply scheme.body = actual := by
  cases concrete : firstNonConcrete actual with
  | none =>
      have instanceMatched :
          scheme.matchInstance? actual = some substitution := by
        simpa [matchClosedSchemeInstance?, concrete] using matched
      exact ⟨rfl, Scheme.matchInstance?_sound instanceMatched⟩
  | some reason =>
      simp [matchClosedSchemeInstance?, concrete] at matched

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

private def qualifiedLocalBinders (source : TypedSource) : List TypedBinder :=
  source.nodes.filterMap fun
    | .statement { form := .letDecl binder initializer, .. } =>
        if polymorphicLetAllowed source binder initializer then some binder
        else none
    | _ => none

private def validateQualifiedBinderPositions (source : TypedSource) :
    Except Error Unit := do
  let allowed := (qualifiedLocalBinders source).map (·.id)
  match (typedSourceBinders source).find? fun binder =>
      !binder.schemeRequirements.isEmpty && !allowed.contains binder.id with
  | some binder => throw (.qualifiedBinderPosition binder.id)
  | none => pure ()

private def firstDuplicateRequirement :
    List RequirementId → Option RequirementId
  | [] => none
  | requirement :: rest =>
      if rest.contains requirement then some requirement
      else firstDuplicateRequirement rest

private def localSchemeRequirements
    (source : TypedSource) : List (TypedBinder × LocalSchemeRequirement) :=
  (qualifiedLocalBinders source).flatMap fun binder =>
    binder.schemeRequirements.map fun requirement => (binder, requirement)

private def validateLocalSchemeRequirements (function : CheckedFunction) :
    Except Error (List RequirementId) := do
  validateQualifiedBinderPositions function.typedBody
  let owned := localSchemeRequirements function.typedBody
  let ownedIds := owned.map fun entry => entry.2.templateRequirement
  match firstDuplicateRequirement ownedIds with
  | some requirement => throw (.duplicateLocalSchemeRequirement requirement)
  | none => pure ()
  for (binder, requirement) in owned do
    let variables :=
      TypedTraitResolution.predicateVariables requirement.predicate
    if !(variables.any fun metavariable =>
        binder.scheme.quantified.contains metavariable) then
      throw (.localSchemeRequirementNotGeneralized binder.id
        requirement.templateRequirement requirement.predicate)
    let matchingRequirements := function.solvedRequirements.filter fun solved =>
      solved.id == requirement.templateRequirement
    let solved ← match matchingRequirements with
      | [] => throw (.missingLocalSchemeRequirement binder.id
          requirement.templateRequirement)
      | [solved] => pure solved
      | matchingRequirements =>
          throw (.duplicateSolvedLocalSchemeRequirement binder.id
            requirement.templateRequirement matchingRequirements.length)
    if solved.predicate != requirement.predicate then
      throw (.localSchemeRequirementPredicateMismatch binder.id
        requirement.templateRequirement requirement.predicate solved.predicate)
    match solved.evidence with
    | .assumption predicate =>
        if predicate != requirement.predicate then
          throw (.localSchemeRequirementEvidenceMismatch binder.id
            requirement.templateRequirement requirement.predicate)
    | .implementation _ =>
        throw (.localSchemeRequirementEvidenceMismatch binder.id
          requirement.templateRequirement requirement.predicate)
  for solved in function.solvedRequirements do
    let variables := TypedTraitResolution.predicateVariables solved.predicate
    if !variables.isEmpty && !ownedIds.contains solved.id then
      match solved.evidence with
      | .assumption _ =>
          throw (.orphanOpenLocalSchemeAssumption solved.id solved.predicate)
      | .implementation _ => pure ()
  pure ownedIds

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

/-- Immediate occurrence edges of one expression node.  Consumers which treat
a lambda as a lexical boundary should avoid following the body edges returned
for its `.lambda` form. -/
def expressionChildNodeIds (node : ExpressionNode) : List NodeId :=
  (expressionChildTasks [] node).map (·.node)

/-- Immediate occurrence edges of one statement node, including assignment
projection expressions and every structured statement body. -/
def statementChildNodeIds (source : TypedSource)
    (node : StatementNode) : List NodeId :=
  (statementChildTasks source [] node).map (·.node)

private def residualChildTasks (source : TypedSource)
    (task : ResidualScopeTask) : List ResidualScopeTask :=
  match source.lookupNode? task.node.occurrenceId with
  | some (.expression node) => expressionChildTasks task.variables node
  | some (.statement node) => statementChildTasks source task.variables node
  | none => []

private def residualTraversalFuel (source : TypedSource) : Nat :=
  let edges := source.nodes.foldl (fun count node =>
    count + match node with
      | .expression expression =>
          (expressionChildTasks [] expression).length
      | .statement statement =>
          (statementChildTasks source [] statement).length) 0
  /- A malformed edge may use the opposite node category with the same
  occurrence identity, causing the first table entry to be traversed once for
  each `NodeId` constructor.  Twice the stored edge count therefore remains a
  conservative bound even before staging performs its stricter table checks. -/
  source.roots.length + 2 * edges + 1

private def collectResidualScopes (source : TypedSource) :
    Nat → List ResidualScopeTask → List ResidualScope →
      Except Error (List ResidualScope)
  | 0, [], scopes => .ok scopes
  | 0, task :: _, _ => .error (.residualScopeTraversalLimit task.node)
  | _ + 1, [], scopes => .ok scopes
  | fuel + 1, task :: rest, scopes =>
      match scopes.find? fun scope => decide (scope.node = task.node) with
      | some scope =>
          if scope.variables = task.variables then
            collectResidualScopes source fuel rest scopes
          else
            .error (.conflictingResidualScope task.node
              scope.variables task.variables)
      | none =>
          let scopes := scopes ++ [{
            node := task.node
            variables := task.variables
          }]
          collectResidualScopes source fuel
            (residualChildTasks source task ++ rest) scopes

private def residualScopes (source : TypedSource) :
    Except Error (List ResidualScope) :=
  let roots := source.roots.map fun node =>
    { node, variables := [] : ResidualScopeTask }
  collectResidualScopes source (residualTraversalFuel source) roots []

private def residualVariablesFor (scopes : List ResidualScope)
    (node : NodeId) : List TypeVarId :=
  ((scopes.find? fun scope => decide (scope.node = node)).map
    (·.variables)).getD []

private def validateNodeBinderSchemes (_source : TypedSource)
    (lexical : List TypeVarId) : Node → Except Error Unit
  | .expression node =>
      match node.form with
      | .lambda parameters _ _ =>
          validateLexicalBinderSchemes lexical parameters
      | _ => pure ()
  | .statement node =>
      match node.form with
      | .letDecl binder _ =>
          validateLexicalBinder lexical binder
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
  validateQualifiedBinderPositions source
  validateLexicalBinderSchemes [] source.inputs
  validateScopedNodes source (← residualScopes source) source.nodes

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
  let localSchemeRequirements ← validateLocalSchemeRequirements specialized
  let lexicalVariables :=
    supportedPolymorphicVariables specialized.typedBody
  validateConcreteTypes (assumptions.flatMap predicateTypes ++
    [specialized.type, specialized.inferredBodyType] ++
    (specialized.solvedRequirements.filter fun requirement =>
      !localSchemeRequirements.contains requirement.id).flatMap requirementTypes)
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

namespace Solcore.Frontend.SourceSpecialization
open SourceInference TypeSystem
private theorem canonicalSubstitution_parameterDomain
    {declared : List TypeParameterId} {supplied canonical : ParameterSubstitution}
    (accepted : canonicalSubstitution declared supplied = .ok canonical) :
    canonical.map Prod.fst = declared := by
  induction declared generalizing canonical with
  | nil => cases accepted; rfl
  | cons parameter rest ih =>
    simp only [canonicalSubstitution] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · cases remaining : canonicalSubstitution rest supplied with
        | error error => simp [remaining, bind, Except.bind] at accepted
        | ok tail =>
          simp only [remaining, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
          subst canonical
          simp only [List.map_cons, ih remaining]

private theorem bind_ok {α β : Type} {computation : Except Error α} {next : α → Except Error β} {result : β}
    (accepted : computation.bind next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computed : computation with
  | error error => simp [computed, Except.bind] at accepted
  | ok value => exact ⟨value, rfl, by simpa only [computed, Except.bind] using accepted⟩

/-- Successful specialization records declaration-order substitutions, even
when its request originally supplied the same bindings in a different order. -/
theorem specializeFunction_parameterDomain {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : ParameterSubstitution} {specialized : SpecializedFunction}
    (accepted : specializeFunction signature function supplied = .ok specialized) :
    specialized.parameterSubstitution.map Prod.fst = signature.scheme.parameters := by
  unfold specializeFunction at accepted
  by_cases guard0 : (signature.id != function.declaration) = true
  · simp only [guard0] at accepted
    cases accepted
  · simp only [guard0] at accepted
    by_cases guard1 : (function.typedBody.owner != function.declaration) = true
    · simp only [guard1] at accepted
      cases accepted
    · simp only [guard1] at accepted
      by_cases guard2 : (signature.scheme.body != function.type) = true
      · simp only [guard2] at accepted
        cases accepted
      · simp only [guard2] at accepted
        by_cases guard3 : (signature.parameterComptime != function.typedBody.inputs.map (·.comptime)) = true
        · simp only [guard3] at accepted
          cases accepted
        · simp only [guard3] at accepted
          by_cases guard4 : (signature.returnComptime != function.returnComptime) = true
          · simp only [guard4] at accepted
            cases accepted
          · simp only [guard4] at accepted
            obtain ⟨check0, _, accepted⟩ := bind_ok accepted
            cases check0
            obtain ⟨check1, _, accepted⟩ := bind_ok accepted
            cases check1
            obtain ⟨check2, _, accepted⟩ := bind_ok accepted
            cases check2
            obtain ⟨check3, _, accepted⟩ := bind_ok accepted
            cases check3
            obtain ⟨canonical, selected, accepted⟩ := bind_ok accepted
            obtain ⟨after0, _, accepted⟩ := bind_ok accepted
            obtain ⟨after1, _, accepted⟩ := bind_ok accepted
            obtain ⟨after2, _, accepted⟩ := bind_ok accepted
            obtain ⟨after3, _, accepted⟩ := bind_ok accepted
            cases analysis : SourceStageAnalysis.analyzeFunction (applyCheckedFunction canonical function) with
            | error error => simp only [analysis] at accepted; cases accepted
            | ok stages =>
              simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
              subst specialized
              exact canonicalSubstitution_parameterDomain selected

/-- Rigid caller specialization changes replacement types and retains the
ordered keys recorded by expression inference. -/
@[simp] theorem applyInstantiation_parameterDomain (substitution : ParameterSubstitution)
    (instantiation : DeclarationInstantiation) :
    (applyInstantiation substitution instantiation).parameterSubstitution.map Prod.fst =
      instantiation.parameterSubstitution.map Prod.fst := by
  simp [applyInstantiation, List.map_map, Function.comp_def]
end Solcore.Frontend.SourceSpecialization

/-! Accepted canonical rigid replacements retain their original concrete check. -/
namespace Solcore.Frontend.SourceSpecialization

open SourceInference TypeSystem

/-- Each replacement in the actual successful declaration-order checker is
concrete. The executable checker and all existing public interfaces are unchanged. -/
theorem canonicalSubstitution_concrete_replacements
    {declared : List TypeParameterId}
    {supplied canonical : ParameterSubstitution}
    (accepted : canonicalSubstitution declared supplied = .ok canonical) :
    ∀ entry ∈ canonical, firstNonConcrete entry.2 = none := by
  induction declared generalizing canonical with
  | nil =>
      cases accepted
      intro entry member
      cases member
  | cons parameter rest ih =>
      cases found : supplied.lookup? parameter with
      | none =>
          simp only [canonicalSubstitution, found] at accepted
          cases accepted
      | some type =>
          cases concrete : firstNonConcrete type with
          | some reason =>
              simp only [canonicalSubstitution, found, concrete, bind,
                Except.bind, pure, Except.pure] at accepted
              cases accepted
          | none =>
              cases remaining : canonicalSubstitution rest supplied with
              | error error =>
                  simp [canonicalSubstitution, found, concrete, remaining,
                    bind, Except.bind] at accepted
              | ok tail =>
                  simp only [canonicalSubstitution, found, concrete, remaining,
                    bind, Except.bind, pure, Except.pure,
                    Except.ok.injEq] at accepted
                  subst canonical
                  intro entry member
                  rcases List.mem_cons.mp member with same | member
                  · subst entry
                    exact concrete
                  · exact ih remaining entry member

end Solcore.Frontend.SourceSpecialization

/-! The accepted residual validator records the lexical quantifiers along the
actual source graph. These receipts expose that existing check to body-view
proofs; they do not run another validator or change specialization. -/
namespace Solcore.Frontend.SourceSpecialization
open SourceInference TypeSystem

/-- The exact children scheduled by the executable residual-scope traversal. -/
def residualScopeChildren (source : TypedSource) (node : NodeId)
    (variables : List TypeVarId) : List (NodeId × List TypeVarId) :=
  (residualChildTasks source { node, variables }).map fun task =>
    (task.node, task.variables)

/-- A lexical scope comes from an actual root and actual child tasks. Entering
an accepted polymorphic let initializer is the only operation that adds keys. -/
inductive ResidualScopePath (source : TypedSource) : NodeId → List TypeVarId → Prop
  | root {node} (member : node ∈ source.roots) : ResidualScopePath source node []
  | child {node variables child childVariables}
      (parent : ResidualScopePath source node variables)
      (member : (child, childVariables) ∈ residualScopeChildren source node variables) :
      ResidualScopePath source child childVariables

/-- Types checked at a node by the actual residual validator. -/
def residualNodeTypes (node : Node) : List Ty := nodeTypes node

/-- Binder types are checked under the lexical scope plus their own quantified
variables. This includes local requirement predicates. -/
def residualBinderTypes (binder : TypedBinder) : List Ty :=
  binder.scheme.body :: binder.schemeRequirements.flatMap fun requirement =>
    predicateTypes requirement.predicate

def residualNodeBinders (node : Node) : List TypedBinder := nodeBinders node

private theorem residual_first_nonlexical {variables : List TypeVarId} (type : Ty)
    (accepted : firstNonLexical variables type = none) :
    ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables := by
  induction type with
  | «variable» metavariable =>
      simp only [firstNonLexical] at accepted
      split at accepted
      · intro candidate member
        simp only [Ty.freeVariables, List.mem_singleton] at member
        subst candidate
        simpa using ‹variables.contains metavariable = true›
      · contradiction
  | parameter | error => cases accepted
  | constructor => simp [Ty.freeVariables]
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
      have leftAccepted : firstNonLexical variables left = none := by
        cases found : firstNonLexical variables left <;>
          simp_all only [firstNonLexical, Option.orElse_some]
      have rightAccepted : firstNonLexical variables right = none := by
        simpa only [firstNonLexical, leftAccepted, Option.orElse_none] using accepted
      intro metavariable member
      simp at member
      exact member.elim (ihLeft leftAccepted metavariable) (ihRight rightAccepted metavariable)
  | proxy inner ih | comptime inner ih => exact ih accepted

private theorem residual_lexical_types {variables : List TypeVarId} {types : List Ty}
    (accepted : validateLexicalTypes variables types = .ok ()) :
    ∀ type ∈ types, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables := by
  have none : types.findSome? (firstNonLexical variables) = none := by
    unfold validateLexicalTypes at accepted
    split at accepted <;> simp_all
  clear accepted
  induction types with
  | nil => simp
  | cons first rest ih =>
      cases found : firstNonLexical variables first with
      | some reason => simp [List.findSome?, found] at none
      | none =>
          have tail : rest.findSome? (firstNonLexical variables) = Option.none := by
            simpa only [List.findSome?, found] using none
          intro type member
          rcases List.mem_cons.mp member with same | member
          · subst type
            exact residual_first_nonlexical first found
          · exact ih tail type member

private theorem residual_append_variables {left right : List TypeVarId}
    {metavariable : TypeVarId} :
    metavariable ∈ appendVariables left right ↔ metavariable ∈ left ∨ metavariable ∈ right := by
  induction right generalizing left with
  | nil => simp [appendVariables]
  | cons head tail ih =>
      simp only [appendVariables, List.foldl_cons]
      change metavariable ∈ appendVariables (if left.contains head then left else left ++ [head]) tail ↔ _
      rw [ih]
      by_cases present : head ∈ left
      · simp only [List.contains_iff_mem.mpr present, if_true, List.mem_cons]
        constructor
        · intro member
          exact member.elim Or.inl (fun later => Or.inr (Or.inr later))
        · intro member
          rcases member with old | same | later
          · exact Or.inl old
          · exact Or.inl (same ▸ present)
          · exact Or.inr later
      · have absent : left.contains head = false := Bool.eq_false_iff.mpr (by simpa using present)
        simp only [absent, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro member
          rcases member with old | later
          · exact old.elim Or.inl (fun same => Or.inr (Or.inl same))
          · exact Or.inr (Or.inr later)
        · intro member
          rcases member with old | same | later
          · exact Or.inl (Or.inl old)
          · exact Or.inl (Or.inr same)
          · exact Or.inr later

private theorem residual_binder {variables : List TypeVarId} {binder : TypedBinder}
    (accepted : validateLexicalBinder variables binder = .ok ()) :
    ∀ type ∈ residualBinderTypes binder, ∀ metavariable ∈ type.freeVariables,
      metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified := by
  intro type member metavariable occurs
  exact residual_append_variables.mp (residual_lexical_types accepted type member metavariable occurs)

private theorem residual_binders {variables : List TypeVarId} {binders : List TypedBinder}
    (accepted : validateLexicalBinderSchemes variables binders = .ok ()) :
    ∀ binder ∈ binders, ∀ type ∈ residualBinderTypes binder, ∀ metavariable ∈ type.freeVariables,
      metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified := by
  induction binders with
  | nil => simp
  | cons binder rest ih =>
      simp only [validateLexicalBinderSchemes] at accepted
      cases first : validateLexicalBinder variables binder with
      | error error => simp [first, bind, Except.bind] at accepted
      | ok done =>
          cases done
          have later : validateLexicalBinderSchemes variables rest = .ok () := by
            simpa only [first, bind, Except.bind] using accepted
          intro selected member
          rcases List.mem_cons.mp member with rfl | member
          · exact residual_binder first
          · exact ih later selected member

private theorem residual_node_binders {source : TypedSource} {variables : List TypeVarId}
    {node : Node} (accepted : validateNodeBinderSchemes source variables node = .ok ()) :
    ∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables,
        metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified := by
  cases node with
  | expression node =>
      cases form : node.form <;>
        simp only [validateNodeBinderSchemes, form, residualNodeBinders, nodeBinders,
          expressionFormBinders] at accepted ⊢ <;> try simp
      exact residual_binders accepted
  | statement node =>
      cases form : node.form <;>
        simp only [validateNodeBinderSchemes, form, residualNodeBinders, nodeBinders] at accepted ⊢
      all_goals try exact residual_binders accepted
      simp only [statementFormBinders, List.mem_singleton]
      intro binder same
      subst binder
      exact residual_binder accepted

private theorem residual_collect_paths {source : TypedSource} {fuel : Nat}
    {tasks : List ResidualScopeTask} {initial final : List ResidualScope}
    (accepted : collectResidualScopes source fuel tasks initial = .ok final)
    (pending : ∀ task ∈ tasks, ResidualScopePath source task.node task.variables)
    (prior : ∀ scope ∈ initial, ResidualScopePath source scope.node scope.variables) :
    ∀ scope ∈ final, ResidualScopePath source scope.node scope.variables := by
  induction fuel generalizing tasks initial with
  | zero =>
      cases tasks with
      | nil => cases accepted; exact prior
      | cons => cases accepted
  | succ fuel ih =>
      cases tasks with
      | nil => cases accepted; exact prior
      | cons task rest =>
          simp only [collectResidualScopes] at accepted
          split at accepted
          · split at accepted
            · exact ih accepted (fun next member => pending next (List.mem_cons_of_mem task member)) prior
            · contradiction
          · apply ih accepted
            · intro child member
              rcases List.mem_append.mp member with new | old
              · exact .child (pending task (List.mem_cons_self)) (List.mem_map.mpr ⟨child,new,rfl⟩)
              · exact pending child (List.mem_cons_of_mem task old)
            · intro scope member
              rcases List.mem_append.mp member with old | new
              · exact prior scope old
              · cases List.mem_singleton.mp new
                exact pending task (List.mem_cons_self)

private theorem residual_scopes_paths {source : TypedSource} {scopes : List ResidualScope}
    (accepted : residualScopes source = .ok scopes) :
    ∀ scope ∈ scopes, ResidualScopePath source scope.node scope.variables := by
  apply residual_collect_paths accepted
  · intro task member
    obtain ⟨node, rootMember, same⟩ := List.mem_map.mp member
    cases same
    exact .root rootMember
  · simp

/-- Every stored node is either outside the traversal and closed, or carries
its actual lexical scope path. Node and binder types retain that exact scope. -/
def ResidualNodeSupported (source : TypedSource) (node : Node) : Prop :=
  ∃ variables,
    (variables = [] ∨ ResidualScopePath source node.id variables) ∧
    (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables) ∧
    (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables,
        metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified)

private theorem residual_validated_node {source : TypedSource} {scopes : List ResidualScope}
    {nodes : List Node} (paths : ∀ scope ∈ scopes, ResidualScopePath source scope.node scope.variables)
    (accepted : validateScopedNodes source scopes nodes = .ok ()) :
    ∀ node ∈ nodes, ResidualNodeSupported source node := by
  induction nodes with
  | nil => simp
  | cons node rest ih =>
      simp only [validateScopedNodes] at accepted
      cases types : validateLexicalTypes (residualVariablesFor scopes node.id) (nodeTypes node) with
      | error error => simp [types, bind, Except.bind] at accepted
      | ok done =>
          cases done
          cases binders : validateNodeBinderSchemes source (residualVariablesFor scopes node.id) node with
          | error error => simp [types, binders, bind, Except.bind] at accepted
          | ok done =>
              cases done
              have later : validateScopedNodes source scopes rest = .ok () := by
                simpa only [types, binders, bind, Except.bind] using accepted
              intro selected member
              rcases List.mem_cons.mp member with same | member
              · subst selected
                refine ⟨residualVariablesFor scopes node.id, ?_, residual_lexical_types types,
                  residual_node_binders binders⟩
                unfold residualVariablesFor
                cases found : scopes.find? (fun scope => decide (scope.node = node.id)) with
                | none => exact Or.inl rfl
                | some scope =>
                    have chosen : decide (scope.node = node.id) = true := List.find?_some (p := fun (entry : ResidualScope) => decide (entry.node = node.id)) found
                    have equal : scope.node = node.id := of_decide_eq_true chosen
                    exact Or.inr (equal ▸ paths scope (List.mem_of_find?_eq_some found))
              · exact ih later selected member

/-- This is a consequence of the existing successful source validator. -/
theorem validateTypedSourceResiduals_node_support {source : TypedSource}
    (accepted : validateTypedSourceResiduals source = .ok ()) :
    ∀ node ∈ source.nodes, ResidualNodeSupported source node := by
  unfold validateTypedSourceResiduals at accepted
  cases positions : validatePolymorphicBinderPositions source with
  | error error => simp [positions, bind, Except.bind] at accepted
  | ok done =>
    cases done
    cases qualified : validateQualifiedBinderPositions source with
    | error error => simp [positions, qualified, bind, Except.bind] at accepted
    | ok done =>
      cases done
      cases inputs : validateLexicalBinderSchemes [] source.inputs with
      | error error => simp [positions, qualified, inputs, bind, Except.bind] at accepted
      | ok done =>
        cases done
        cases scopes : residualScopes source with
        | error error => simp [positions, qualified, inputs, scopes, bind, Except.bind] at accepted
        | ok actualScopes =>
          apply residual_validated_node (residual_scopes_paths scopes)
          simpa only [positions, qualified, inputs, scopes, bind, Except.bind] using accepted

private theorem residual_reject_ok {α : Type} {condition : Prop} [Decidable condition]
    {action : Except Error α} {error : Error} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

/-- Every node of the actual specialized output passed the existing scoped
validator. No body-typing or execution premise is needed. -/
theorem specializeFunction_residual_node_support {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SpecializedFunction}
    (accepted : specializeFunction signature function supplied = .ok specialized) :
    ∀ node ∈ specialized.function.typedBody.nodes,
      ResidualNodeSupported specialized.function.typedBody node := by
  unfold specializeFunction at accepted
  iterate 5 have accepted := residual_reject_ok accepted
  iterate 4 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, residuals, accepted⟩ := bind_ok accepted
  iterate 3 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction (applyCheckedFunction canonical function) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
      simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
      subst specialized
      exact validateTypedSourceResiduals_node_support residuals

private theorem residual_expression_task_variables {variables : List TypeVarId}
    {node : ExpressionNode} {task : ResidualScopeTask}
    (member : task ∈ expressionChildTasks variables node) : task.variables = variables := by
  cases form : node.form <;>
    simp only [expressionChildTasks, form, expressionTasks, statementTasks] at member
  all_goals try contradiction
  all_goals
    obtain ⟨_, _, same⟩ := List.mem_map.mp member
    cases same
    rfl

private theorem residual_projection_task_variables {variables : List TypeVarId}
    {projections : List PlaceProjection} {task : ResidualScopeTask}
    (member : task ∈ projectionTasks variables projections) : task.variables = variables := by
  obtain ⟨projection, _, found⟩ := List.mem_filterMap.mp member
  cases projection with
  | index key =>
      cases Option.some.inj found
      rfl
  | member name index => cases found

private theorem residual_for_item_task_variables {variables : List TypeVarId}
    {item : ForItemForm} {task : ResidualScopeTask}
    (member : task ∈ forItemTasks variables item) : task.variables = variables := by
  cases item with
  | letDecl binder initializer =>
      obtain ⟨_, _, same⟩ := List.mem_map.mp member
      cases same
      rfl
  | expression expression =>
      cases List.mem_singleton.mp member
      rfl
  | assignValue assignment operator value =>
      rcases List.mem_append.mp member with projected | value
      · exact residual_projection_task_variables projected
      · cases List.mem_singleton.mp value
        rfl
  | assignBitNot assignment => exact residual_projection_task_variables member

private theorem residual_statement_task_variables {source : TypedSource}
    {variables : List TypeVarId} {node : StatementNode} {task : ResidualScopeTask}
    (member : task ∈ statementChildTasks source variables node) :
    task.variables = variables ∨ ∃ binder initializer,
      node.form = .letDecl binder (some initializer) ∧
      task.node = .expression initializer ∧
      task.variables = appendVariables variables binder.scheme.quantified := by
  cases form : node.form with
  | letDecl binder initializer =>
      simp only [statementChildTasks, form] at member
      obtain ⟨value, present, same⟩ := List.mem_map.mp member
      cases same
      cases initializer with
      | none => cases present
      | some initializer =>
          have sameValue : value = initializer := List.mem_singleton.mp present
          subst value
          split
          · exact Or.inr ⟨binder, initializer, rfl, rfl, rfl⟩
          · exact Or.inl rfl
  | returnStmt value =>
      obtain ⟨_, _, same⟩ := List.mem_map.mp (show task ∈ expressionTasks variables value.toList by simpa only [statementChildTasks, form] using member)
      cases same
      exact Or.inl rfl
  | expression value tail =>
      obtain ⟨_, _, same⟩ := List.mem_map.mp (show task ∈ expressionTasks variables [value] by simpa only [statementChildTasks, form] using member)
      cases same
      exact Or.inl rfl
  | assignValue assignment operator value =>
      simp only [statementChildTasks, form] at member
      rcases List.mem_append.mp member with projected | value
      · exact Or.inl (residual_projection_task_variables projected)
      · obtain ⟨_, _, same⟩ := List.mem_map.mp value
        cases same
        exact Or.inl rfl
  | assignBitNot assignment =>
      exact Or.inl (residual_projection_task_variables (show task ∈ projectionTasks variables assignment.target.projections by simpa only [statementChildTasks, form, assignmentTasks] using member))
  | ifThen condition thenBody elseBody =>
      simp only [statementChildTasks, form, List.mem_append] at member
      rcases member with (condition | thenBody) | elseBody
      all_goals
        obtain ⟨_, _, same⟩ := List.mem_map.mp (by assumption)
        cases same
        exact Or.inl rfl
  | block body =>
      obtain ⟨_, _, same⟩ := List.mem_map.mp (show task ∈ statementTasks variables body by simpa only [statementChildTasks, form] using member)
      cases same
      exact Or.inl rfl
  | matchWith resolution =>
      simp only [statementChildTasks, form, List.mem_append] at member
      rcases member with (scrutinee | arms) | defaultBody
      · obtain ⟨_, _, same⟩ := List.mem_map.mp scrutinee
        cases same
        exact Or.inl rfl
      · obtain ⟨_, _, taskMember⟩ := List.mem_flatMap.mp arms
        obtain ⟨_, _, same⟩ := List.mem_map.mp taskMember
        cases same
        exact Or.inl rfl
      · obtain ⟨_, _, same⟩ := List.mem_map.mp defaultBody
        cases same
        exact Or.inl rfl
  | forLoop initializer condition post body =>
      simp only [statementChildTasks, form, List.mem_append] at member
      rcases member with ((initializers | test) | body) | post
      · obtain ⟨_, _, taskMember⟩ := List.mem_flatMap.mp initializers
        exact Or.inl (residual_for_item_task_variables taskMember)
      · obtain ⟨_, _, same⟩ := List.mem_map.mp test
        cases same
        exact Or.inl rfl
      · obtain ⟨_, _, same⟩ := List.mem_map.mp body
        cases same
        exact Or.inl rfl
      · obtain ⟨_, _, taskMember⟩ := List.mem_flatMap.mp post
        exact Or.inl (residual_for_item_task_variables taskMember)
  | whileLoop condition body =>
      simp only [statementChildTasks, form, List.mem_append] at member
      rcases member with test | body
      all_goals
        obtain ⟨_, _, same⟩ := List.mem_map.mp (by assumption)
        cases same
        exact Or.inl rfl
  | breakStmt | continueStmt => simp [statementChildTasks, form] at member

/-- A newly introduced scope key belongs to the actual let binder on this
edge. All expression, control-flow and header edges preserve the scope. -/
theorem residualScopeChildren_new_quantifier {source : TypedSource}
    {parent child : NodeId} {variables childVariables : List TypeVarId}
    (member : (child, childVariables) ∈ residualScopeChildren source parent variables)
    {metavariable : TypeVarId} (occurs : metavariable ∈ childVariables)
    (fresh : metavariable ∉ variables) :
    ∃ statement binder initializer,
      source.lookupNode? parent.occurrenceId = some (.statement statement) ∧
      statement.form = .letDecl binder (some initializer) ∧
      child = .expression initializer ∧ metavariable ∈ binder.scheme.quantified := by
  obtain ⟨task, taskMember, pair⟩ := List.mem_map.mp member
  have childSame := congrArg Prod.fst pair
  have variablesSame := congrArg Prod.snd pair
  simp only at childSame variablesSame
  unfold residualChildTasks at taskMember
  cases found : source.lookupNode? parent.occurrenceId with
  | none => simp only [found] at taskMember; cases taskMember
  | some node =>
      cases node with
      | expression expression =>
          have same := residual_expression_task_variables (by simpa only [found] using taskMember)
          exact False.elim (fresh ((variablesSame.symm.trans same) ▸ occurs))
      | statement statement =>
          rcases residual_statement_task_variables (by simpa only [found] using taskMember) with same | ⟨binder, initializer, form, childForm, variablesForm⟩
          · exact False.elim (fresh ((variablesSame.symm.trans same) ▸ occurs))
          · refine ⟨statement, binder, initializer, rfl, form, childSame.symm.trans childForm, ?_⟩
            have supported := residual_append_variables.mp ((variablesSame.symm.trans variablesForm) ▸ occurs)
            exact supported.resolve_left fresh

/-- Every key in a reached lexical scope has a genuine ancestor declaration.
This relates the validator scope to the original binder used by inference
lifetime receipts, including nested generalized declarations. -/
theorem ResidualScopePath.quantifier_origin {source : TypedSource}
    {node : NodeId} {variables : List TypeVarId}
    (path : ResidualScopePath source node variables)
    {metavariable : TypeVarId} (occurs : metavariable ∈ variables) :
    ∃ parent parentVariables statement binder initializer,
      ResidualScopePath source parent parentVariables ∧
      source.lookupNode? parent.occurrenceId = some (.statement statement) ∧
      statement.form = .letDecl binder (some initializer) ∧
      metavariable ∈ binder.scheme.quantified := by
  induction path with
  | root member => cases occurs
  | @child parent variables child childVariables prior edge ih =>
      by_cases present : metavariable ∈ variables
      · exact ih present
      · obtain ⟨statement, binder, initializer, found, form, _, quantified⟩ :=
          residualScopeChildren_new_quantifier edge occurs present
        exact ⟨parent, variables, statement, binder, initializer, prior, found, form, quantified⟩

/-- A genuine table lookup uses the support derived from specialization. -/
theorem specializeFunction_residual_lookup_support {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SpecializedFunction}
    (accepted : specializeFunction signature function supplied = .ok specialized)
    {id : OccurrenceId} {node : Node}
    (found : specialized.function.typedBody.lookupNode? id = some node) :
    ResidualNodeSupported specialized.function.typedBody node :=
  specializeFunction_residual_node_support accepted node (List.mem_of_find?_eq_some found)

/-- Every flexible variable inspected by the validator belongs to a genuine
ancestor let binder, recovered from the actual scope traversal. -/
theorem ResidualNodeSupported.quantifier_origin {source : TypedSource} {node : Node}
    (supported : ResidualNodeSupported source node) {type : Ty}
    (inspected : type ∈ residualNodeTypes node) {metavariable : TypeVarId}
    (occurs : metavariable ∈ type.freeVariables) :
    ∃ parent parentVariables statement binder initializer,
      ResidualScopePath source parent parentVariables ∧
      source.lookupNode? parent.occurrenceId = some (.statement statement) ∧
      statement.form = .letDecl binder (some initializer) ∧
      metavariable ∈ binder.scheme.quantified := by
  obtain ⟨variables, path, types, _⟩ := supported
  have member := types type inspected metavariable occurs
  rcases path with empty | path
  · cases empty
    cases member
  · exact path.quantifier_origin member

/-- A suffix of the actual validator traversal, preserving every intermediate
scope. It ties a quantifier's declaration to the particular inspected node. -/
inductive ResidualScopeTail (source : TypedSource) (first : NodeId)
    (firstVariables : List TypeVarId) : NodeId → List TypeVarId → Prop
  | refl : ResidualScopeTail source first firstVariables first firstVariables
  | child {parent parentVariables node variables}
      (prior : ResidualScopeTail source first firstVariables parent parentVariables)
      (edge : (node, variables) ∈ residualScopeChildren source parent parentVariables) :
      ResidualScopeTail source first firstVariables node variables

theorem ResidualScopePath.quantifier_ancestor {source : TypedSource}
    {node : NodeId} {variables : List TypeVarId}
    (path : ResidualScopePath source node variables)
    {metavariable : TypeVarId} (occurs : metavariable ∈ variables) :
    ∃ parent parentVariables statement binder initializer initializerVariables,
      ResidualScopePath source parent parentVariables ∧
      source.lookupNode? parent.occurrenceId = some (.statement statement) ∧
      statement.form = .letDecl binder (some initializer) ∧
      (.expression initializer, initializerVariables) ∈
        residualScopeChildren source parent parentVariables ∧
      ResidualScopeTail source (.expression initializer) initializerVariables node variables ∧
      metavariable ∈ binder.scheme.quantified := by
  induction path with
  | root member => cases occurs
  | @child parent variables child childVariables prior edge ih =>
      by_cases present : metavariable ∈ variables
      · obtain ⟨ancestor, ancestorVariables, statement, binder, initializer,
          initializerVariables, path, found, form, entered, tail, quantified⟩ := ih present
        exact ⟨ancestor, ancestorVariables, statement, binder, initializer,
          initializerVariables, path, found, form, entered, .child tail edge, quantified⟩
      · obtain ⟨statement, binder, initializer, found, form, same, quantified⟩ :=
          residualScopeChildren_new_quantifier edge occurs present
        subst child
        exact ⟨parent, variables, statement, binder, initializer, childVariables,
          prior, found, form, edge, .refl, quantified⟩

/-- The actual source validator determines both the owner and the path from
that owner's initializer to this precise node. -/
theorem ResidualNodeSupported.quantifier_ancestor {source : TypedSource} {node : Node}
    (supported : ResidualNodeSupported source node) {type : Ty}
    (inspected : type ∈ residualNodeTypes node) {metavariable : TypeVarId}
    (occurs : metavariable ∈ type.freeVariables) :
    ∃ parent parentVariables statement binder initializer initializerVariables variables,
      ResidualScopePath source parent parentVariables ∧
      source.lookupNode? parent.occurrenceId = some (.statement statement) ∧
      statement.form = .letDecl binder (some initializer) ∧
      (.expression initializer, initializerVariables) ∈
        residualScopeChildren source parent parentVariables ∧
      ResidualScopeTail source (.expression initializer) initializerVariables node.id variables ∧
      metavariable ∈ binder.scheme.quantified := by
  obtain ⟨variables, path, types, _⟩ := supported
  have member := types type inspected metavariable occurs
  rcases path with empty | path
  · cases empty
    cases member
  · obtain ⟨parent, parentVariables, statement, binder, initializer, initializerVariables,
        path, found, form, entered, tail, quantified⟩ := path.quantifier_ancestor member
    exact ⟨parent, parentVariables, statement, binder, initializer, initializerVariables,
      variables, path, found, form, entered, tail, quantified⟩

end Solcore.Frontend.SourceSpecialization

namespace Solcore.Frontend.SourceSpecialization
open SourceInference

/-- The executable expression scheduler preserves every canonical child edge. -/
theorem expressionChildNodeIds_eq_references (node : ExpressionNode) :
    expressionChildNodeIds node = node.form.references := by
  cases node with
  | mk id span type form requirements coercions localStart =>
    cases form <;> simp [expressionChildNodeIds, expressionChildTasks,
      expressionTasks, statementTasks, ExpressionForm.references, List.map_map,
      Function.comp_def]

private theorem projectionTasks_nodes (variables : List TypeSystem.TypeVarId)
    (projections : List PlaceProjection) :
    (projectionTasks variables projections).map (·.node) =
      projections.flatMap PlaceProjection.references := by
  induction projections with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp_all [projectionTasks, PlaceProjection.references]

private theorem forItemTasks_nodes (variables : List TypeSystem.TypeVarId) (item : ForItemForm) :
    (forItemTasks variables item).map (·.node) = item.references := by
  cases item with
  | letDecl binder initializer => cases initializer <;> rfl
  | expression value => rfl
  | assignValue assignment operator value =>
    simp [forItemTasks, assignmentTasks, projectionTasks_nodes, ForItemForm.references,
      AssignmentResolution.references, PlaceResolution.references]
  | assignBitNot assignment => exact projectionTasks_nodes _ _

/-- Statement scheduling may reorder loop body and post items; every scheduled
child still belongs to the same canonical statement edge set. -/
theorem statementChildNodeIds_references {source : TypedSource} {node : StatementNode}
    {child : NodeId} (member : child ∈ statementChildNodeIds source node) :
    child ∈ node.form.references := by
  cases node with
  | mk id span type form =>
    cases form <;>
      simp only [statementChildNodeIds, statementChildTasks, expressionTasks,
        statementTasks, assignmentTasks, projectionTasks_nodes, forItemTasks_nodes,
        StatementForm.references, AssignmentResolution.references, PlaceResolution.references,
        MatchResolution.references, List.map_map,
        List.map_flatMap, List.map_append, Function.comp_def] at member ⊢
    all_goals simp_all [or_left_comm, or_comm, TypedMatchCase.references]

end Solcore.Frontend.SourceSpecialization

/-! An accepted residual traversal gives one exact scope for every actual path.
The same executable conflict check establishes this agreement. -/
namespace Solcore.Frontend.SourceSpecialization
open SourceInference TypeSystem

private def ResidualRecorded (scopes : List ResidualScope) (node : NodeId)
    (variables : List TypeVarId) : Prop :=
  scopes.find? (fun scope => decide (scope.node = node)) = some { node, variables }

private theorem residual_recorded_append {scopes : List ResidualScope}
    {node : NodeId} {variables : List TypeVarId}
    (recorded : ResidualRecorded scopes node variables) (extra : List ResidualScope) :
    ResidualRecorded (scopes ++ extra) node variables := by
  unfold ResidualRecorded at *
  rw [List.find?_append, recorded]
  rfl

private theorem residual_collect_recorded {source : TypedSource} {fuel : Nat}
    {tasks : List ResidualScopeTask} {initial final : List ResidualScope}
    (accepted : collectResidualScopes source fuel tasks initial = .ok final) :
    (∀ node variables, ResidualRecorded initial node variables → ResidualRecorded final node variables) ∧
    (∀ task ∈ tasks, ResidualRecorded final task.node task.variables) := by
  induction fuel generalizing tasks initial with
  | zero =>
    cases tasks with
    | nil => cases accepted; exact ⟨fun _ _ present => present, by simp⟩
    | cons => cases accepted
  | succ fuel ih =>
    cases tasks with
    | nil => cases accepted; exact ⟨fun _ _ present => present, by simp⟩
    | cons task rest =>
      cases found : initial.find? (fun scope => decide (scope.node = task.node)) with
      | some scope =>
        simp only [collectResidualScopes, found] at accepted
        split at accepted
        next same =>
          obtain ⟨old, remaining⟩ := ih accepted
          have head : ResidualRecorded final task.node task.variables := by
            apply old
            have sameNode : scope.node = task.node := by
              simpa only [decide_eq_true_eq] using List.find?_some found
            have scopeEq : scope = { node := task.node, variables := task.variables } := by
              cases scope
              simp_all
            simpa only [ResidualRecorded, scopeEq] using found
          refine ⟨old, ?_⟩
          intro pending member
          rcases List.mem_cons.mp member with sameTask | later
          · simpa only [sameTask] using head
          · exact remaining pending later
        next different => contradiction
      | none =>
        simp only [collectResidualScopes, found] at accepted
        obtain ⟨old, remaining⟩ := ih accepted
        have head : ResidualRecorded final task.node task.variables := by
          apply old
          unfold ResidualRecorded
          rw [List.find?_append, found]
          simp
        refine ⟨fun node variables present => old node variables (residual_recorded_append present _), ?_⟩
        intro pending member
        rcases List.mem_cons.mp member with sameTask | later
        · simpa only [sameTask] using head
        · exact remaining pending (List.mem_append_right _ later)


private theorem residual_collect_new_children {source : TypedSource} {fuel : Nat}
    {tasks : List ResidualScopeTask} {initial final : List ResidualScope}
    (accepted : collectResidualScopes source fuel tasks initial = .ok final) :
    ∀ scope ∈ final, scope ∉ initial →
      ∀ task ∈ residualChildTasks source { node := scope.node, variables := scope.variables },
        ResidualRecorded final task.node task.variables := by
  induction fuel generalizing tasks initial with
  | zero =>
    cases tasks with
    | nil => cases accepted; intro scope member absent; exact (absent member).elim
    | cons => cases accepted
  | succ fuel ih =>
    cases tasks with
    | nil => cases accepted; intro scope member absent; exact (absent member).elim
    | cons task rest =>
      cases found : initial.find? (fun scope => decide (scope.node = task.node)) with
      | some scope =>
        simp only [collectResidualScopes, found] at accepted
        split at accepted
        · exact ih accepted
        · contradiction
      | none =>
        simp only [collectResidualScopes, found] at accepted
        intro scope member absent
        by_cases entered : scope ∈ initial ++ [{ node := task.node, variables := task.variables }]
        · rcases List.mem_append.mp entered with old | fresh
          · exact (absent old).elim
          · have same := List.mem_singleton.mp fresh
            subst scope
            intro child selected
            exact (residual_collect_recorded accepted).2 child
              (List.mem_append_left _ selected)
        · exact ih accepted scope member entered

private theorem residual_scopes_record_path {source : TypedSource} {scopes : List ResidualScope}
    (accepted : residualScopes source = .ok scopes) {node : NodeId} {variables : List TypeVarId}
    (path : ResidualScopePath source node variables) : ResidualRecorded scopes node variables := by
  have completed := residual_collect_recorded accepted
  have children := residual_collect_new_children accepted
  induction path with
  | root member =>
    exact completed.2 { node := _, variables := [] }
      (List.mem_map.mpr ⟨_, member, rfl⟩)
  | @child parent variables child childVariables prior edge ih =>
    have member : ({ node := parent, variables } : ResidualScope) ∈ scopes :=
      List.mem_of_find?_eq_some ih
    obtain ⟨task, selected, same⟩ := List.mem_map.mp edge
    have known := children _ member (by simp) task selected
    have nodeEq := congrArg Prod.fst same
    have variablesEq := congrArg Prod.snd same
    change task.node = child at nodeEq
    change task.variables = childVariables at variablesEq
    simpa only [nodeEq, variablesEq] using known

private theorem residual_validated_path_data {source : TypedSource} {scopes : List ResidualScope}
    {nodes : List Node} (accepted : validateScopedNodes source scopes nodes = .ok ()) :
    ∀ node ∈ nodes,
      (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables,
        metavariable ∈ residualVariablesFor scopes node.id) ∧
      (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
        ∀ metavariable ∈ type.freeVariables,
          metavariable ∈ residualVariablesFor scopes node.id ∨ metavariable ∈ binder.scheme.quantified) := by
  induction nodes with
  | nil => simp
  | cons node rest ih =>
    simp only [validateScopedNodes] at accepted
    obtain ⟨done, types, accepted⟩ := bind_ok accepted
    cases done
    obtain ⟨done, binders, accepted⟩ := bind_ok accepted
    cases done
    intro selected member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      exact ⟨residual_lexical_types types, residual_node_binders binders⟩
    · exact ih accepted selected later

private theorem residual_validated_scopes {source : TypedSource}
    (accepted : validateTypedSourceResiduals source = .ok ()) :
    ∃ scopes, residualScopes source = .ok scopes ∧ validateScopedNodes source scopes source.nodes = .ok () := by
  unfold validateTypedSourceResiduals at accepted
  iterate 3 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨scopes, actual, accepted⟩ := bind_ok accepted
  exact ⟨scopes, actual, accepted⟩

/-- Two real paths to the same node use the same scope. The successful
executable validator has already rejected conflicting scopes. -/
theorem validateTypedSourceResiduals_scope_unique {source : TypedSource}
    (accepted : validateTypedSourceResiduals source = .ok ())
    {node : NodeId} {left right : List TypeVarId}
    (first : ResidualScopePath source node left)
    (second : ResidualScopePath source node right) : left = right := by
  obtain ⟨scopes, actual, _⟩ := residual_validated_scopes accepted
  have a := residual_scopes_record_path actual first
  have b := residual_scopes_record_path actual second
  exact congrArg ResidualScope.variables (Option.some.inj (a.symm.trans b))

/-- Support belongs to the scope of the supplied actual path, rather than an
unrelated existential path through the same table. -/
theorem validateTypedSourceResiduals_path_support {source : TypedSource}
    (accepted : validateTypedSourceResiduals source = .ok ())
    {node : Node} (member : node ∈ source.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath source node.id variables) :
    (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables) ∧
    (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified) := by
  obtain ⟨scopes, actual, validated⟩ := residual_validated_scopes accepted
  have recorded := residual_scopes_record_path actual path
  have exactScope : residualVariablesFor scopes node.id = variables := by
    unfold residualVariablesFor
    rw [recorded]
    rfl
  exact exactScope ▸ residual_validated_path_data validated node member

private theorem specializeFunction_residual_acceptance {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SpecializedFunction}
    (accepted : specializeFunction signature function supplied = .ok specialized) :
    validateTypedSourceResiduals specialized.function.typedBody = .ok () := by
  unfold specializeFunction at accepted
  iterate 5 have accepted := residual_reject_ok accepted
  iterate 4 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, residuals, accepted⟩ := bind_ok accepted
  iterate 3 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction (applyCheckedFunction canonical function) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
    simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
    subst specialized
    exact residuals

/-- Exact scope agreement follows from the actual specialization receipt. -/
theorem specializeFunction_residual_scope_unique {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SpecializedFunction}
    (accepted : specializeFunction signature function supplied = .ok specialized)
    {node : NodeId} {left right : List TypeVarId}
    (first : ResidualScopePath specialized.function.typedBody node left)
    (second : ResidualScopePath specialized.function.typedBody node right) : left = right :=
  validateTypedSourceResiduals_scope_unique (specializeFunction_residual_acceptance accepted) first second

/-- Every inspected type is supported by the exact path chosen in the actual
specialized body. This also preserves each nested binder's own quantifiers. -/
theorem specializeFunction_residual_path_support {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SpecializedFunction}
    (accepted : specializeFunction signature function supplied = .ok specialized)
    {node : Node} (member : node ∈ specialized.function.typedBody.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath specialized.function.typedBody node.id variables) :
    (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables) ∧
    (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified) :=
  validateTypedSourceResiduals_path_support (specializeFunction_residual_acceptance accepted) member path

end Solcore.Frontend.SourceSpecialization

/-! Actual lexical child selection changes scope only at a generalized lambda
boundary. The following facts expose existing scheduling, without another pass. -/
namespace Solcore.Frontend.SourceSpecialization
open SourceInference TypeSystem

private theorem residual_expression_child_ids (variables : List TypeVarId)
    (expression : ExpressionNode) :
    (expressionChildTasks variables expression).map (·.node) =
      expressionChildNodeIds expression := by
  cases expression with
  | mk id span type form requirements coercions localStart =>
    cases form <;> simp [expressionChildTasks, expressionChildNodeIds,
      expressionTasks, statementTasks, List.map_map, Function.comp_def]

private theorem residual_projection_child_ids (variables : List TypeVarId)
    (projections : List PlaceProjection) :
    (projectionTasks variables projections).map (·.node) =
      (projectionTasks [] projections).map (·.node) := by
  induction projections with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simpa [projectionTasks] using ih

private theorem residual_item_child_ids (variables : List TypeVarId) (item : ForItemForm) :
    (forItemTasks variables item).map (·.node) =
      (forItemTasks [] item).map (·.node) := by
  cases item <;> simp [forItemTasks, assignmentTasks, List.map_map,
    Function.comp_def, residual_projection_child_ids]

private theorem residual_statement_child_ids (source : TypedSource)
    (variables : List TypeVarId) (statement : StatementNode) :
    (statementChildTasks source variables statement).map (·.node) =
      statementChildNodeIds source statement := by
  cases statement with
  | mk id span type form =>
    cases form <;> simp [statementChildTasks, statementChildNodeIds,
      expressionTasks, statementTasks, assignmentTasks, List.map_map,
      List.map_flatMap, Function.comp_def, residual_projection_child_ids,
      residual_item_child_ids]

theorem residualScopeChildren_ids (source : TypedSource) (node : NodeId)
    (variables : List TypeVarId) :
    (residualScopeChildren source node variables).map Prod.fst =
      match source.lookupNode? node.occurrenceId with
      | some (.expression expression) => expressionChildNodeIds expression
      | some (.statement statement) => statementChildNodeIds source statement
      | none => [] := by
  unfold residualScopeChildren residualChildTasks
  cases source.lookupNode? node.occurrenceId with
  | none => rfl
  | some found =>
    cases found <;> simp only [List.map_map, Function.comp_def]
    · exact residual_expression_child_ids _ _
    · exact residual_statement_child_ids _ _ _

theorem residualScopeChildren_new_quantifier_direct {source : TypedSource}
    {parent child : NodeId} {variables childVariables : List TypeVarId}
    (member : (child, childVariables) ∈ residualScopeChildren source parent variables)
    {metavariable : TypeVarId} (occurs : metavariable ∈ childVariables)
    (fresh : metavariable ∉ variables) :
    ∃ statement binder initializer,
      source.lookupNode? parent.occurrenceId = some (.statement statement) ∧
      statement.form = .letDecl binder (some initializer) ∧
      child = .expression initializer ∧ metavariable ∈ binder.scheme.quantified ∧
      isDirectLambdaInitializer source initializer = true := by
  obtain ⟨statement, binder, initializer, found, form, same, quantified⟩ :=
    residualScopeChildren_new_quantifier member occurs fresh
  refine ⟨statement, binder, initializer, found, form, same, quantified, ?_⟩
  by_cases allowed : polymorphicLetAllowed source binder (some initializer) = true
  · have parts : (!binder.scheme.quantified.isEmpty) = true ∧
        isDirectLambdaInitializer source initializer = true := by
      simpa only [polymorphicLetAllowed, Option.any_some, Bool.and_eq_true] using allowed
    exact parts.2
  · have disabled : polymorphicLetAllowed source binder (some initializer) = false :=
      Bool.eq_false_iff.mpr allowed
    simp only [residualScopeChildren, residualChildTasks, found, statementChildTasks,
      form, disabled, Bool.false_eq_true, ↓reduceIte, Option.toList_some,
      List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at member
    exact False.elim (fresh (member.2 ▸ occurs))

end Solcore.Frontend.SourceSpecialization
