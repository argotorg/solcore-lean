import Solcore.Frontend.SourceInference.Types

/-!
Closing specialization for checked generic source functions.

The resolved signature supplies the authoritative declaration-parameter order,
including parameters which do not occur in the function type or body.  The
result keeps source/declaration identities intact while closing every semantic
type retained by source inference.  This initial profile produces fully ground
top-level functions and deliberately defers local let-polymorphism.
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
  | residualType (reason : NonConcreteType)
  deriving Repr, DecidableEq

/-- Worklist identity for one declaration specialized at concrete arguments in
authoritative signature order. -/
structure SpecializationKey where
  declaration : Resolved.DeclarationId
  arguments : List Ty
  deriving Repr, BEq, DecidableEq

/-- A declaration-order specialization together with the fully closed checked
source carrier.  `assumptions` are the signature's specialized where
predicates; the checked function retains all original owner and occurrence
identities.  The initial profile rejects quantified local binders explicitly;
support for local let-polymorphism belongs to a later specialization slice. -/
structure SpecializedFunction where
  key : SpecializationKey
  declaration : Resolved.DeclarationId
  parameterSubstitution : ParameterSubstitution
  assumptions : List ProgramPredicate
  function : CheckedFunction
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
  | .builtinBoolean value => .builtinBoolean value

def applyCallResolution (substitution : ParameterSubstitution) :
    CallResolution → CallResolution
  | .indirect => .indirect
  | .declaration instantiation =>
      .declaration (applyInstantiation substitution instantiation)

def applyExpressionForm (substitution : ParameterSubstitution) :
    ExpressionForm → ExpressionForm
  | .literal literal => .literal literal
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
  | .proxy inner => .proxy (substitution.apply inner)
  | .index base index => .index base index

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
  | .ifThen condition thenBody elseBody =>
      .ifThen condition thenBody elseBody
  | .block body => .block body

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
  | .builtinBoolean _ => []
  | .declaration instantiation => instantiationTypes instantiation

private def callResolutionTypes : CallResolution → List Ty
  | .indirect => []
  | .declaration instantiation => instantiationTypes instantiation

private def expressionFormTypes : ExpressionForm → List Ty
  | .reference _ resolution => referenceTypes resolution
  | .lambda _ returnType _ => [returnType]
  | .call _ _ resolution => callResolutionTypes resolution
  | .proxy inner => [inner]
  | .literal _
  | .group _
  | .tuple _
  | .unary _ _
  | .binary _ _ _
  | .conditional _ _ _
  | .index _ _ => []

private def statementFormTypes : StatementForm → List Ty
  | .letDecl _ _ => []
  | .returnStmt _
  | .expression _ _
  | .ifThen _ _ _
  | .block _ => []

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

private def firstRigidOrError : Ty → Option NonConcreteType
  | .variable _
  | .constructor _ => none
  | .parameter id => some (.rigid id)
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right =>
      (firstRigidOrError left).orElse fun _ => firstRigidOrError right
  | .proxy inner
  | .comptime inner => firstRigidOrError inner
  | .error => some .error

private def validateConcreteScheme (scheme : Scheme) : Except Error Unit := do
  match scheme.freeVariables with
  | metavariable :: _ => throw (.residualType (.flexible metavariable))
  | [] => pure ()
  match firstRigidOrError scheme.body with
  | some reason => throw (.residualType reason)
  | none => pure ()

private def validateConcreteBinderSchemes :
    List TypedBinder → Except Error Unit
  | [] => .ok ()
  | binder :: rest => do
      validateConcreteScheme binder.scheme
      validateConcreteBinderSchemes rest

/-- Quantified locals are a profile-level rejection and therefore take
precedence over incidental open types in any earlier monomorphic binder. -/
private def validateConcreteBinders (binders : List TypedBinder) :
    Except Error Unit := do
  match binders.find? fun binder => !binder.scheme.quantified.isEmpty with
  | some binder =>
      throw (.polymorphicBinder binder.id binder.scheme.quantified)
  | none => pure ()
  validateConcreteBinderSchemes binders

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
  validateConcreteBinders (typedSourceBinders specialized.typedBody)
  validateConcreteTypes (assumptions.flatMap predicateTypes ++
    checkedFunctionTypes specialized)
  pure {
    key := {
      declaration := function.declaration
      arguments := canonical.map Prod.snd
    }
    declaration := function.declaration
    parameterSubstitution := canonical
    assumptions
    function := specialized
  }

end Solcore.Frontend.SourceSpecialization
