import Solcore.SourceSemantics.Instantiation
import Solcore.Frontend.SourceInference.Types

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
  { binder with scheme := applyScheme substitution binder.scheme }

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
