import Solcore.Frontend.ProgramSignatures
import Solcore.Frontend.SourceInference.Identity
import Solcore.Frontend.TypedTraitResolution
import Solcore.Syntax.Term

/-!
Occurrence-addressed typed source carrier.

This module is deliberately independent of the inference traversal.  It records
the facts needed by later specialization without changing which source programs
the current checker accepts.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

open TypeSystem

/-- One predicate owned by a generalized local scheme.  The stable template
requirement identifies the assumption used inside the initializer body; the
predicate records how that assumption depends on the scheme's quantified
variables. -/
structure LocalSchemeRequirement where
  templateRequirement : RequirementId
  predicate : ProgramPredicate
  deriving Repr, BEq, DecidableEq

namespace LocalSchemeRequirement

/-- Apply a flexible inference substitution to the predicate while preserving
the template requirement identity. -/
def applySubstitution (substitution : Substitution)
    (requirement : LocalSchemeRequirement) : LocalSchemeRequirement :=
  { requirement with
    predicate := TypedTraitResolution.applySubstitution substitution
      requirement.predicate }

/-- Apply a rigid declaration-parameter substitution to the predicate while
preserving the template requirement identity. -/
def applyParameters (substitution : ParameterSubstitution)
    (requirement : LocalSchemeRequirement) : LocalSchemeRequirement :=
  { requirement with
    predicate := ProgramPredicate.applyParameters substitution
      requirement.predicate }

end LocalSchemeRequirement

/-- One typed local binding, retaining its stable lexical identity. -/
structure TypedBinder where
  id : Resolved.LocalId
  name : String
  scheme : Scheme
  /-- Trait assumptions abstracted together with this local scheme.  Empty
  until qualified local generalization is enabled by source inference. -/
  schemeRequirements : List LocalSchemeRequirement := []
  /-- Whether this parameter is required during staged evaluation.  Named
  function inputs and explicitly marked lambda parameters retain the bit;
  ordinary lexical binders leave it false. -/
  comptime : Bool := false
  span : Option Syntax.SourceSpan := none
  deriving Repr, BEq, DecidableEq

/-- The selected and instantiated view of one top-level declaration. -/
structure DeclarationInstantiation where
  declaration : Resolved.DeclarationId
  parameterSubstitution : ParameterSubstitution
  type : Ty
  predicates : List ProgramPredicate
  /-- Staging markers copied from the canonical declaration signature. -/
  parameterComptime : List Bool := []
  returnComptime : Bool := false
  deriving Repr, BEq, DecidableEq

/-- One constructor selected from a data declaration after its rigid type
parameters have been instantiated at this occurrence. -/
structure DataConstructorInstantiation where
  constructor : ProgramDataConstructorId
  parameterSubstitution : ParameterSubstitution
  payloadTypes : List Ty
  resultType : Ty
  deriving Repr, BEq, DecidableEq

/-- One evidence-bearing edge in an inserted coercion path. -/
structure CoercionStep where
  requirement : RequirementId
  methodRequirements : List RequirementId := []
  source : Ty
  target : Ty
  deriving Repr, BEq, DecidableEq

/-- The fully explicit semantic plan for one source integer literal.  The
source spelling remains on `ExpressionForm`, while this carrier records the
decoded mathematical value, selected result type, and the exact builtin `Int`
obligation which justifies constructing that result. -/
structure IntegerLiteralResolution where
  rawValue : Nat
  targetType : Ty
  requirement : RequirementId
  deriving Repr, BEq, DecidableEq

namespace IntegerLiteralResolution

/-- The builtin `Int<Target>` goal owned by this literal occurrence. -/
def predicate (resolution : IntegerLiteralResolution) : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate resolution.targetType

/-- Close flexible type variables without changing the decoded value or the
stable requirement identity. -/
def applySubstitution (substitution : Substitution)
    (resolution : IntegerLiteralResolution) : IntegerLiteralResolution := {
  resolution with targetType := substitution.apply resolution.targetType
}

end IntegerLiteralResolution

/-- The exact supported projection of one source match pattern.  Keeping this
small source carrier separate from the semantic classification preserves every
written group and span without admitting unsupported pattern syntax. -/
inductive MatchPatternSource where
  | wildcard (span marker : Syntax.SourceSpan)
  | integerLiteral (span : Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
  | binder (span : Syntax.SourceSpan) (name : String)
  | constructor
      (span : Syntax.SourceSpan)
      (leadingDot : Option Syntax.SourceSpan)
      (qualifiers : List String)
      (name : String)
      (argumentCount : Nat)
  | group (span : Syntax.SourceSpan) (inner : MatchPatternSource)
  | tuple (span : Syntax.SourceSpan) (elementCount : Nat)
  deriving Repr, BEq, DecidableEq

/-- Prefix instruction for a recursively nested pattern.  Child counts make
the flat source-order stream lossless while keeping the executable carrier a
first-order list with derived decidable equality. -/
inductive MatchPatternInstruction where
  | wildcard
  | integerLiteral
      (source : Syntax.CoreLiteralValue)
      (resolution : IntegerLiteralResolution)
  | binder (binder : TypedBinder)
  | constructor
      (instantiation : DataConstructorInstantiation)
      (argumentCount : Nat)
  | tuple (elementCount : Nat)
  deriving Repr, BEq, DecidableEq

/-- The supported semantic classification of one source match pattern. -/
inductive MatchPatternResolution where
  | wildcard
  | integerLiteral
      (source : Syntax.CoreLiteralValue)
      (resolution : IntegerLiteralResolution)
  | binder (binder : TypedBinder)
  | constructor
      (instantiation : DataConstructorInstantiation)
      (arguments : List MatchPatternInstruction)
  | tuple (elements : List MatchPatternInstruction)
  deriving Repr, BEq, DecidableEq

/-- A source-preserving pattern carrier for the initial executable match
profile.  Numeric patterns own their exact builtin-`Int` requirement just as
expression literals do, while wildcard patterns own no requirement. -/
structure TypedMatchPattern where
  source : MatchPatternSource
  type : Ty
  resolution : MatchPatternResolution
  requirements : List RequirementId := []
  deriving Repr, BEq, DecidableEq

/-- Metadata for applying an indirectly obtained function type.  A source
argument list is bundled into one product before it is compared with the
function parameter, so any coercion of that bundle belongs here rather than to
the call expression's result coercion path. -/
structure IndirectCallResolution where
  /-- The source argument-list arity.  This is retained separately because
  `Ty.productMany` does not distinguish one product-valued argument from
  several arguments whose types form the same product. -/
  argumentCount : Nat
  argumentTypeBeforeCoercion : Ty
  argumentTypeAfterCoercion : Ty
  argumentCoercions : List CoercionStep := []
  deriving Repr, BEq, DecidableEq

/-- The semantic target selected for a source name occurrence. -/
inductive ReferenceResolution where
  | local (binder : Resolved.LocalId)
  | declaration (instantiation : DeclarationInstantiation)
  | builtinFunction (function : BuiltinFunctionId)
  | builtinBoolean (value : Bool)
  deriving Repr, BEq, DecidableEq

/-- How a call's callee was selected.  An indirect call obtains its function
type from the referenced callee expression node and retains any coercion of
the bundled arguments separately from the call result. -/
inductive CallResolution where
  | indirect (metadata : IndirectCallResolution)
  | declaration (instantiation : DeclarationInstantiation)
  | builtinFunction (function : BuiltinFunctionId)
  deriving Repr, BEq, DecidableEq

/-- Category-safe identity of one expression occurrence. -/
structure ExpressionId where
  occurrence : OccurrenceId
  deriving Repr, BEq, DecidableEq

/-- Category-safe identity of one statement occurrence. -/
structure StatementId where
  occurrence : OccurrenceId
  deriving Repr, BEq, DecidableEq

/-- One checked source match arm.  Branch statements remain occurrence edges
into the common typed-source table; the original arm and pattern spans remain
available through `span` and `pattern.source`. -/
structure TypedMatchCase where
  span : Syntax.SourceSpan
  pattern : TypedMatchPattern
  body : List StatementId
  deriving Repr, BEq, DecidableEq

/-- Complete metadata for a terminal single-scrutinee match.  The hidden local
is allocated from the declaration's stable local-ID stream during inference so
Core lowering can evaluate the scrutinee exactly once without risking capture.
`requirements` is the exact source-order concatenation of the pattern-owned
requirements and is checked again before lowering. -/
structure MatchResolution where
  scrutinee : ExpressionId
  hiddenScrutinee : Resolved.LocalId
  cases : List TypedMatchCase
  defaultBody : Option (List StatementId)
  requirements : List RequirementId := []
  deriving Repr, BEq, DecidableEq

/-- One projection on an assignable source place.  Mapping indexes retain the
already typed key occurrence; member projections retain the selected stable
position rather than repeating source lookup at runtime. -/
inductive PlaceProjection where
  | index (key : ExpressionId)
  | member (name : String) (index : Nat)
  deriving Repr, BEq, DecidableEq

/-- A place rooted at one stable lexical binder. -/
structure PlaceResolution where
  root : Resolved.LocalId
  projections : List PlaceProjection
  type : Ty
  deriving Repr, BEq, DecidableEq

/-- A checked assignment including every operator-owned requirement in
source order.  Plain `=` owns no requirement. -/
structure AssignmentResolution where
  target : PlaceResolution
  requirements : List RequirementId := []
  deriving Repr, BEq, DecidableEq

/-- Typed item used by a canonical `for` initializer or post clause. -/
inductive ForItemForm where
  | letDecl (binder : TypedBinder) (initializer : Option ExpressionId)
  | expression (expression : ExpressionId)
  | assignValue
      (assignment : AssignmentResolution)
      (operator : Syntax.ValueAssignOp)
      (value : ExpressionId)
  | assignBitNot (assignment : AssignmentResolution)
  deriving Repr, BEq, DecidableEq

/-- Category-preserving identity of either typed source-node kind. -/
inductive NodeId where
  | expression (id : ExpressionId)
  | statement (id : StatementId)
  deriving Repr, BEq, DecidableEq

/-- One initialized local-scheme template together with the exact binder and
initializer occurrence which own it. -/
structure LocalSchemeTemplateSite where
  binder : TypedBinder
  initializer : NodeId
  requirement : LocalSchemeRequirement
  deriving Repr, BEq, DecidableEq

/-- One primary requirement attachment together with its exact source
occurrence.  Secondary mirrors are deliberately excluded. -/
structure PrimaryRequirementSite where
  occurrence : NodeId
  requirement : RequirementId
  deriving Repr, BEq, DecidableEq

namespace NodeId

def occurrenceId : NodeId → OccurrenceId
  | .expression id => id.occurrence
  | .statement id => id.occurrence

end NodeId

/-- Typed expression shape.  Recursive children are occurrence identities, so
the carrier is compact and does not duplicate subtrees.  Source inference uses
`integerLiteral` for integer syntax; `literal` remains only as the strict Word
compatibility form for manually assembled typed IR. -/
inductive ExpressionForm where
  | literal (literal : Syntax.CoreLiteralValue)
  | integerLiteral
      (source : Syntax.CoreLiteralValue)
      (resolution : IntegerLiteralResolution)
  | reference (name : String) (resolution : ReferenceResolution)
  | group (inner : ExpressionId)
  | tuple (elements : List ExpressionId)
  | unary (operator : Syntax.UnaryOp) (operand : ExpressionId)
  | binary
      (left : ExpressionId) (operator : Syntax.BinaryOp) (right : ExpressionId)
  | conditional
      (condition thenBranch elseBranch : ExpressionId)
  | lambda
      (parameters : List TypedBinder)
      (returnType : Ty)
      (body : List StatementId)
  | call
      (callee : ExpressionId)
      (arguments : List ExpressionId)
      (resolution : CallResolution)
  | constructor
      (instantiation : DataConstructorInstantiation)
      (arguments : List ExpressionId)
  | member (base : ExpressionId) (name : String) (index : Nat)
  | proxy (inner : Ty)
  | index (base index : ExpressionId)
  deriving Repr, BEq, DecidableEq

/-- One typed expression occurrence.  `requirements` contains every obligation
introduced at this occurrence in source-inference order; `coercions` gives the
ordered result-conversion subset with its source and target types, and `type`
is always the type after that path.  Indirect argument-bundle conversions live
in `CallResolution.indirect` metadata. -/
structure ExpressionNode where
  id : ExpressionId
  span : Syntax.SourceSpan
  type : Ty
  form : ExpressionForm
  requirements : List RequirementId := []
  coercions : List CoercionStep := []
  deriving Repr, BEq, DecidableEq

/-- Typed statement shape for every statement form accepted by the current
source-inference traversal. -/
inductive StatementForm where
  | letDecl (binder : TypedBinder) (initializer : Option ExpressionId)
  | returnStmt (value : Option ExpressionId)
  | expression (expression : ExpressionId) (trailingSemicolon : Bool)
  | assignValue
      (assignment : AssignmentResolution)
      (operator : Syntax.ValueAssignOp)
      (value : ExpressionId)
  | assignBitNot (assignment : AssignmentResolution)
  | ifThen
      (condition : ExpressionId)
      (thenBody : List StatementId)
      (elseBody : Option (List StatementId))
  | block (body : List StatementId)
  | matchWith (resolution : MatchResolution)
  | forLoop
      (initializer : List ForItemForm)
      (condition : ExpressionId)
      (post : List ForItemForm)
      (body : List StatementId)
  | whileLoop (condition : ExpressionId) (body : List StatementId)
  | breakStmt
  | continueStmt
  deriving Repr, BEq, DecidableEq

/-- One typed statement occurrence and its inferred result type. -/
structure StatementNode where
  id : StatementId
  span : Syntax.SourceSpan
  type : Ty
  form : StatementForm
  deriving Repr, BEq, DecidableEq

/-- A heterogeneous node table preserves one occurrence order while keeping
expression and statement identities statically distinct. -/
inductive Node where
  | expression (node : ExpressionNode)
  | statement (node : StatementNode)
  deriving Repr, BEq, DecidableEq

namespace PlaceProjection

/-- Category-preserving expression edges retained by one place projection. -/
def references : PlaceProjection → List NodeId
  | .index key => [.expression key]
  | .member _ _ => []

end PlaceProjection

namespace PlaceResolution

/-- Every expression edge retained by an assignable place, in projection
order. -/
def references (place : PlaceResolution) : List NodeId :=
  place.projections.flatMap PlaceProjection.references

end PlaceResolution

namespace AssignmentResolution

/-- Expression edges retained by the target place of one assignment. -/
def references (assignment : AssignmentResolution) : List NodeId :=
  assignment.target.references

end AssignmentResolution

namespace ForItemForm

/-- Direct occurrence edges retained by one `for` initializer or post item. -/
def references : ForItemForm → List NodeId
  | .letDecl _ initializer => initializer.map NodeId.expression |>.toList
  | ForItemForm.expression expressionId => [NodeId.expression expressionId]
  | .assignValue assignment _ value =>
      assignment.references ++ [NodeId.expression value]
  | .assignBitNot assignment => assignment.references

end ForItemForm

namespace ExpressionForm

/-- Direct occurrence edges retained by one expression form. -/
def references : ExpressionForm → List NodeId
  | .literal _ => []
  | .integerLiteral _ _ => []
  | .reference _ _ => []
  | .group inner => [NodeId.expression inner]
  | .tuple elements => elements.map NodeId.expression
  | .unary _ operand => [NodeId.expression operand]
  | .binary left _ right =>
      [NodeId.expression left, NodeId.expression right]
  | .conditional condition thenBranch elseBranch =>
      [NodeId.expression condition, NodeId.expression thenBranch,
        NodeId.expression elseBranch]
  | .lambda _ _ body => body.map NodeId.statement
  | .call callee arguments _ =>
      NodeId.expression callee :: arguments.map NodeId.expression
  | .constructor _ arguments => arguments.map NodeId.expression
  | .member base _ _ => [NodeId.expression base]
  | .proxy _ => []
  | .index base key => [NodeId.expression base, NodeId.expression key]

end ExpressionForm

namespace TypedMatchCase

/-- Statement edges retained by one match case. -/
def references (matchCase : TypedMatchCase) : List NodeId :=
  matchCase.body.map NodeId.statement

end TypedMatchCase

namespace MatchResolution

/-- Every edge retained by a match, in source order. -/
def references (resolution : MatchResolution) : List NodeId :=
  [NodeId.expression resolution.scrutinee] ++
    resolution.cases.flatMap TypedMatchCase.references ++
    (resolution.defaultBody.getD []).map NodeId.statement

end MatchResolution

namespace StatementForm

/-- Direct occurrence edges retained by one statement form. -/
def references : StatementForm → List NodeId
  | .letDecl _ initializer => initializer.map NodeId.expression |>.toList
  | .returnStmt value => value.map NodeId.expression |>.toList
  | StatementForm.expression expressionId _ => [NodeId.expression expressionId]
  | .assignValue assignment _ value =>
      assignment.references ++ [NodeId.expression value]
  | .assignBitNot assignment => assignment.references
  | .ifThen condition thenBody elseBody =>
      [NodeId.expression condition] ++ thenBody.map NodeId.statement ++
        (elseBody.getD []).map NodeId.statement
  | .block body => body.map NodeId.statement
  | .matchWith resolution => resolution.references
  | .forLoop initializer condition post body =>
      initializer.flatMap ForItemForm.references ++
        [NodeId.expression condition] ++
        post.flatMap ForItemForm.references ++ body.map NodeId.statement
  | .whileLoop condition body =>
      NodeId.expression condition :: body.map NodeId.statement
  | .breakStmt => []
  | .continueStmt => []

end StatementForm

namespace Node

/-- Direct category-preserving occurrence edges retained by one node. -/
def references : Node → List NodeId
  | .expression node => node.form.references
  | .statement node => node.form.references

end Node

/-- Typed source for one declaration.  All recursive edges point into `nodes`;
`roots` retain the checked entry points in order, including standalone
expression roots. -/
structure TypedSource where
  owner : Resolved.DeclarationId
  inputs : List TypedBinder
  roots : List NodeId
  nodes : List Node
  deriving Repr, BEq, DecidableEq

private def applyFinalToParameters (substitution : Substitution)
    (parameters : ParameterSubstitution) : ParameterSubstitution :=
  parameters.map fun entry => (entry.1, substitution.apply entry.2)

namespace TypedBinder

/-- Apply the final inference substitution without entering quantified scheme
variables. -/
def applySubstitution (substitution : Substitution)
    (binder : TypedBinder) : TypedBinder :=
  let substitution := substitution.without binder.scheme.quantified
  { binder with
    scheme := Scheme.apply substitution binder.scheme
    schemeRequirements := binder.schemeRequirements.map
      (LocalSchemeRequirement.applySubstitution substitution) }

end TypedBinder

namespace DeclarationInstantiation

/-- Retain the complete result of instantiating one resolved declaration,
including staging metadata which is independent of type substitution. -/
def ofInstantiated (signature : ProgramFunctionSignature)
    (instantiated : InstantiatedConstrainedDeclaration) :
    DeclarationInstantiation := {
  declaration := signature.id
  parameterSubstitution := instantiated.parameterSubstitution
  type := instantiated.body
  predicates := instantiated.predicates
  parameterComptime := signature.parameterComptime
  returnComptime := signature.returnComptime
}

/-- Close every flexible type position retained by an instantiation. -/
def applySubstitution (substitution : Substitution)
    (instantiation : DeclarationInstantiation) : DeclarationInstantiation :=
  { instantiation with
    parameterSubstitution :=
      applyFinalToParameters substitution instantiation.parameterSubstitution
    type := substitution.apply instantiation.type
    predicates := instantiation.predicates.map
      (TypedTraitResolution.applySubstitution substitution) }

end DeclarationInstantiation

namespace DataConstructorInstantiation

def applySubstitution (substitution : Substitution)
    (instantiation : DataConstructorInstantiation) :
    DataConstructorInstantiation := {
  instantiation with
  parameterSubstitution :=
    applyFinalToParameters substitution instantiation.parameterSubstitution
  payloadTypes := instantiation.payloadTypes.map substitution.apply
  resultType := substitution.apply instantiation.resultType
}

end DataConstructorInstantiation

namespace CoercionStep

/-- Every proof obligation owned by this edge, with the primary
`Coerce<From, To>` requirement first and method predicates following in
declaration order. -/
def requirements (step : CoercionStep) : List RequirementId :=
  step.requirement :: step.methodRequirements

def applySubstitution (substitution : Substitution)
    (step : CoercionStep) : CoercionStep :=
  { step with
    source := substitution.apply step.source
    target := substitution.apply step.target }

end CoercionStep

namespace CoercionPath

/-- Check exact endpoints and adjacency for an ordered coercion path.  The
empty path is valid precisely when its endpoints agree. -/
def isValid (source target : Ty) : List CoercionStep → Bool
  | [] => source == target
  | step :: rest =>
      step.source == source &&
        match rest with
        | [] => step.target == target
        | _ => isValid step.target target rest

end CoercionPath

namespace IndirectCallResolution

def applySubstitution (substitution : Substitution)
    (metadata : IndirectCallResolution) : IndirectCallResolution := {
  argumentCount := metadata.argumentCount
  argumentTypeBeforeCoercion :=
    substitution.apply metadata.argumentTypeBeforeCoercion
  argumentTypeAfterCoercion :=
    substitution.apply metadata.argumentTypeAfterCoercion
  argumentCoercions := metadata.argumentCoercions.map
    (CoercionStep.applySubstitution substitution)
}

def hasValidArgumentCoercionPath
    (metadata : IndirectCallResolution) : Bool :=
  CoercionPath.isValid metadata.argumentTypeBeforeCoercion
    metadata.argumentTypeAfterCoercion metadata.argumentCoercions

end IndirectCallResolution

namespace ReferenceResolution

def applySubstitution (substitution : Substitution) :
    ReferenceResolution → ReferenceResolution
  | .local binder => .local binder
  | .declaration instantiation =>
      .declaration (instantiation.applySubstitution substitution)
  | .builtinFunction function => .builtinFunction function
  | .builtinBoolean value => .builtinBoolean value

end ReferenceResolution

namespace CallResolution

def applySubstitution (substitution : Substitution) :
    CallResolution → CallResolution
  | .indirect metadata =>
      .indirect (metadata.applySubstitution substitution)
  | .declaration instantiation =>
      .declaration (instantiation.applySubstitution substitution)
  | .builtinFunction function => .builtinFunction function

end CallResolution

namespace ExpressionForm

/-- Apply a final substitution to all semantic types embedded directly in an
expression shape.  Child occurrence identities remain stable. -/
def applySubstitution (substitution : Substitution) : ExpressionForm → ExpressionForm :=
  fun form => match form with
    | .literal value => .literal value
    | .integerLiteral source resolution =>
        .integerLiteral source (resolution.applySubstitution substitution)
    | .reference name resolution =>
        .reference name (resolution.applySubstitution substitution)
    | .group inner => .group inner
    | .tuple elements => .tuple elements
    | .unary operator operand => .unary operator operand
    | .binary left operator right => .binary left operator right
    | .conditional condition thenBranch elseBranch =>
        .conditional condition thenBranch elseBranch
    | .lambda parameters returnType body =>
        .lambda
          (parameters.map (TypedBinder.applySubstitution substitution))
          (substitution.apply returnType) body
    | .call callee arguments resolution =>
        .call callee arguments (resolution.applySubstitution substitution)
    | .constructor instantiation arguments =>
        .constructor (instantiation.applySubstitution substitution) arguments
    | .member base name memberIndex => .member base name memberIndex
    | .proxy inner => .proxy (substitution.apply inner)
    | .index base key => .index base key

end ExpressionForm

namespace ExpressionNode

/-- The type produced by the source expression before its retained output
coercion path.  For an uncoerced expression the stored post-coercion type is
also its raw type. -/
def rawType (node : ExpressionNode) : Ty :=
  match node.coercions with
  | [] => node.type
  | first :: _ => first.source

/-- Every retained output coercion begins at `rawType`, composes edge by edge,
and ends at the expression node's authoritative post-coercion `type`. -/
def hasValidCoercionPath (node : ExpressionNode) : Bool :=
  CoercionPath.isValid node.rawType node.type node.coercions

def applySubstitution (substitution : Substitution)
    (node : ExpressionNode) : ExpressionNode :=
  { node with
    type := substitution.apply node.type
    form := node.form.applySubstitution substitution
    coercions := node.coercions.map (CoercionStep.applySubstitution substitution) }

end ExpressionNode

namespace MatchPatternInstruction

/-- Close retained pattern-instruction types without changing binder
identities or structural classification. -/
def applySubstitution (substitution : Substitution) :
    MatchPatternInstruction → MatchPatternInstruction
  | .wildcard => .wildcard
  | .integerLiteral source resolution =>
      .integerLiteral source (resolution.applySubstitution substitution)
  | .binder selectedBinder =>
      .binder (selectedBinder.applySubstitution substitution)
  | .constructor instantiation argumentCount =>
      .constructor (instantiation.applySubstitution substitution) argumentCount
  | .tuple elementCount => .tuple elementCount

end MatchPatternInstruction

namespace MatchPatternResolution

def applySubstitution (substitution : Substitution) :
    MatchPatternResolution → MatchPatternResolution
  | .wildcard => .wildcard
  | .integerLiteral source resolution =>
      .integerLiteral source (resolution.applySubstitution substitution)
  | .binder selectedBinder =>
      .binder (selectedBinder.applySubstitution substitution)
  | .constructor instantiation arguments =>
      .constructor (instantiation.applySubstitution substitution)
        (arguments.map (MatchPatternInstruction.applySubstitution substitution))
  | .tuple elements =>
      .tuple (elements.map (MatchPatternInstruction.applySubstitution substitution))

end MatchPatternResolution

namespace TypedMatchPattern

def applySubstitution (substitution : Substitution)
    (pattern : TypedMatchPattern) : TypedMatchPattern := {
  pattern with
  type := substitution.apply pattern.type
  resolution := pattern.resolution.applySubstitution substitution
}

end TypedMatchPattern

namespace TypedMatchCase

def applySubstitution (substitution : Substitution)
    (arm : TypedMatchCase) : TypedMatchCase := {
  arm with pattern := arm.pattern.applySubstitution substitution
}

end TypedMatchCase

namespace MatchResolution

def applySubstitution (substitution : Substitution)
    (resolution : MatchResolution) : MatchResolution := {
  resolution with
  cases := resolution.cases.map (TypedMatchCase.applySubstitution substitution)
}

end MatchResolution

namespace PlaceResolution

def applySubstitution (substitution : Substitution)
    (place : PlaceResolution) : PlaceResolution := {
  place with type := substitution.apply place.type
}

end PlaceResolution

namespace AssignmentResolution

def applySubstitution (substitution : Substitution)
    (assignment : AssignmentResolution) : AssignmentResolution := {
  assignment with target := assignment.target.applySubstitution substitution
}

end AssignmentResolution

namespace ForItemForm

def applySubstitution (substitution : Substitution) :
    ForItemForm → ForItemForm
  | .letDecl binder initializer =>
      .letDecl (binder.applySubstitution substitution) initializer
  | .expression expressionId => .expression expressionId
  | .assignValue assignment operator value =>
      .assignValue (assignment.applySubstitution substitution) operator value
  | .assignBitNot assignment =>
      .assignBitNot (assignment.applySubstitution substitution)

end ForItemForm

namespace StatementForm

/-- Apply a final substitution to binder schemes embedded in a statement. -/
def applySubstitution (substitution : Substitution) : StatementForm → StatementForm :=
  fun form => match form with
    | .letDecl binder initializer =>
        .letDecl (binder.applySubstitution substitution) initializer
    | .returnStmt value => .returnStmt value
    | .expression expressionId trailingSemicolon =>
        .expression expressionId trailingSemicolon
    | .assignValue assignment operator value =>
        .assignValue (assignment.applySubstitution substitution) operator value
    | .assignBitNot assignment =>
        .assignBitNot (assignment.applySubstitution substitution)
    | .ifThen condition thenBody elseBody =>
        .ifThen condition thenBody elseBody
    | .block body => .block body
    | .matchWith resolution =>
        .matchWith (resolution.applySubstitution substitution)
    | .forLoop initializer condition post body =>
        .forLoop
          (initializer.map (ForItemForm.applySubstitution substitution))
          condition (post.map (ForItemForm.applySubstitution substitution)) body
    | .whileLoop condition body => .whileLoop condition body
    | .breakStmt => .breakStmt
    | .continueStmt => .continueStmt

end StatementForm

namespace StatementNode

def applySubstitution (substitution : Substitution)
    (node : StatementNode) : StatementNode :=
  { node with
    type := substitution.apply node.type
    form := node.form.applySubstitution substitution }

end StatementNode

namespace MatchPatternInstruction

/-- Binder identities introduced by a flat pattern instruction stream. -/
def binderIds (instructions : List MatchPatternInstruction) :
    List Resolved.LocalId :=
  instructions.filterMap fun instruction =>
    match instruction with
    | .binder selectedBinder => some selectedBinder.id
    | .wildcard | .integerLiteral .. | .constructor .. | .tuple .. => none

end MatchPatternInstruction

namespace TypedMatchPattern

/-- Binder identities introduced by a resolved pattern root and its flat
children. -/
def binderIds (pattern : TypedMatchPattern) : List Resolved.LocalId :=
  match pattern.resolution with
  | .wildcard | .integerLiteral .. => []
  | .binder selectedBinder => [selectedBinder.id]
  | .constructor _ arguments | .tuple arguments =>
      MatchPatternInstruction.binderIds arguments

end TypedMatchPattern

namespace ForItemForm

/-- Local definitions retained directly by one `for` header item. -/
def definedLocalIds : ForItemForm → List Resolved.LocalId
  | .letDecl selectedBinder _ => [selectedBinder.id]
  | .expression _ | .assignValue .. | .assignBitNot _ => []

/-- Initialized lexical binders retained directly by one `for` header item.
This inventory deliberately includes generalized binders with no qualified
requirements, unlike the template-site inventory below. -/
def initializedLetBinders : ForItemForm → List TypedBinder
  | .letDecl binder (some _) => [binder]
  | .letDecl _ none | .expression _ | .assignValue .. | .assignBitNot _ => []

/-- Qualified-local template identities materialized by an initialized `let`
in a `for` initializer or post clause.  Uninitialized declarations do not own
an initializer scope and therefore contribute no templates. -/
def localSchemeTemplateSites : ForItemForm → List LocalSchemeTemplateSite
  | .letDecl binder (some initializer) =>
      binder.schemeRequirements.map fun requirement => {
        binder
        initializer := .expression initializer
        requirement
      }
  | .letDecl _ none | .expression _ | .assignValue .. | .assignBitNot _ => []

/-- Stable qualified-template identities in predicate order. -/
def localSchemeTemplateIds : ForItemForm → List RequirementId
  | .letDecl binder (some _) =>
      binder.schemeRequirements.map fun requirement =>
        requirement.templateRequirement
  | .letDecl _ none | .expression _ | .assignValue .. | .assignBitNot _ => []

end ForItemForm

namespace ExpressionForm

/-- Local definitions retained directly by one expression form. -/
def definedLocalIds : ExpressionForm → List Resolved.LocalId
  | .lambda parameters _ _ => parameters.map (fun binder => binder.id)
  | .literal _ | .integerLiteral .. | .reference .. | .group _ | .tuple _ |
      .unary .. | .binary .. | .conditional .. | .call .. | .constructor .. |
      .member .. | .proxy _ | .index .. => []

end ExpressionForm

namespace StatementForm

/-- Local definitions retained directly by one statement form. -/
def definedLocalIds : StatementForm → List Resolved.LocalId
  | .letDecl selectedBinder _ => [selectedBinder.id]
  | .matchWith resolution =>
      resolution.hiddenScrutinee ::
        resolution.cases.flatMap fun matchCase => matchCase.pattern.binderIds
  | .forLoop initializer _ post _ =>
      initializer.flatMap ForItemForm.definedLocalIds ++
        post.flatMap ForItemForm.definedLocalIds
  | .returnStmt _ | .expression .. | .assignValue .. | .assignBitNot _ |
      .ifThen .. | .block _ | .whileLoop .. | .breakStmt | .continueStmt => []

/-- Initialized lexical binders materialized directly by one statement node,
including initialized lets in `for` initializer and post clauses. -/
def initializedLetBinders : StatementForm → List TypedBinder
  | .letDecl binder (some _) => [binder]
  | .forLoop initializer _ post _ =>
      initializer.flatMap ForItemForm.initializedLetBinders ++
        post.flatMap ForItemForm.initializedLetBinders
  | .letDecl _ none | .returnStmt _ | .expression .. | .assignValue .. |
      .assignBitNot _ | .ifThen .. | .block _ | .matchWith _ | .whileLoop .. |
      .breakStmt | .continueStmt => []

/-- Qualified-local template identities materialized directly by initialized
statement lets, including initialized lets in `for` initializer and post
clauses.  Child occurrence bodies are represented by their own table nodes. -/
def localSchemeTemplateSites : StatementForm → List LocalSchemeTemplateSite
  | .letDecl binder (some initializer) =>
      binder.schemeRequirements.map fun requirement => {
        binder
        initializer := .expression initializer
        requirement
      }
  | .forLoop initializer _ post _ =>
      initializer.flatMap ForItemForm.localSchemeTemplateSites ++
        post.flatMap ForItemForm.localSchemeTemplateSites
  | .letDecl _ none | .returnStmt _ | .expression .. | .assignValue .. |
      .assignBitNot _ | .ifThen .. | .block _ | .matchWith _ | .whileLoop .. |
      .breakStmt | .continueStmt => []

/-- Stable qualified-template identities in predicate order. -/
def localSchemeTemplateIds : StatementForm → List RequirementId
  | .letDecl binder (some _) =>
      binder.schemeRequirements.map fun requirement =>
        requirement.templateRequirement
  | .forLoop initializer _ post _ =>
      initializer.flatMap ForItemForm.localSchemeTemplateIds ++
        post.flatMap ForItemForm.localSchemeTemplateIds
  | .letDecl _ none | .returnStmt _ | .expression .. | .assignValue .. |
      .assignBitNot _ | .ifThen .. | .block _ | .matchWith _ | .whileLoop .. |
      .breakStmt | .continueStmt => []

end StatementForm

namespace ForItemForm

/-- Primary requirement identities owned by assignments in one `for` header
item.  Expression and local-declaration requirements belong to their own
source nodes and therefore are not mirrored here. -/
def primaryRequirementIds : ForItemForm → List RequirementId
  | .assignValue assignment _ _ | .assignBitNot assignment =>
      assignment.requirements
  | .letDecl .. | .expression _ => []

end ForItemForm

namespace StatementForm

/-- Primary requirement identities owned directly by one statement form.
Match aggregates and coercion metadata are mirrors and deliberately excluded. -/
def primaryRequirementIds : StatementForm → List RequirementId
  | .assignValue assignment _ _ | .assignBitNot assignment =>
      assignment.requirements
  | .matchWith resolution =>
      resolution.cases.flatMap fun matchCase => matchCase.pattern.requirements
  | .forLoop initializer _ post _ =>
      initializer.flatMap ForItemForm.primaryRequirementIds ++
        post.flatMap ForItemForm.primaryRequirementIds
  | .letDecl .. | .returnStmt _ | .expression .. | .ifThen .. | .block _ |
      .whileLoop .. | .breakStmt | .continueStmt => []

end StatementForm

namespace Node

/-- Recover the category-preserving identity stored by one node. -/
def id : Node → NodeId
  | .expression node => .expression node.id
  | .statement node => .statement node.id

/-- Erase the expression/statement category while retaining source identity. -/
def occurrenceId : Node → OccurrenceId
  | node => node.id.occurrenceId

def applySubstitution (substitution : Substitution) : Node → Node
  | .expression node => .expression (node.applySubstitution substitution)
  | .statement node => .statement (node.applySubstitution substitution)

/-- Local binders introduced directly by one heterogeneous source node.
Nested statement and expression bodies are represented by their own table
nodes and are therefore counted when those nodes are visited. -/
def definedLocalIds : Node → List Resolved.LocalId
  | .expression node => node.form.definedLocalIds
  | .statement node => node.form.definedLocalIds

/-- Initialized lexical binders materialized directly by one heterogeneous
source node. -/
def initializedLetBinders : Node → List TypedBinder
  | .expression _ => []
  | .statement node => node.form.initializedLetBinders

/-- Qualified-local template identities materialized directly by one
heterogeneous source node. -/
def localSchemeTemplateSites : Node → List LocalSchemeTemplateSite
  | .expression _ => []
  | .statement node => node.form.localSchemeTemplateSites

/-- Stable qualified-template identities in predicate order. -/
def localSchemeTemplateIds : Node → List RequirementId
  | .expression _ => []
  | .statement node => node.form.localSchemeTemplateIds

/-- Primary requirement identities retained directly by one heterogeneous
source node. -/
def primaryRequirementIds : Node → List RequirementId
  | .expression node => node.requirements
  | .statement node => node.form.primaryRequirementIds

/-- Exact primary attachments owned directly by one heterogeneous node. -/
def primaryRequirementSites : Node → List PrimaryRequirementSite
  | .expression node =>
      node.requirements.map fun requirement => {
        occurrence := .expression node.id
        requirement
      }
  | .statement node =>
      node.form.primaryRequirementIds.map fun requirement => {
        occurrence := .statement node.id
        requirement
      }

end Node

namespace TypedSource

/-- Stable local definitions in declaration-input and node-table order.  This
is the canonical executable inventory used by finalization and mirrored by
the declarative ownership judgment. -/
def definedLocalIds (source : TypedSource) : List Resolved.LocalId :=
  source.inputs.map (fun binder => binder.id) ++
    source.nodes.flatMap Node.definedLocalIds

/-- Every initialized lexical binder in node-table order.  The inventory is
independent of qualified-requirement cardinality so that capture validation
also covers ordinary generalized values. -/
def initializedLetBinders (source : TypedSource) : List TypedBinder :=
  source.nodes.flatMap Node.initializedLetBinders

/-- Stable qualified-local template inventory in node-table and predicate
order.  Only initialized lexical lets own template requirements. -/
def localSchemeTemplateIds (source : TypedSource) : List RequirementId :=
  source.nodes.flatMap Node.localSchemeTemplateIds

/-- Full initialized local-scheme template inventory in node-table and
predicate order. -/
def localSchemeTemplateSites (source : TypedSource) :
    List LocalSchemeTemplateSite :=
  source.nodes.flatMap Node.localSchemeTemplateSites

/-- Stable primary requirement inventory in node-table and attachment order.
This excludes every secondary mirror of a requirement identity. -/
def primaryRequirementIds (source : TypedSource) : List RequirementId :=
  source.nodes.flatMap Node.primaryRequirementIds

/-- Exact primary requirement attachments in node-table and attachment order. -/
def primaryRequirementSites (source : TypedSource) : List PrimaryRequirementSite :=
  source.nodes.flatMap Node.primaryRequirementSites

/-- Declaration entries and direct child slots, retaining expression/statement
categories.  A closed occurrence forest names every retained node exactly once
in this incoming-position inventory. -/
def incomingNodeIds (source : TypedSource) : List NodeId :=
  source.roots ++ source.nodes.flatMap Node.references

/-- First node with the requested exact category-preserving identity. -/
def lookupNodeId? (source : TypedSource) (id : NodeId) : Option Node :=
  source.nodes.find? fun node => decide (node.id = id)

/-- First node with the requested declaration-owned occurrence identity. -/
def lookupNode? (source : TypedSource) (id : OccurrenceId) : Option Node :=
  source.nodes.find? fun node => decide (node.occurrenceId = id)

/-- Typed expression lookup without permitting a statement ID at the API
boundary. -/
def lookupExpression? (source : TypedSource)
    (id : ExpressionId) : Option ExpressionNode :=
  match source.lookupNode? id.occurrence with
  | some (.expression node) => some node
  | _ => none

/-- Typed statement lookup without permitting an expression ID at the API
boundary. -/
def lookupStatement? (source : TypedSource)
    (id : StatementId) : Option StatementNode :=
  match source.lookupNode? id.occurrence with
  | some (.statement node) => some node
  | _ => none

/-- Close every embedded flexible type while preserving all stable identities
and source-table order. -/
def applySubstitution (substitution : Substitution)
    (source : TypedSource) : TypedSource :=
  { source with
    inputs := source.inputs.map (TypedBinder.applySubstitution substitution)
    nodes := source.nodes.map (Node.applySubstitution substitution) }

end TypedSource

end Solcore.Frontend.SourceInference
