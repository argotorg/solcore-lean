import Solcore.Test.SourceCoreNamedBranchSource
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.SourceSemantics.Dynamic.Evaluation

/-! One unchanged original function captures an identity lambda as a generalized
local, stores its Word call result in an ordinary local, then calls the Bool instance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
open Solcore Core Frontend SourceInference SourceSemantics

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function local(flag: Bool) returns (Word, Bool) { let f = lam(value) { return value; }; let x = f(11); return (x, f(flag)); }"}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}

structure WordNode (source : TypedSource) where
  node : ExpressionNode
  literal : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .integerLiteral literal resolution
  target : resolution.targetType = .word
  requirements : node.requirements = [resolution.requirement]
  coercions : node.coercions = []

theorem WordNode.evaluates {source : TypedSource} (node : WordNode source)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context node.node.id type) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id
      (.word (Word.ofNatModulo node.resolution.rawValue)) heap := by
  have valid : IntegerLiteralValid context node.literal node.resolution := by
    cases typed with
    | intro contains raw _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans node.found)
      rw [node.form] at raw
      cases raw with | integerLiteral valid => exact valid
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context node.literal node.resolution
      (.word (Word.ofNatModulo node.resolution.rawValue)) := by
    cases valid with
    | word meaning target evidence =>
      generalize resolutionEq : node.resolution = resolution at *
      cases resolution with
      | mk value type requirement =>
        dsimp only at target
        subst type
        exact .word meaning evidence
    | integer _ target _ => rw [node.target] at target; cases target
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .integerLiteral (by rw [node.requirements,node.coercions]; rfl) constructs
  · rw [node.coercions]; exact .nil

structure CallShape (source : TypedSource) (binder : TypedBinder)
    (argument : ExpressionId) (type : TypeSystem.Ty) where
  callee : Tests.SourceCoreNamedBranch.Read source binder (.function type type)
  node : ExpressionNode
  metadata : IndirectCallResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .call callee.node.id [argument] (.indirect metadata)
  arity : metadata.argumentCount = 1
  argumentCoercions : metadata.argumentCoercions = []
  requirements : node.requirements = []
  coercions : node.coercions = []

structure Shape (source : TypedSource) where
  flag : TypedBinder
  binder : TypedBinder
  parameter : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  initialized : StatementNode
  lambda : ExpressionNode
  identityReturn : StatementNode
  parameterRead : Tests.SourceCoreNamedBranch.Read source parameter (.variable typeVariable)
  literal : WordNode source
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  wordCall : CallShape source binder literal.node.id .word
  boolCall : CallShape source binder flagRead.node.id .bool
  valueBinder : TypedBinder
  valueInitialized : StatementNode
  valueRead : Tests.SourceCoreNamedBranch.Read source valueBinder .word
  tuple : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [flag]
  flagScheme : flag.scheme = .mono .bool
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (.variable typeVariable)⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  valueScheme : valueBinder.scheme = .mono .word
  roots : source.roots = [.statement initialized.id, .statement valueInitialized.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl binder (some lambda.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] (.variable typeVariable) [identityReturn.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  identityFound : source.lookupStatement? identityReturn.id = some identityReturn
  identityForm : identityReturn.form = .returnStmt (some parameterRead.node.id)
  literalValue : literal.resolution.rawValue = 11
  valueFound : source.lookupStatement? valueInitialized.id = some valueInitialized
  valueForm : valueInitialized.form = .letDecl valueBinder (some wordCall.node.id)
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [valueRead.node.id, boolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some tuple.id)

def Shape.descriptor {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] (.variable shape.typeVariable) [shape.identityReturn.id]

def Shape.allocatedHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨before.cells ++ [{ type := shape.binder.scheme.body, value := none, generalized := some (shape.descriptor context environment) }]⟩

theorem Shape.captures {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

/-- The original let stores one principal descriptor. It performs no lambda
body call and selects neither the Word nor Bool instance at allocation. -/
theorem Shape.initializes {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (extended : BinderExtends source.owner context shape.binder nextContext) :
    Dynamic.StatementExecutes program context evidence source environment before shape.initialized.id
      nextContext (.fallthrough ((shape.binder.id, ⟨before.cells.length⟩) :: environment))
      (shape.allocatedHeap context environment before) := by
  apply Dynamic.StatementExecutes.letInitializedGeneralized
    (lookupStatement?_sound shape.initializedFound) shape.initializedForm
    (shape.captures context environment) (by rw [shape.scheme]; simp) extended
  exact .append

end Tests.SourceCoreSelectedInterleavedLocal
