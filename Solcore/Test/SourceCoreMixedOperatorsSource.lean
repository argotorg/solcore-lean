import Solcore.Test.SourceCoreMixedOperatorsFixture
import Solcore.Test.SourceCoreMixedImperativeSourceSteps

/-! Exact original operator occurrences retain both ordered identity calls and
the following builtin value leaf in the original ordered pair. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreMixedImperative (StatementAt BooleanAt)
open Tests.SourceCoreSelectedInterleavedLocal (CallShape)

structure Shape (source : TypedSource) where
  flag : TypedBinder
  f : IdentityShape source
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  falseNode : BooleanAt source false
  firstCall : CallShape source f.binder flagRead.node.id .bool
  secondCall : CallShape source f.binder falseNode.node.id .bool
  negated : ExpressionNode
  negatedFound : source.lookupExpression? negated.id = some negated
  negatedForm : negated.form = .unary .logicalNot secondCall.node.id
  negatedRequirements : negated.requirements = []
  negatedCoercions : negated.coercions = []
  binary : ExpressionNode
  binaryFound : source.lookupExpression? binary.id = some binary
  binaryForm : binary.form = .binary firstCall.node.id .logicalAnd negated.id
  binaryRequirements : binary.requirements = []
  binaryCoercions : binary.coercions = []
  builtin : ExpressionNode
  builtinName : String
  builtinFound : source.lookupExpression? builtin.id = some builtin
  builtinForm : builtin.form = .reference builtinName (.builtinFunction .wordToInteger)
  builtinRequirements : builtin.requirements = []
  builtinCoercions : builtin.coercions = []
  initialized : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [binary.id,builtin.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement initialized.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  fFlag : f.binder.id ≠ flag.id

private def identity (source : TypedSource) (binder : TypedBinder)
    (lambda parameterNode : ExpressionNode) (returned : StatementNode) : IO (IdentityShape source) := do
  let .lambda [parameter] (.variable typeVar) _ := lambda.form | throw (IO.userError "identity original lambda")
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVar)
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (.variable typeVar)⟩) "identity principal scheme"
  let ⟨requirements⟩ ← observed (binder.schemeRequirements = []) "identity scheme requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVar)) "identity parameter"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "identity parameter requirements"
  let ⟨found⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "identity lambda occurrence"
  let ⟨form⟩ ← observed (lambda.form = .lambda [parameter] (.variable typeVar) [returned.id]) "identity body"
  let ⟨raw⟩ ← observed (lambda.rawType = binder.scheme.body) "identity raw type"
  let ⟨type⟩ ← observed (lambda.type = binder.scheme.body) "identity type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "identity lambda requirements"
  let ⟨coercions⟩ ← observed (lambda.coercions = []) "identity lambda coercions"
  let ⟨returnFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "identity return identity"
  let ⟨returnForm⟩ ← observed (returned.form = .returnStmt (some parameterRead.node.id)) "identity return parameter"
  return ⟨binder,parameter,typeVar,lambda,returned,parameterRead,scheme,requirements,parameterScheme,
    parameterRequirements,found,form,raw,type,lambdaRequirements,coercions,returnFound,returnForm⟩

private def boolean (source : TypedSource) (node : ExpressionNode) (value : Bool) :
    IO (BooleanAt source value) := do
  let .reference name (.builtinBoolean _) := node.form | throw (IO.userError "binary original Boolean")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "binary Boolean identity"
  let ⟨form⟩ ← observed (node.form = .reference name (.builtinBoolean value)) "binary Boolean value"
  let ⟨requirements⟩ ← observed (node.requirements = []) "binary Boolean requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "binary Boolean coercions"
  return ⟨node,name,found,form,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "builtin original input")
  let [.expression parameterRead,.statement identityReturn,.expression lambda,.statement initialized,
       .expression flagNode,.expression firstCallee,.expression firstExpr,
       .expression falseExpr,.expression secondCallee,.expression secondExpr,.expression negated,.expression binary,
       .expression builtin,.expression tuple,.statement returned] := source.nodes | throw (IO.userError "operator original graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "builtin original declaration")
  let f ← identity source binder lambda parameterRead identityReturn
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let falseNode ← boolean source falseExpr false
  let firstCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder flagRead.node.id .bool firstCallee firstExpr
  let secondCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder falseNode.node.id .bool secondCallee secondExpr
  let ⟨negatedFound⟩ ← observed (source.lookupExpression? negated.id = some negated) "negated identity"
  let ⟨negatedForm⟩ ← observed (negated.form = .unary .logicalNot secondCall.node.id) "negated operand"
  let ⟨negatedRequirements⟩ ← observed (negated.requirements = []) "negated requirements"
  let ⟨negatedCoercions⟩ ← observed (negated.coercions = []) "negated coercions"
  let ⟨binaryFound⟩ ← observed (source.lookupExpression? binary.id = some binary) "binary identity"
  let ⟨binaryForm⟩ ← observed (binary.form = .binary firstCall.node.id .logicalAnd negated.id) "binary ordered branches"
  let ⟨binaryRequirements⟩ ← observed (binary.requirements = []) "binary requirements"
  let ⟨binaryCoercions⟩ ← observed (binary.coercions = []) "binary coercions"
  let .reference builtinName (.builtinFunction .wordToInteger) := builtin.form
    | throw (IO.userError "original builtin reference")
  let ⟨builtinFound⟩ ← observed (source.lookupExpression? builtin.id = some builtin) "builtin identity"
  let ⟨builtinForm⟩ ← observed (builtin.form = .reference builtinName (.builtinFunction .wordToInteger)) "builtin form"
  let ⟨builtinRequirements⟩ ← observed (builtin.requirements = []) "builtin requirements"
  let ⟨builtinCoercions⟩ ← observed (builtin.coercions = []) "builtin coercions"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "declaration identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl f.binder (some f.lambda.id)) "declaration form"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "tuple identity"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [binary.id,builtin.id]) "tuple order"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "return form"
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "original inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement returned.id]) "original roots"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "flag scheme"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ flag.id) "distinct identities"
  return ⟨flag,f,flagRead,falseNode,firstCall,secondCall,negated,negatedFound,negatedForm,negatedRequirements,negatedCoercions,binary,binaryFound,binaryForm,
    binaryRequirements,binaryCoercions,builtin,builtinName,builtinFound,builtinForm,builtinRequirements,builtinCoercions,
    ⟨initialized,initializedFound,initializedForm⟩,tuple,tupleFound,tupleForm,tupleRequirements,tupleCoercions,
    ⟨returned,returnedFound,returnedForm⟩,inputs,roots,flagScheme,fFlag⟩

end Tests.SourceCoreMixedOperators
