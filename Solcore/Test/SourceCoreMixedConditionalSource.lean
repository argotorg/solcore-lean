import Solcore.Test.SourceCoreMixedConditionalFixture
import Solcore.Test.SourceCoreMixedImperativeSourceSteps

/-! Exact original conditional occurrences retain both identity-call branches and
the following builtin value leaf in the original ordered pair. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreMixedImperative (StatementAt BooleanAt)
open Tests.SourceCoreSelectedInterleavedLocal (CallShape)

structure Shape (source : TypedSource) where
  flag : TypedBinder
  f : IdentityShape source
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  trueNode : BooleanAt source true
  falseNode : BooleanAt source false
  yesCall : CallShape source f.binder trueNode.node.id .bool
  noCall : CallShape source f.binder falseNode.node.id .bool
  conditional : ExpressionNode
  conditionalFound : source.lookupExpression? conditional.id = some conditional
  conditionalForm : conditional.form = .conditional flagRead.node.id yesCall.node.id noCall.node.id
  conditionalRequirements : conditional.requirements = []
  conditionalCoercions : conditional.coercions = []
  builtin : ExpressionNode
  builtinName : String
  builtinFound : source.lookupExpression? builtin.id = some builtin
  builtinForm : builtin.form = .reference builtinName (.builtinFunction .wordToInteger)
  builtinRequirements : builtin.requirements = []
  builtinCoercions : builtin.coercions = []
  initialized : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [conditional.id,builtin.id]
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
  let .reference name (.builtinBoolean _) := node.form | throw (IO.userError "conditional original Boolean")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "conditional Boolean identity"
  let ⟨form⟩ ← observed (node.form = .reference name (.builtinBoolean value)) "conditional Boolean value"
  let ⟨requirements⟩ ← observed (node.requirements = []) "conditional Boolean requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "conditional Boolean coercions"
  return ⟨node,name,found,form,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "builtin original input")
  let [.expression parameterRead,.statement identityReturn,.expression lambda,.statement initialized,
       .expression flagNode,.expression trueExpr,.expression yesCallee,.expression yesExpr,
       .expression falseExpr,.expression noCallee,.expression noExpr,.expression conditional,
       .expression builtin,.expression tuple,.statement returned] := source.nodes | throw (IO.userError "builtin original graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "builtin original declaration")
  let f ← identity source binder lambda parameterRead identityReturn
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let trueNode ← boolean source trueExpr true
  let falseNode ← boolean source falseExpr false
  let yesCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder trueNode.node.id .bool yesCallee yesExpr
  let noCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder falseNode.node.id .bool noCallee noExpr
  let ⟨conditionalFound⟩ ← observed (source.lookupExpression? conditional.id = some conditional) "conditional identity"
  let ⟨conditionalForm⟩ ← observed (conditional.form = .conditional flagRead.node.id yesCall.node.id noCall.node.id) "conditional ordered branches"
  let ⟨conditionalRequirements⟩ ← observed (conditional.requirements = []) "conditional requirements"
  let ⟨conditionalCoercions⟩ ← observed (conditional.coercions = []) "conditional coercions"
  let .reference builtinName (.builtinFunction .wordToInteger) := builtin.form
    | throw (IO.userError "original builtin reference")
  let ⟨builtinFound⟩ ← observed (source.lookupExpression? builtin.id = some builtin) "builtin identity"
  let ⟨builtinForm⟩ ← observed (builtin.form = .reference builtinName (.builtinFunction .wordToInteger)) "builtin form"
  let ⟨builtinRequirements⟩ ← observed (builtin.requirements = []) "builtin requirements"
  let ⟨builtinCoercions⟩ ← observed (builtin.coercions = []) "builtin coercions"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "declaration identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl f.binder (some f.lambda.id)) "declaration form"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "tuple identity"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [conditional.id,builtin.id]) "tuple order"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "return form"
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "original inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement returned.id]) "original roots"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "flag scheme"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ flag.id) "distinct identities"
  return ⟨flag,f,flagRead,trueNode,falseNode,yesCall,noCall,conditional,conditionalFound,conditionalForm,
    conditionalRequirements,conditionalCoercions,builtin,builtinName,builtinFound,builtinForm,builtinRequirements,builtinCoercions,
    ⟨initialized,initializedFound,initializedForm⟩,tuple,tupleFound,tupleForm,tupleRequirements,tupleCoercions,
    ⟨returned,returnedFound,returnedForm⟩,inputs,roots,flagScheme,fFlag⟩

end Tests.SourceCoreMixedConditional
