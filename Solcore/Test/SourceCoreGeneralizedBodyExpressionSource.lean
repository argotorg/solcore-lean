import Solcore.Test.SourceCoreGeneralizedBodyExpressionFixture
import Solcore.Test.SourceCoreMixedImperativeSourceSteps

/-! The complete original lambda keeps both parameter reads, its captured Bool,
and its numeric leaf. Observations record syntax and typing metadata only. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read observeRead)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode)
open Tests.SourceCoreMixedImperative (StatementAt)

def resultType (type : TypeSystem.Ty) : TypeSystem.Ty := .product (.product type type) (.product .bool .word)
def resultValue (value : Dynamic.Value) (flag : Bool) : Dynamic.Value :=
  .product (.product value value) (.product (.bool flag) (.word (Word.ofNatModulo 0)))
def outputValue (flag : Bool) : Dynamic.Value :=
  .product (resultValue (.word (Word.ofNatModulo 11)) flag) (resultValue (.bool flag) flag)

structure PairAt (source : TypedSource) (left right : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .tuple [left,right]
  requirements : node.requirements = []
  coercions : node.coercions = []

structure CallShape (source : TypedSource) (binder : TypedBinder)
    (argument : ExpressionId) (type : TypeSystem.Ty) where
  callee : Read source binder (.function type (resultType type))
  node : ExpressionNode
  metadata : IndirectCallResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .call callee.node.id [argument] (.indirect metadata)
  arity : metadata.argumentCount = 1
  argumentCoercions : metadata.argumentCoercions = []
  requirements : node.requirements = []
  coercions : node.coercions = []

structure LambdaShape (source : TypedSource) where
  binder : TypedBinder
  parameter : TypedBinder
  flag : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  lambda : ExpressionNode
  returned : StatementNode
  first : Read source parameter (.variable typeVariable)
  second : Read source parameter (.variable typeVariable)
  duplicate : PairAt source first.node.id second.node.id
  capture : Read source flag .bool
  zero : WordNode source
  extra : PairAt source capture.node.id zero.node.id
  result : PairAt source duplicate.node.id extra.node.id
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (resultType (.variable typeVariable))⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] (resultType (.variable typeVariable)) [returned.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  returnFound : source.lookupStatement? returned.id = some returned
  returnForm : returned.form = .returnStmt (some result.node.id)
  zeroValue : zero.resolution.rawValue = 0
  parameterFlag : parameter.id ≠ flag.id

structure Shape (source : TypedSource) where
  f : LambdaShape source
  literal : WordNode source
  flagRead : Read source f.flag .bool
  wordCall : CallShape source f.binder literal.node.id .word
  boolCall : CallShape source f.binder flagRead.node.id .bool
  initialized : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tuple : PairAt source wordCall.node.id boolCall.node.id
  returned : StatementAt source (.returnStmt (some tuple.node.id))
  inputs : source.inputs = [f.flag]
  roots : source.roots = [.statement initialized.node.id,.statement returned.node.id]
  flagScheme : f.flag.scheme = .mono .bool
  literalValue : literal.resolution.rawValue = 11
  fFlag : f.binder.id ≠ f.flag.id
abbrev Shape.flag {source : TypedSource} (shape : Shape source) := shape.f.flag

private def pair (source : TypedSource) (left right : ExpressionId) (node : ExpressionNode) : IO (PairAt source left right) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "pair occurrence"
  let ⟨form⟩ ← observed (node.form = .tuple [left,right]) "pair ordered children"
  let ⟨requirements⟩ ← observed (node.requirements = []) "pair requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "pair coercions"
  return ⟨node,found,form,requirements,coercions⟩

private def call (source : TypedSource) (binder : TypedBinder) (argument : ExpressionId) (type : TypeSystem.Ty)
    (callee node : ExpressionNode) : IO (CallShape source binder argument type) := do
  let read ← observeRead source binder callee (.function type (resultType type))
  let .call _ _ (.indirect metadata) := node.form | throw (IO.userError "indirect call")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "call occurrence"
  let ⟨form⟩ ← observed (node.form = .call read.node.id [argument] (.indirect metadata)) "call ordered argument"
  let ⟨arity⟩ ← observed (metadata.argumentCount = 1) "call arity"
  let ⟨argumentCoercions⟩ ← observed (metadata.argumentCoercions = []) "call argument coercions"
  let ⟨requirements⟩ ← observed (node.requirements = []) "call requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "call coercions"
  return ⟨read,node,metadata,found,form,arity,argumentCoercions,requirements,coercions⟩

private def wordNode (source : TypedSource) (node : ExpressionNode) : IO (WordNode source) := do
  let .integerLiteral literal resolution := node.form | throw (IO.userError "imperative Word literal")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "Word identity"
  let ⟨form⟩ ← observed (node.form = .integerLiteral literal resolution) "Word form"
  let ⟨target⟩ ← observed (resolution.targetType = .word) "Word target"
  let ⟨requirements⟩ ← observed (node.requirements = [resolution.requirement]) "Word requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "Word coercions"
  return ⟨node,literal,resolution,found,form,target,requirements,coercions⟩


def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "original input")
  let [.expression first,.expression second,.expression duplicate,.expression capture,.expression zero,
      .expression extra,.expression result,.statement lambdaReturn,.expression lambda,.statement initialized,
      .expression literal,.expression wordCallee,.expression wordCall,.expression flagRead,
      .expression boolCallee,.expression boolCall,.expression tuple,.statement returned] := source.nodes
    | throw (IO.userError "complete original duplicate graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "original generalized binder")
  let .lambda [parameter] _ _ := lambda.form | throw (IO.userError "original lambda")
  let .variable typeVar := parameter.scheme.body | throw (IO.userError "principal parameter")
  let first ← observeRead source parameter first (.variable typeVar)
  let second ← observeRead source parameter second (.variable typeVar)
  let duplicate ← pair source first.node.id second.node.id duplicate
  let capture ← observeRead source flag capture .bool
  let zero ← wordNode source zero
  let extra ← pair source capture.node.id zero.node.id extra
  let result ← pair source duplicate.node.id extra.node.id result
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (resultType (.variable typeVar))⟩) "principal duplicate scheme"
  let ⟨requirements⟩ ← observed (binder.schemeRequirements = []) "principal requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVar)) "parameter scheme"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "parameter requirements"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "lambda occurrence"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [parameter] (resultType (.variable typeVar)) [lambdaReturn.id]) "lambda body"
  let ⟨lambdaRaw⟩ ← observed (lambda.rawType = binder.scheme.body) "lambda raw"
  let ⟨lambdaType⟩ ← observed (lambda.type = binder.scheme.body) "lambda type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "lambda requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "lambda coercions"
  let ⟨returnFound⟩ ← observed (source.lookupStatement? lambdaReturn.id = some lambdaReturn) "lambda return occurrence"
  let ⟨returnForm⟩ ← observed (lambdaReturn.form = .returnStmt (some result.node.id)) "lambda return expression"
  let ⟨zeroValue⟩ ← observed (zero.resolution.rawValue = 0) "numeric leaf zero"
  let ⟨parameterFlag⟩ ← observed (parameter.id ≠ flag.id) "captured binder differs"
  let f : LambdaShape source := ⟨binder,parameter,flag,typeVar,lambda,lambdaReturn,first,second,duplicate,capture,zero,extra,result,
    scheme,requirements,parameterScheme,parameterRequirements,lambdaFound,lambdaForm,lambdaRaw,lambdaType,
    lambdaRequirements,lambdaCoercions,returnFound,returnForm,zeroValue,parameterFlag⟩
  let literal ← wordNode source literal
  let flagRead ← observeRead source flag flagRead .bool
  let wordCall ← call source binder literal.node.id .word wordCallee wordCall
  let boolCall ← call source binder flagRead.node.id .bool boolCallee boolCall
  let tuple ← pair source wordCall.node.id boolCall.node.id tuple
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "declaration occurrence"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl f.binder (some f.lambda.id)) "declaration form"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "return occurrence"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.node.id)) "return form"
  let ⟨inputs⟩ ← observed (source.inputs = [f.flag]) "complete original parameters"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement returned.id]) "complete original roots"
  let ⟨flagScheme⟩ ← observed (f.flag.scheme = .mono .bool) "flag scheme"
  let ⟨literalValue⟩ ← observed (literal.resolution.rawValue = 11) "argument literal"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ f.flag.id) "capture distinct from declaration"
  return ⟨f,literal,flagRead,wordCall,boolCall,⟨initialized,initializedFound,initializedForm⟩,tuple,
    ⟨returned,returnedFound,returnedForm⟩,inputs,roots,flagScheme,literalValue,fFlag⟩

end Tests.SourceCoreGeneralizedBodyExpression
