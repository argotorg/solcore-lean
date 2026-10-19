import Solcore.Test.SourceCoreGeneralizedIdentitySource
import Solcore.Test.SourceCoreMixedImperativeSourceState
import Solcore.Test.SourceCoreSelectedInterleavedLocalFixture

/-! Exact original occurrences for nested lexical blocks and conditional
identity calls. The observer below validates every relationship in the graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode CallShape)

structure StatementAt (source : TypedSource) (form : StatementForm) where
  node : StatementNode
  found : source.lookupStatement? node.id = some node
  formEq : node.form = form

structure BooleanAt (source : TypedSource) (value : Bool) where
  node : ExpressionNode
  name : String
  found : source.lookupExpression? node.id = some node
  form : node.form = .reference name (.builtinBoolean value)
  requirements : node.requirements = []
  coercions : node.coercions = []

structure Shape (source : TypedSource) where
  flag : TypedBinder
  f : IdentityShape source
  first : TypedBinder
  g : IdentityShape source
  chosen : TypedBinder
  eleven : WordNode source
  seventeen : WordNode source
  falseNode : BooleanAt source false
  condition : Tests.SourceCoreNamedBranch.Read source flag .bool
  firstRead : Tests.SourceCoreNamedBranch.Read source first .word
  chosenRead : Tests.SourceCoreNamedBranch.Read source chosen .word
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  firstCall : CallShape source f.binder eleven.node.id .word
  chosenCall : CallShape source g.binder firstRead.node.id .word
  thenCall : CallShape source f.binder chosenRead.node.id .word
  elseCall : CallShape source f.binder falseNode.node.id .bool
  finalWordCall : CallShape source f.binder seventeen.node.id .word
  finalBoolCall : CallShape source f.binder flagRead.node.id .bool
  fLet : StatementAt source (.letDecl f.binder (some f.lambda.id))
  firstLet : StatementAt source (.letDecl first (some firstCall.node.id))
  gLet : StatementAt source (.letDecl g.binder (some g.lambda.id))
  chosenLet : StatementAt source (.letDecl chosen (some chosenCall.node.id))
  thenDiscard : StatementAt source (.expression thenCall.node.id true)
  elseDiscard : StatementAt source (.expression elseCall.node.id true)
  branch : StatementAt source (.ifThen condition.node.id
    [gLet.node.id, chosenLet.node.id, thenDiscard.node.id] (some [elseDiscard.node.id]))
  block : StatementAt source (.block [firstLet.node.id, branch.node.id])
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [finalWordCall.node.id, finalBoolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement fLet.node.id,.statement block.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  firstScheme : first.scheme = .mono .word
  chosenScheme : chosen.scheme = .mono .word
  elevenValue : eleven.resolution.rawValue = 11
  seventeenValue : seventeen.resolution.rawValue = 17
  fFlag : f.binder.id ≠ flag.id
  firstF : first.id ≠ f.binder.id
  firstFlag : first.id ≠ flag.id
  gFirst : g.binder.id ≠ first.id
  gF : g.binder.id ≠ f.binder.id
  gFlag : g.binder.id ≠ flag.id
  chosenG : chosen.id ≠ g.binder.id
  chosenFirst : chosen.id ≠ first.id
  chosenF : chosen.id ≠ f.binder.id
  chosenFlag : chosen.id ≠ flag.id

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def statementAt (source : TypedSource) (node : StatementNode) (form : StatementForm) :
    IO (StatementAt source form) := do
  let ⟨found⟩ ← observed (source.lookupStatement? node.id = some node) "imperative statement identity"
  let ⟨formEq⟩ ← observed (node.form = form) "imperative original statement form"
  return ⟨node,found,formEq⟩

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

private def wordNode (source : TypedSource) (node : ExpressionNode) : IO (WordNode source) := do
  let .integerLiteral literal resolution := node.form | throw (IO.userError "imperative Word literal")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "Word identity"
  let ⟨form⟩ ← observed (node.form = .integerLiteral literal resolution) "Word form"
  let ⟨target⟩ ← observed (resolution.targetType = .word) "Word target"
  let ⟨requirements⟩ ← observed (node.requirements = [resolution.requirement]) "Word requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "Word coercions"
  return ⟨node,literal,resolution,found,form,target,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "imperative input")
  let .expression fRead ::.statement fReturn ::.expression fLambda ::.statement fInit ::
       .expression elevenNode ::.expression firstCallee ::.expression firstCallNode ::.statement firstInit ::
       .expression conditionNode ::.expression gRead ::.statement gReturn ::.expression gLambda ::.statement gInit ::
       .expression firstReadNode ::.expression chosenCallee ::.expression chosenCallNode ::.statement chosenInit ::
       .expression chosenReadNode ::.expression thenCallee ::.expression thenCallNode ::.statement thenStmt ::
       .expression falseExpr ::.expression elseCallee ::.expression elseCallNode ::.statement elseStmt ::
       .statement branchNode ::.statement blockNode ::
       .expression seventeenNode ::.expression finalWordCallee ::.expression finalWordNode ::
       .expression flagNode ::.expression finalBoolCallee ::.expression finalBoolNode ::
       .expression tuple ::.statement returnNode :: [] := source.nodes | throw (IO.userError "imperative original graph")
  let .letDecl fBinder _ := fInit.form | throw (IO.userError "imperative f declaration")
  let .letDecl first _ := firstInit.form | throw (IO.userError "imperative first declaration")
  let .letDecl gBinder _ := gInit.form | throw (IO.userError "imperative g declaration")
  let .letDecl chosen _ := chosenInit.form | throw (IO.userError "imperative chosen declaration")
  let f ← identity source fBinder fLambda fRead fReturn
  let g ← identity source gBinder gLambda gRead gReturn
  let eleven ← wordNode source elevenNode
  let seventeen ← wordNode source seventeenNode
  let .reference falseName (.builtinBoolean false) := falseExpr.form | throw (IO.userError "imperative false")
  let ⟨falseFound⟩ ← observed (source.lookupExpression? falseExpr.id = some falseExpr) "false identity"
  let ⟨falseForm⟩ ← observed (falseExpr.form = .reference falseName (.builtinBoolean false)) "false form"
  let ⟨falseRequirements⟩ ← observed (falseExpr.requirements = []) "false requirements"
  let ⟨falseCoercions⟩ ← observed (falseExpr.coercions = []) "false coercions"
  let falseNode : BooleanAt source false := ⟨falseExpr,falseName,falseFound,falseForm,falseRequirements,falseCoercions⟩
  let condition ← Tests.SourceCoreNamedBranch.observeRead source flag conditionNode .bool
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead source first firstReadNode .word
  let chosenRead ← Tests.SourceCoreNamedBranch.observeRead source chosen chosenReadNode .word
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let firstCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder eleven.node.id .word firstCallee firstCallNode
  let chosenCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source g.binder firstRead.node.id .word chosenCallee chosenCallNode
  let thenCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder chosenRead.node.id .word thenCallee thenCallNode
  let elseCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder falseNode.node.id .bool elseCallee elseCallNode
  let finalWordCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder seventeen.node.id .word finalWordCallee finalWordNode
  let finalBoolCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder flagRead.node.id .bool finalBoolCallee finalBoolNode
  let fLet ← statementAt source fInit (.letDecl f.binder (some f.lambda.id))
  let firstLet ← statementAt source firstInit (.letDecl first (some firstCall.node.id))
  let gLet ← statementAt source gInit (.letDecl g.binder (some g.lambda.id))
  let chosenLet ← statementAt source chosenInit (.letDecl chosen (some chosenCall.node.id))
  let thenDiscard ← statementAt source thenStmt (.expression thenCall.node.id true)
  let elseDiscard ← statementAt source elseStmt (.expression elseCall.node.id true)
  let branch ← statementAt source branchNode (.ifThen condition.node.id [gLet.node.id,chosenLet.node.id,thenDiscard.node.id] (some [elseDiscard.node.id]))
  let block ← statementAt source blockNode (.block [firstLet.node.id,branch.node.id])
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "tuple identity"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [finalWordCall.node.id,finalBoolCall.node.id]) "tuple order"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "tuple coercions"
  let returned ← statementAt source returnNode (.returnStmt (some tuple.id))
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "imperative source inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement fLet.node.id,.statement block.node.id,.statement returned.node.id]) "imperative root order"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "flag scheme"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono .word) "first scheme"
  let ⟨chosenScheme⟩ ← observed (chosen.scheme = .mono .word) "chosen scheme"
  let ⟨elevenValue⟩ ← observed (eleven.resolution.rawValue = 11) "first literal"
  let ⟨seventeenValue⟩ ← observed (seventeen.resolution.rawValue = 17) "final literal"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ flag.id) "f/flag"
  let ⟨firstF⟩ ← observed (first.id ≠ f.binder.id) "first/f"
  let ⟨firstFlag⟩ ← observed (first.id ≠ flag.id) "first/flag"
  let ⟨gFirst⟩ ← observed (g.binder.id ≠ first.id) "g/first"
  let ⟨gF⟩ ← observed (g.binder.id ≠ f.binder.id) "g/f"
  let ⟨gFlag⟩ ← observed (g.binder.id ≠ flag.id) "g/flag"
  let ⟨chosenG⟩ ← observed (chosen.id ≠ g.binder.id) "chosen/g"
  let ⟨chosenFirst⟩ ← observed (chosen.id ≠ first.id) "chosen/first"
  let ⟨chosenF⟩ ← observed (chosen.id ≠ f.binder.id) "chosen/f"
  let ⟨chosenFlag⟩ ← observed (chosen.id ≠ flag.id) "chosen/flag"
  return ⟨flag,f,first,g,chosen,eleven,seventeen,falseNode,condition,firstRead,chosenRead,flagRead,
    firstCall,chosenCall,thenCall,elseCall,finalWordCall,finalBoolCall,fLet,firstLet,gLet,chosenLet,thenDiscard,elseDiscard,
    branch,block,tuple,tupleFound,tupleForm,tupleRequirements,tupleCoercions,returned,inputs,roots,flagScheme,firstScheme,
    chosenScheme,elevenValue,seventeenValue,fFlag,firstF,firstFlag,gFirst,gF,gFlag,chosenG,chosenFirst,chosenF,chosenFlag⟩

end Tests.SourceCoreMixedImperative
