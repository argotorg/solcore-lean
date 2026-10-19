import Solcore.Test.SourceCoreMixedImperativeSourceSteps

/-! The complete original mapping transaction and for header occurrences. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode CallShape)
open Tests.SourceCoreMixedImperative (StatementAt BooleanAt)

def mappingType : TypeSystem.Ty := .mapping .word .word
structure Shape (source : TypedSource) where
  flag : TypedBinder
  table : TypedBinder
  active : TypedBinder
  f : IdentityShape source
  key : WordNode source
  initialKey : WordNode source
  postKey : WordNode source
  readKey : WordNode source
  ten : WordNode source
  one : WordNode source
  two : WordNode source
  falseNode : BooleanAt source false
  inputRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  guardRead : Tests.SourceCoreNamedBranch.Read source active .bool
  tableRead : Tests.SourceCoreNamedBranch.Read source table mappingType
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  wordCall : CallShape source f.binder ten.node.id .word
  keyCall : CallShape source f.binder readKey.node.id .word
  boolCall : CallShape source f.binder flagRead.node.id .bool
  fLet : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tableLet : StatementAt source (.letDecl table none)
  activeLet : StatementAt source (.letDecl active (some inputRead.node.id))
  tableWrite : StatementAt source (.assignValue ⟨⟨table.id,[.index key.node.id],.word⟩,[]⟩ .equal wordCall.node.id)
  activeWrite : StatementAt source (.assignValue ⟨⟨active.id,[],.bool⟩,[]⟩ .equal falseNode.node.id)
  continuing : StatementAt source .continueStmt
  loop : StatementAt source (.forLoop
    [.assignValue ⟨⟨table.id,[.index initialKey.node.id],.word⟩,[]⟩ .add one.node.id]
    guardRead.node.id [.assignValue ⟨⟨table.id,[.index postKey.node.id],.word⟩,[]⟩ .add two.node.id]
    [activeWrite.node.id,continuing.node.id])
  lookup : ExpressionNode
  lookupFound : source.lookupExpression? lookup.id = some lookup
  lookupForm : lookup.form = .index tableRead.node.id keyCall.node.id
  lookupRequirements : lookup.requirements = []
  lookupCoercions : lookup.coercions = []
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [lookup.id,boolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement fLet.node.id,.statement tableLet.node.id,
    .statement activeLet.node.id,.statement tableWrite.node.id,.statement loop.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  tableScheme : table.scheme = .mono mappingType
  activeScheme : active.scheme = .mono .bool
  keyValue : key.resolution.rawValue = 3
  initialKeyValue : initialKey.resolution.rawValue = 3
  postKeyValue : postKey.resolution.rawValue = 3
  readKeyValue : readKey.resolution.rawValue = 3
  tenValue : ten.resolution.rawValue = 10
  oneValue : one.resolution.rawValue = 1
  twoValue : two.resolution.rawValue = 2
  fFlag : f.binder.id ≠ flag.id
  tableFlag : table.id ≠ flag.id
  tableF : table.id ≠ f.binder.id
  activeFlag : active.id ≠ flag.id
  activeF : active.id ≠ f.binder.id
  activeTable : active.id ≠ table.id

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

private def booleanNode (source : TypedSource) (node : ExpressionNode) (value : Bool) :
    IO (BooleanAt source value) := do
  let .reference name _ := node.form | throw (IO.userError "loop Boolean form")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "loop Boolean identity"
  let ⟨form⟩ ← observed (node.form = .reference name (.builtinBoolean value)) "loop Boolean value"
  let ⟨requirements⟩ ← observed (node.requirements = []) "loop Boolean requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "loop Boolean coercions"
  return ⟨node,name,found,form,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "mapping input")
  let [.expression fRead,.statement fReturn,.expression fLambda,.statement fInit,
      .statement tableInit,.expression inputNode,.statement activeInit,
      .expression keyExpr,.expression tenExpr,.expression wordCallee,.expression wordCallNode,
      .statement tableWriteNode,.expression initialKeyExpr,.expression oneExpr,.expression guardNode,
      .expression falseExpr,.statement activeWriteNode,.statement continuingNode,
      .expression postKeyExpr,.expression twoExpr,.statement loopNode,
      .expression tableNode,.expression readKeyExpr,.expression keyCallee,.expression keyCallNode,.expression lookup,.expression flagNode,.expression boolCallee,.expression boolCallNode,
      .expression tuple,.statement returnNode] := source.nodes
    | throw (IO.userError "mapping original complete graph")
  let .letDecl fBinder _ := fInit.form | throw (IO.userError "mapping f declaration")
  let .letDecl table _ := tableInit.form | throw (IO.userError "mapping table declaration")
  let .letDecl active _ := activeInit.form | throw (IO.userError "mapping active declaration")
  let f ← identity source fBinder fLambda fRead fReturn
  let key ← wordNode source keyExpr
  let initialKey ← wordNode source initialKeyExpr
  let postKey ← wordNode source postKeyExpr
  let readKey ← wordNode source readKeyExpr
  let ten ← wordNode source tenExpr
  let one ← wordNode source oneExpr
  let two ← wordNode source twoExpr
  let falseNode ← booleanNode source falseExpr false
  let inputRead ← Tests.SourceCoreNamedBranch.observeRead source flag inputNode .bool
  let guardRead ← Tests.SourceCoreNamedBranch.observeRead source active guardNode .bool
  let tableRead ← Tests.SourceCoreNamedBranch.observeRead source table tableNode mappingType
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let wordCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder ten.node.id .word wordCallee wordCallNode
  let keyCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder readKey.node.id .word keyCallee keyCallNode
  let boolCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder flagRead.node.id .bool boolCallee boolCallNode
  let fLet ← statementAt source fInit (.letDecl f.binder (some f.lambda.id))
  let tableLet ← statementAt source tableInit (.letDecl table none)
  let activeLet ← statementAt source activeInit (.letDecl active (some inputRead.node.id))
  let tableWrite ← statementAt source tableWriteNode (.assignValue ⟨⟨table.id,[.index key.node.id],.word⟩,[]⟩ .equal wordCall.node.id)
  let activeWrite ← statementAt source activeWriteNode (.assignValue ⟨⟨active.id,[],.bool⟩,[]⟩ .equal falseNode.node.id)
  let continuing ← statementAt source continuingNode .continueStmt
  let loop ← statementAt source loopNode (.forLoop
    [.assignValue ⟨⟨table.id,[.index initialKey.node.id],.word⟩,[]⟩ .add one.node.id]
    guardRead.node.id [.assignValue ⟨⟨table.id,[.index postKey.node.id],.word⟩,[]⟩ .add two.node.id]
    [activeWrite.node.id,continuing.node.id])
  let returned ← statementAt source returnNode (.returnStmt (some tuple.id))
  let ⟨lookupFound⟩ ← observed (source.lookupExpression? lookup.id = some lookup) "mapping read identity"
  let ⟨lookupForm⟩ ← observed (lookup.form = .index tableRead.node.id keyCall.node.id) "mapping read base-before-key"
  let ⟨lookupRequirements⟩ ← observed (lookup.requirements = []) "mapping read requirements"
  let ⟨lookupCoercions⟩ ← observed (lookup.coercions = []) "mapping read coercions"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "mapping tupleFound"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [lookup.id,boolCall.node.id]) "mapping tupleForm"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "mapping tupleRequirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "mapping tupleCoercions"
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "mapping inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement fLet.node.id,.statement tableLet.node.id,.statement activeLet.node.id,.statement tableWrite.node.id,.statement loop.node.id,.statement returned.node.id]) "mapping roots"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "mapping flagScheme"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "mapping tableScheme"
  let ⟨activeScheme⟩ ← observed (active.scheme = .mono .bool) "mapping activeScheme"
  let ⟨keyValue⟩ ← observed (key.resolution.rawValue = 3) "mapping keyValue"
  let ⟨initialKeyValue⟩ ← observed (initialKey.resolution.rawValue = 3) "mapping initialKeyValue"
  let ⟨postKeyValue⟩ ← observed (postKey.resolution.rawValue = 3) "mapping postKeyValue"
  let ⟨readKeyValue⟩ ← observed (readKey.resolution.rawValue = 3) "mapping read key"
  let ⟨tenValue⟩ ← observed (ten.resolution.rawValue = 10) "mapping tenValue"
  let ⟨oneValue⟩ ← observed (one.resolution.rawValue = 1) "mapping oneValue"
  let ⟨twoValue⟩ ← observed (two.resolution.rawValue = 2) "mapping twoValue"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ flag.id) "mapping fFlag"
  let ⟨tableFlag⟩ ← observed (table.id ≠ flag.id) "mapping tableFlag"
  let ⟨tableF⟩ ← observed (table.id ≠ f.binder.id) "mapping tableF"
  let ⟨activeFlag⟩ ← observed (active.id ≠ flag.id) "mapping activeFlag"
  let ⟨activeF⟩ ← observed (active.id ≠ f.binder.id) "mapping activeF"
  let ⟨activeTable⟩ ← observed (active.id ≠ table.id) "mapping activeTable"
  return {
    flag := flag
    table := table
    active := active
    f := f
    key := key
    initialKey := initialKey
    postKey := postKey
    readKey := readKey
    ten := ten
    one := one
    two := two
    falseNode := falseNode
    inputRead := inputRead
    guardRead := guardRead
    tableRead := tableRead
    flagRead := flagRead
    wordCall := wordCall
    keyCall := keyCall
    boolCall := boolCall
    fLet := fLet
    tableLet := tableLet
    activeLet := activeLet
    tableWrite := tableWrite
    activeWrite := activeWrite
    continuing := continuing
    loop := loop
    lookup := lookup
    lookupFound := lookupFound
    lookupForm := lookupForm
    lookupRequirements := lookupRequirements
    lookupCoercions := lookupCoercions
    tuple := tuple
    tupleFound := tupleFound
    tupleForm := tupleForm
    tupleRequirements := tupleRequirements
    tupleCoercions := tupleCoercions
    returned := returned
    inputs := inputs
    roots := roots
    flagScheme := flagScheme
    tableScheme := tableScheme
    activeScheme := activeScheme
    keyValue := keyValue
    initialKeyValue := initialKeyValue
    postKeyValue := postKeyValue
    readKeyValue := readKeyValue
    tenValue := tenValue
    oneValue := oneValue
    twoValue := twoValue
    fFlag := fFlag
    tableFlag := tableFlag
    tableF := tableF
    activeFlag := activeFlag
    activeF := activeF
    activeTable := activeTable
  }

end Tests.SourceCoreMixedIndexRead
