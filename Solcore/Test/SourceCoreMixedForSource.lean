import Solcore.Test.SourceCoreMixedImperativeSourceSteps

/-! Every field is checked against the unchanged original loop body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedFor
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode CallShape)
open Tests.SourceCoreMixedImperative (StatementAt BooleanAt)

structure Shape (source : TypedSource) where
  flag : TypedBinder
  active : TypedBinder
  first : TypedBinder
  counter : TypedBinder
  f : IdentityShape source
  zero : WordNode source
  one : WordNode source
  trueNode : BooleanAt source true
  firstFalse : BooleanAt source false
  inputRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  guardRead : Tests.SourceCoreNamedBranch.Read source active .bool
  phaseRead : Tests.SourceCoreNamedBranch.Read source first .bool
  counterRead : Tests.SourceCoreNamedBranch.Read source counter .word
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  wordCall : CallShape source f.binder counterRead.node.id .word
  boolCall : CallShape source f.binder flagRead.node.id .bool
  fLet : StatementAt source (.letDecl f.binder (some f.lambda.id))
  firstLet : StatementAt source (.letDecl first (some trueNode.node.id))
  counterLet : StatementAt source (.letDecl counter (some zero.node.id))
  firstWrite : StatementAt source (.assignValue ⟨⟨first.id,[],.bool⟩,[]⟩ .equal firstFalse.node.id)
  continuing : StatementAt source .continueStmt
  breaking : StatementAt source .breakStmt
  branch : StatementAt source (.ifThen phaseRead.node.id [firstWrite.node.id,continuing.node.id] (some [breaking.node.id]))
  loop : StatementAt source (.forLoop [.letDecl active (some inputRead.node.id)] guardRead.node.id
    [.assignValue ⟨⟨counter.id,[],.word⟩,[]⟩ .add one.node.id] [branch.node.id])
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [wordCall.node.id,boolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement fLet.node.id,
    .statement firstLet.node.id,.statement counterLet.node.id,.statement loop.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  activeScheme : active.scheme = .mono .bool
  firstScheme : first.scheme = .mono .bool
  counterScheme : counter.scheme = .mono .word
  zeroValue : zero.resolution.rawValue = 0
  oneValue : one.resolution.rawValue = 1
  fFlag : f.binder.id ≠ flag.id
  activeFlag : active.id ≠ flag.id
  activeF : active.id ≠ f.binder.id
  firstFlag : first.id ≠ flag.id
  firstF : first.id ≠ f.binder.id
  firstActive : first.id ≠ active.id
  counterFlag : counter.id ≠ flag.id
  counterF : counter.id ≠ f.binder.id
  counterActive : counter.id ≠ active.id
  counterFirst : counter.id ≠ first.id

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
  let [flag] := source.inputs | throw (IO.userError "loop input")
  let .expression fRead :: .statement fReturn :: .expression fLambda :: .statement fInit ::
      .expression trueExpr :: .statement firstInit :: .expression zeroExpr :: .statement counterInit ::
      .expression inputNode :: .expression guardNode :: .expression phaseNode ::
      .expression firstFalseExpr :: .statement firstWriteNode :: .statement continuingNode ::
      .statement breakingNode :: .statement branchNode :: .expression oneExpr :: .statement loopNode ::
      .expression counterNode :: .expression wordCallee :: .expression wordCallNode ::
      .expression flagNode :: .expression boolCallee :: .expression boolCallNode ::
      .expression tuple :: .statement returnNode :: [] := source.nodes
    | throw (IO.userError "for original graph")
  let .letDecl fBinder _ := fInit.form | throw (IO.userError "loop f declaration")
  let .forLoop [.letDecl active _] _ _ _ := loopNode.form | throw (IO.userError "for active header declaration")
  let .letDecl first _ := firstInit.form | throw (IO.userError "loop first declaration")
  let .letDecl counter _ := counterInit.form | throw (IO.userError "loop counter declaration")
  let f ← identity source fBinder fLambda fRead fReturn
  let zero ← wordNode source zeroExpr
  let one ← wordNode source oneExpr
  let trueNode ← booleanNode source trueExpr true
  let firstFalse ← booleanNode source firstFalseExpr false
  let inputRead ← Tests.SourceCoreNamedBranch.observeRead source flag inputNode .bool
  let guardRead ← Tests.SourceCoreNamedBranch.observeRead source active guardNode .bool
  let phaseRead ← Tests.SourceCoreNamedBranch.observeRead source first phaseNode .bool
  let counterRead ← Tests.SourceCoreNamedBranch.observeRead source counter counterNode .word
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let wordCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder counterRead.node.id .word wordCallee wordCallNode
  let boolCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder flagRead.node.id .bool boolCallee boolCallNode
  let fLet ← statementAt source fInit (.letDecl f.binder (some f.lambda.id))
  let firstLet ← statementAt source firstInit (.letDecl first (some trueNode.node.id))
  let counterLet ← statementAt source counterInit (.letDecl counter (some zero.node.id))
  let firstWrite ← statementAt source firstWriteNode (.assignValue ⟨⟨first.id,[],.bool⟩,[]⟩ .equal firstFalse.node.id)
  let continuing ← statementAt source continuingNode .continueStmt
  let breaking ← statementAt source breakingNode .breakStmt
  let branch ← statementAt source branchNode (.ifThen phaseRead.node.id [firstWrite.node.id,continuing.node.id] (some [breaking.node.id]))
  let loop ← statementAt source loopNode (.forLoop [.letDecl active (some inputRead.node.id)] guardRead.node.id
    [.assignValue ⟨⟨counter.id,[],.word⟩,[]⟩ .add one.node.id] [branch.node.id])
  let returned ← statementAt source returnNode (.returnStmt (some tuple.id))
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "loop tupleFound"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [wordCall.node.id,boolCall.node.id]) "loop tupleForm"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "loop tupleRequirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "loop tupleCoercions"
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "loop inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement fLet.node.id,.statement firstLet.node.id,.statement counterLet.node.id,.statement loop.node.id,.statement returned.node.id]) "loop roots"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "loop flagScheme"
  let ⟨activeScheme⟩ ← observed (active.scheme = .mono .bool) "loop activeScheme"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono .bool) "loop firstScheme"
  let ⟨counterScheme⟩ ← observed (counter.scheme = .mono .word) "loop counterScheme"
  let ⟨zeroValue⟩ ← observed (zero.resolution.rawValue = 0) "loop zeroValue"
  let ⟨oneValue⟩ ← observed (one.resolution.rawValue = 1) "loop oneValue"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ flag.id) "loop fFlag"
  let ⟨activeFlag⟩ ← observed (active.id ≠ flag.id) "loop activeFlag"
  let ⟨activeF⟩ ← observed (active.id ≠ f.binder.id) "loop activeF"
  let ⟨firstFlag⟩ ← observed (first.id ≠ flag.id) "loop firstFlag"
  let ⟨firstF⟩ ← observed (first.id ≠ f.binder.id) "loop firstF"
  let ⟨firstActive⟩ ← observed (first.id ≠ active.id) "loop firstActive"
  let ⟨counterFlag⟩ ← observed (counter.id ≠ flag.id) "loop counterFlag"
  let ⟨counterF⟩ ← observed (counter.id ≠ f.binder.id) "loop counterF"
  let ⟨counterActive⟩ ← observed (counter.id ≠ active.id) "loop counterActive"
  let ⟨counterFirst⟩ ← observed (counter.id ≠ first.id) "loop counterFirst"
  return {
    flag := flag
    active := active
    first := first
    counter := counter
    f := f
    zero := zero
    one := one
    trueNode := trueNode
    firstFalse := firstFalse
    inputRead := inputRead
    guardRead := guardRead
    phaseRead := phaseRead
    counterRead := counterRead
    flagRead := flagRead
    wordCall := wordCall
    boolCall := boolCall
    fLet := fLet
    firstLet := firstLet
    counterLet := counterLet
    firstWrite := firstWrite
    continuing := continuing
    breaking := breaking
    branch := branch
    loop := loop
    tuple := tuple
    returned := returned
    tupleFound := tupleFound
    tupleForm := tupleForm
    tupleRequirements := tupleRequirements
    tupleCoercions := tupleCoercions
    inputs := inputs
    roots := roots
    flagScheme := flagScheme
    activeScheme := activeScheme
    firstScheme := firstScheme
    counterScheme := counterScheme
    zeroValue := zeroValue
    oneValue := oneValue
    fFlag := fFlag
    activeFlag := activeFlag
    activeF := activeF
    firstFlag := firstFlag
    firstF := firstF
    firstActive := firstActive
    counterFlag := counterFlag
    counterF := counterF
    counterActive := counterActive
    counterFirst := counterFirst
  }

end Tests.SourceCoreMixedFor
