import Solcore.Test.SourceCoreGeneralizedExportFixture
import Solcore.Test.SourceCoreNamedBranchSource
import Solcore.SourceSemantics.Dynamic.Evaluation

/-! Exact original factory graphs. A generalized declaration stores its
principal descriptor; returning an instance does not execute its body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read observeRead)

structure LambdaShape (source : TypedSource) where
  input : TypedBinder
  inputType : TypeSystem.Ty
  binder : TypedBinder
  parameter : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  resultType : TypeSystem.Ty
  bodyBinder : TypedBinder
  bodyChoice : bodyBinder = parameter ∨ bodyBinder = input
  initialized : StatementNode
  lambda : ExpressionNode
  bodyReturn : StatementNode
  bodyRead : Read source bodyBinder resultType
  inputs : source.inputs = [input]
  inputScheme : input.scheme = .mono inputType
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) resultType⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  parameterInputDistinct : parameter.id ≠ input.id
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl binder (some lambda.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] resultType [bodyReturn.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  bodyFound : source.lookupStatement? bodyReturn.id = some bodyReturn
  bodyForm : bodyReturn.form = .returnStmt (some bodyRead.node.id)

structure MakeShape (source : TypedSource) where
  principal : LambdaShape source
  inputType : principal.inputType = .bool
  resultType : principal.resultType = .variable principal.typeVariable
  identity : principal.bodyBinder = principal.parameter
  wordRead : Read source principal.binder (.function .word .word)
  boolRead : Read source principal.binder (.function .bool .bool)
  tuple : ExpressionNode
  returned : StatementNode
  roots : source.roots = [.statement principal.initialized.id, .statement returned.id]
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [wordRead.node.id, boolRead.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some tuple.id)

structure CaptureShape (source : TypedSource) where
  principal : LambdaShape source
  inputType : principal.inputType = .word
  resultType : principal.resultType = .word
  captured : principal.bodyBinder = principal.input
  read : Read source principal.binder (.function .bool .word)
  returned : StatementNode
  roots : source.roots = [.statement principal.initialized.id, .statement returned.id]
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some read.node.id)

structure TickShape (source : TypedSource) where
  input : TypedBinder
  read : Read source input .bool
  returned : StatementNode
  inputs : source.inputs = [input]
  inputScheme : input.scheme = .mono .bool
  roots : source.roots = [.statement returned.id]
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some read.node.id)

def observeLambda (source : TypedSource) (captured : Bool)
    (bodyValue : ExpressionNode) (bodyReturn : StatementNode)
    (lambda : ExpressionNode) (initialized : StatementNode) : IO (LambdaShape source) := do
  let [input] := source.inputs | throw (IO.userError "export factory parameter count")
  let .letDecl binder _ := initialized.form | throw (IO.userError "export factory declaration")
  let .lambda [parameter] resultType _ := lambda.form | throw (IO.userError "export factory lambda")
  let [typeVariable] := binder.scheme.quantified | throw (IO.userError "export principal quantifier")
  let inputType := if captured then TypeSystem.Ty.word else .bool
  let bodyBinder := if captured then input else parameter
  let bodyRead ← observeRead source bodyBinder bodyValue resultType
  let ⟨inputs⟩ ← observed (source.inputs = [input]) "export factory input identity"
  let ⟨inputScheme⟩ ← observed (input.scheme = .mono inputType) "export factory input type"
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) resultType⟩)
    "export exact principal scheme"
  let ⟨schemeRequirements⟩ ← observed (binder.schemeRequirements = []) "export principal requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVariable)) "export lambda parameter"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "export lambda requirements"
  let ⟨parameterInputDistinct⟩ ← observed (parameter.id ≠ input.id) "export distinct captured parameter"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "export declaration identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl binder (some lambda.id)) "export declaration initializer"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "export lambda identity"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [parameter] resultType [bodyReturn.id]) "export lambda original body"
  let ⟨lambdaRaw⟩ ← observed (lambda.rawType = binder.scheme.body) "export lambda raw type"
  let ⟨lambdaType⟩ ← observed (lambda.type = binder.scheme.body) "export lambda result type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "export initializer requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "export initializer coercions"
  let ⟨bodyFound⟩ ← observed (source.lookupStatement? bodyReturn.id = some bodyReturn) "export inner return identity"
  let ⟨bodyForm⟩ ← observed (bodyReturn.form = .returnStmt (some bodyRead.node.id)) "export inner return read"
  return ⟨input,inputType,binder,parameter,typeVariable,resultType,bodyBinder,
    by cases captured <;> simp [bodyBinder],initialized,lambda,bodyReturn,bodyRead,inputs,inputScheme,
    scheme,schemeRequirements,parameterScheme,parameterRequirements,parameterInputDistinct,initializedFound,initializedForm,
    lambdaFound,lambdaForm,lambdaRaw,lambdaType,lambdaRequirements,lambdaCoercions,bodyFound,bodyForm⟩

def observeMake (source : TypedSource) : IO (MakeShape source) := do
  let [.expression bodyValue,.statement bodyReturn,.expression lambda,.statement initialized,
       .expression wordNode,.expression boolNode,.expression tuple,.statement returned] := source.nodes
    | throw (IO.userError "make original complete graph")
  let principal ← observeLambda source false bodyValue bodyReturn lambda initialized
  let ⟨inputType⟩ ← observed (principal.inputType = .bool) "make Bool input"
  let ⟨resultType⟩ ← observed (principal.resultType = .variable principal.typeVariable) "make identity result"
  let ⟨identity⟩ ← observed (principal.bodyBinder = principal.parameter) "make identity binder"
  let wordRead ← observeRead source principal.binder wordNode (.function .word .word)
  let boolRead ← observeRead source principal.binder boolNode (.function .bool .bool)
  let ⟨roots⟩ ← observed (source.roots = [.statement principal.initialized.id,.statement returned.id]) "make original roots"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "make tuple identity"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [wordRead.node.id,boolRead.node.id]) "make ordered instance reads"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "make tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "make tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "make return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "make return tuple"
  return ⟨principal,inputType,resultType,identity,wordRead,boolRead,tuple,returned,roots,
    tupleFound,tupleForm,tupleRequirements,tupleCoercions,returnedFound,returnedForm⟩

def observeCapture (source : TypedSource) : IO (CaptureShape source) := do
  let [.expression bodyValue,.statement bodyReturn,.expression lambda,.statement initialized,
       .expression readNode,.statement returned] := source.nodes
    | throw (IO.userError "capture original complete graph")
  let principal ← observeLambda source true bodyValue bodyReturn lambda initialized
  let ⟨inputType⟩ ← observed (principal.inputType = .word) "capture Word input"
  let ⟨resultType⟩ ← observed (principal.resultType = .word) "capture Word result"
  let ⟨captured⟩ ← observed (principal.bodyBinder = principal.input) "capture original input binder"
  let read ← observeRead source principal.binder readNode (.function .bool .word)
  let ⟨roots⟩ ← observed (source.roots = [.statement principal.initialized.id,.statement returned.id]) "capture original roots"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "capture return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some read.node.id)) "capture return instance"
  return ⟨principal,inputType,resultType,captured,read,returned,roots,returnedFound,returnedForm⟩

def observeTick (source : TypedSource) : IO (TickShape source) := do
  let [input] := source.inputs | throw (IO.userError "tick input")
  let [.expression node,.statement returned] := source.nodes | throw (IO.userError "tick original complete graph")
  let read ← observeRead source input node .bool
  let ⟨inputs⟩ ← observed (source.inputs = [input]) "tick input identity"
  let ⟨inputScheme⟩ ← observed (input.scheme = .mono .bool) "tick input type"
  let ⟨roots⟩ ← observed (source.roots = [.statement returned.id]) "tick original roots"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "tick return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some read.node.id)) "tick return read"
  return ⟨input,read,returned,inputs,inputScheme,roots,returnedFound,returnedForm⟩

def LambdaShape.descriptor {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] shape.resultType [shape.bodyReturn.id]

def LambdaShape.allocatedHeap {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := shape.binder.scheme.body, value := none, generalized := some (shape.descriptor context environment)}]⟩

theorem LambdaShape.captures {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

theorem LambdaShape.initializes {source : TypedSource} (shape : LambdaShape source)
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

end Tests.SourceCoreGeneralizedExport
