import Solcore.SourceSemantics.CoreLowering.NamedInvocationFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.ReachedBuiltinExpressionFaultPaths
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinCertificates

/-! A singleton function body adds one genuine Source edge to the actual
builtin expression path. Its native child and body completions keep the same
token and body store; caller restoration remains a separate receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedPrimitiveBodyFaultPaths
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ReachedExpressionFaultOrigins
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)
open NamedInvocationFaultPostContracts

/-- These are the actual static singleton Source and emitted builtin fields. -/
structure SingletonAt (values : SourceCoreCompatibleValues.Context)
    (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (statement : StatementId) (node : StatementNode)
    (expression : ExpressionId) (expressionNode : ExpressionNode)
    (fuel : Nat) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (lowered : SourceCoreBasic.LoweredExpr) (body : Expr) (fellThrough escaped : Word) : Prop where
  statements : function.body = [statement]
  found : function.source.lookupStatement? statement = some node
  form : node.form = .expression expression false ∨ node.form = .returnStmt (some expression)
  expressionFound : function.source.lookupExpression? expression = some expressionNode
  expressionTyped : ExpressionHasType function.source context expression expressionNode.type
  resultType : expressionNode.type = function.resultType
  tree : CompatibleExpressionBuiltins.Tree fuel values function.source context solved reasonAt scope expression lowered
  projection : values.checked.catalog.project function.resultType = .ok lowered.type
  emitted : body = CompatibleStatements.finish lowered.type
    (LocalLoop.returnValue lowered.type lowered.expression) fellThrough escaped

/-- The leaf remains indexed by its actual final Source heap and reason. -/
inductive BodyPath : {after : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
    PrimitiveOrigin after reason token → Program → Dynamic.Closure → SourceSemantics.Context →
    Dynamic.Environment → Dynamic.Heap → ExpressionId → Prop where
  | tail {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
      {statement : StatementId} {node : StatementNode} {expression : ExpressionId}
      (body : function.body = [statement]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .expression expression false)
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence
        function.source environment before expression) :
      BodyPath origin program function context environment before expression
  | returning {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
      {statement : StatementId} {node : StatementNode} {expression : ExpressionId}
      (body : function.body = [statement]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .returnStmt (some expression))
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence
        function.source environment before expression) :
      BodyPath origin program function context environment before expression

/-- This projection constructs the real function fault directly from its child. -/
theorem BodyPath.source_fault {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap} {expression : ExpressionId}
    (path : BodyPath origin program function context environment before expression) :
    Dynamic.FunctionStatementsFault program context function.evidence function.source
      environment before function.body context reason after := by
  cases path with
  | tail body contains form failed _ =>
    rw [body]
    exact .tailExpression contains form failed
  | returning body contains form failed _ =>
    rw [body]
    exact .singleton (.returnValue contains form failed)

/-- Static emission and both actual evaluations associate the selected Source
child with the same body completion. The original model is fixed throughout. -/
def model_bodyPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) : BodyFaultPost :=
  fun program function context environment before actual initialStore body reason after token mapping world bodyStore =>
    ∃ origin : PrimitiveOrigin after reason token,
      ∃ scope statement node expression expressionNode fuel solved reasonAt lowered sourceBody fellThrough escaped ξ,
        SingletonAt (.initial checked) function context scope statement node expression expressionNode fuel solved reasonAt
          lowered sourceBody fellThrough escaped ∧
        body = sourceBody.rename ξ ∧
        BodyPath origin program function context environment before expression ∧
        NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin ∧
        Evaluates actual initialStore (lowered.expression.rename ξ)
          (.inLeft lowered.type (.word token)) bodyStore ∧
        Evaluates actual initialStore body (.inLeft lowered.type (.word token)) bodyStore

/-- The same actual child packet supplies the singleton path and native link. -/
theorem model_bodyPost.of_child {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode}
    {expression : ExpressionId} {expressionNode : ExpressionNode} {fuel : Nat}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {sourceBody : Expr} {fellThrough escaped : Word}
    {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming}
    {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
    (singleton : SingletonAt (.initial checked) function context scope statement node expression expressionNode
      fuel solved reasonAt lowered sourceBody fellThrough escaped)
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment before expression reason after token mapping world bodyStore)
    (child : Evaluates actual initialStore (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) bodyStore)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft lowered.type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore
      (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  refine ⟨origin, scope, statement, node, expression, expressionNode, fuel, solved, reasonAt,
    lowered, sourceBody, fellThrough, escaped, ξ, singleton, rfl, ?_, transported, model, child, completed⟩
  rcases singleton.form with tail | returning
  · exact .tail singleton.statements (lookupStatement?_sound singleton.found) tail failed path
  · exact .returning singleton.statements (lookupStatement?_sound singleton.found) returning failed path

end Solcore.SourceSemantics.CoreLowering.ReachedNamedPrimitiveBodyFaultPaths
