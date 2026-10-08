import Solcore.SourceSemantics.CoreLowering.ReachedNamedPrimitiveBodyFaultPaths

/-! A discard prefix and the literal singleton suffix retain one actual causal
leaf. Source/native prefix receipts name the same reached heap and body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedSequentialBodyFaultPaths
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ReachedExpressionFaultOrigins
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)
open NamedInvocationFaultPostContracts
open ReachedNamedPrimitiveBodyFaultPaths (SingletonAt BodyPath)

def suffix (function : Dynamic.Closure) (statement : StatementId) : Dynamic.Closure :=
  {function with body := [statement]}

/-- Both actual compiler children and the exact main emission are static receipts. -/
structure SequentialAt (values : SourceCoreCompatibleValues.Context)
    (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (statement : StatementId) (node : StatementNode)
    (expression : ExpressionId) (expressionNode : ExpressionNode) (fuel : Nat)
    (last : StatementId) (lastNode : StatementNode) (lastExpression : ExpressionId)
    (lastExpressionNode : ExpressionNode) (lastFuel : Nat) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (lowered lastLowered : SourceCoreBasic.LoweredExpr)
    (body : Expr) (fellThrough escaped : Word) : Prop where
  statements : function.body = [statement, last]
  found : function.source.lookupStatement? statement = some node
  form : node.form = .expression expression true
  expressionFound : function.source.lookupExpression? expression = some expressionNode
  expressionTyped : ExpressionHasType function.source context expression expressionNode.type
  tree : CompatibleExpressionBuiltins.Tree fuel values function.source context solved reasonAt scope expression lowered
  final : SingletonAt values (suffix function last) context scope last lastNode lastExpression lastExpressionNode
    lastFuel solved reasonAt lastLowered
    (CompatibleStatements.finish lastLowered.type (LocalLoop.returnValue lastLowered.type lastLowered.expression)
      fellThrough escaped) fellThrough escaped
  emitted : body = CompatibleStatements.finish lastLowered.type
    (LocalSequence.discard (LocalLoop.controlType lastLowered.type) lowered.expression
      (LocalLoop.returnValue lastLowered.type lastLowered.expression)) fellThrough escaped

/-- The successful Source prefix and the singleton leaf share their actual middle heap. -/
inductive SequentialPath : {after : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
    PrimitiveOrigin after reason token → Program → Dynamic.Closure → SourceSemantics.Context →
    Dynamic.Environment → Dynamic.Heap → Prop where
  | head {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
      {statement last : StatementId} {node : StatementNode} {expression : ExpressionId}
      (body : function.body = [statement, last]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .expression expression true)
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence
        function.source environment before expression) :
      SequentialPath origin program function context environment before
  | tail {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before middle : Dynamic.Heap}
      {statement last : StatementId} {node : StatementNode} {expression lastExpression : ExpressionId}
      {value : Dynamic.Value}
      (body : function.body = [statement, last]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .expression expression true)
      (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before expression value middle)
      (child : BodyPath origin program (suffix function last) context environment middle lastExpression) :
      SequentialPath origin program function context environment before

theorem SequentialPath.source_fault {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (path : SequentialPath origin program function context environment before) :
    Dynamic.FunctionStatementsFault program context function.evidence function.source
      environment before function.body context reason after := by
  cases path with
  | head body contains form failed _ =>
    rw [body]
    exact .head (.expression contains form failed)
  | tail body contains form first child =>
    rw [body]
    exact .tail (.expression contains form first) child.source_fault

/-- The exact child evaluations retain native sequencing beside the real Source path. -/
def model_bodyPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) : BodyFaultPost :=
  fun program function context environment before actual initialStore body reason after token mapping world bodyStore =>
    ∃ origin : PrimitiveOrigin after reason token,
      ∃ scope statement node expression expressionNode fuel last lastNode lastExpression lastExpressionNode lastFuel
        solved reasonAt lowered lastLowered sourceBody fellThrough escaped ξ,
        SequentialAt (.initial checked) function context scope statement node expression expressionNode fuel
          last lastNode lastExpression lastExpressionNode lastFuel solved reasonAt lowered lastLowered
          sourceBody fellThrough escaped ∧
        body = sourceBody.rename ξ ∧
        NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin ∧
        ((Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after ∧
          ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence
            function.source environment before expression ∧
          Evaluates actual initialStore (lowered.expression.rename ξ)
            (.inLeft lowered.type (.word token)) bodyStore) ∨
          ∃ middle sourceValue payload middleStore initialMap initialWorld middleMap middleWorld,
            Dynamic.ExpressionEvaluates program context function.evidence function.source environment before expression sourceValue middle ∧
            BodyPath origin program (suffix function last) context environment middle lastExpression ∧
            Evaluates actual initialStore (lowered.expression.rename ξ) (.inRight .word payload) middleStore ∧
            CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore ∧
            LocationMap.Extends initialMap middleMap ∧ WorldExtends initialWorld middleWorld ∧
            AdministrativePreserved initialMap initialStore middleMap middleStore ∧ Dynamic.HeapMetadataExtend before middle ∧
            LocationMap.Extends middleMap mapping ∧ WorldExtends middleWorld world ∧
            AdministrativePreserved middleMap middleStore mapping bodyStore ∧ Dynamic.HeapMetadataExtend middle after ∧
            Evaluates (payload :: actual) middleStore
              (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ))
              (.inLeft lastLowered.type (.word token)) bodyStore) ∧
        Evaluates actual initialStore body (.inLeft lastLowered.type (.word token)) bodyStore

section Constructors
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {scope : SourceCoreLocalCell.Scope} {statement last : StatementId} {node lastNode : StatementNode}
  {expression lastExpression : ExpressionId} {expressionNode lastExpressionNode : ExpressionNode}
  {fuel lastFuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {lowered lastLowered : SourceCoreBasic.LoweredExpr} {sourceBody : Expr} {fellThrough escaped : Word}
  {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming}
  {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
  (sequential : SequentialAt (.initial checked) function context scope statement node expression expressionNode fuel
    last lastNode lastExpression lastExpressionNode lastFuel solved reasonAt lowered lastLowered sourceBody fellThrough escaped)

include sequential in
theorem model_bodyPost.of_head
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before expression reason after)
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment before expression reason after token mapping world bodyStore)
    (child : Evaluates actual initialStore (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) bodyStore)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft lastLowered.type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore
      (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  exact ⟨origin, scope, statement, node, expression, expressionNode, fuel, last, lastNode,
    lastExpression, lastExpressionNode, lastFuel, solved, reasonAt, lowered, lastLowered, sourceBody,
    fellThrough, escaped, ξ, sequential, rfl,
    transported, model, Or.inl ⟨failed, path, child⟩, completed⟩

include sequential in
theorem model_bodyPost.of_tail {middle : Dynamic.Heap} {sourceValue : Dynamic.Value} {payload : Value}
    {middleStore : Store} {initialMap middleMap : LocationMap} {initialWorld middleWorld : StoreTyping}
    (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before expression sourceValue middle)
    (firstNative : Evaluates actual initialStore (lowered.expression.rename ξ) (.inRight .word payload) middleStore)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
    (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore)
    (firstMetadata : Dynamic.HeapMetadataExtend before middle)
    (maps : LocationMap.Extends middleMap mapping) (worlds : WorldExtends middleWorld world)
    (frame : AdministrativePreserved middleMap middleStore mapping bodyStore)
    (metadata : Dynamic.HeapMetadataExtend middle after)
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment middle lastExpression reason after)
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment middle lastExpression reason after token mapping world bodyStore)
    (child : Evaluates (payload :: actual) middleStore
      (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ))
      (.inLeft lastLowered.type (.word token)) bodyStore)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft lastLowered.type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore
      (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  have lastPath : BodyPath origin program (suffix function last) context environment middle lastExpression := by
    rcases sequential.final.form with tail | returning
    · exact .tail rfl (lookupStatement?_sound sequential.final.found) tail failed path
    · exact .returning rfl (lookupStatement?_sound sequential.final.found) returning failed path
  exact ⟨origin, scope, statement, node, expression, expressionNode, fuel, last, lastNode,
    lastExpression, lastExpressionNode, lastFuel, solved, reasonAt, lowered, lastLowered, sourceBody,
    fellThrough, escaped, ξ, sequential, rfl,
    transported, model, Or.inr ⟨middle, sourceValue, payload, middleStore, initialMap, initialWorld,
      middleMap, middleWorld, first, lastPath, firstNative, middleHeaps, firstMaps, firstWorlds, firstFrame,
      firstMetadata, maps, worlds, frame, metadata, child⟩, completed⟩
end Constructors

/-- Finite projection exposes the same coupled leaf; it performs no Source fault traversal. -/
theorem model_bodyPost.source_path {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {actual : Environment} {initialStore bodyStore : Store} {body : Expr}
    {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
    (post : model_bodyPost checked functions registry program function context environment before actual initialStore
      body reason after token mapping world bodyStore) :
    ∃ origin : PrimitiveOrigin after reason token,
      SequentialPath origin program function context environment before ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin := by
  obtain ⟨origin, scope, statement, node, expression, expressionNode, fuel, last, lastNode,
    lastExpression, lastExpressionNode, lastFuel, solved, reasonAt, lowered, lastLowered, sourceBody,
    fellThrough, escaped, ξ, sequential, _sameBody, transported, model, route, _completed⟩ := post
  refine ⟨origin, ?_, transported, model⟩
  rcases route with ⟨failed, path, _child⟩ | tail
  · exact .head sequential.statements (lookupStatement?_sound sequential.found) sequential.form failed path
  · obtain ⟨middle, sourceValue, payload, middleStore, initialMap, initialWorld, middleMap, middleWorld,
      first, path, _firstNative, _middleHeaps, _firstMaps, _firstWorlds, _firstFrame, _firstMetadata,
      _maps, _worlds, _frame, _metadata, _child⟩ := tail
    exact .tail sequential.statements (lookupStatement?_sound sequential.found) sequential.form first path

end Solcore.SourceSemantics.CoreLowering.ReachedNamedSequentialBodyFaultPaths
