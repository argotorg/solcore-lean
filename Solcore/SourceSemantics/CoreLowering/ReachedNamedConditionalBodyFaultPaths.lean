import Solcore.SourceSemantics.CoreLowering.ReachedNamedSequentialBodyFaultPaths

/-! A literal conditional with two explicit return branches keeps the actual
condition or selected branch fault, its reached heap, and the same body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedConditionalBodyFaultPaths
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ReachedExpressionFaultOrigins
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)
open NamedInvocationFaultPostContracts

/-- The exact loop compiler envelope includes its real empty suffix. -/
structure ConditionalAt (values : SourceCoreCompatibleValues.Context)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (statement : StatementId) (node : StatementNode) (condition : ExpressionId) (conditionNode : ExpressionNode)
    (conditionFuel : Nat) (branch : Bool → StatementId) (branchNode : Bool → StatementNode)
    (expression : Bool → ExpressionId) (expressionNode : Bool → ExpressionNode) (fuel : Bool → Nat)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (conditionCode : Expr) (code : Bool → Expr) (type : Ty) (body : Expr) (fellThrough escaped : Word) : Prop where
  statements : function.body = [statement]
  found : function.source.lookupStatement? statement = some node
  form : node.form = .ifThen condition [branch true] (some [branch false])
  conditionFound : function.source.lookupExpression? condition = some conditionNode
  conditionTyped : ExpressionHasType function.source context condition conditionNode.type
  conditionType : conditionNode.type = .bool
  conditionTree : CompatibleExpressionBuiltins.Tree conditionFuel values function.source context solved reasonAt scope condition ⟨.bool, conditionCode⟩
  branchFound : ∀ b, function.source.lookupStatement? (branch b) = some (branchNode b)
  branchForm : ∀ b, (branchNode b).form = .returnStmt (some (expression b))
  expressionFound : ∀ b, function.source.lookupExpression? (expression b) = some (expressionNode b)
  expressionTyped : ∀ b, ExpressionHasType function.source context (expression b) (expressionNode b).type
  resultType : ∀ b, (expressionNode b).type = function.resultType
  tree : ∀ b, CompatibleExpressionBuiltins.Tree (fuel b) values function.source context solved reasonAt scope (expression b) ⟨type, code b⟩
  projection : values.checked.catalog.project function.resultType = .ok type
  emitted : body = CompatibleStatements.finish type
    (LocalLoop.sequence type
      (LocalLoop.conditional type conditionCode (LocalLoop.returnValue type (code true)) (LocalLoop.returnValue type (code false)))
      (LocalLoop.fallthrough type)) fellThrough escaped

/-- The selected Source edge is constructed at its actual middle heap. -/
inductive ConditionalPath : {after : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
    PrimitiveOrigin after reason token → Program → Dynamic.Closure → SourceSemantics.Context →
    Dynamic.Environment → Dynamic.Heap → Prop where
  | condition {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
      {statement : StatementId} {node : StatementNode} {condition : ExpressionId} {thenStmt elseStmt : StatementId}
      (body : function.body = [statement]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .ifThen condition [thenStmt] (some [elseStmt]))
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before condition reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence function.source environment before condition) :
      ConditionalPath origin program function context environment before
  | branch {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
      {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before middle : Dynamic.Heap}
      {statement : StatementId} {node : StatementNode} {condition : ExpressionId}
      {branch : Bool → StatementId} {branchNode : Bool → StatementNode} {expression : Bool → ExpressionId}
      (boolean : Bool) (body : function.body = [statement]) (contains : ContainsStatement function.source statement node)
      (form : node.form = .ifThen condition [branch true] (some [branch false]))
      (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before condition (.bool boolean) middle)
      (branchContains : ContainsStatement function.source (branch boolean) (branchNode boolean))
      (branchForm : (branchNode boolean).form = .returnStmt (some (expression boolean)))
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment middle (expression boolean) reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence function.source environment middle (expression boolean)) :
      ConditionalPath origin program function context environment before

theorem ConditionalPath.source_fault {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    {origin : PrimitiveOrigin after reason token} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (path : ConditionalPath origin program function context environment before) :
    Dynamic.FunctionStatementsFault program context function.evidence function.source environment before function.body context reason after := by
  cases path with
  | condition body contains form failed _ =>
    rw [body]
    exact .singleton (.ifCondition contains form failed)
  | branch boolean body contains form first branchContains branchForm failed _ =>
    rw [body]
    cases boolean with
    | false => exact .singleton (.ifFalseBody contains form first (.head (.returnValue branchContains branchForm failed)))
    | true => exact .singleton (.ifTrueBody contains form first (.head (.returnValue branchContains branchForm failed)))

/-- Native route fields retain both actual evaluations and real prefix effects. -/
inductive Route {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) {after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    (origin : PrimitiveOrigin after reason token) (program : Program) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (expression : Bool → ExpressionId) (conditionCode : Expr) (code : Bool → Expr)
    (type : Ty) (actual : Environment) (initialStore bodyStore : Store) (ξ : Renaming)
    (mapping : LocationMap) (world : StoreTyping) : Prop where
  | condition
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before condition reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence function.source environment before condition)
      (evaluated : Evaluates actual initialStore (conditionCode.rename ξ) (.inLeft .bool (.word token)) bodyStore) :
      Route functions registry origin program function context environment before condition expression conditionCode code type actual initialStore bodyStore ξ mapping world
  | branch {middle : Dynamic.Heap} {middleStore : Store} {initialMap middleMap : LocationMap} {initialWorld middleWorld : StoreTyping}
      (boolean : Bool)
      (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before condition (.bool boolean) middle)
      (firstNative : Evaluates actual initialStore (conditionCode.rename ξ) (.inRight .word (.bool boolean)) middleStore)
      (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
      (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
      (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore) (firstMetadata : Dynamic.HeapMetadataExtend before middle)
      (maps : LocationMap.Extends middleMap mapping) (worlds : WorldExtends middleWorld world)
      (frame : AdministrativePreserved middleMap middleStore mapping bodyStore) (metadata : Dynamic.HeapMetadataExtend middle after)
      (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment middle (expression boolean) reason after)
      (child : ReachedBuiltinExpressionFaultPaths.ExpressionPath origin program context function.evidence function.source environment middle (expression boolean))
      (evaluated : Evaluates (.bool boolean :: actual) middleStore
        ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ)) (.inLeft type (.word token)) bodyStore) :
      Route functions registry origin program function context environment before condition expression conditionCode code type actual initialStore bodyStore ξ mapping world

/-- Literal compiler emission, selected causal route and full body evaluation stay coupled. -/
def model_bodyPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) : BodyFaultPost :=
  fun program function context environment before actual initialStore body reason after token mapping world bodyStore =>
    ∃ origin : PrimitiveOrigin after reason token,
      ∃ scope statement node condition conditionNode conditionFuel branch branchNode expression expressionNode fuel
        solved reasonAt conditionCode code type sourceBody fellThrough escaped ξ,
        ConditionalAt (.initial checked) function context scope statement node condition conditionNode conditionFuel
          branch branchNode expression expressionNode fuel solved reasonAt conditionCode code type sourceBody fellThrough escaped ∧
        body = sourceBody.rename ξ ∧
        NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin ∧
        Route functions registry origin program function context environment before condition expression conditionCode code type actual initialStore bodyStore ξ mapping world ∧
        Evaluates actual initialStore body (.inLeft type (.word token)) bodyStore

section Constructors
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode}
  {condition : ExpressionId} {conditionNode : ExpressionNode} {conditionFuel : Nat}
  {branch : Bool → StatementId} {branchNode : Bool → StatementNode} {expression : Bool → ExpressionId}
  {expressionNode : Bool → ExpressionNode} {fuel : Bool → Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {conditionCode : Expr} {code : Bool → Expr} {type : Ty}
  {sourceBody : Expr} {fellThrough escaped : Word} {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming}
  {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
  (conditional : ConditionalAt (.initial checked) function context scope statement node condition conditionNode conditionFuel
    branch branchNode expression expressionNode fuel solved reasonAt conditionCode code type sourceBody fellThrough escaped)

include conditional in
theorem model_bodyPost.of_route
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment before condition reason after token mapping world bodyStore)
    (child : Evaluates actual initialStore (conditionCode.rename ξ) (.inLeft .bool (.word token)) bodyStore)
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment before condition reason after)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  exact ⟨origin, scope, statement, node, condition, conditionNode, conditionFuel, branch, branchNode, expression,
    expressionNode, fuel, solved, reasonAt, conditionCode, code, type, sourceBody, fellThrough, escaped, ξ,
    conditional, rfl, transported, model, .condition failed path child, completed⟩

include conditional in
theorem model_bodyPost.of_branch {middle : Dynamic.Heap} {middleStore : Store}
    {initialMap middleMap : LocationMap} {initialWorld middleWorld : StoreTyping} (boolean : Bool)
    (first : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before condition (.bool boolean) middle)
    (firstNative : Evaluates actual initialStore (conditionCode.rename ξ) (.inRight .word (.bool boolean)) middleStore)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
    (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore) (firstMetadata : Dynamic.HeapMetadataExtend before middle)
    (maps : LocationMap.Extends middleMap mapping) (worlds : WorldExtends middleWorld world)
    (frame : AdministrativePreserved middleMap middleStore mapping bodyStore) (metadata : Dynamic.HeapMetadataExtend middle after)
    (failed : Dynamic.ExpressionFaults program context function.evidence function.source environment middle (expression boolean) reason after)
    (retained : ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry
      program context function.evidence function.source environment middle (expression boolean) reason after token mapping world bodyStore)
    (child : Evaluates (.bool boolean :: actual) middleStore ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ)) (.inLeft type (.word token)) bodyStore)
    (completed : Evaluates actual initialStore (sourceBody.rename ξ) (.inLeft type (.word token)) bodyStore) :
    model_bodyPost checked functions registry program function context environment before actual initialStore (sourceBody.rename ξ) reason after token mapping world bodyStore := by
  obtain ⟨origin, path, transported, model⟩ := retained
  exact ⟨origin, scope, statement, node, condition, conditionNode, conditionFuel, branch, branchNode, expression,
    expressionNode, fuel, solved, reasonAt, conditionCode, code, type, sourceBody, fellThrough, escaped, ξ,
    conditional, rfl, transported, model,
    .branch boolean first firstNative middleHeaps firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata failed path child, completed⟩
end Constructors

theorem model_bodyPost.source_path {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {actual : Environment} {initialStore bodyStore : Store} {body : Expr}
    {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping}
    (post : model_bodyPost checked functions registry program function context environment before actual initialStore body reason after token mapping world bodyStore) :
    ∃ origin : PrimitiveOrigin after reason token,
      ConditionalPath origin program function context environment before ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin := by
  obtain ⟨origin, scope, statement, node, condition, conditionNode, conditionFuel, branch, branchNode, expression,
    expressionNode, fuel, solved, reasonAt, conditionCode, code, type, sourceBody, fellThrough, escaped, ξ,
    conditional, _sameBody, transported, model, route, _completed⟩ := post
  refine ⟨origin, ?_, transported, model⟩
  cases route with
  | condition failed path _ => exact .condition conditional.statements (lookupStatement?_sound conditional.found) conditional.form failed path
  | branch boolean first _ _ _ _ _ _ _ _ _ _ failed path _ =>
    exact .branch boolean conditional.statements (lookupStatement?_sound conditional.found) conditional.form first
      (lookupStatement?_sound (conditional.branchFound boolean)) (conditional.branchForm boolean) failed path

end Solcore.SourceSemantics.CoreLowering.ReachedNamedConditionalBodyFaultPaths
