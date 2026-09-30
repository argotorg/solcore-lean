import Solcore.Frontend.SourceCoreBasic
import Solcore.SourceSemantics.CoreLowering.HeapMutation

/-! Composition laws for the actual ordinary-local statement compiler.

Each law combines independent source derivations with child Core derivations
and an equation of `SourceCoreBasic.lowerStatements`. Temporary result binders
are explicit in the Core premises. No unrestricted heap weakening, whole-body
compiler correctness, staging correctness or termination theorem is assumed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicStatements

open Frontend Frontend.SourceInference TypeSystem

private theorem prepend
    {program : Program} {context middleContext finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment nextEnvironment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id
      middleContext (.fallthrough nextEnvironment) middle)
    (tail : Dynamic.FunctionStatementsExecuteOutcome program middleContext evidence source
      nextEnvironment middle rest finalContext outcome after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
      (id :: rest) finalContext outcome after := by
  cases rest with
  | nil =>
      cases tail with
      | control execute =>
          cases execute
          exact .control (.singleton contains notTail head)
      | fault fault => cases fault
  | cons next rest =>
      cases tail with
      | control execute => exact .control (.cons head execute)
      | fault fault => exact .fault (.tail head fault)

private theorem fault_prefix
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {reason : Dynamic.SemanticFault} (rest : List StatementId)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
      (id :: rest) context (.fault reason) after := by
  cases rest with
  | nil => exact .fault (.singleton fault)
  | cons _ _ => exact .fault (.head fault)

private theorem returned_prefix
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {value : Dynamic.Value} (rest : List StatementId)
    (contains : ContainsStatement source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (returned : Dynamic.StatementExecutes program context evidence source environment before id
      context (.returned value) after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
      (id :: rest) context (.returned value) after := by
  cases rest with
  | nil => exact .control (.singleton contains notTail returned)
  | cons _ _ => exact .control (.terminal returned (.returned value))

section Prefix

variable {program : Program} {context middleContext finalContext : Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {scope : SourceCoreBasic.Scope} {environment : Dynamic.Environment}
  {coreEnvironment : Core.Environment} {before middle after : Dynamic.Heap}
  {store middleStore finalStore : Core.Store} {world : Core.StoreTyping}
  {fuel : Nat} {id : StatementId} {rest : List StatementId} {node : StatementNode}
  {resultType : Core.Ty} {reason : Core.Word} {body : Core.Expr}
  {outcome : Dynamic.ControlOutcome} {result : Core.Value}

/-- Allocation chooses the same source/Core location before the continuation. -/
theorem letUninitialized_prefix
    {binder : TypedBinder} {payloadType : Core.Ty} {location : Dynamic.Location}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .letDecl binder none)
    (binding : SourceCoreBasic.lowerBinder source scope binder = .ok payloadType)
    (monomorphic : binder.scheme.quantified = [])
    (extension : BinderExtends source.owner context binder middleContext)
    (types : LocalCell.TypeRepresents binder.scheme.body payloadType)
    (related : LocalCell.HeapRepresents before.cells store world)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location middle)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source
      ((binder.id, payloadType) :: scope) rest resultType reason = .ok body)
    (tailSource : Dynamic.FunctionStatementsExecuteOutcome program middleContext evidence source
      ((binder.id, location) :: environment) middle rest finalContext outcome after)
    (tailCore : Core.Evaluates
      (.cellRef (Core.OptionalCell.cellType payloadType) location.index :: coreEnvironment)
      (store ++ [.inLeft payloadType .unit]) body result finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.letUninitialized payloadType body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) finalContext outcome after ∧
      Core.Evaluates coreEnvironment store (Core.LocalSequence.letUninitialized payloadType body)
        result finalStore := by
  refine ⟨SourceCoreBasic.lowerStatements_letUninitialized metadata form binding tailLowered,
    prepend contains (by intro expression; rw [form]; intro impossible; cases impossible)
      (.letUninitialized contains form monomorphic extension allocated) tailSource, ?_⟩
  have locationEq := (related.allocate_uninitialized types allocated).1
  exact Core.LocalSequence.letUninitialized_evaluates payloadType (locationEq ▸ tailCore)

/-- Initializer effects precede allocation. The Core continuation is evaluated
with the successful payload inserted after its new lexical cell reference. -/
theorem letInitialized_prefix
    {binder : TypedBinder} {initializer : ExpressionId} {expression : Core.Expr}
    {location : Dynamic.Location} {allocatedHeap : Dynamic.Heap}
    (value : SourceStagedValue.Value)
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .letDecl binder (some initializer))
    (binding : SourceCoreBasic.lowerBinder source scope binder = .ok (SourceStagedValue.coreType value))
    (monomorphic : binder.scheme.quantified = [])
    (extension : BinderExtends source.owner context binder middleContext)
    (binderType : binder.scheme.body = SourceStagedValue.sourceType value)
    (initializerLowered : SourceCoreBasic.lowerExpression fuel source scope initializer reason =
      .ok ⟨SourceStagedValue.coreType value, expression⟩)
    (initializerSource : Dynamic.ExpressionEvaluates program context evidence source environment
      before initializer (StagedValue.toSource value) middle)
    (initializerCore : Core.Evaluates coreEnvironment store expression
      (.inRight .word (SourceStagedValue.toCore value)) middleStore)
    (related : LocalCell.HeapRepresents middle.cells middleStore world)
    (allocated : Dynamic.Heap.Allocates middle binder.scheme.body
      (some (StagedValue.toSource value)) location allocatedHeap)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source
      ((binder.id, SourceStagedValue.coreType value) :: scope) rest resultType reason = .ok body)
    (tailSource : Dynamic.FunctionStatementsExecuteOutcome program middleContext evidence source
      ((binder.id, location) :: environment) allocatedHeap rest finalContext outcome after)
    (tailCore : Core.Evaluates
      (.cellRef (Core.OptionalCell.cellType (SourceStagedValue.coreType value)) location.index ::
        SourceStagedValue.toCore value :: coreEnvironment)
      (middleStore ++ [.inRight .unit (SourceStagedValue.toCore value)])
      (body.weakenAt 1) result finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.letInitialized resultType (SourceStagedValue.coreType value) expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) finalContext outcome after ∧
      Core.Evaluates coreEnvironment store
        (Core.LocalSequence.letInitialized resultType (SourceStagedValue.coreType value) expression body)
        result finalStore := by
  refine ⟨SourceCoreBasic.lowerStatements_letInitialized metadata form binding initializerLowered tailLowered,
    prepend contains (by intro expression; rw [form]; intro impossible; cases impossible)
      (.letInitialized contains form initializerSource monomorphic extension allocated) tailSource, ?_⟩
  have locationEq := (related.allocate_initialized value (binderType ▸ allocated)).1
  exact Core.LocalSequence.letInitialized_success resultType (SourceStagedValue.coreType value)
    initializerCore (locationEq ▸ tailCore)

theorem discard_prefix
    {expressionId : ExpressionId} {valueType : Core.Ty} {expression : Core.Expr}
    (value : SourceStagedValue.Value)
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .expression expressionId true)
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨valueType, expression⟩)
    (expressionSource : Dynamic.ExpressionEvaluates program context evidence source environment
      before expressionId (StagedValue.toSource value) middle)
    (expressionCore : Core.Evaluates coreEnvironment store expression
      (.inRight .word (SourceStagedValue.toCore value)) middleStore)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source scope rest resultType reason = .ok body)
    (tailSource : Dynamic.FunctionStatementsExecuteOutcome program context evidence source
      environment middle rest finalContext outcome after)
    (tailCore : Core.Evaluates (SourceStagedValue.toCore value :: coreEnvironment) middleStore
      (body.weakenAt 0) result finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.discard resultType expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) finalContext outcome after ∧
      Core.Evaluates coreEnvironment store (Core.LocalSequence.discard resultType expression body)
        result finalStore := by
  exact ⟨SourceCoreBasic.lowerStatements_discard metadata form lowered tailLowered,
    prepend contains (by intro expression; rw [form]; intro impossible; cases impossible)
      (.expression contains form expressionSource) tailSource,
    Core.LocalSequence.discard_success resultType expressionCore tailCore⟩

/-- The reference is captured before RHS evaluation. The store supplied by the
RHS is the one read and written; temporary binders are exposed in the premises. -/
theorem assign_prefix
    {assignment : AssignmentResolution} {rhs : ExpressionId} {expression : Core.Expr}
    {index : Nat} {payloadType : Core.Ty} {location : Core.Location}
    {rhsStore : Core.Store} {updatedRoot : Dynamic.Value} {value oldValue : Core.Value}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .assignValue assignment .equal rhs)
    (target : SourceCoreBasic.lowerAssignment source scope assignment .equal = .ok (index, payloadType))
    (lowered : SourceCoreBasic.lowerExpression fuel source scope rhs reason = .ok ⟨payloadType, expression⟩)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source scope rest resultType reason = .ok body)
    (assignmentSource : Dynamic.SourcePlaceAssignment program context evidence source
      (Dynamic.AssignmentValueApplies .equal) environment before assignment.target rhs updatedRoot middle)
    (lookup : coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) location))
    (rhsCore : Core.Evaluates (.cellRef (Core.OptionalCell.cellType payloadType) location :: coreEnvironment)
      store (expression.weakenAt 0) (.inRight .word value) rhsStore)
    (readable : rhsStore.read? location = some oldValue)
    (written : rhsStore.write? location (.inRight .unit value) = some middleStore)
    (tailSource : Dynamic.FunctionStatementsExecuteOutcome program context evidence source
      environment middle rest finalContext outcome after)
    (tailCore : Core.Evaluates
      (.unit :: value :: .cellRef (Core.OptionalCell.cellType payloadType) location :: coreEnvironment)
      middleStore (((body.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.assign resultType (.var index) expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) finalContext outcome after ∧
      Core.Evaluates coreEnvironment store
        (Core.LocalSequence.assign resultType (.var index) expression body) result finalStore := by
  exact ⟨SourceCoreBasic.lowerStatements_assign metadata form target lowered tailLowered,
    prepend contains (by intro expression; rw [form]; intro impossible; cases impossible)
      (.assignValue contains form assignmentSource) tailSource,
    Core.LocalSequence.assign_success resultType (.var lookup) rhsCore readable written tailCore⟩

end Prefix

section Terminal

variable {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : SourceCoreBasic.Scope} {environment : Dynamic.Environment}
  {coreEnvironment : Core.Environment} {before after : Dynamic.Heap} {store finalStore : Core.Store}
  {fuel : Nat} {id : StatementId} {rest : List StatementId} {node : StatementNode}
  {resultType : Core.Ty} {reason : Core.Word} {expression : Core.Expr} {expressionId : ExpressionId}

/-- A return never requires lowering or evaluating any trailing statement. -/
theorem return_prefix
    (value : SourceStagedValue.Value)
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, resultType))
    (form : node.form = .returnStmt (some expressionId))
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨resultType, expression⟩)
    (sourceEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment
      before expressionId (StagedValue.toSource value) after)
    (coreEvaluation : Core.Evaluates coreEnvironment store expression
      (.inRight .word (SourceStagedValue.toCore value)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.returned (StagedValue.toSource value)) after ∧
      Core.Evaluates coreEnvironment store expression
        (.inRight .word (SourceStagedValue.toCore value)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_return metadata form lowered,
    returned_prefix rest contains
      (by intro expression; rw [form]; intro impossible; cases impossible)
      (.returnValue contains form sourceEvaluation), coreEvaluation⟩

theorem returnUnit_prefix
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .returnStmt none) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) .unit reason =
        .ok (Core.LanguageResult.success .unit) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.returned .unit) before ∧
      Core.Evaluates coreEnvironment store (Core.LanguageResult.success .unit)
        (.inRight .word .unit) store :=
  ⟨SourceCoreBasic.lowerStatements_returnUnit metadata form,
    returned_prefix rest contains
      (by intro expression; rw [form]; intro impossible; cases impossible)
      (.returnUnit contains form), .inRight .unit⟩

theorem tailExpression
    (value : SourceStagedValue.Value)
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, resultType))
    (form : node.form = .expression expressionId false)
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨resultType, expression⟩)
    (sourceEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment
      before expressionId (StagedValue.toSource value) after)
    (coreEvaluation : Core.Evaluates coreEnvironment store expression
      (.inRight .word (SourceStagedValue.toCore value)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope [id] resultType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        [id] context (.returned (StagedValue.toSource value)) after ∧
      Core.Evaluates coreEnvironment store expression
        (.inRight .word (SourceStagedValue.toCore value)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_tail metadata form lowered,
    .control (.tailExpression contains form sourceEvaluation), coreEvaluation⟩

theorem return_fault
    {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, resultType))
    (form : node.form = .returnStmt (some expressionId))
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨resultType, expression⟩)
    (sourceFault : Dynamic.ExpressionFaults program context evidence source environment
      before expressionId fault after)
    (coreFailure : Core.Evaluates coreEnvironment store expression (.inLeft resultType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store expression (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_return metadata form lowered,
    fault_prefix rest (.returnValue contains form sourceFault), coreFailure⟩

theorem tailExpression_fault
    {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, resultType))
    (form : node.form = .expression expressionId false)
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨resultType, expression⟩)
    (sourceFault : Dynamic.ExpressionFaults program context evidence source environment
      before expressionId fault after)
    (coreFailure : Core.Evaluates coreEnvironment store expression (.inLeft resultType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope [id] resultType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        [id] context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store expression (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_tail metadata form lowered,
    .fault (.tailExpression contains form sourceFault), coreFailure⟩

theorem letInitialized_fault
    {binder : TypedBinder} {payloadType : Core.Ty} {body : Core.Expr}
    {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .letDecl binder (some expressionId))
    (binding : SourceCoreBasic.lowerBinder source scope binder = .ok payloadType)
    (monomorphic : binder.scheme.quantified = [])
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨payloadType, expression⟩)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source ((binder.id, payloadType) :: scope)
      rest resultType reason = .ok body)
    (sourceFault : Dynamic.ExpressionFaults program context evidence source environment
      before expressionId fault after)
    (coreFailure : Core.Evaluates coreEnvironment store expression (.inLeft payloadType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.letInitialized resultType payloadType expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store
        (Core.LocalSequence.letInitialized resultType payloadType expression body)
        (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_letInitialized metadata form binding lowered tailLowered,
    fault_prefix rest (.letInitializer contains form monomorphic sourceFault),
    Core.LocalSequence.letInitialized_failure resultType payloadType coreFailure⟩

theorem discard_fault
    {valueType : Core.Ty} {body : Core.Expr} {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .expression expressionId true)
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨valueType, expression⟩)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source scope rest resultType reason = .ok body)
    (sourceFault : Dynamic.ExpressionFaults program context evidence source environment
      before expressionId fault after)
    (coreFailure : Core.Evaluates coreEnvironment store expression (.inLeft valueType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.discard resultType expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store (Core.LocalSequence.discard resultType expression body)
        (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_discard metadata form lowered tailLowered,
    fault_prefix rest (.expression contains form sourceFault),
    Core.LocalSequence.discard_failure resultType coreFailure⟩

theorem assign_fault
    {assignment : AssignmentResolution} {index : Nat} {payloadType : Core.Ty}
    {body : Core.Expr} {location : Core.Location} {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .assignValue assignment .equal expressionId)
    (target : SourceCoreBasic.lowerAssignment source scope assignment .equal = .ok (index, payloadType))
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨payloadType, expression⟩)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source scope rest resultType reason = .ok body)
    (sourceFault : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment
      before assignment.target .equal expressionId fault after)
    (lookup : coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) location))
    (coreFailure : Core.Evaluates
      (.cellRef (Core.OptionalCell.cellType payloadType) location :: coreEnvironment)
      store (expression.weakenAt 0) (.inLeft payloadType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.assign resultType (.var index) expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store
        (Core.LocalSequence.assign resultType (.var index) expression body)
        (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_assign metadata form target lowered tailLowered,
    fault_prefix rest (.assignValue contains form sourceFault),
    Core.LocalSequence.assign_failure resultType (.var lookup) coreFailure⟩

end Terminal

/-- A complete two-statement specimen: allocate an absent scalar/product local,
then return that local. The actual compiler emits a finite language failure;
the independent source semantics faults at precisely the new location. Any
trailing statements are ignored by the explicit return. No child evaluation or
whole-program correspondence assumption occurs in this theorem. -/
theorem uninitialized_then_return
    {program : Program} {context localContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreBasic.Scope} {environment : Dynamic.Environment}
    {coreEnvironment : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    {world : Core.StoreTyping} {letId returnId : StatementId} {letNode returnNode : StatementNode}
    {binder : TypedBinder} {payloadType : Core.Ty} {readId : ExpressionId}
    (trailing : List StatementId) (reason : Core.Word)
    (unique : NodeOccurrencesUnique source)
    (letContains : ContainsStatement source letId letNode)
    (letMetadata : SourceCoreBasic.readStatement source letId = .ok (letNode, .unit))
    (letForm : letNode.form = .letDecl binder none)
    (binding : SourceCoreBasic.lowerBinder source scope binder = .ok payloadType)
    (monomorphic : binder.scheme.quantified = [])
    (extension : BinderExtends source.owner context binder localContext)
    (binderTypes : LocalCell.TypeRepresents binder.scheme.body payloadType)
    (returnContains : ContainsStatement source returnId returnNode)
    (returnMetadata : SourceCoreBasic.readStatement source returnId = .ok (returnNode, payloadType))
    (returnForm : returnNode.form = .returnStmt (some readId))
    (site : LocalCell.ReadSite source ((binder.id, payloadType) :: scope) readId payloadType)
    (readBinder : site.binder = binder.id)
    (readMetadata : SourceCoreBasic.readExpression source readId = .ok (site.node, payloadType))
    (related : LocalCell.HeapRepresents heap.cells store world) :
    let body := Core.OptionalCell.read payloadType (.var site.index) reason
    let expression := Core.LocalSequence.letUninitialized payloadType body
    let allocatedHeap : Dynamic.Heap :=
      ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩
    let allocatedStore := store ++ [Core.Value.inLeft payloadType .unit]
    SourceCoreBasic.lowerStatements 3 source scope (letId :: returnId :: trailing)
        payloadType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        (letId :: returnId :: trailing) localContext
        (.fault (.uninitializedLocation ⟨heap.cells.length⟩)) allocatedHeap ∧
      Core.Evaluates coreEnvironment store expression
        (.inLeft payloadType (.word reason)) allocatedStore ∧
      LocalCell.HeapRepresents allocatedHeap.cells allocatedStore
        (world ++ [Core.OptionalCell.cellType payloadType]) ∧
      (∀ definitions, Core.HasType (SourceCoreLocalCell.coreContext scope) expression
        (Core.LanguageResult.resultType payloadType) definitions) ∧
      ∃ required,
        (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel
          (.initial expression coreEnvironment store) =
            .done (.inLeft payloadType (.word reason)) allocatedStore) ∧
        (∀ runtimeFuel result finalStore, Core.runStateful runtimeFuel
          (.initial expression coreEnvironment store) = .done result finalStore →
            result = .inLeft payloadType (.word reason) ∧ finalStore = allocatedStore) := by
  dsimp only
  let location : Dynamic.Location := ⟨heap.cells.length⟩
  let allocatedHeap : Dynamic.Heap :=
    ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩
  have allocation : Dynamic.Heap.Allocates heap binder.scheme.body none location allocatedHeap := .append
  have indexZero : site.index = 0 := by
    have slot := site.slot
    rw [readBinder] at slot
    simp [SourceCoreLocalCell.lookup?] at slot
    exact slot.symm
  have sourceLookup : Dynamic.Environment.LooksUp ((binder.id, location) :: environment)
      site.binder location := by
    rw [readBinder]
    exact .head
  have coreLookup :
      (Core.Value.cellRef (Core.OptionalCell.cellType payloadType) location.index :: coreEnvironment)[site.index]? =
        some (.cellRef (Core.OptionalCell.cellType payloadType) location.index) := by
    rw [indexZero]
    rfl
  have coreRead : (store ++ [Core.Value.inLeft payloadType .unit]).read? location.index =
      some (.inLeft payloadType .unit) := by
    change (store ++ [Core.Value.inLeft payloadType .unit]).read? heap.cells.length = _
    rw [related.length_eq]
    simp [Core.Store.read?]
  obtain ⟨sourceFault, coreFailure⟩ := site.uninitialized program localContext evidence
    ((binder.id, location) :: environment) allocatedHeap
    (.cellRef (Core.OptionalCell.cellType payloadType) location.index :: coreEnvironment)
    (store ++ [.inLeft payloadType .unit]) location _ sourceLookup allocation.reads_new
    (binderTypes.source_unique site.types) rfl rfl coreLookup coreRead reason
  have readLowered := SourceCoreBasic.lowerExpression_local (fuel := 0) readMetadata site.form
    (site.lower unique reason)
  obtain ⟨returnLowered, returnSource, returnCore⟩ := return_fault (rest := trailing)
    returnContains returnMetadata returnForm readLowered sourceFault coreFailure
  obtain ⟨lowered, sourceFault, evaluated⟩ := letUninitialized_prefix letContains letMetadata letForm
    binding monomorphic extension binderTypes related allocation returnLowered returnSource returnCore
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
  refine ⟨lowered, sourceFault, evaluated, (related.allocate_uninitialized binderTypes allocation).2,
    ?_, required, completes, ?_⟩
  · intro definitions
    exact Core.LocalSequence.letUninitialized_hasType (binderTypes.wellFormed definitions)
      (site.core_hasType reason definitions)
  · intro runtimeFuel result finalStore completed
    exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) evaluated

end Solcore.SourceSemantics.CoreLowering.BasicStatements
