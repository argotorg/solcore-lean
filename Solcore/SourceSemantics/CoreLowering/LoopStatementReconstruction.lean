import Solcore.SourceSemantics.CoreLowering.LoopFiniteReflection

/-! Compositional source-trace reconstruction for generated statement helpers.
Only syntax certificates, represented initial state, and finite Core
executions are supplied; source child executions are constructed here. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Internal CoreProof

theorem stagedTyped (value : SourceStagedValue.Value) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world (SourceStagedValue.toCore value) (SourceStagedValue.coreType value) :=
  GeneralHeap.ValueRepresents.runtime_hasType (mapping := []) (.scalar value)

private theorem valid_extend
    {compilation : SourceCorePrimitive.Context} {owner : Resolved.DeclarationId}
    {context middle : Context} {binder : TypedBinder}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (extension : BinderExtends owner context binder middle) :
    PrimitiveExpressions.ContextValid compilation middle := by
  cases extension
  exact ⟨valid.ledger, valid.valid.transport rfl rfl rfl⟩

theorem expression_meaning
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt id type code depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : PrimitiveExpressions.ContextValid compilation context)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ) :
    ∃ outcome value,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome heap ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment heap reasonAt id type outcome value ∧
      Core.Evaluates actual store (code.rename ξ) value store := by
  obtain ⟨outcome, value, sourceEval, related, coreEval⟩ :=
    GeneralExpressions.Primitive.preserves tree program context evidence valid environments heaps
  exact ⟨outcome, value, sourceEval, related,
    (GeneralExpressions.Primitive.readOnly tree).evaluation_rename coreEval layout.agrees⟩

theorem prepend
    {program : Program} {context middleContext finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {mode : Bool}
    {environment nextEnvironment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {rest : List StatementId} {type : Core.Ty}
    {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (contains : ContainsStatement source id node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough nextEnvironment) middle)
    (tail : Meaning program middleContext evidence source reasonAt mode nextEnvironment middle rest type finalContext outcome after result) :
    Meaning program context evidence source reasonAt mode environment before (id :: rest) type finalContext outcome after result := by
  cases mode with
  | false =>
    cases tail with
    | control execution related => exact .control (.cons head execution) related
    | fault fault related => exact .fault (.tail head fault) related
  | true =>
    cases rest with
    | nil =>
      cases tail with
      | control execution related =>
        cases execution
        exact .control (.singleton contains (notTail rfl rfl) head) related
      | fault fault _ => cases fault
    | cons next rest =>
      cases tail with
      | control execution related => exact .control (.cons head execution) related
      | fault fault related => exact .fault (.tail head fault) related

theorem terminal
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {mode : Bool}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {rest : List StatementId} {type : Core.Ty}
    {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (contains : ContainsStatement source id node) (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after)
    (terminal : Dynamic.TerminalControl outcome) (related : ControlRepresents type outcome result) :
    Meaning program context evidence source reasonAt mode environment before (id :: rest) type finalContext outcome after result := by
  cases mode with
  | false => exact .control (.terminal head terminal) related
  | true =>
    cases rest with
    | nil => exact .control (.singleton contains notTail head) related
    | cons => exact .control (.terminal head terminal) related

theorem head_fault
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {mode : Bool}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {type : Core.Ty} {reason : Dynamic.SemanticFault} {word : Core.Word}
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after)
    (related : FaultRepresents program evidence source reasonAt reason word) :
    Meaning program context evidence source reasonAt mode environment before (id :: rest) type context (.fault reason) after
      (.inLeft (Core.LocalLoop.controlType type) (.word word)) := by
  cases mode with
  | false => exact .fault (.head fault) related
  | true => cases rest with
    | nil => exact .fault (.singleton fault) related
    | cons => exact .fault (.head fault) related

theorem reflects_nil (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (mode : Bool) (type : Core.Ty) :
    Reflects compilation program evidence source reasonAt scope context mode [] type (Core.LocalLoop.fallthrough type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ _ _ heaps _ evaluated
  simp only [Core.LoopRenaming.fallthrough] at evaluated
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.fallthrough_evaluates type actual store)
  refine ⟨context, _, heap, mapping, world, .control ?_ (.fallthrough environment), heaps, .refl _, .refl _, .refl _ _⟩
  cases mode <;> exact .nil

theorem reflects_breaking
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty}
    (contains : ContainsStatement source id node) (form : node.form = .breakStmt) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.breaking type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ _ _ heaps _ evaluated
  simp only [Core.LoopRenaming.breaking] at evaluated
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.breaking_evaluates type actual store)
  exact ⟨context, _, heap, mapping, world,
    terminal contains (by intro expression; simp [form]) (.breakStmt contains form) (.breaking environment) (.breaking environment),
    heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_continuing
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty}
    (contains : ContainsStatement source id node) (form : node.form = .continueStmt) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.continuing type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ _ _ heaps _ evaluated
  simp only [Core.LoopRenaming.continuing] at evaluated
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.continuing_evaluates type actual store)
  exact ⟨context, _, heap, mapping, world,
    terminal contains (by intro expression; simp [form]) (.continueStmt contains form) (.continuing environment) (.continuing environment),
    heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_returnUnit
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (contains : ContainsStatement source id node) (form : node.form = .returnStmt none) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) .unit (Core.LocalLoop.returned .unit) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ _ _ heaps _ evaluated
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returned_evaluates Core.Evaluates.unit)
  exact ⟨context, _, heap, mapping, world,
    terminal contains (by intro expression; simp [form]) (.returnUnit contains form) (.returned .unit) (.returned .unit rfl),
    heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_returnValue
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty}
    {valueId : ExpressionId} {code : Core.Expr} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .returnStmt (some valueId))
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId type code depth) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.returnValue type code) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.returnValue] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returnValue_success type coreEval)
      exact ⟨context, _, heap, mapping, world,
        terminal contains (by intro expression; simp [form]) (.returnValue contains form sourceEval) (.returned _) (.returned staged typed),
        heaps, .refl _, .refl _, .refl _ _⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returnValue_failure type coreEval)
      exact ⟨context, _, heap, mapping, world,
        head_fault (.returnValue contains form sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_tailExpression
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {id : StatementId} {node : StatementNode} {type : Core.Ty} {valueId : ExpressionId} {code : Core.Expr} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .expression valueId false)
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId type code depth) :
    Reflects compilation program evidence source reasonAt scope context true [id] type (Core.LocalLoop.returnValue type code) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.returnValue] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returnValue_success type coreEval)
      exact ⟨context, _, heap, mapping, world, .control (.tailExpression contains form sourceEval) (.returned staged typed),
        heaps, .refl _, .refl _, .refl _ _⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returnValue_failure type coreEval)
      exact ⟨context, _, heap, mapping, world, .fault (.tailExpression contains form sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩


private theorem notTail_expression {mode semicolon : Bool} {rest : List StatementId}
    {node : StatementNode} {valueId : ExpressionId}
    (form : node.form = .expression valueId semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false) :
    mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
  intro sameMode empty expression impossible
  rw [form] at impossible
  cases impossible
  simp [sameMode, empty] at notTail

theorem reflects_discard
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode semicolon : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type valueType : Core.Ty}
    {valueId : ExpressionId} {code body : Core.Expr} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .expression valueId semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId valueType code depth)
    (tail : Reflects compilation program evidence source reasonAt scope context mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.discard (Core.LocalLoop.controlType type) code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.discard] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      obtain ⟨size, sized⟩ := evaluation_has_size evaluated
      obtain ⟨_, _, continuation⟩ := sized.bind_success coreEval
      obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
        tail wellFormed valid environments heaps (layout.insert (stagedTyped staged world))
          (by simpa only [rename_insert] using continuation.sound)
      exact ⟨finalContext, outcome, after, finalMap, finalWorld,
        prepend contains (notTail_expression form notTail) (.expression contains form sourceEval) meaning,
        finalHeaps, maps, worlds, frame⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalSequence.discard_failure (Core.LocalLoop.controlType type) coreEval)
      exact ⟨context, _, heap, mapping, world,
        head_fault (.expression contains form sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_letUninitialized
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context middleContext : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type payload : Core.Ty} {body : Core.Expr} {binder : TypedBinder}
    (contains : ContainsStatement source id node) (form : node.form = .letDecl binder none)
    (binding : BinderCertificate source scope binder payload)
    (extension : BinderExtends source.owner context binder middleContext)
    (tail : Reflects compilation program evidence source reasonAt ((binder.id, payload) :: scope) middleContext mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.letUninitialized payload body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.letUninitialized] at evaluated
  have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
      ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
  obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
  have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
  have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
    rw [← heaps.runtime_hasTypes.length_eq]; simp
  have nextLayout := (layout.extend worlds).bind (Core.RuntimeValueHasType.cellRef found)
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨_, _, continuation⟩ := sized.let_body (Core.OptionalCell.allocate_evaluates payload actual store)
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, futureWorlds, frame⟩ :=
    tail wellFormed (valid_extend valid extension) nextEnvironments nextHeaps nextLayout continuation.sound
  exact ⟨finalContext, outcome, after, finalMap, finalWorld,
    prepend contains (by intros; simp [form]) (.letUninitialized contains form binding.monomorphic extension allocated) meaning,
    finalHeaps, (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
    worlds.trans futureWorlds, (GeneralHeap.AdministrativePreserved.allocate mapping store (.inLeft payload .unit)).trans frame⟩

theorem reflects_letInitialized
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context middleContext : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type payload : Core.Ty} {code body : Core.Expr} {binder : TypedBinder}
    {initializer : ExpressionId} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .letDecl binder (some initializer))
    (binding : BinderCertificate source scope binder payload)
    (extension : BinderExtends source.owner context binder middleContext)
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payload code depth)
    (tail : Reflects compilation program evidence source reasonAt ((binder.id, payload) :: scope) middleContext mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType type) payload code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.letInitialized] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      have allocated : Dynamic.Heap.Allocates heap binder.scheme.body (some (StagedValue.toSource staged))
          ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := some (StagedValue.toSource staged) }]⟩ := .append
      have sameSource : binder.scheme.body = SourceStagedValue.sourceType staged := binding.types.source_unique (typed ▸ stagedTypes staged)
      have cell : CellRepresents {type := binder.scheme.body, value := some (StagedValue.toSource staged)}
          (.inRight .unit (SourceStagedValue.toCore staged)) payload := by
        rw [sameSource, ← typed]; exact .initialized staged
      obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
      have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
      have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
        rw [← heaps.runtime_hasTypes.length_eq]; simp
      have nextLayout := ((layout.extend worlds).insert (stagedTyped staged _)).bind (Core.RuntimeValueHasType.cellRef found)
      obtain ⟨size, sized⟩ := evaluation_has_size evaluated
      obtain ⟨_, _, allocation⟩ := sized.bind_success coreEval
      obtain ⟨_, _, continuation⟩ := allocation.let_body (Core.OptionalCell.allocateInitialized_evaluates (.var rfl))
      obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, futureWorlds, frame⟩ :=
        tail wellFormed (valid_extend valid extension) nextEnvironments nextHeaps nextLayout
          (by simpa only [rename_insert_lift, Core.Store.allocate] using continuation.sound)
      exact ⟨finalContext, outcome, after, finalMap, finalWorld,
        prepend contains (by intros; simp [form]) (.letInitialized contains form sourceEval binding.monomorphic extension allocated) meaning,
        finalHeaps, (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
        worlds.trans futureWorlds,
        (GeneralHeap.AdministrativePreserved.allocate mapping store (.inRight .unit (SourceStagedValue.toCore staged))).trans frame⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated
        (Core.LocalSequence.letInitialized_failure (Core.LocalLoop.controlType type) payload coreEval)
      exact ⟨context, _, heap, mapping, world,
        head_fault (.letInitializer contains form binding.monomorphic sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩

private theorem cellsWrite_set {cells : List Dynamic.Cell} {index : Nat}
    {previous : Dynamic.Cell} (selected : Dynamic.Heap.CellAt cells index previous)
    (replacement : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite cells index replacement (cells.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

/-- Basic expression RHS evaluation leaves its heap unchanged. The captured
source location and independently mapped Core location identify the same cell. -/
private theorem equal_assignment
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {target : PlaceResolution} {rhs : ExpressionId} {index : Nat} {payloadType : Core.Ty}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (slot : SourceCoreLocalCell.lookup? scope target.root = some (index, payloadType))
    (bare : target.projections = []) (value : SourceStagedValue.Value)
    (valueType : SourceStagedValue.coreType value = payloadType)
    (rhsEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment
      heap rhs (StagedValue.toSource value) heap) :
    ∃ (coreLocation : Core.Location) (after : Dynamic.Heap) (finalStore : Core.Store),
      Dynamic.SourcePlaceAssignment program context evidence source
        (Dynamic.AssignmentValueApplies .equal) environment heap target rhs (StagedValue.toSource value) after ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) ∧
      (∃ oldValue, store.read? coreLocation = some oldValue) ∧
      store.write? coreLocation (.inRight .unit (SourceStagedValue.toCore value)) = some finalStore ∧
      GeneralHeap.HeapRepresents mapping world after finalStore ∧
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨location, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
    environments.lookup_heap heaps slot
  let replacement : Dynamic.Cell := { cell with value := some (StagedValue.toSource value) }
  let after : Dynamic.Heap := ⟨heap.cells.set location.index replacement⟩
  have sourceWrite : Dynamic.Heap.Writes heap location (some (StagedValue.toSource value)) after := by
    cases read with
    | intro selected => exact .intro (.intro selected) (cellsWrite_set selected replacement)
  obtain ⟨finalStore, written, heapRelated⟩ := heaps.write_initialized reference value valueType sourceWrite
  let captured : Dynamic.ResolvedPlace := {
    location, rootType := cell.type, valueType := target.type, projections := [], selected := cell.value
  }
  have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap target captured heap := by
    apply Dynamic.SourcePlaceResolves.intro lookup read
    · rw [bare]; exact .nil
    · exact read
    · exact represented.rootInitialValue
    · exact .nil
  exact ⟨coreLocation, after, finalStore,
    .intro resolved rhsEvaluated
      (.intro read rfl represented.rootInitialValue (.leaf (.equal cell.value (StagedValue.toSource value))) sourceWrite),
    coreLookup, ⟨stored, coreRead⟩, written, heapRelated, environments,
    GeneralHeap.AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) written⟩


theorem reflects_assign
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type payload : Core.Ty}
    {rhs : ExpressionId} {code body : Core.Expr} {depth index : Nat} {assignment : AssignmentResolution}
    (contains : ContainsStatement source id node) (form : node.form = .assignValue assignment .equal rhs)
    (target : AssignmentCertificate source scope assignment .equal index payload)
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payload code depth)
    (tail : Reflects compilation program evidence source reasonAt scope context mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.assign (Core.LocalLoop.controlType type) (.var index) code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.assign] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      obtain ⟨location, afterWrite, writtenStore, assigned, lookup, ⟨old, readable⟩, written,
        updatedHeaps, updatedEnvironments, writeFrame⟩ := equal_assignment environments heaps target.slot target.bare staged typed sourceEval
      have actualLookup := layout.agrees lookup
      have referenceTyped : Core.RuntimeValueHasType world
          (.cellRef (Core.OptionalCell.cellType payload) location) (Core.OptionalCell.referenceType payload) := by
        obtain ⟨found, foundEq, foundTyped⟩ := Core.RuntimeEnvironmentHasTypes.lookup layout.typed
          (layout.respects (SourceCoreLocalCell.lookup?_context target.slot))
        rw [actualLookup] at foundEq
        cases foundEq
        exact foundTyped
      obtain ⟨size, sized⟩ := evaluation_has_size evaluated
      obtain ⟨_, _, rhsEvaluation⟩ := sized.let_body (.var actualLookup)
      obtain ⟨_, _, writeEvaluation⟩ := rhsEvaluation.bind_success
        (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)
      have writeEval : Core.Evaluates
          (SourceStagedValue.toCore staged :: .cellRef (Core.OptionalCell.cellType payload) location :: actual) store
          (.storeCell (.var 1) (.inRight .unit (.var 0))) .unit writtenStore :=
        .storeCell (.var rfl) readable (.inRight (.var rfl)) written
      obtain ⟨_, _, continuation⟩ := writeEvaluation.let_body writeEval
      have nextLayout := ((layout.insert referenceTyped).insert (stagedTyped staged world)).insert Core.RuntimeValueHasType.unit
      obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
        tail wellFormed valid updatedEnvironments updatedHeaps nextLayout
          (by simpa only [rename_insert] using continuation.sound)
      exact ⟨finalContext, outcome, after, finalMap, finalWorld,
        prepend contains (by intros; simp [form]) (.assignValue contains form assigned) meaning,
        finalHeaps, maps, worlds, writeFrame.trans frame⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨sourceLocation, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
        environments.lookup_heap heaps target.slot
      let captured : Dynamic.ResolvedPlace := {
        location := sourceLocation, rootType := cell.type, valueType := assignment.target.type,
        projections := [], selected := cell.value
      }
      have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap assignment.target captured heap := by
        apply Dynamic.SourcePlaceResolves.intro lookup read
        · rw [target.bare]; exact .nil
        · exact read
        · exact represented.rootInitialValue
        · exact .nil
      have core := Core.LocalSequence.assign_failure (next := body.rename ξ) (Core.LocalLoop.controlType type)
        (Core.Evaluates.var (layout.agrees coreLookup))
        (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated core
      exact ⟨context, _, heap, mapping, world,
        head_fault (.assignValue contains form (.rhs resolved sourceFault)) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
