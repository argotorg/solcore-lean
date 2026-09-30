import Solcore.SourceSemantics.CoreLowering.ControlStatementTree

/-! Whole scoped-control correspondence over mapped source cells and arbitrary
typed administrative cells. All child evaluations follow from the static tree;
blocks restore lexical environments while retaining heap changes. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- Select the independent list judgment used by the source language. -/
def Executes (tailReturns : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (statements : List StatementId)
    (finalContext : Context) (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  if tailReturns then
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
      statements finalContext outcome after
  else Dynamic.StatementsExecuteOutcome program context evidence source environment before
      statements finalContext outcome after

/-- The control envelope contains fallthrough, return, or the provider token
of an uninitialized read. Source fault locations and Core locations remain
separate. The expression-level provenance is retained as an explicit witness. -/
inductive OutcomeRepresents (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (administrativeContext : Core.Context) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) :
    Dynamic.ControlOutcome → Core.Value → Prop where
  | fallthrough {scope environment coreEnvironment}
      (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
      OutcomeRepresents program evidence source mapping world administrativeContext reasonAt type
        (.fallthrough environment) (.inRight .word (.inLeft type .unit))
  | returned (value : SourceStagedValue.Value) (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents program evidence source mapping world administrativeContext reasonAt type
        (.returned (StagedValue.toSource value)) (.inRight .word (.inRight .unit (SourceStagedValue.toCore value)))
  | uninitialized (site : ExpressionId) (location : Dynamic.Location)
      {context : Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {root : ExpressionId}
      (origin : ControlExpressions.UninitializedAt program context evidence source environment heap root site location) :
      OutcomeRepresents program evidence source mapping world administrativeContext reasonAt type
        (.fault (.uninitializedLocation location)) (.inLeft (Core.LocalControl.controlType type) (.word (reasonAt site)))

private theorem nil_executes (tailReturns : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Executes tailReturns program context evidence source environment heap [] context (.fallthrough environment) heap := by
  cases tailReturns <;> exact .control .nil

private theorem fault_head
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {id : StatementId}
    {reason : Dynamic.SemanticFault} (tailReturns : Bool) (rest : List StatementId)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Executes tailReturns program context evidence source environment before (id :: rest) context (.fault reason) after := by
  cases tailReturns with
  | false => exact .fault (.head fault)
  | true => cases rest with
    | nil => exact .fault (.singleton fault)
    | cons => exact .fault (.head fault)

private theorem terminal_head
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
    (tailReturns : Bool) (rest : List StatementId) (contains : ContainsStatement source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after)
    (terminal : Dynamic.TerminalControl outcome) :
    Executes tailReturns program context evidence source environment before (id :: rest) finalContext outcome after := by
  cases tailReturns with
  | false => exact .control (.terminal head terminal)
  | true => cases rest with
    | nil => exact .control (.singleton contains notTail head)
    | cons => exact .control (.terminal head terminal)

private theorem prepend
    {program : Program} {context middleContext finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment nextEnvironment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {outcome : Dynamic.ControlOutcome} {tailReturns : Bool}
    (contains : ContainsStatement source id node)
    (notTail : tailReturns = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id
      middleContext (.fallthrough nextEnvironment) middle)
    (tail : Executes tailReturns program middleContext evidence source nextEnvironment middle
      rest finalContext outcome after) :
    Executes tailReturns program context evidence source environment before (id :: rest) finalContext outcome after := by
  cases tailReturns with
  | false => cases tail with
    | control execute => exact .control (.cons head execute)
    | fault fault => exact .fault (.tail head fault)
  | true => cases rest with
    | nil =>
        cases tail with
        | control execute => cases execute; exact .control (.singleton contains (notTail rfl rfl) head)
        | fault fault => cases fault
    | cons => cases tail with
      | control execute => exact .control (.cons head execute)
      | fault fault => exact .fault (.tail head fault)

private theorem scoped_block
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node) (form : node.form = .block statements)
    (evaluated : Executes false program context evidence source environment before statements finalContext outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id context
      (Dynamic.restoreControl environment outcome) after := by
  cases evaluated with
  | control execute => exact .control (.block contains form execute)
  | fault fault => exact .fault (.block contains form fault)

private theorem scoped_if_true
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool true) middle)
    (evaluated : Executes false program context evidence source environment middle thenBody finalContext outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id context
      (Dynamic.restoreControl environment outcome) after := by
  cases evaluated with
  | control execute => exact .control (.ifTrue contains form conditionEvaluated execute)
  | fault fault => exact .fault (.ifTrueBody contains form conditionEvaluated fault)

private theorem scoped_if_false
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool false) middle)
    (evaluated : Executes false program context evidence source environment middle (elseBody.getD []) finalContext outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id context
      (Dynamic.restoreControl environment outcome) after := by
  cases elseBody with
  | none =>
      cases evaluated with
      | control execute => cases execute; exact .control (.ifFalseWithoutElse contains form conditionEvaluated)
      | fault fault => cases fault
  | some statements =>
      cases evaluated with
      | control execute => exact .control (.ifFalseWithElse contains form conditionEvaluated execute)
      | fault fault => exact .fault (.ifFalseBody contains form conditionEvaluated fault)

private theorem weaken_three {environment : Core.Environment} {store finalStore : Core.Store}
    {expression : Core.Expr} {result : Core.Value}
    (restricted : Core.HeapEffects.Expression expression)
    (evaluation : Core.Evaluates environment store expression result finalStore) (reference value : Core.Value) :
    Core.Evaluates (.unit :: value :: reference :: environment) store
      (((expression.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore :=
  (((restricted.weakenAt 0).weakenAt 0).evaluation_weakenAt_zero
    ((restricted.weakenAt 0).evaluation_weakenAt_zero
      (restricted.evaluation_weakenAt_zero evaluation reference) value) .unit)

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


/-- Finite whole-list correspondence, including extensions of both location
representations and preservation of installed administrative cells. -/
def Result (tailReturns : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) (statements : List StatementId)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (store : Core.Store) (code : Core.Expr)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (administrativeContext : Core.Context) : Prop :=
  ∃ finalContext outcome after result finalStore finalMapping finalWorld,
    Executes tailReturns program context evidence source environment heap statements finalContext outcome after ∧
    OutcomeRepresents program evidence source finalMapping finalWorld administrativeContext reasonAt type outcome result ∧
    Core.Evaluates coreEnvironment store code result finalStore ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

private theorem scoped_sequence
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {type : Core.Ty} {tailReturns : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    {environment : Dynamic.Environment} {heap middleHeap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store middleStore : Core.Store}
    {mapping middleMapping : GeneralHeap.LocationMap} {world middleWorld : Core.StoreTyping}
    {administrativeContext : Core.Context} {computation next : Core.Expr}
    {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (contains : ContainsStatement source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (head : Dynamic.StatementExecutesOutcome program context evidence source environment heap id context
      (Dynamic.restoreControl environment outcome) middleHeap)
    (related : OutcomeRepresents program evidence source middleMapping middleWorld administrativeContext reasonAt type outcome result)
    (coreHead : Core.Evaluates coreEnvironment store computation result middleStore)
    (heaps : GeneralHeap.HeapRepresents middleMapping middleWorld middleHeap middleStore)
    (mapsExtended : GeneralHeap.LocationMap.Extends mapping middleMapping)
    (worldsExtended : Core.WorldExtends world middleWorld)
    (frame : GeneralHeap.AdministrativePreserved mapping store middleMapping middleStore)
    (nextRestricted : Core.HeapEffects.Expression next)
    (tail : GeneralHeap.EnvRepresents middleMapping middleWorld administrativeContext scope environment coreEnvironment →
      Result tailReturns program context evidence source reasonAt type rest environment middleHeap
        coreEnvironment middleStore next middleMapping middleWorld administrativeContext) :
    Result tailReturns program context evidence source reasonAt type (id :: rest) environment heap
      coreEnvironment store (Core.LocalControl.sequence type computation next) mapping world administrativeContext := by
  cases related with
  | fallthrough branchEnvironments =>
      cases head with
      | control head =>
          obtain ⟨finalContext, finalOutcome, after, finalValue, finalStore, finalMapping, finalWorld,
            tailSource, tailRelated, tailCore, finalHeaps, finalMaps, finalWorlds, tailFrame⟩ :=
            tail (environments.extend mapsExtended worldsExtended)
          have shifted := (nextRestricted.weakenAt 0).evaluation_weakenAt_zero
            (nextRestricted.evaluation_weakenAt_zero tailCore (.inLeft type .unit)) .unit
          exact ⟨_, _, _, _, _, _, _, prepend contains (fun _ _ => notTail) head tailSource,
            tailRelated, Core.LocalControl.sequence_fallthrough type coreHead shifted, finalHeaps,
            mapsExtended.trans finalMaps, worldsExtended.trans finalWorlds, frame.trans tailFrame⟩
  | returned value typed =>
      cases head with
      | control head =>
          exact ⟨_, _, _, _, _, _, _, terminal_head tailReturns rest contains notTail head (.returned _),
            .returned value typed, Core.LocalControl.sequence_returned type coreHead,
            heaps, mapsExtended, worldsExtended, frame⟩
  | uninitialized site location origin =>
      cases head with
      | control head =>
          exact ⟨_, _, _, _, _, _, _, terminal_head tailReturns rest contains notTail head (.fault _),
            .uninitialized site location origin, Core.LocalControl.sequence_failure type coreHead,
            heaps, mapsExtended, worldsExtended, frame⟩
      | fault fault =>
          exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest fault, .uninitialized site location origin,
            Core.LocalControl.sequence_failure type coreHead, heaps, mapsExtended, worldsExtended, frame⟩

/-- A static certificate determines a finite source execution and matching
Core execution for this loop-free fragment. No child evaluation is assumed. -/
theorem Tree.preserves
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree source reasonAt scope context tailReturns statements type code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Result tailReturns program context evidence source reasonAt type statements environment heap
      coreEnvironment store code mapping world administrativeContext := by
  induction tree generalizing environment heap coreEnvironment store world mapping with
  | @nil scope context tailReturns type =>
      exact ⟨_, _, _, _, _, _, _, nil_executes tailReturns program context evidence source environment heap,
        .fallthrough environments, Core.LocalControl.fallthrough_evaluates type coreEnvironment store,
        heaps, .refl _, .refl _, .refl _ _⟩
  | @returnUnit scope context tailReturns id node rest metadata form =>
      exact ⟨_, _, _, _, _, _, _, terminal_head tailReturns rest metadata.contains
        (by intro expression; rw [form]; intro impossible; cases impossible)
        (.returnUnit metadata.contains form) (.returned _), .returned .unit rfl,
        Core.LocalControl.returned_evaluates .unit, heaps, .refl _, .refl _, .refl _ _⟩
  | @returnValue scope context tailReturns id node valueId resultType valueCode valueDepth rest metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              exact ⟨_, _, _, _, _, _, _, terminal_head tailReturns rest metadata.contains
                (by intro expression; rw [form]; intro impossible; cases impossible)
                (.returnValue metadata.contains form sourceEvaluation) (.returned _), .returned staged typed,
                Core.LocalControl.returnValue_success resultType coreEvaluation, heaps, .refl _, .refl _, .refl _ _⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest
                (.returnValue metadata.contains form sourceFault), .uninitialized site location origin,
                Core.LocalControl.returnValue_failure resultType coreEvaluation, heaps, .refl _, .refl _, .refl _ _⟩
  | @tailExpression scope context id node valueId resultType valueCode valueDepth metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              exact ⟨_, _, _, _, _, _, _, .control (.tailExpression metadata.contains form sourceEvaluation),
                .returned staged typed, Core.LocalControl.returnValue_success resultType coreEvaluation,
                heaps, .refl _, .refl _, .refl _ _⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, .fault (.tailExpression metadata.contains form sourceFault),
                .uninitialized site location origin, Core.LocalControl.returnValue_failure resultType coreEvaluation,
                heaps, .refl _, .refl _, .refl _ _⟩
  | @letUninitialized scope context middleContext tailReturns id rest node binder payloadType resultType body
      metadata form binding extension tail ih =>
      have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
          ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
      obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
        tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih nextEnvironments nextHeaps
      have sourceExecution := prepend metadata.contains
        (by intros _ _ expression; rw [form]; intro impossible; cases impossible)
        (.letUninitialized metadata.contains form binding.monomorphic extension allocated) tailSource
      exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated,
        Core.LocalSequence.letUninitialized_evaluates payloadType tailCore, finalHeaps,
        GeneralHeap.LocationMap.Extends.trans ⟨_, rfl⟩ mapsExtended,
        (Core.WorldExtends.trans ⟨_, rfl⟩ extended),
        GeneralHeap.AdministrativePreserved.trans (GeneralHeap.AdministrativePreserved.allocate _ _ _) tailFrame⟩
  | @letInitialized scope context middleContext tailReturns id rest node binder payloadType resultType
      initializer initializerCode body initializerDepth metadata form binding extension value tail ih =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              have binderType : binder.scheme.body = SourceStagedValue.sourceType staged :=
                binding.types.source_unique (typed ▸ stagedTypes staged)
              have allocated : Dynamic.Heap.Allocates heap binder.scheme.body (some (StagedValue.toSource staged))
                  ⟨heap.cells.length⟩
                  ⟨heap.cells ++ [{ type := binder.scheme.body, value := some (StagedValue.toSource staged) }]⟩ := .append
              have cell : CellRepresents
                  { type := binder.scheme.body, value := some (StagedValue.toSource staged) }
                  (.inRight .unit (SourceStagedValue.toCore staged)) payloadType := by
                rw [binderType, ← typed]
                exact .initialized staged
              obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih nextEnvironments nextHeaps
              have shifted := tail.heapEffects.evaluation_weakenAt tailCore 1 (SourceStagedValue.toCore staged)
              simp only [Core.Environment.insertAt] at shifted
              have sourceExecution := prepend metadata.contains
                (by intros _ _ expression; rw [form]; intro impossible; cases impossible)
                (.letInitialized metadata.contains form sourceEvaluation binding.monomorphic extension allocated) tailSource
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated,
                Core.LocalSequence.letInitialized_success (Core.LocalControl.controlType resultType) payloadType coreEvaluation shifted,
                finalHeaps, GeneralHeap.LocationMap.Extends.trans ⟨_, rfl⟩ mapsExtended,
                (Core.WorldExtends.trans ⟨_, rfl⟩ extended),
                GeneralHeap.AdministrativePreserved.trans (GeneralHeap.AdministrativePreserved.allocate _ _ _) tailFrame⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest
                (.letInitializer metadata.contains form binding.monomorphic sourceFault), .uninitialized site location origin,
                Core.LocalSequence.letInitialized_failure (Core.LocalControl.controlType resultType) payloadType coreEvaluation,
                heaps, .refl _, .refl _, .refl _ _⟩
  | @discard scope context tailReturns id rest node nodeType valueId valueType resultType valueCode body valueDepth semicolon
      metadata form notTail statementType value tail ih =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih environments heaps
              have notTailForm : tailReturns = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
                intro isFunction empty expression same
                rw [form] at same
                cases same
                simp [isFunction, empty] at notTail
              have sourceExecution := prepend metadata.contains notTailForm
                (.expression metadata.contains form sourceEvaluation) tailSource
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated,
                Core.LocalSequence.discard_success (Core.LocalControl.controlType resultType) coreEvaluation
                  (tail.heapEffects.evaluation_weakenAt_zero tailCore (SourceStagedValue.toCore staged)),
                finalHeaps, mapsExtended, extended, tailFrame⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest (.expression metadata.contains form sourceFault),
                .uninitialized site location origin,
                Core.LocalSequence.discard_failure (Core.LocalControl.controlType resultType) coreEvaluation,
                heaps, .refl _, .refl _, .refl _ _⟩
  | @assign scope context tailReturns id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth
      metadata form target value tail ih =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨coreLocation, updatedHeap, updatedStore, assignmentSource, lookup, ⟨oldValue, readable⟩,
                written, updatedHeaps, updatedEnvironments, updatedFrame⟩ := equal_assignment environments heaps
                  target.slot target.bare staged typed sourceEvaluation
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih updatedEnvironments updatedHeaps
              have rhsShifted := (GeneralExpressions.Control.readOnly value).evaluation_weakenAt_zero coreEvaluation
                (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation)
              have shifted := weaken_three tail.heapEffects tailCore
                (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) (SourceStagedValue.toCore staged)
              have sourceExecution := prepend metadata.contains
                (by intros _ _ expression; rw [form]; intro impossible; cases impossible)
                (.assignValue metadata.contains form assignmentSource) tailSource
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated,
                Core.LocalSequence.assign_success (Core.LocalControl.controlType resultType) (.var lookup)
                  rhsShifted readable written shifted, finalHeaps, mapsExtended, extended, updatedFrame.trans tailFrame⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨targetLocation, coreTarget, cell, current, sourceLookup, coreLookup, _, read, _, cellRelated⟩ :=
                environments.lookup_heap heaps target.slot
              let captured : Dynamic.ResolvedPlace := {
                location := targetLocation, rootType := cell.type, valueType := assignment.target.type,
                projections := [], selected := cell.value
              }
              have resolved : Dynamic.SourcePlaceResolves program context evidence source environment
                  heap assignment.target captured heap := by
                apply Dynamic.SourcePlaceResolves.intro sourceLookup read
                · rw [target.bare]; exact .nil
                · exact read
                · exact cellRelated.rootInitialValue
                · exact .nil
              have rhsShifted := (GeneralExpressions.Control.readOnly value).evaluation_weakenAt_zero coreEvaluation
                (.cellRef (Core.OptionalCell.cellType payloadType) coreTarget)
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest
                (.assignValue metadata.contains form (.rhs resolved sourceFault)), .uninitialized site location origin,
                Core.LocalSequence.assign_failure (Core.LocalControl.controlType resultType) (.var coreLookup) rhsShifted,
                heaps, .refl _, .refl _, .refl _ _⟩
  | @block scope context tailReturns id rest node nodeType statements resultType blockCode body
      metadata form block tail blockIH tailIH =>
      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
        blockSource, blockRelated, blockCore, finalHeaps, mapsExtended, extended, frame⟩ := blockIH environments heaps
      exact scoped_sequence metadata.contains (by intro expression; rw [form]; intro impossible; cases impossible)
        environments (scoped_block metadata.contains form blockSource) blockRelated blockCore finalHeaps mapsExtended extended frame
        tail.heapEffects (fun nextEnvironments => tailIH nextEnvironments finalHeaps)
  | @ifThen scope context tailReturns id rest node nodeType condition thenBody elseBody resultType
      conditionCode thenCode elseCode body conditionDepth metadata form conditionTree thenTree elseTree tail thenIH elseIH tailIH =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves conditionTree program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases staged with
          | bool boolean =>
              cases sourceEvaluation with
              | value sourceEvaluation =>
                  cases boolean with
                  | true =>
                      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                        branchSource, branchRelated, branchCore, finalHeaps, mapsExtended, extended, frame⟩ := thenIH environments heaps
                      have conditionalCore := Core.LocalControl.conditional_true (elseBranch := elseCode) resultType coreEvaluation
                        (thenTree.heapEffects.evaluation_weakenAt_zero branchCore (.bool true))
                      exact scoped_sequence metadata.contains (by intro expression; rw [form]; intro impossible; cases impossible)
                        environments (scoped_if_true metadata.contains form sourceEvaluation branchSource) branchRelated conditionalCore
                        finalHeaps mapsExtended extended frame tail.heapEffects (fun nextEnvironments => tailIH nextEnvironments finalHeaps)
                  | false =>
                      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                        branchSource, branchRelated, branchCore, finalHeaps, mapsExtended, extended, frame⟩ := elseIH environments heaps
                      have conditionalCore := Core.LocalControl.conditional_false (thenBranch := thenCode) resultType coreEvaluation
                        (elseTree.heapEffects.evaluation_weakenAt_zero branchCore (.bool false))
                      exact scoped_sequence metadata.contains (by intro expression; rw [form]; intro impossible; cases impossible)
                        environments (scoped_if_false metadata.contains form sourceEvaluation branchSource) branchRelated conditionalCore
                        finalHeaps mapsExtended extended frame tail.heapEffects (fun nextEnvironments => tailIH nextEnvironments finalHeaps)
          | unit | word | product => cases typed
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest (.ifCondition metadata.contains form sourceFault),
                .uninitialized site location origin,
                Core.LocalControl.sequence_failure resultType (Core.LocalControl.conditional_failure resultType coreEvaluation),
                heaps, .refl _, .refl _, .refl _ _⟩

/-- The function boundary preserves the source fallthrough outcome explicitly.
For non-Unit results the compiler emits its supplied missing-return token; it
does not turn that source outcome into an invented semantic fault. -/
inductive FinishedOutcomeRepresents (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (administrativeContext : Core.Context) (reasonAt : ExpressionId → Core.Word) (fellThroughReason : Core.Word) :
    Core.Ty → Dynamic.ControlOutcome → Core.Value → Prop where
  | unitFallthrough {scope environment coreEnvironment}
      (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
      FinishedOutcomeRepresents program evidence source mapping world administrativeContext reasonAt fellThroughReason
        .unit (.fallthrough environment) (.inRight .word .unit)
  | missingReturn {scope environment coreEnvironment type} (nonUnit : type ≠ .unit)
      (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
      FinishedOutcomeRepresents program evidence source mapping world administrativeContext reasonAt fellThroughReason
        type (.fallthrough environment) (.inLeft type (.word fellThroughReason))
  | returned (value : SourceStagedValue.Value) {type : Core.Ty} (typed : SourceStagedValue.coreType value = type) :
      FinishedOutcomeRepresents program evidence source mapping world administrativeContext reasonAt fellThroughReason
        type (.returned (StagedValue.toSource value)) (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (site : ExpressionId) (location : Dynamic.Location) (type : Core.Ty)
      {context : Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {root : ExpressionId}
      (origin : ControlExpressions.UninitializedAt program context evidence source environment heap root site location) :
      FinishedOutcomeRepresents program evidence source mapping world administrativeContext reasonAt fellThroughReason
        type (.fault (.uninitializedLocation location)) (.inLeft type (.word (reasonAt site)))

/-- The fallback used by the existing executable function compiler. -/
def fallback (type : Core.Ty) (fellThroughReason : Core.Word) : Core.Expr :=
  if type = .unit then Core.LanguageResult.success .unit
  else Core.LanguageResult.failure type (.word fellThroughReason)

theorem Tree.finish_preserves
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    (tree : Tree source reasonAt scope context true statements type flow)
    (fellThroughReason : Core.Word) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after ∧
      FinishedOutcomeRepresents program evidence source finalMapping finalWorld administrativeContext reasonAt fellThroughReason
        type outcome result ∧
      Core.Evaluates coreEnvironment store (Core.LocalControl.finish type flow (fallback type fellThroughReason)) result finalStore ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore := by
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceEvaluation, related, coreEvaluation, finalHeaps, mapsExtended, worldsExtended, frame⟩ :=
    tree.preserves program evidence environments heaps
  cases related with
  | fallthrough finalEnvironments =>
      by_cases unitType : type = .unit
      · subst type
        refine ⟨_, _, _, _, _, _, _, sourceEvaluation, .unitFallthrough finalEnvironments,
          Core.LocalControl.finish_fallthrough .unit coreEvaluation ?_, finalHeaps, mapsExtended, worldsExtended, frame⟩
        simp only [fallback, ↓reduceIte, Core.LanguageResult.success, Core.Expr.weakenAt]
        exact .inRight .unit
      · refine ⟨_, _, _, _, _, _, _, sourceEvaluation, .missingReturn unitType finalEnvironments,
          Core.LocalControl.finish_fallthrough type coreEvaluation ?_, finalHeaps, mapsExtended, worldsExtended, frame⟩
        simp only [fallback, unitType, ↓reduceIte, Core.LanguageResult.failure, Core.Expr.weakenAt]
        exact .inLeft .word
  | returned value typed =>
      exact ⟨_, _, _, _, _, _, _, sourceEvaluation, .returned value typed,
        Core.LocalControl.finish_returned type coreEvaluation, finalHeaps, mapsExtended, worldsExtended, frame⟩
  | uninitialized site location origin =>
      exact ⟨_, _, _, _, _, _, _, sourceEvaluation, .uninitialized site location type origin,
        Core.LocalControl.finish_failure type coreEvaluation, finalHeaps, mapsExtended, worldsExtended, frame⟩

theorem Tree.hasType_with_administrative
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    (tree : Tree source reasonAt scope context tailReturns statements type flow)
    (wellFormed : Core.Ty.WellFormed [] type) (administrativeContext : Core.Context) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) flow (Core.LocalControl.resultType type) := by
  have respects : Core.Renaming.Respects Core.Renaming.id (SourceCoreLocalCell.coreContext scope)
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) := by
    intro index foundType found
    change (SourceCoreLocalCell.coreContext scope ++ administrativeContext)[index]? = some foundType
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simpa using (tree.hasType wellFormed).rename respects

theorem Tree.finish_hasType
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    (tree : Tree source reasonAt scope context true statements type flow)
    (wellFormed : Core.Ty.WellFormed [] type) (administrativeContext : Core.Context) (fellThroughReason : Core.Word) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      (Core.LocalControl.finish type flow (fallback type fellThroughReason)) (Core.LanguageResult.resultType type) := by
  apply Core.LocalControl.finish_hasType wellFormed (tree.hasType_with_administrative wellFormed administrativeContext)
  unfold fallback
  split
  · rename_i unitType
    subst type
    exact Core.LanguageResult.success_hasType .unit
  · exact Core.LanguageResult.failure_hasType wellFormed .word

end Solcore.SourceSemantics.CoreLowering.ControlStatements
