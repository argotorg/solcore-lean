import Solcore.SourceSemantics.CoreLowering.BasicStatementMeaning
import Solcore.SourceSemantics.CoreLowering.GeneralExpressions
import Solcore.SourceSemantics.CoreLowering.HeapEffectsRenaming
import Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame

/-! Whole basic statement-list correspondence over mapped source cells and
administrative Core cells. The structural statement certificate includes the
source binder-context extensions; it assumes neither child evaluation nor
whole-list evaluation. Extracting those context extensions from arbitrary
successful statement lowering remains a separate obligation. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.GeneralStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- Basic statements may change the heap, but never construct or call a Core
closure. This static restriction permits exact temporary-binder insertion. -/
theorem heapEffects {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth) : Core.HeapEffects.Expression code := by
  induction tree with
  | nil | returnUnit => exact .inRight .unit
  | returnValue _ _ _ value | tailExpression _ _ value =>
      exact .of_readOnly (GeneralExpressions.Basic.readOnly value)
  | letUninitialized _ _ _ _ _ tail => exact .letE (.newCell (.inLeft .unit)) tail
  | letInitialized _ _ _ _ value _ tail =>
      exact .caseE (.of_readOnly (GeneralExpressions.Basic.readOnly value)) (.inLeft .var)
        (.letE (.newCell (.inRight .var)) (tail.weakenAt 1))
  | assign _ _ _ value _ tail =>
      exact .letE .var
        (.caseE ((Core.HeapEffects.Expression.of_readOnly (GeneralExpressions.Basic.readOnly value)).weakenAt 0)
          (.inLeft .var) (.letE (.storeCell .var (.inRight .var)) (((tail.weakenAt 0).weakenAt 0).weakenAt 0)))
  | discard _ _ value _ tail =>
      exact .caseE (.of_readOnly (GeneralExpressions.Basic.readOnly value)) (.inLeft .var) (tail.weakenAt 0)

inductive OutcomeRepresents (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (administrativeContext : Core.Context) (reason : Core.Word) :
    Core.Ty → Dynamic.ControlOutcome → Core.Value → Prop where
  | fallthrough {scope environment coreEnvironment}
      (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
      OutcomeRepresents mapping world administrativeContext reason .unit (.fallthrough environment) (.inRight .word .unit)
  | returned (value : SourceStagedValue.Value) {type : Core.Ty}
      (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents mapping world administrativeContext reason type (.returned (StagedValue.toSource value))
        (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (location : Dynamic.Location) (type : Core.Ty) :
      OutcomeRepresents mapping world administrativeContext reason type (.fault (.uninitializedLocation location))
        (.inLeft type (.word reason))

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

theorem preserves
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      OutcomeRepresents finalMapping finalWorld administrativeContext reason type outcome result ∧
      Core.Evaluates coreEnvironment store code result finalStore ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore := by
  induction tree generalizing environment heap coreEnvironment store world mapping with
  | nil =>
      exact ⟨_, _, _, _, _, _, _, .control .nil, .fallthrough environments,
        .inRight .unit, heaps, .refl _, .refl _, .refl _ _⟩
  | @returnUnit scope context id node rest metadata form =>
      obtain ⟨_, sourceExecution, coreExecution⟩ := returnUnit_prefix (fuel := 0)
        (scope := scope) (reason := reason) metadata.contains (metadata.read unique) form
      exact ⟨_, _, _, _, _, _, _, sourceExecution, .returned .unit rfl, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @returnValue scope context id node valueId resultType valueCode valueDepth rest metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := return_prefix staged metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceEvaluation coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .returned staged typed, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
      | uninitialized faultSite location provenance =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := return_fault metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @tailExpression scope context id node valueId resultType valueCode valueDepth metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := Solcore.SourceSemantics.CoreLowering.BasicStatements.tailExpression staged metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceEvaluation coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .returned staged typed, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
      | uninitialized faultSite location provenance =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := tailExpression_fault metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @letUninitialized scope context middleContext id rest node binder payloadType resultType body bodyDepth
      metadata form binding extension tail ih =>
      have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
          ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
      obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
        tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih nextEnvironments nextHeaps
      have sourceExecution := prepend metadata.contains
        (by intro expression; rw [form]; intro impossible; cases impossible)
        (.letUninitialized metadata.contains form binding.monomorphic extension allocated) tailSource
      have coreExecution := Core.LocalSequence.letUninitialized_evaluates payloadType tailCore
      exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps,
        GeneralHeap.LocationMap.Extends.trans ⟨_, rfl⟩ mapsExtended,
        (Core.WorldExtends.trans ⟨_, rfl⟩ extended),
        GeneralHeap.AdministrativePreserved.trans (GeneralHeap.AdministrativePreserved.allocate _ _ _) tailFrame⟩
  | @letInitialized scope context middleContext id rest node binder payloadType resultType
      initializer initializerCode body initializerDepth bodyDepth metadata form binding extension value tail ih =>
      let fuel := max initializerDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
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
              have shifted := (heapEffects tail).evaluation_weakenAt tailCore 1 (SourceStagedValue.toCore staged)
              simp only [Core.Environment.insertAt] at shifted
              have sourceExecution := prepend metadata.contains
                (by intro expression; rw [form]; intro impossible; cases impossible)
                (.letInitialized metadata.contains form sourceEvaluation binding.monomorphic extension allocated) tailSource
              have coreExecution := Core.LocalSequence.letInitialized_success resultType payloadType coreEvaluation shifted
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps,
                GeneralHeap.LocationMap.Extends.trans ⟨_, rfl⟩ mapsExtended,
        (Core.WorldExtends.trans ⟨_, rfl⟩ extended),
        GeneralHeap.AdministrativePreserved.trans (GeneralHeap.AdministrativePreserved.allocate _ _ _) tailFrame⟩
      | uninitialized faultSite location provenance =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := letInitialized_fault metadata.contains
                (metadata.read unique) form binding.lower binding.monomorphic valueLowered tailLowered
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @discard scope context id rest node valueId valueType resultType valueCode body valueDepth bodyDepth
      metadata form value tail ih =>
      let fuel := max valueDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih environments heaps
              have shifted := (heapEffects tail).evaluation_weakenAt_zero tailCore (SourceStagedValue.toCore staged)
              obtain ⟨_, sourceExecution, coreExecution⟩ := discard_prefix staged metadata.contains
                (metadata.read unique) form valueLowered sourceEvaluation coreEvaluation tailLowered tailSource shifted
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps, mapsExtended, extended, tailFrame⟩
      | uninitialized faultSite location provenance =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := discard_fault metadata.contains
                (metadata.read unique) form valueLowered tailLowered sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @assign scope context id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth bodyDepth
      metadata form target value tail ih =>
      let fuel := max rhsDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨coreLocation, updatedHeap, updatedStore, assignmentSource, lookup, ⟨oldValue, readable⟩,
                written, updatedHeaps, updatedEnvironments, updatedFrame⟩ := equal_assignment environments heaps
                  target.slot target.bare staged typed sourceEvaluation
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih updatedEnvironments updatedHeaps
              have rhsShifted := (GeneralExpressions.Basic.readOnly value).evaluation_weakenAt_zero coreEvaluation
                (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation)
              have shifted := weaken_three (heapEffects tail) tailCore
                (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) (SourceStagedValue.toCore staged)
              obtain ⟨_, sourceExecution, coreExecution⟩ := assign_prefix metadata.contains
                (metadata.read unique) form target.lower valueLowered tailLowered assignmentSource
                lookup rhsShifted readable written tailSource shifted
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps, mapsExtended, extended,
                GeneralHeap.AdministrativePreserved.trans updatedFrame tailFrame⟩
      | uninitialized faultSite location provenance =>
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
              have rhsShifted := (GeneralExpressions.Basic.readOnly value).evaluation_weakenAt_zero coreEvaluation
                (.cellRef (Core.OptionalCell.cellType payloadType) coreTarget)
              obtain ⟨_, sourceExecution, coreExecution⟩ := assign_fault metadata.contains
                (metadata.read unique) form target.lower valueLowered tailLowered
                (.rhs resolved sourceFault) coreLookup rhsShifted
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩

theorem hasType {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth) (administrativeContext : Core.Context) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code (Core.LanguageResult.resultType type) := by
  have respects : Core.Renaming.Respects Core.Renaming.id (SourceCoreLocalCell.coreContext scope)
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) := by
    intro index foundType found
    change (SourceCoreLocalCell.coreContext scope ++ administrativeContext)[index]? = some foundType
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simpa using tree.hasType.rename respects

/-- A static Tree supplies the actual compiler equation and finite execution.
It also preserves initial captures, existing administrative code cells, and
both representation extensions. This is not certificate extraction from an
arbitrary successful statement compiler call. -/
theorem lower_run_preserves
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (compilationFuel : Nat) (enough : depth ≤ compilationFuel)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    SourceCoreBasic.lowerStatements compilationFuel source scope statements type reason = .ok code ∧
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code =
      some (Core.LanguageResult.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      OutcomeRepresents finalMapping finalWorld administrativeContext reason type outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment store) =
        .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment store) =
        .done actual actualStore → actual = result ∧ actualStore = finalStore) := by
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceExecution, related, coreExecution, finalHeaps, mapsExtended, worldsExtended, administrativePreserved⟩ :=
    preserves tree unique program evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreExecution
  refine ⟨tree.lower unique compilationFuel enough, Core.infer_complete (hasType tree administrativeContext),
    finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, finalHeaps, mapsExtended, worldsExtended,
    environments.extend mapsExtended worldsExtended, administrativePreserved, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreExecution

end Solcore.SourceSemantics.CoreLowering.GeneralStatements
