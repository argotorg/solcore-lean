import Solcore.SourceSemantics.CoreLowering.LoopStatementTree
import Solcore.SourceSemantics.CoreLowering.LoopStatementLayout
import Solcore.SourceSemantics.CoreLowering.LoopFiniteComposition
import Solcore.SourceSemantics.CoreLowering.LoopAdministration
import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews
import Solcore.SourceSemantics.CoreLowering.ScalarAssignmentReflection

/-! Successful finite statement traces for the default while profile. Every
temporary lexical layout is quantified explicitly so generated nested loop
closures capture the actual environment in which they are installed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements
open Internal ScalarStatementViews

def SuccessResult (type : Core.Ty) (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (store : Core.Store) (after : Dynamic.Heap) (outcome : Dynamic.ControlOutcome)
    (actual : Core.Environment) (code : Core.Expr) : Prop :=
  ∃ result finalStore finalMapping finalWorld,
    ControlRepresents type outcome result ∧ Core.Evaluates actual store code result finalStore ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

def Success (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (context : Context) (functionMode : Bool)
    (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store}
    {finalContext : Context} {outcome : Dynamic.ControlOutcome},
    Core.Ty.WellFormed [] type →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    ListExecutes functionMode program context evidence source environment heap statements finalContext outcome after →
    SuccessResult type mapping world store after outcome actual (code.rename ξ)

private theorem expression_success
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store} {value : Dynamic.Value}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (executed : Dynamic.ExpressionEvaluates program context evidence source environment heap id value after) :
    after = heap ∧ ∃ staged : SourceStagedValue.Value,
      value = StagedValue.toSource staged ∧ SourceStagedValue.coreType staged = type ∧
      Core.Evaluates actual store (code.rename ξ) (.inRight .word (SourceStagedValue.toCore staged)) store := by
  obtain ⟨rfl, staged, same, typed, evaluated⟩ :=
    ScalarExpressionReflection.Primitive.source_success tree unique environments heaps executed
  exact ⟨rfl, staged, same, typed, (GeneralExpressions.Primitive.readOnly tree).evaluation_rename evaluated layout.agrees⟩

theorem success_nil (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (context : Context) (mode : Bool) (type : Core.Ty) :
    Success program evidence source scope context mode [] type (Core.LocalLoop.fallthrough type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    _ _ heaps _ executed
  obtain ⟨rfl, rfl, rfl⟩ := nil_view mode executed
  exact ⟨_, store, mapping, world, .fallthrough environment, Core.LocalLoop.fallthrough_evaluates type actual store,
    heaps, .refl _, .refl _, .refl _ _⟩

theorem success_breaking
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type : Core.Ty}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .breakStmt) :
    Success program evidence source scope context mode (id :: rest) type (Core.LocalLoop.breaking type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    _ _ heaps _ executed
  rcases cons_view mode unique contains (by intros; simp [form]) executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
  · obtain ⟨_, impossible, _⟩ := breaking unique contains form head
    contradiction
  · obtain ⟨rfl, rfl, rfl⟩ := breaking unique contains form head
    exact ⟨_, store, mapping, world, .breaking environment, Core.LocalLoop.breaking_evaluates type actual store,
      heaps, .refl _, .refl _, .refl _ _⟩

theorem success_continuing
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type : Core.Ty}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .continueStmt) :
    Success program evidence source scope context mode (id :: rest) type (Core.LocalLoop.continuing type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    _ _ heaps _ executed
  rcases cons_view mode unique contains (by intros; simp [form]) executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
  · obtain ⟨_, impossible, _⟩ := continuing unique contains form head
    contradiction
  · obtain ⟨rfl, rfl, rfl⟩ := continuing unique contains form head
    exact ⟨_, store, mapping, world, .continuing environment, Core.LocalLoop.continuing_evaluates type actual store,
      heaps, .refl _, .refl _, .refl _ _⟩

theorem success_returnUnit
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt none) :
    Success program evidence source scope context mode (id :: rest) .unit (Core.LocalLoop.returned .unit) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    _ _ heaps _ executed
  rcases cons_view mode unique contains (by intros; simp [form]) executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
  · obtain ⟨_, impossible, _⟩ := returnUnit unique contains form head
    contradiction
  · obtain ⟨rfl, rfl, rfl⟩ := returnUnit unique contains form head
    exact ⟨_, store, mapping, world, .returned .unit rfl, Core.LocalLoop.returned_evaluates .unit,
      heaps, .refl _, .refl _, .refl _ _⟩

theorem success_returnValue
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type : Core.Ty} {valueId : ExpressionId} {code : Core.Expr} {depth : Nat}
    {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some valueId))
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId type code depth) :
    Success program evidence source scope context mode (id :: rest) type (Core.LocalLoop.returnValue type code) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    _ environments heaps layout executed
  rcases cons_view mode unique contains (by intros; simp [form]) executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
  · obtain ⟨_, _, impossible, _⟩ := returnValue unique contains form head
    contradiction
  · obtain ⟨rfl, value, rfl, evaluated⟩ := returnValue unique contains form head
    obtain ⟨rfl, staged, rfl, typed, core⟩ := expression_success tree unique environments heaps layout evaluated
    refine ⟨_, store, mapping, world, .returned staged typed, ?_, heaps, .refl _, .refl _, .refl _ _⟩
    simpa only [Core.LoopRenaming.returnValue] using Core.LocalLoop.returnValue_success type core


private theorem stagedTyped (value : SourceStagedValue.Value) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world (SourceStagedValue.toCore value) (SourceStagedValue.coreType value) :=
  GeneralHeap.ValueRepresents.runtime_hasType (mapping := []) (.scalar value)

private theorem notTail_expression {mode semicolon : Bool} {rest : List StatementId}
    {node : StatementNode} {valueId : ExpressionId}
    (form : node.form = .expression valueId semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false) :
    mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
  intro sameMode empty expression impossible
  rw [form] at impossible
  cases impossible
  simp [sameMode, empty] at notTail

theorem success_discard
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode semicolon : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type valueType : Core.Ty} {valueId : ExpressionId} {code body : Core.Expr} {depth : Nat}
    {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression valueId semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId valueType code depth)
    (tail : Success program evidence source scope context mode rest type body) :
    Success program evidence source scope context mode (id :: rest) type
      (Core.LocalSequence.discard (Core.LocalLoop.controlType type) code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  rcases cons_view mode unique contains (notTail_expression form notTail) executed with ⟨_, nextEnv, middle, head, tailSource⟩ | ⟨head, terminal⟩
  · obtain ⟨rfl, sameEnv, sourceValue, evaluated⟩ := expression unique contains form head
    cases sameEnv
    obtain ⟨rfl, staged, _, _, core⟩ := expression_success tree unique environments heaps layout evaluated
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, maps, worlds, frame⟩ :=
      tail wellFormed environments heaps (layout.insert (stagedTyped staged world)) tailSource
    refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, worlds, frame⟩
    simpa only [Core.LoopRenaming.discard] using
      Core.LocalSequence.discard_success (Core.LocalLoop.controlType type) core (by simpa only [rename_insert] using tailCore)
  · obtain ⟨_, rfl, _⟩ := expression unique contains form head
    cases terminal

theorem success_assign
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type payload : Core.Ty} {rhs : ExpressionId} {code body : Core.Expr} {depth index : Nat}
    {assignment : AssignmentResolution} {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .assignValue assignment .equal rhs)
    (target : AssignmentCertificate source scope assignment .equal index payload)
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payload code depth)
    (tail : Success program evidence source scope context mode rest type body) :
    Success program evidence source scope context mode (id :: rest) type
      (Core.LocalSequence.assign (Core.LocalLoop.controlType type) (.var index) code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  rcases cons_view mode unique contains (by intros; simp [form]) executed with ⟨_, nextEnv, middle, head, tailSource⟩ | ⟨head, terminal⟩
  · obtain ⟨rfl, sameEnv, updated, assigned⟩ := assignValue unique contains form head
    cases sameEnv
    obtain ⟨staged, location, updatedStore, _, typed, rhsCore, lookup, ⟨old, readable⟩, written, updatedHeaps, writeFrame⟩ :=
      ScalarAssignmentReflection.source_success tree unique target.slot target.bare environments heaps assigned
    have actualLookup := layout.agrees lookup
    have referenceTyped : Core.RuntimeValueHasType world
        (.cellRef (Core.OptionalCell.cellType payload) location) (Core.OptionalCell.referenceType payload) := by
      obtain ⟨found, foundEq, foundTyped⟩ := Core.RuntimeEnvironmentHasTypes.lookup layout.typed
        (layout.respects (SourceCoreLocalCell.lookup?_context target.slot))
      rw [actualLookup] at foundEq
      cases foundEq
      exact foundTyped
    have nextLayout := ((layout.insert referenceTyped).insert (stagedTyped staged world)).insert Core.RuntimeValueHasType.unit
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, maps, worlds, frame⟩ :=
      tail wellFormed environments updatedHeaps nextLayout tailSource
    have renamedRhs := (GeneralExpressions.Primitive.readOnly tree).evaluation_rename rhsCore layout.agrees
    have shiftedRhs := ((GeneralExpressions.Primitive.readOnly tree).rename ξ).evaluation_weakenAt_zero renamedRhs
      (.cellRef (Core.OptionalCell.cellType payload) location)
    refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, worlds, writeFrame.trans frame⟩
    simpa only [Core.LoopRenaming.assign, Core.Expr.rename] using
      Core.LocalSequence.assign_success (Core.LocalLoop.controlType type) (.var actualLookup) shiftedRhs readable written
        (by simpa only [rename_insert] using tailCore)
  · obtain ⟨_, rfl, _⟩ := assignValue unique contains form head
    cases terminal

theorem success_letUninitialized
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context middleContext : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type payload : Core.Ty} {body : Core.Expr} {binder : TypedBinder}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .letDecl binder none) (binding : BinderCertificate source scope binder payload)
    (extension : BinderExtends source.owner context binder middleContext)
    (tail : Success program evidence source ((binder.id, payload) :: scope) middleContext mode rest type body) :
    Success program evidence source scope context mode (id :: rest) type
      (Core.LocalSequence.letUninitialized payload body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  rcases cons_view mode unique contains (by intros; simp [form]) executed with ⟨_, nextEnv, middle, head, tailSource⟩ | ⟨head, terminal⟩
  · obtain ⟨otherExtension, location, sameEnv, allocated⟩ := letUninitialized unique contains form head
    cases sameEnv
    have sameContext := Dynamic.BinderExtends.functional otherExtension extension
    subst_vars
    obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
    have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
    have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
      rw [← heaps.runtime_hasTypes.length_eq]; simp
    have nextLayout := (layout.extend worlds).bind (Core.RuntimeValueHasType.cellRef found)
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, maps, futureWorlds, frame⟩ :=
      tail wellFormed nextEnvironments nextHeaps nextLayout tailSource
    refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps,
      (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps, worlds.trans futureWorlds,
      (GeneralHeap.AdministrativePreserved.allocate mapping store (.inLeft payload .unit)).trans frame⟩
    simpa only [Core.LoopRenaming.letUninitialized] using Core.LocalSequence.letUninitialized_evaluates payload tailCore
  · obtain ⟨_, _, rfl, _⟩ := letUninitialized unique contains form head
    cases terminal

theorem success_letInitialized
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context middleContext : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type payload : Core.Ty} {code body : Core.Expr} {binder : TypedBinder}
    {initializer : ExpressionId} {depth : Nat} {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .letDecl binder (some initializer)) (binding : BinderCertificate source scope binder payload)
    (extension : BinderExtends source.owner context binder middleContext)
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payload code depth)
    (tail : Success program evidence source ((binder.id, payload) :: scope) middleContext mode rest type body) :
    Success program evidence source scope context mode (id :: rest) type
      (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType type) payload code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  rcases cons_view mode unique contains (by intros; simp [form]) executed with ⟨_, nextEnv, middle, head, tailSource⟩ | ⟨head, terminal⟩
  · obtain ⟨otherExtension, location, sourceValue, initializedHeap, sameEnv, evaluated, allocated⟩ :=
      letInitialized unique contains form binding.monomorphic head
    cases sameEnv
    have sameContext := Dynamic.BinderExtends.functional otherExtension extension
    subst_vars
    obtain ⟨rfl, staged, rfl, typed, initializerCore⟩ := expression_success tree unique environments heaps layout evaluated
    have sameSource : binder.scheme.body = SourceStagedValue.sourceType staged :=
      binding.types.source_unique (typed ▸ stagedTypes staged)
    have cell : CellRepresents {type := binder.scheme.body, value := some (StagedValue.toSource staged)}
        (.inRight .unit (SourceStagedValue.toCore staged)) payload := by
      rw [sameSource, ← typed]; exact .initialized staged
    obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
    have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
    have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
      rw [← heaps.runtime_hasTypes.length_eq]; simp
    have nextLayout := ((layout.extend worlds).insert (stagedTyped staged _)).bind (Core.RuntimeValueHasType.cellRef found)
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, maps, futureWorlds, frame⟩ :=
      tail wellFormed nextEnvironments nextHeaps nextLayout tailSource
    refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps,
      (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps, worlds.trans futureWorlds,
      (GeneralHeap.AdministrativePreserved.allocate mapping store (.inRight .unit (SourceStagedValue.toCore staged))).trans frame⟩
    simpa only [Core.LoopRenaming.letInitialized] using
      Core.LocalSequence.letInitialized_success (Core.LocalLoop.controlType type) payload initializerCore
        (by simpa only [rename_insert_lift, Core.Store.allocate] using tailCore)
  · obtain ⟨_, _, _, _, rfl, _, _⟩ := letInitialized unique contains form binding.monomorphic head
    cases terminal


private theorem ControlRepresents.restore {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {value : Core.Value}
    (related : ControlRepresents type outcome value) (environment : Dynamic.Environment) :
    ControlRepresents type (Dynamic.restoreControl environment outcome) value := by
  cases related with
  | fallthrough => exact .fallthrough environment
  | returned value typed => exact .returned value typed
  | breaking => exact .breaking environment
  | continuing => exact .continuing environment

private theorem restored_fallthrough {environment next : Dynamic.Environment} {outcome : Dynamic.ControlOutcome}
    (same : Dynamic.restoreControl environment outcome = .fallthrough next) : next = environment := by
  cases outcome <;> simp_all [Dynamic.restoreControl]

/-- A scoped head restores the lexical context and local names before the
following statement; it may still allocate cells that remain in the heap. -/
def ScopedSuccess (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (context : Context) (id : StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store}
    {finalContext : Context} {outcome : Dynamic.ControlOutcome},
    Core.Ty.WellFormed [] type →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Dynamic.StatementExecutes program context evidence source environment heap id finalContext outcome after →
    finalContext = context ∧ (∀ next, outcome = .fallthrough next → next = environment) ∧
    SuccessResult type mapping world store after outcome actual (code.rename ξ)

theorem success_scoped
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type : Core.Ty} {code body : Core.Expr}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (notTail : ∀ value, node.form ≠ .expression value false)
    (head : ScopedSuccess program evidence source scope context id type code)
    (tail : Success program evidence source scope context mode rest type body) :
    Success program evidence source scope context mode (id :: rest) type (Core.LocalLoop.sequence type code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  rcases cons_view mode unique contains (fun _ _ => notTail) executed with ⟨_, nextEnv, middle, headSource, tailSource⟩ | ⟨headSource, terminal⟩
  · obtain ⟨rfl, sameEnv, result, middleStore, middleMapping, middleWorld, related, headCore, middleHeaps, maps, worlds, frame⟩ :=
      head wellFormed environments heaps layout headSource
    have envEq := sameEnv nextEnv rfl
    subst nextEnv
    cases related with
    | fallthrough =>
      have shiftedLayout := (((layout.extend worlds).insert
        (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType) (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
        (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
      obtain ⟨result, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, mapsAgain, worldsAgain, frameAgain⟩ :=
        tail wellFormed (environments.extend maps worlds) middleHeaps shiftedLayout tailSource
      refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps,
        maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩
      simpa only [Core.LoopRenaming.sequence] using
        Core.LocalLoop.sequence_fallthrough type headCore (by simpa only [rename_insert] using tailCore)
  · obtain ⟨rfl, _, result, finalStore, finalMapping, finalWorld, related, headCore, finalHeaps, maps, worlds, frame⟩ :=
      head wellFormed environments heaps layout headSource
    refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, worlds, frame⟩
    cases related with
    | fallthrough => cases terminal
    | returned => simpa only [Core.LoopRenaming.sequence] using Core.LocalLoop.sequence_returned type headCore
    | breaking => simpa only [Core.LoopRenaming.sequence, Core.LocalLoop.breakingValue] using Core.LocalLoop.sequence_transfer type headCore
    | continuing => simpa only [Core.LoopRenaming.sequence, Core.LocalLoop.continuingValue] using Core.LocalLoop.sequence_transfer type headCore

theorem success_block_head
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {id : StatementId} {statements : List StatementId}
    {node : StatementNode} {type : Core.Ty} {code : Core.Expr}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .block statements)
    (body : Success program evidence source scope context false statements type code) :
    ScopedSuccess program evidence source scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  obtain ⟨rfl, innerContext, innerOutcome, rfl, inner⟩ := block unique contains form executed
  refine ⟨rfl, fun _ same => restored_fallthrough same, ?_⟩
  obtain ⟨result, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
    body wellFormed environments heaps layout inner
  exact ⟨result, finalStore, finalMapping, finalWorld, ControlRepresents.restore related environment, core, finalHeaps, maps, worlds, frame⟩

theorem success_if_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {id : StatementId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {node : StatementNode} {type : Core.Ty} {condition : ExpressionId}
    {conditionCode thenCode elseCode : Core.Expr} {depth : Nat} {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (thenCorrect : Success program evidence source scope context false thenBody type thenCode)
    (elseCorrect : Success program evidence source scope context false (elseBody.getD []) type elseCode) :
    ScopedSuccess program evidence source scope context id type (Core.LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  obtain ⟨rfl, boolean, middle, innerContext, innerOutcome, conditionSource, rfl, branch⟩ := ifThen unique contains form executed
  obtain ⟨rfl, staged, same, typed, conditionCore⟩ := expression_success conditionTree unique environments heaps layout conditionSource
  obtain ⟨other, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
  cases same
  refine ⟨rfl, fun _ same => restored_fallthrough same, ?_⟩
  cases boolean with
  | false =>
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, branchCore, finalHeaps, maps, worlds, frame⟩ :=
      elseCorrect wellFormed environments heaps (layout.insert (Core.RuntimeValueHasType.bool (value := false))) branch
    refine ⟨result, finalStore, finalMapping, finalWorld, ControlRepresents.restore related environment, ?_, finalHeaps, maps, worlds, frame⟩
    rw [Core.LoopRenaming.conditional]
    exact Core.LocalControl.choose_false (Core.LocalLoop.controlType type)
      conditionCore (by simpa only [rename_insert] using branchCore)
  | true =>
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, branchCore, finalHeaps, maps, worlds, frame⟩ :=
      thenCorrect wellFormed environments heaps (layout.insert (Core.RuntimeValueHasType.bool (value := true))) branch
    refine ⟨result, finalStore, finalMapping, finalWorld, ControlRepresents.restore related environment, ?_, finalHeaps, maps, worlds, frame⟩
    rw [Core.LoopRenaming.conditional]
    exact Core.LocalControl.choose_true (Core.LocalLoop.controlType type)
      conditionCore (by simpa only [rename_insert] using branchCore)

theorem success_while_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {id : StatementId} {statements : List StatementId}
    {node : StatementNode} {type : Core.Ty} {condition : ExpressionId} {conditionCode bodyCode : Core.Expr}
    {depth : Nat} {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .whileLoop condition statements)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Success program evidence source scope context false statements type bodyCode) :
    ScopedSuccess program evidence source scope context id type (Core.LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  obtain ⟨rfl, innerContext, innerOutcome, rfl, loop⟩ := whileLoop unique contains form executed
  obtain ⟨installedHeaps, extended, unmapped, selfTyped, installed, installFrame⟩ :=
    LoopAdministration.install selfReason heaps layout.typed wellFormed
      (conditionTree.hasType.rename layout.respects) ((bodyTyped wellFormed).rename layout.respects)
      (Core.LocalLoop.fallthrough_hasType wellFormed)
  have bodyPreserves : BodyPreserves program finalContext evidence source scope admin environment canonical actual actualContext
      type store.length statements (bodyCode.rename ξ) := by
    intro bodyMapping bodyWorld bodyHeap bodyAfter bodyStore bodyFinalContext bodyOutcome
      bodyEnvironments bodyHeaps actualTyped locationTyped bodySource
    have bodyLayout : Layout bodyWorld (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ :=
      ⟨layout.respects, layout.agrees, actualTyped⟩
    have shiftedLayout := ((bodyLayout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert
      Core.RuntimeValueHasType.unit).insert (Core.RuntimeValueHasType.bool (value := true))
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
      bodyCorrect wellFormed bodyEnvironments bodyHeaps shiftedLayout bodySource
    exact ⟨result, finalStore, finalMapping, finalWorld, related,
      by simpa only [rename_insert, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, Core.LoopExecution.bodyCode] using core, finalHeaps, maps, worlds, frame⟩
  obtain ⟨result, finalStore, finalMapping, finalWorld, related, trace, finalHeaps, maps, worlds, frame⟩ :=
    Internal.while_success loop conditionTree unique layout.agrees bodyPreserves
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed
  refine ⟨rfl, fun _ same => restored_fallthrough same, result, finalStore, finalMapping, finalWorld,
    ControlRepresents.restore related environment, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  simpa only [Core.LoopRenaming.whileLoop] using trace.whileLoop_evaluates


private theorem tailExpression_view
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {valueId : ExpressionId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression valueId false)
    (executed : Dynamic.FunctionStatementsExecute program context evidence source environment heap [id] finalContext outcome after) :
    finalContext = context ∧ ∃ value, outcome = .returned value ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap valueId value after := by
  have shape : ∀ other, ContainsStatement source id other → other.form = .expression valueId false := by
    intro other otherContains
    have same : other = node := Option.some.inj
      ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
    exact same ▸ form
  cases executed with
  | tailExpression otherContains otherForm evaluated =>
    have actualForm := shape _ otherContains
    rw [otherForm] at actualForm
    cases actualForm
    exact ⟨rfl, _, rfl, evaluated⟩
  | singleton otherContains notTail _ => exact False.elim (notTail valueId (shape _ otherContains))

theorem success_tailExpression
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {id : StatementId}
    {node : StatementNode} {type : Core.Ty} {valueId : ExpressionId} {code : Core.Expr} {depth : Nat}
    {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression valueId false)
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId type code depth) :
    Success program evidence source scope context true [id] type (Core.LocalLoop.returnValue type code) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    _ environments heaps layout executed
  obtain ⟨rfl, value, rfl, evaluated⟩ := tailExpression_view unique contains form executed
  obtain ⟨rfl, staged, rfl, typed, core⟩ := expression_success tree unique environments heaps layout evaluated
  refine ⟨_, store, mapping, world, .returned staged typed, ?_, heaps, .refl _, .refl _, .refl _ _⟩
  simpa only [Core.LoopRenaming.returnValue] using Core.LocalLoop.returnValue_success type core

/-- Every finite successful source execution of this complete static while
profile has a Core execution. Child source executions are taken from the
supplied independent derivation; the static tree assumes none of them. -/
theorem Tree.source_success
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {mode : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context mode statements type code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    Success program evidence source scope context mode statements type code := by
  induction tree with
  | nil => exact success_nil program evidence source _ _ _ _
  | breaking _ metadata form => exact success_breaking unique metadata.contains form
  | continuing _ metadata form => exact success_continuing unique metadata.contains form
  | returnUnit _ metadata form => exact success_returnUnit unique metadata.contains form
  | returnValue _ metadata form value => exact success_returnValue unique metadata.contains form value
  | tailExpression metadata form value => exact success_tailExpression unique metadata.contains form value
  | letUninitialized metadata form binding extension _ ih =>
    exact success_letUninitialized unique metadata.contains form binding extension ih
  | letInitialized metadata form binding extension value _ ih =>
    exact success_letInitialized unique metadata.contains form binding extension value ih
  | assign metadata form target value _ ih => exact success_assign unique metadata.contains form target value ih
  | discard metadata form notTail _ value _ ih => exact success_discard unique metadata.contains form notTail value ih
  | block metadata form _ _ bodyIH tailIH =>
    exact success_scoped unique metadata.contains (by intro value; simp [form])
      (success_block_head unique metadata.contains form bodyIH) tailIH
  | ifThen metadata form condition _ _ _ thenIH elseIH tailIH =>
    exact success_scoped unique metadata.contains (by intro value; simp [form])
      (success_if_head unique metadata.contains form condition thenIH elseIH) tailIH
  | whileLoop metadata form condition loopBody _ bodyIH tailIH =>
    exact success_scoped unique metadata.contains (by intro value; simp [form])
      (success_while_head unique metadata.contains form condition loopBody.hasType bodyIH) tailIH

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
