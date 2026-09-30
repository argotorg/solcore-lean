import Solcore.SourceSemantics.CoreLowering.LoopStatementSuccess

/-! Finite semantic-fault reflection for the static while profile. Evidence
coverage is required for retained integer dictionaries. Fault traces and
successful prefixes come from the independent source judgments. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements
open Internal ScalarStatementViews

def FaultResult (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) (mapping : GeneralHeap.LocationMap)
    (world : Core.StoreTyping) (store : Core.Store) (after : Dynamic.Heap) (reason : Dynamic.SemanticFault)
    (actual : Core.Environment) (code : Core.Expr) : Prop :=
  ∃ resultReason finalStore finalMapping finalWorld,
    FaultRepresents program evidence source reasonAt reason resultReason ∧
    Core.Evaluates actual store code (.inLeft (Core.LocalLoop.controlType type) (.word resultReason)) finalStore ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

def Fault (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (functionMode : Bool) (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store}
    {finalContext : Context} {reason : Dynamic.SemanticFault},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    ListFaults functionMode program context evidence source environment heap statements finalContext reason after →
    FaultResult program evidence source reasonAt type mapping world store after reason actual (code.rename ξ)

private theorem stagedTypedFault (value : SourceStagedValue.Value) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world (SourceStagedValue.toCore value) (SourceStagedValue.coreType value) :=
  GeneralHeap.ValueRepresents.runtime_hasType (mapping := []) (.scalar value)

private theorem expression_success_prefix
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

private theorem expression_fault
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store} {reason : Dynamic.SemanticFault}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (fault : Dynamic.ExpressionFaults program context evidence source environment heap id reason after) :
    after = heap ∧ ∃ word,
      FaultRepresents program evidence source reasonAt reason word ∧
      Core.Evaluates actual store (code.rename ξ) (.inLeft type (.word word)) store := by
  obtain ⟨rfl, site, location, rfl, origin, evaluated⟩ :=
    ScalarExpressionReflection.Primitive.source_fault tree unique valid covers environments heaps fault
  exact ⟨rfl, reasonAt site, .uninitialized site location origin,
    (GeneralExpressions.Primitive.readOnly tree).evaluation_rename evaluated layout.agrees⟩

private theorem valid_extend
    {compilation : SourceCorePrimitive.Context} {owner : Resolved.DeclarationId}
    {context middle : Context} {binder : TypedBinder}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (extension : BinderExtends owner context binder middle) :
    PrimitiveExpressions.ContextValid compilation middle := by
  cases extension
  exact ⟨valid.ledger, valid.valid.transport rfl rfl rfl⟩

private theorem covers_extend
    {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId}
    {context middle : Context} {binder : TypedBinder}
    (covers : evidence.Covers context) (extension : BinderExtends owner context binder middle) :
    evidence.Covers middle := covers.transportBinders (.cons extension (.nil _))

private theorem notTail_expression_fault {mode semicolon : Bool} {rest : List StatementId}
    {node : StatementNode} {valueId : ExpressionId}
    (form : node.form = .expression valueId semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false) :
    mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
  intro sameMode empty expression impossible
  rw [form] at impossible
  cases impossible
  simp [sameMode, empty] at notTail

theorem fault_nil (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (mode : Bool) (type : Core.Ty) :
    Fault compilation program evidence source reasonAt scope context mode [] type (Core.LocalLoop.fallthrough type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    _ _ _ _ _ _ fault
  exact False.elim (nil_cannot_fault mode fault)

theorem fault_breaking
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node) (form : node.form = .breakStmt) :
    Fault compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.breaking type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    _ _ _ _ _ _ fault
  rcases cons_fault_view mode unique contains (by intros; simp [form]) fault with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
  · exact False.elim (breaking_cannot_fault unique contains form head)
  · obtain ⟨_, impossible, _⟩ := breaking unique contains form head
    contradiction

theorem fault_continuing
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node) (form : node.form = .continueStmt) :
    Fault compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.continuing type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    _ _ _ _ _ _ fault
  rcases cons_fault_view mode unique contains (by intros; simp [form]) fault with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
  · exact False.elim (continuing_cannot_fault unique contains form head)
  · obtain ⟨_, impossible, _⟩ := continuing unique contains form head
    contradiction

theorem fault_returnUnit
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node) (form : node.form = .returnStmt none) :
    Fault compilation program evidence source reasonAt scope context mode (id :: rest) .unit (Core.LocalLoop.returned .unit) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    _ _ _ _ _ _ fault
  rcases cons_fault_view mode unique contains (by intros; simp [form]) fault with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
  · exact False.elim (returnUnit_cannot_fault unique contains form head)
  · obtain ⟨_, impossible, _⟩ := returnUnit unique contains form head
    contradiction

theorem fault_returnValue
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type : Core.Ty} {valueId : ExpressionId} {code : Core.Expr} {depth : Nat}
    {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some valueId))
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId type code depth) :
    Fault compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.returnValue type code) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    _ valid covers environments heaps layout fault
  rcases cons_fault_view mode unique contains (by intros; simp [form]) fault with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
  · obtain ⟨rfl, word, related, core⟩ := expression_fault tree unique valid covers environments heaps layout
      (returnValue_fault unique contains form head)
    refine ⟨word, store, mapping, world, related, ?_, heaps, .refl _, .refl _, .refl _ _⟩
    simpa only [Core.LoopRenaming.returnValue] using Core.LocalLoop.returnValue_failure type core
  · obtain ⟨_, _, impossible, _⟩ := returnValue unique contains form head
    contradiction

theorem fault_discard
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode semicolon : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type valueType : Core.Ty} {valueId : ExpressionId} {code body : Core.Expr} {depth : Nat}
    {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression valueId semicolon) (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId valueType code depth)
    (tail : Fault compilation program evidence source reasonAt scope context mode rest type body) :
    Fault compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.discard (Core.LocalLoop.controlType type) code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    wellFormed valid covers environments heaps layout fault
  rcases cons_fault_view mode unique contains (notTail_expression_fault form notTail) fault with ⟨_, head⟩ | ⟨_, nextEnv, middle, head, tailSource⟩
  · obtain ⟨rfl, word, related, core⟩ := expression_fault tree unique valid covers environments heaps layout
      (ScalarStatementViews.expression_fault unique contains form head)
    refine ⟨word, store, mapping, world, related, ?_, heaps, .refl _, .refl _, .refl _ _⟩
    simpa only [Core.LoopRenaming.discard] using Core.LocalSequence.discard_failure (Core.LocalLoop.controlType type) core
  · obtain ⟨rfl, sameEnv, sourceValue, evaluated⟩ := expression unique contains form head
    cases sameEnv
    obtain ⟨rfl, staged, _, _, core⟩ := expression_success_prefix tree unique environments heaps layout evaluated
    obtain ⟨word, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, maps, worlds, frame⟩ :=
      tail wellFormed valid covers environments heaps (layout.insert (stagedTypedFault staged world)) tailSource
    refine ⟨word, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, worlds, frame⟩
    simpa only [Core.LoopRenaming.discard] using
      Core.LocalSequence.discard_success (Core.LocalLoop.controlType type) core (by simpa only [rename_insert] using tailCore)


theorem fault_assign
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type payload : Core.Ty} {rhs : ExpressionId} {code body : Core.Expr} {depth index : Nat}
    {assignment : AssignmentResolution} {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .assignValue assignment .equal rhs)
    (target : AssignmentCertificate source scope assignment .equal index payload)
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payload code depth)
    (tail : Fault compilation program evidence source reasonAt scope context mode rest type body) :
    Fault compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.assign (Core.LocalLoop.controlType type) (.var index) code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    wellFormed valid covers environments heaps layout fault
  rcases cons_fault_view mode unique contains (by intros; simp [form]) fault with ⟨_, head⟩ | ⟨_, nextEnv, middle, head, tailSource⟩
  · obtain ⟨rfl, site, location, rfl, origin, rhsCore⟩ := ScalarAssignmentReflection.source_fault tree unique valid covers
      target.slot target.bare environments heaps (assignValue_fault unique contains form head)
    obtain ⟨_, coreLocation, _, lookup, _⟩ := environments.lookup target.slot
    have renamed := (GeneralExpressions.Primitive.readOnly tree).evaluation_rename rhsCore layout.agrees
    have shifted := ((GeneralExpressions.Primitive.readOnly tree).rename ξ).evaluation_weakenAt_zero renamed
      (.cellRef (Core.OptionalCell.cellType payload) coreLocation)
    refine ⟨reasonAt site, store, mapping, world, .uninitialized site location origin, ?_, heaps, .refl _, .refl _, .refl _ _⟩
    simpa only [Core.LoopRenaming.assign, Core.Expr.rename] using
      Core.LocalSequence.assign_failure (Core.LocalLoop.controlType type) (.var (layout.agrees lookup)) shifted
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
    have nextLayout := ((layout.insert referenceTyped).insert (stagedTypedFault staged world)).insert Core.RuntimeValueHasType.unit
    obtain ⟨word, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, maps, worlds, frame⟩ :=
      tail wellFormed valid covers environments updatedHeaps nextLayout tailSource
    have renamedRhs := (GeneralExpressions.Primitive.readOnly tree).evaluation_rename rhsCore layout.agrees
    have shiftedRhs := ((GeneralExpressions.Primitive.readOnly tree).rename ξ).evaluation_weakenAt_zero renamedRhs
      (.cellRef (Core.OptionalCell.cellType payload) location)
    refine ⟨word, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, worlds, writeFrame.trans frame⟩
    simpa only [Core.LoopRenaming.assign, Core.Expr.rename] using
      Core.LocalSequence.assign_success (Core.LocalLoop.controlType type) (.var actualLookup) shiftedRhs readable written
        (by simpa only [rename_insert] using tailCore)

theorem fault_letUninitialized
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context middleContext : Context}
    {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type payload : Core.Ty} {body : Core.Expr} {binder : TypedBinder}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .letDecl binder none) (binding : BinderCertificate source scope binder payload)
    (extension : BinderExtends source.owner context binder middleContext)
    (tail : Fault compilation program evidence source reasonAt ((binder.id, payload) :: scope) middleContext mode rest type body) :
    Fault compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.letUninitialized payload body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    wellFormed valid covers environments heaps layout fault
  rcases cons_fault_view mode unique contains (by intros; simp [form]) fault with ⟨_, head⟩ | ⟨_, nextEnv, middle, head, tailSource⟩
  · exact False.elim (letUninitialized_cannot_fault unique contains form binding.monomorphic head)
  · obtain ⟨otherExtension, location, sameEnv, allocated⟩ := letUninitialized unique contains form head
    cases sameEnv
    have sameContext := Dynamic.BinderExtends.functional otherExtension extension
    subst_vars
    obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
    have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
    have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
      rw [← heaps.runtime_hasTypes.length_eq]; simp
    have nextLayout := (layout.extend worlds).bind (Core.RuntimeValueHasType.cellRef found)
    obtain ⟨word, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, maps, futureWorlds, frame⟩ :=
      tail wellFormed (valid_extend valid extension) (covers_extend covers extension) nextEnvironments nextHeaps nextLayout tailSource
    refine ⟨word, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps,
      (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps, worlds.trans futureWorlds,
      (GeneralHeap.AdministrativePreserved.allocate mapping store (.inLeft payload .unit)).trans frame⟩
    simpa only [Core.LoopRenaming.letUninitialized] using Core.LocalSequence.letUninitialized_evaluates payload tailCore

theorem fault_letInitialized
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context middleContext : Context} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type payload : Core.Ty} {code body : Core.Expr} {binder : TypedBinder}
    {initializer : ExpressionId} {depth : Nat} {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .letDecl binder (some initializer)) (binding : BinderCertificate source scope binder payload)
    (extension : BinderExtends source.owner context binder middleContext)
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payload code depth)
    (tail : Fault compilation program evidence source reasonAt ((binder.id, payload) :: scope) middleContext mode rest type body) :
    Fault compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType type) payload code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    wellFormed valid covers environments heaps layout fault
  rcases cons_fault_view mode unique contains (by intros; simp [form]) fault with ⟨_, head⟩ | ⟨_, nextEnv, middle, head, tailSource⟩
  · obtain ⟨rfl, word, related, core⟩ := expression_fault tree unique valid covers environments heaps layout
      (letInitialized_fault unique contains form binding.monomorphic head)
    refine ⟨word, store, mapping, world, related, ?_, heaps, .refl _, .refl _, .refl _ _⟩
    simpa only [Core.LoopRenaming.letInitialized] using
      Core.LocalSequence.letInitialized_failure (Core.LocalLoop.controlType type) payload core
  · obtain ⟨otherExtension, location, sourceValue, initializedHeap, sameEnv, evaluated, allocated⟩ :=
      letInitialized unique contains form binding.monomorphic head
    cases sameEnv
    have sameContext := Dynamic.BinderExtends.functional otherExtension extension
    subst_vars
    obtain ⟨rfl, staged, rfl, typed, initializerCore⟩ := expression_success_prefix tree unique environments heaps layout evaluated
    have sameSource : binder.scheme.body = SourceStagedValue.sourceType staged :=
      binding.types.source_unique (typed ▸ stagedTypes staged)
    have cell : CellRepresents {type := binder.scheme.body, value := some (StagedValue.toSource staged)}
        (.inRight .unit (SourceStagedValue.toCore staged)) payload := by
      rw [sameSource, ← typed]; exact .initialized staged
    obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
    have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
    have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
      rw [← heaps.runtime_hasTypes.length_eq]; simp
    have nextLayout := ((layout.extend worlds).insert (stagedTypedFault staged _)).bind (Core.RuntimeValueHasType.cellRef found)
    obtain ⟨word, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, maps, futureWorlds, frame⟩ :=
      tail wellFormed (valid_extend valid extension) (covers_extend covers extension) nextEnvironments nextHeaps nextLayout tailSource
    refine ⟨word, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps,
      (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps, worlds.trans futureWorlds,
      (GeneralHeap.AdministrativePreserved.allocate mapping store (.inRight .unit (SourceStagedValue.toCore staged))).trans frame⟩
    simpa only [Core.LoopRenaming.letInitialized] using
      Core.LocalSequence.letInitialized_success (Core.LocalLoop.controlType type) payload initializerCore
        (by simpa only [rename_insert_lift, Core.Store.allocate] using tailCore)


def ScopedFault (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (id : StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store} {reason : Dynamic.SemanticFault},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Dynamic.StatementFaults program context evidence source environment heap id reason after →
    FaultResult program evidence source reasonAt type mapping world store after reason actual (code.rename ξ)

theorem fault_scoped
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {type : Core.Ty} {code body : Core.Expr}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (notTail : ∀ value, node.form ≠ .expression value false)
    (headSuccess : ScopedSuccess program evidence source scope context id type code)
    (headFault : ScopedFault compilation program evidence source reasonAt scope context id type code)
    (tail : Fault compilation program evidence source reasonAt scope context mode rest type body) :
    Fault compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.sequence type code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    wellFormed valid covers environments heaps layout fault
  rcases cons_fault_view mode unique contains (fun _ _ => notTail) fault with ⟨_, head⟩ | ⟨_, nextEnv, middle, headSource, tailSource⟩
  · obtain ⟨word, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
      headFault wellFormed valid covers environments heaps layout head
    refine ⟨word, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, worlds, frame⟩
    simpa only [Core.LoopRenaming.sequence] using Core.LocalLoop.sequence_failure type core
  · obtain ⟨rfl, sameEnv, result, middleStore, middleMapping, middleWorld, related, headCore, middleHeaps, maps, worlds, frame⟩ :=
      headSuccess wellFormed environments heaps layout headSource
    have envEq := sameEnv nextEnv rfl
    subst nextEnv
    cases related with
    | fallthrough =>
      have shiftedLayout := (((layout.extend worlds).insert
        (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType) (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
        (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
      obtain ⟨word, finalStore, finalMapping, finalWorld, related, tailCore, finalHeaps, mapsAgain, worldsAgain, frameAgain⟩ :=
        tail wellFormed valid covers (environments.extend maps worlds) middleHeaps shiftedLayout tailSource
      refine ⟨word, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps,
        maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩
      simpa only [Core.LoopRenaming.sequence] using
        Core.LocalLoop.sequence_fallthrough type headCore (by simpa only [rename_insert] using tailCore)

theorem fault_block_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {id : StatementId} {statements : List StatementId} {node : StatementNode} {type : Core.Ty} {code : Core.Expr}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .block statements)
    (body : Fault compilation program evidence source reasonAt scope context false statements type code) :
    ScopedFault compilation program evidence source reasonAt scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store reason
    wellFormed valid covers environments heaps layout fault
  obtain ⟨_, inner⟩ := block_fault unique contains form fault
  exact body wellFormed valid covers environments heaps layout inner

theorem fault_if_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {id : StatementId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {node : StatementNode} {type : Core.Ty} {condition : ExpressionId}
    {conditionCode thenCode elseCode : Core.Expr} {depth : Nat} {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (thenCorrect : Fault compilation program evidence source reasonAt scope context false thenBody type thenCode)
    (elseCorrect : Fault compilation program evidence source reasonAt scope context false (elseBody.getD []) type elseCode) :
    ScopedFault compilation program evidence source reasonAt scope context id type (Core.LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store reason
    wellFormed valid covers environments heaps layout fault
  rcases ifThen_fault unique contains form fault with conditionFault | ⟨value, _, evaluated, invalid, _, _⟩ | ⟨boolean, middle, _, evaluated, branch⟩
  · obtain ⟨rfl, word, related, core⟩ := expression_fault conditionTree unique valid covers environments heaps layout conditionFault
    refine ⟨word, store, mapping, world, related, ?_, heaps, .refl _, .refl _, .refl _ _⟩
    rw [Core.LoopRenaming.conditional]
    exact Core.LocalControl.choose_failure (Core.LocalLoop.controlType type) core
  · obtain ⟨_, staged, rfl, typed, _⟩ := expression_success_prefix conditionTree unique environments heaps layout evaluated
    obtain ⟨_, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
    exact False.elim (invalid True.intro)
  · obtain ⟨rfl, staged, same, typed, conditionCore⟩ := expression_success_prefix conditionTree unique environments heaps layout evaluated
    obtain ⟨other, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
    cases same
    cases boolean with
    | false =>
      obtain ⟨word, finalStore, finalMapping, finalWorld, related, branchCore, finalHeaps, maps, worlds, frame⟩ :=
        elseCorrect wellFormed valid covers environments heaps (layout.insert (Core.RuntimeValueHasType.bool (value := false))) branch
      refine ⟨word, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, worlds, frame⟩
      rw [Core.LoopRenaming.conditional]
      exact Core.LocalControl.choose_false (Core.LocalLoop.controlType type)
        conditionCore (by simpa only [rename_insert] using branchCore)
    | true =>
      obtain ⟨word, finalStore, finalMapping, finalWorld, related, branchCore, finalHeaps, maps, worlds, frame⟩ :=
        thenCorrect wellFormed valid covers environments heaps (layout.insert (Core.RuntimeValueHasType.bool (value := true))) branch
      refine ⟨word, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, worlds, frame⟩
      rw [Core.LoopRenaming.conditional]
      exact Core.LocalControl.choose_true (Core.LocalLoop.controlType type)
        conditionCore (by simpa only [rename_insert] using branchCore)

theorem fault_while_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {id : StatementId} {statements : List StatementId}
    {node : StatementNode} {type : Core.Ty} {condition : ExpressionId} {conditionCode bodyCode : Core.Expr}
    {depth : Nat} {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .whileLoop condition statements)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Success program evidence source scope context false statements type bodyCode)
    (bodyFaultCorrect : Fault compilation program evidence source reasonAt scope context false statements type bodyCode) :
    ScopedFault compilation program evidence source reasonAt scope context id type (Core.LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store reason
    wellFormed valid covers environments heaps layout fault
  have loop := whileLoop_fault unique contains form fault
  obtain ⟨installedHeaps, extended, unmapped, selfTyped, installed, installFrame⟩ :=
    LoopAdministration.install selfReason heaps layout.typed wellFormed
      (conditionTree.hasType.rename layout.respects) ((bodyTyped wellFormed).rename layout.respects)
      (Core.LocalLoop.fallthrough_hasType wellFormed)
  have bodyPreserves : BodyPreserves program context evidence source scope admin environment canonical actual actualContext
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
  have bodyFaultPreserves : BodyFaultPreserves program context evidence source scope admin environment canonical actual actualContext
      type store.length statements (bodyCode.rename ξ) reasonAt := by
    intro bodyMapping bodyWorld bodyHeap bodyAfter bodyStore bodyFinalContext bodyReason
      bodyEnvironments bodyHeaps actualTyped locationTyped bodySource
    have bodyLayout : Layout bodyWorld (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ :=
      ⟨layout.respects, layout.agrees, actualTyped⟩
    have shiftedLayout := ((bodyLayout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert
      Core.RuntimeValueHasType.unit).insert (Core.RuntimeValueHasType.bool (value := true))
    obtain ⟨word, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
      bodyFaultCorrect wellFormed valid covers bodyEnvironments bodyHeaps shiftedLayout bodySource
    exact ⟨word, finalStore, finalMapping, finalWorld, related,
      by simpa only [rename_insert, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, Core.LoopExecution.bodyCode] using core, finalHeaps, maps, worlds, frame⟩
  obtain ⟨word, finalStore, finalMapping, finalWorld, related, trace, finalHeaps, maps, worlds, frame⟩ :=
    Internal.while_fault loop conditionTree unique valid covers layout.agrees bodyPreserves bodyFaultPreserves
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed
  refine ⟨word, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  simpa only [Core.LoopRenaming.whileLoop] using trace.whileLoop_evaluates


private theorem tailExpression_fault_view
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {valueId : ExpressionId} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression valueId false)
    (fault : Dynamic.FunctionStatementsFault program context evidence source environment heap [id] finalContext reason after) :
    Dynamic.ExpressionFaults program context evidence source environment heap valueId reason after := by
  have shape : ∀ other, ContainsStatement source id other → other.form = .expression valueId false := by
    intro other otherContains
    have same : other = node := Option.some.inj
      ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
    exact same ▸ form
  cases fault with
  | tailExpression otherContains otherForm evaluated =>
    have actualForm := shape _ otherContains
    rw [otherForm] at actualForm
    cases actualForm
    exact evaluated
  | singleton head => exact ScalarStatementViews.expression_fault unique contains form head

theorem fault_tailExpression
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {id : StatementId}
    {node : StatementNode} {type : Core.Ty} {valueId : ExpressionId} {code : Core.Expr} {depth : Nat}
    {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression valueId false)
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId type code depth) :
    Fault compilation program evidence source reasonAt scope context true [id] type (Core.LocalLoop.returnValue type code) := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext reason
    _ valid covers environments heaps layout fault
  obtain ⟨rfl, word, related, core⟩ := expression_fault tree unique valid covers environments heaps layout
    (tailExpression_fault_view unique contains form fault)
  refine ⟨word, store, mapping, world, related, ?_, heaps, .refl _, .refl _, .refl _ _⟩
  simpa only [Core.LoopRenaming.returnValue] using Core.LocalLoop.returnValue_failure type core

/-- Whole-list fault correspondence, including successful earlier iterations.
The only dynamic premise is the complete independent source fault derivation. -/
theorem Tree.source_fault
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {mode : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context mode statements type code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    Fault compilation program evidence source reasonAt scope context mode statements type code := by
  induction tree with
  | nil => exact fault_nil compilation program evidence source reasonAt _ _ _ _
  | breaking _ metadata form => exact fault_breaking unique metadata.contains form
  | continuing _ metadata form => exact fault_continuing unique metadata.contains form
  | returnUnit _ metadata form => exact fault_returnUnit unique metadata.contains form
  | returnValue _ metadata form value => exact fault_returnValue unique metadata.contains form value
  | tailExpression metadata form value => exact fault_tailExpression unique metadata.contains form value
  | letUninitialized metadata form binding extension _ ih =>
    exact fault_letUninitialized unique metadata.contains form binding extension ih
  | letInitialized metadata form binding extension value _ ih =>
    exact fault_letInitialized unique metadata.contains form binding extension value ih
  | assign metadata form target value _ ih => exact fault_assign unique metadata.contains form target value ih
  | discard metadata form notTail _ value _ ih => exact fault_discard unique metadata.contains form notTail value ih
  | block metadata form body _ bodyIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_block_head unique metadata.contains form (body.source_success unique program evidence))
      (fault_block_head unique metadata.contains form bodyIH) tailIH
  | ifThen metadata form condition thenBody elseBody _ thenIH elseIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_if_head unique metadata.contains form condition
        (thenBody.source_success unique program evidence) (elseBody.source_success unique program evidence))
      (fault_if_head unique metadata.contains form condition thenIH elseIH) tailIH
  | whileLoop metadata form condition loopBody _ bodyIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_while_head unique metadata.contains form condition loopBody.hasType (loopBody.source_success unique program evidence))
      (fault_while_head unique metadata.contains form condition loopBody.hasType
        (loopBody.source_success unique program evidence) bodyIH) tailIH

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
