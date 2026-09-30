import Solcore.SourceSemantics.CoreLowering.ForInitializerSuccess

/-! Successful initializers followed by a finite iteration fault preserve the
specified source failure. Initializer faults themselves are handled through
the independent header theorem at the scoped statement boundary. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Internal Default

def InitializersFault (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope) (context : Context) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment loopEnvironment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap initialized after : Dynamic.Heap} {store : Core.Store}
    {loopContext : Context} {reason : Dynamic.SemanticFault},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Dynamic.ForItemsExecute program context evidence source environment heap items loopContext loopEnvironment initialized →
    Dynamic.ForLoopFaults program loopContext evidence source loopEnvironment initialized condition post statements reason after →
    Default.FaultResult program evidence source reasonAt type mapping world store after reason actual (code.rename ξ)

theorem fault_initializers_empty
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {statements : List StatementId} {post : List ForItemForm} {type : Core.Ty}
    {condition : ExpressionId} {conditionCode bodyCode postCode : Core.Expr} {depth : Nat} {selfReason : Core.Word}
    (unique : NodeOccurrencesUnique source)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Success program evidence source scope context false statements type bodyCode)
    (bodyFaultCorrect : Fault compilation program evidence source reasonAt scope context false statements type bodyCode)
    (postTree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context post postCode) :
    InitializersFault compilation program evidence source reasonAt scope context [] condition post statements type
      (Core.LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  intro mapping world admin environment loopEnvironment canonical actual actualContext ξ heap initialized after store loopContext reason
    wellFormed valid covers environments heaps layout initialSource loop
  cases initialSource
  have postTyped := postTree.hasType wellFormed (by
    intro scope context code endpoint
    cases endpoint
    exact Core.LocalLoop.fallthrough_hasType wellFormed)
  obtain ⟨installedHeaps, extended, unmapped, selfTyped, installed, installFrame⟩ :=
    LoopAdministration.install selfReason heaps layout.typed wellFormed
      (conditionTree.hasType.rename layout.respects) ((bodyTyped wellFormed).rename layout.respects)
      (postTyped.rename layout.respects)
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
  obtain ⟨result, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
    Internal.for_fault loop conditionTree unique valid covers layout.agrees bodyPreserves bodyFaultPreserves
      (Reflection.post_preserves postTree unique layout.respects layout.agrees)
      (Reflection.post_fault_preserves postTree unique valid covers layout.respects layout.agrees)
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed
  refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  rw [Core.LoopRenaming.iterate]
  apply Core.LocalLoop.iterate_evaluates
  apply Core.LocalLoop.invoke_success _ _ (.var rfl) _ core
  exact installed

theorem fault_initializers_prepend
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {item : ForItemForm} {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (header : ForHeaders.Tree compilation source reasonAt type
      (fun scope context code => InitializersFault compilation program evidence source reasonAt scope context rest condition post statements type code)
      scope context [item] code)
    (unique : NodeOccurrencesUnique source) :
    InitializersFault compilation program evidence source reasonAt scope context (item :: rest) condition post statements type code := by
  intro mapping world admin environment loopEnvironment canonical actual actualContext ξ heap initialized after store loopContext reason
    wellFormed valid covers environments heaps layout initialSource loop
  cases initialSource with
  | cons head remaining =>
    obtain ⟨tail, contextEq, environmentEq, heapEq, maps, worlds, frame, agreement⟩ :=
      header.source_success unique program evidence environments heaps layout (.cons head .nil)
    have extension : ForHeaders.ContextExtends source.owner context tail.context := by
      rw [contextEq]
      cases head with
      | letUninitialized _ extension _ | letInitialized _ _ extension _ | letInitializedGeneralized _ _ extension _ =>
          exact .binder extension
      | expression | assignValue | assignBitNot => exact .refl _ _
    rw [← contextEq, ← environmentEq, ← heapEq] at remaining
    obtain ⟨result, finalStore, finalMap, finalWorld, related, core, finalHeaps, tailMaps, tailWorlds, tailFrame⟩ :=
      tail.certificate wellFormed (extension.valid valid) (extension.covers covers) tail.environments tail.heaps tail.layout remaining loop
    exact ⟨result, finalStore, finalMap, finalWorld, related, agreement.wrap core, finalHeaps,
      maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame⟩

theorem fault_for_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm} {condition : ExpressionId}
    {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (header : ForHeaders.Tree compilation source reasonAt type (fun _ _ _ => True) scope context items code)
    (correct : InitializersFault compilation program evidence source reasonAt scope context items condition post statements type code) :
    ScopedFault compilation program evidence source reasonAt scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store reason
    wellFormed valid covers environments heaps layout fault
  rcases ForSourceViews.fault unique contains form fault with ⟨finalContext, initialFault⟩ | ⟨loopContext, loopEnvironment, initialized, initialSource, loopFault⟩
  · exact header.source_fault unique program evidence valid covers environments heaps layout initialFault
  · exact correct wellFormed valid covers environments heaps layout initialSource loopFault

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
