import Solcore.SourceSemantics.CoreLowering.ForPostPreservation
import Solcore.SourceSemantics.CoreLowering.ForSourceViews

/-! Successful initializer and iteration composition under arbitrary actual
lexical layouts, for use by the complete static for-tree induction. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Internal Default

def InitializersSuccess (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (context : Context) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment loopEnvironment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap initialized after : Dynamic.Heap} {store : Core.Store}
    {loopContext finalContext : Context} {outcome : Dynamic.ControlOutcome},
    Core.Ty.WellFormed [] type →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Dynamic.ForItemsExecute program context evidence source environment heap items loopContext loopEnvironment initialized →
    Dynamic.ForLoopExecutes program loopContext evidence source loopEnvironment initialized condition post statements finalContext outcome after →
    Default.SuccessResult type mapping world store after outcome actual (code.rename ξ)

theorem success_initializers_empty
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {statements : List StatementId} {post : List ForItemForm} {type : Core.Ty}
    {condition : ExpressionId} {conditionCode bodyCode postCode : Core.Expr} {depth : Nat} {selfReason : Core.Word}
    (unique : NodeOccurrencesUnique source)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Success program evidence source scope context false statements type bodyCode)
    (postTree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context post postCode) :
    InitializersSuccess program evidence source scope context [] condition post statements type
      (Core.LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  intro mapping world admin environment loopEnvironment canonical actual actualContext ξ heap initialized after store loopContext finalContext outcome
    wellFormed environments heaps layout initialSource loop
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
  obtain ⟨result, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
    Internal.for_success loop conditionTree unique layout.agrees bodyPreserves
      (Reflection.post_preserves postTree unique layout.respects layout.agrees)
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed
  refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  rw [Core.LoopRenaming.iterate]
  apply Core.LocalLoop.iterate_evaluates
  apply Core.LocalLoop.invoke_success _ _ (.var rfl) _ core
  exact installed

theorem success_initializers_prepend
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {item : ForItemForm} {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (header : ForHeaders.Tree compilation source reasonAt type
      (fun scope context code => InitializersSuccess program evidence source scope context rest condition post statements type code)
      scope context [item] code)
    (unique : NodeOccurrencesUnique source) :
    InitializersSuccess program evidence source scope context (item :: rest) condition post statements type code := by
  intro mapping world admin environment loopEnvironment canonical actual actualContext ξ heap initialized after store loopContext finalContext outcome
    wellFormed environments heaps layout initialSource loop
  cases initialSource with
  | cons head remaining =>
    obtain ⟨tail, contextEq, environmentEq, heapEq, maps, worlds, frame, agreement⟩ :=
      header.source_success unique program evidence environments heaps layout (.cons head .nil)
    rw [← contextEq, ← environmentEq, ← heapEq] at remaining
    obtain ⟨result, finalStore, finalMap, finalWorld, related, core, finalHeaps, tailMaps, tailWorlds, tailFrame⟩ :=
      tail.certificate wellFormed tail.environments tail.heaps tail.layout remaining loop
    exact ⟨result, finalStore, finalMap, finalWorld, related, agreement.wrap core, finalHeaps,
      maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame⟩

private theorem restore_related {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {value : Core.Value}
    (related : ControlRepresents type outcome value) (environment : Dynamic.Environment) :
    ControlRepresents type (Dynamic.restoreControl environment outcome) value := by
  cases related with
  | fallthrough => exact .fallthrough environment
  | returned value typed => exact .returned value typed
  | breaking => exact .breaking environment
  | continuing => exact .continuing environment

theorem success_for_head
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (correct : InitializersSuccess program evidence source scope context items condition post statements type code) :
    ScopedSuccess program evidence source scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  obtain ⟨rfl, loopContext, loopFinalContext, loopEnvironment, initialized, loopOutcome, rfl, initialization, loop⟩ :=
    ForSourceViews.success unique contains form executed
  obtain ⟨result, finalStore, finalMap, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
    correct wellFormed environments heaps layout initialization loop
  refine ⟨rfl, ?_, result, finalStore, finalMap, finalWorld, restore_related related environment, core, finalHeaps, maps, worlds, frame⟩
  intro next same
  cases loopOutcome <;> simp_all [Dynamic.restoreControl]

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
