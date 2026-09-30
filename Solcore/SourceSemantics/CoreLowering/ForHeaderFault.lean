import Solcore.SourceSemantics.CoreLowering.ForHeaderSuccess

/-! Preservation of supplied independent header faults. Successful prefixes
use their source derivations and exact Core continuation agreement; faulting
heads use the independent scalar-expression/assignment fault rules. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements CoreProof
open LoopStatements Reflection

private theorem item_context_extends
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment finalEnvironment : Dynamic.Environment} {heap after : Dynamic.Heap} {item : ForItemForm}
    (executed : Dynamic.ForItemExecutes program context evidence source environment heap item finalContext finalEnvironment after) :
    ContextExtends source.owner context finalContext := by
  cases executed with
  | letUninitialized _ extension _ | letInitialized _ _ extension _ | letInitializedGeneralized _ _ extension _ =>
      exact .binder extension
  | expression | assignValue | assignBitNot => exact .refl _ _

def FaultResult (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (actual : Core.Environment) (store : Core.Store) (code : Core.Expr) : Prop :=
  ∃ token finalStore finalMap finalWorld,
    Internal.FaultRepresents program evidence source reasonAt reason token ∧
    Core.Evaluates actual store code (.inLeft (Core.LocalLoop.controlType type) (.word token)) finalStore ∧
    GeneralHeap.HeapRepresents finalMap finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMap finalStore

def Fault (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty)
    (scope : SourceCoreLocalCell.Scope) (context : Context) (items : List ForItemForm) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store} {finalContext : Context} {reason : Dynamic.SemanticFault},
    PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Dynamic.ForItemsFault program context evidence source environment heap items finalContext reason after →
    FaultResult program evidence source reasonAt type reason after mapping world actual store (code.rename ξ)

private theorem fault_after_success
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {type : Core.Ty}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {item : ForItemForm} {rest : List ForItemForm} {code : Core.Expr}
    (header : Tree compilation source reasonAt type
      (fun scope context code => Fault compilation program evidence source reasonAt type scope context rest code)
      scope context [item] code)
    (unique : NodeOccurrencesUnique source)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment middleEnvironment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap middle after : Dynamic.Heap} {store : Core.Store}
    {middleContext finalContext : Context} {reason : Dynamic.SemanticFault}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (head : Dynamic.ForItemExecutes program context evidence source environment heap item middleContext middleEnvironment middle)
    (fault : Dynamic.ForItemsFault program middleContext evidence source middleEnvironment middle rest finalContext reason after) :
    FaultResult program evidence source reasonAt type reason after mapping world actual store (code.rename ξ) := by
  obtain ⟨tail, contextEq, environmentEq, heapEq, maps, worlds, frame, agreement⟩ :=
    header.source_success unique program evidence environments heaps layout (.cons head .nil)
  have extension := item_context_extends head
  rw [← contextEq] at extension fault
  rw [← environmentEq, ← heapEq] at fault
  obtain ⟨token, finalStore, finalMap, finalWorld, related, core, finalHeaps, tailMaps, tailWorlds, tailFrame⟩ :=
    tail.certificate (extension.valid valid) (extension.covers covers) tail.environments tail.heaps tail.layout fault
  exact ⟨token, finalStore, finalMap, finalWorld, related, agreement.wrap core, finalHeaps,
    maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame⟩

theorem Tree.source_fault
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {type : Core.Ty} {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt type continuation scope context items code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    Fault compilation program evidence source reasonAt type scope context items code := by
  induction tree with
  | nil _ =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault
  | letUninitialized binding extension _ ih =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault with
    | head fault =>
      cases fault with
      | polymorphicLet impossible _ => exact False.elim (impossible binding.monomorphic)
    | tail head fault =>
      exact fault_after_success (.letUninitialized binding extension (.nil ih)) unique valid covers environments heaps layout head fault
  | @letInitialized scope context middleContext binder rest payload initializer initializerCode body depth binding extension valueTree tail ih =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault with
    | head fault =>
      cases fault with
      | polymorphicLet impossible _ => exact False.elim (impossible binding.monomorphic)
      | letInitializer _ fault =>
        obtain ⟨rfl, site, location, rfl, origin, evaluated⟩ :=
          ScalarExpressionReflection.Primitive.source_fault valueTree unique valid covers environments heaps fault
        have core := (GeneralExpressions.Primitive.readOnly valueTree).evaluation_rename evaluated layout.agrees
        refine ⟨_, store, mapping, world, .uninitialized site location origin, ?_, heaps, .refl _, .refl _, .refl _ _⟩
        simpa only [Core.LoopRenaming.letInitialized] using Core.LocalSequence.letInitialized_failure
          (Core.LocalLoop.controlType type) payload core
    | tail head fault =>
      exact fault_after_success (.letInitialized binding extension valueTree (.nil ih)) unique valid covers environments heaps layout head fault
  | discard valueTree _ ih =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault with
    | head fault =>
      cases fault with
      | expression fault =>
        obtain ⟨rfl, site, location, rfl, origin, evaluated⟩ :=
          ScalarExpressionReflection.Primitive.source_fault valueTree unique valid covers environments heaps fault
        have core := (GeneralExpressions.Primitive.readOnly valueTree).evaluation_rename evaluated layout.agrees
        refine ⟨_, store, mapping, world, .uninitialized site location origin, ?_, heaps, .refl _, .refl _, .refl _ _⟩
        simpa only [Core.LoopRenaming.discard] using Core.LocalSequence.discard_failure (Core.LocalLoop.controlType type) core
    | tail head fault =>
      exact fault_after_success (.discard valueTree (.nil ih)) unique valid covers environments heaps layout head fault
  | assign target valueTree _ ih =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault with
    | head fault =>
      cases fault with
      | assignValue fault =>
        obtain ⟨rfl, site, location, rfl, origin, evaluated⟩ :=
          ScalarAssignmentReflection.source_fault valueTree unique valid covers target.slot target.bare environments heaps fault
        obtain ⟨_, _, _, _, _, lookup, _, _, _, _⟩ := environments.lookup_heap heaps target.slot
        have core := (GeneralExpressions.Primitive.readOnly valueTree).evaluation_rename evaluated layout.agrees
        refine ⟨_, store, mapping, world, .uninitialized site location origin, ?_, heaps, .refl _, .refl _, .refl _ _⟩
        simpa only [Core.LoopRenaming.assign, Core.Expr.rename] using
          Core.LocalSequence.assign_failure (Core.LocalLoop.controlType type) (.var (layout.agrees lookup))
            (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero core _)
    | tail head fault =>
      exact fault_after_success (.assign target valueTree (.nil ih)) unique valid covers environments heaps layout head fault

end Solcore.SourceSemantics.CoreLowering.ForHeaders
