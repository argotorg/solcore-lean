import Solcore.SourceSemantics.CoreLowering.ForFiniteReflection
import Solcore.SourceSemantics.CoreLowering.LoopWhileReflection

/-! Reconstruct initialization and iteration under the actual lexical scope.
The header continuation is a structural induction contract, while all source
header executions are built from its static tree and the represented heap. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

inductive InitializersMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (items : List ForItemForm) (condition : ExpressionId)
    (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) :
    Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {loopContext loopFinalContext loopEnvironment initialized outcome after result}
      (initialization : Dynamic.ForItemsExecute program context evidence source environment before items
        loopContext loopEnvironment initialized)
      (iteration : Dynamic.ForLoopExecutes program loopContext evidence source loopEnvironment initialized
        condition post statements loopFinalContext outcome after)
      (related : ControlRepresents type outcome result) :
      InitializersMeaning program context evidence source reasonAt environment before items condition post statements type outcome after result
  | initialFault {finalContext reason word after}
      (fault : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      InitializersMeaning program context evidence source reasonAt environment before items condition post statements type
        (.fault reason) after (.inLeft (Core.LocalLoop.controlType type) (.word word))
  | iterationFault {loopContext loopEnvironment initialized reason word after}
      (initialization : Dynamic.ForItemsExecute program context evidence source environment before items
        loopContext loopEnvironment initialized)
      (fault : Dynamic.ForLoopFaults program loopContext evidence source loopEnvironment initialized
        condition post statements reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      InitializersMeaning program context evidence source reasonAt environment before items condition post statements type
        (.fault reason) after (.inLeft (Core.LocalLoop.controlType type) (.word word))

def InitializersResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (items : List ForItemForm) (condition : ExpressionId)
    (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ outcome after finalMap finalWorld,
    InitializersMeaning program context evidence source reasonAt environment before items condition post statements type outcome after result ∧
    GeneralHeap.HeapRepresents finalMap finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMap finalStore

def InitializersReflects (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (items : List ForItemForm) (condition : ExpressionId)
    (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store finalStore : Core.Store} {result : Core.Value},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Core.Evaluates actual store (code.rename ξ) result finalStore →
    InitializersResult program context evidence source reasonAt environment heap items condition post statements type
      mapping world store result finalStore

theorem reflects_initializers_empty
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {statements : List StatementId} {post : List ForItemForm} {type : Core.Ty}
    {condition : ExpressionId} {conditionCode bodyCode postCode : Core.Expr} {depth : Nat} {selfReason : Core.Word}
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Reflects compilation program evidence source reasonAt scope context false statements type bodyCode)
    (postTree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context post postCode) :
    InitializersReflects compilation program evidence source reasonAt scope context [] condition post statements type
      (Core.LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.iterate] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨entrySize, _, entry⟩ := sized.iterate_entry
  have postTyped := postTree.hasType wellFormed (by
    intro scope context code endpoint
    cases endpoint
    exact Core.LocalLoop.fallthrough_hasType wellFormed)
  obtain ⟨installedHeaps, extended, unmapped, selfTyped, installed, installFrame⟩ :=
    LoopAdministration.install selfReason heaps layout.typed wellFormed
      (conditionTree.hasType.rename layout.respects) ((bodyTyped wellFormed).rename layout.respects)
      (postTyped.rename layout.respects)
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    for_reflect conditionTree valid layout.agrees
      (bodyCorrect.body wellFormed valid layout.respects layout.agrees)
      (post_constructs postTree valid layout.respects layout.agrees) entrySize
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed entry
  refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  cases meaning with
  | control sourceLoop related => exact .control .nil sourceLoop related
  | fault sourceFault related => exact .iterationFault .nil sourceFault related

/-- One statically certified initializer prefix composes with the recursive
initializer contract. It does not assume a source execution of either part. -/
theorem reflects_initializers_prepend
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {item : ForItemForm} {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (header : ForHeaders.Tree compilation source reasonAt type
      (fun scope context code => InitializersReflects compilation program evidence source reasonAt scope context
        rest condition post statements type code) scope context [item] code) :
    InitializersReflects compilation program evidence source reasonAt scope context (item :: rest) condition post statements type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  have construction := header.construct program evidence valid environments heaps layout
  cases construction with
  | continues tail execution contextExtension maps worlds frame agreement =>
    obtain ⟨outcome, after, finalMap, finalWorld, meaning, finalHeaps, tailMaps, tailWorlds, tailFrame⟩ :=
      tail.certificate wellFormed (contextExtension.valid valid) tail.environments tail.heaps tail.layout (agreement.unwrap evaluated)
    refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame⟩
    cases execution with
    | cons head empty =>
      cases empty
      cases meaning with
      | control initialization iteration related => exact .control (.cons head initialization) iteration related
      | initialFault fault related => exact .initialFault (.tail head fault) related
      | iterationFault initialization fault related => exact .iterationFault (.cons head initialization) fault related
  | @fault finalContext reason word after finalMap finalWorld finalStore fault related finalHeaps maps worlds frame evaluation =>
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated evaluation
    refine ⟨.fault reason, _, _, _, ?_, finalHeaps, maps, worlds, frame⟩
    cases fault with
    | head fault => exact .initialFault (.head fault) related
    | tail _ impossible => cases impossible

theorem reflects_for_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {id : StatementId} {node : StatementNode} {items : List ForItemForm} {condition : ExpressionId}
    {post : List ForItemForm} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (contains : ContainsStatement source id node) (form : node.form = .forLoop items condition post statements)
    (correct : InitializersReflects compilation program evidence source reasonAt scope context items condition post statements type code) :
    ScopedReflects compilation program evidence source reasonAt scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    correct wellFormed valid environments heaps layout evaluated
  refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame⟩
  cases meaning with
  | control initialization iteration related => exact .control (.forLoop contains form initialization iteration) related
  | initialFault fault related => exact .fault (.forInitializer contains form fault) related
  | iterationFault initialization fault related => exact .fault (.forIteration contains form initialization fault) related

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
