import Solcore.SourceSemantics.CoreLowering.LoopFiniteComposition
import Solcore.SourceSemantics.CoreLowering.ForSourceInduction
import Solcore.SourceSemantics.CoreLowering.ForLoopCoreEdges

/-! Preservation of a supplied finite for-iteration success trace. Body and
post contracts are structural induction interfaces and must be discharged
before applying this theorem at an accepted compiler boundary. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal

open Frontend Frontend.SourceInference TypeSystem LocalCell
open Core.LoopExecution

def PostPreserves (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (canonical actual : Core.Environment) (actualContext : Core.Context)
    (type : Core.Ty) (location : Core.Location) (items : List ForItemForm) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap}
    {store : Core.Store} {finalContext : Context} {finalEnvironment : Dynamic.Environment},
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Core.RuntimeEnvironmentHasTypes world actual actualContext →
    world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
    Dynamic.ForItemsExecute program context evidence source environment heap items finalContext finalEnvironment after →
    ∀ continued : Bool, ∃ finalStore finalMap finalWorld,
      Core.Evaluates ((if continued then CoreProof.ForLoop.continuingPrefix type else CoreProof.ForLoop.fallthroughPrefix type) ++
        entryEnvironment type location actual) store (CoreProof.ForLoop.postCode code) (Core.LocalLoop.fallthroughValue type) finalStore ∧
      GeneralHeap.HeapRepresents finalMap finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMap finalStore

private theorem condition_evaluates
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {condition : ExpressionId} {code : Core.Expr} {depth : Nat}
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool code depth)
    (unique : NodeOccurrencesUnique source)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store} {ξ : Core.Renaming} {boolean : Bool}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual)
    (type : Core.Ty) (location : Core.Location)
    (evaluation : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool boolean) after) :
    after = heap ∧ Core.Evaluates (entryEnvironment type location actual) store
      (conditionCode (code.rename ξ)) (.inRight .word (.bool boolean)) store := by
  obtain ⟨rfl, staged, same, typed, core⟩ := ScalarExpressionReflection.Primitive.source_success tree unique environments heaps evaluation
  obtain ⟨other, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
  cases same
  have restricted := GeneralExpressions.Primitive.readOnly tree
  have renamed := restricted.evaluation_rename core agree
  have shifted := (restricted.rename ξ).evaluation_weakenAt_zero renamed
    (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)
  have shiftedAgain := ((restricted.rename ξ).weakenAt 0).evaluation_weakenAt_zero shifted .unit
  exact ⟨rfl, shiftedAgain⟩

private theorem self_retained
    {mapping futureMapping : GeneralHeap.LocationMap} {before after : Core.Store}
    {location : Core.Location} {value : Core.Value}
    (unmapped : location ∉ mapping) (read : before.read? location = some value)
    (frame : GeneralHeap.AdministrativePreserved mapping before futureMapping after) :
    location ∉ futureMapping ∧ after.read? location = some value := by
  have bounded : location < before.length := by
    exact (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨unmapped, same⟩ := frame location unmapped bounded
  exact ⟨unmapped, same.trans read⟩

/-- Result supplied by one finite source for derivation after self-cell
installation. The closure identity in every recursive edge is exact. -/
def ForSuccessResult (type : Core.Ty) (condition body post : Core.Expr) (selfReason : Core.Word)
    (location : Core.Location) (actual : Core.Environment)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ result finalStore finalMapping finalWorld,
    ControlRepresents type outcome result ∧
    Core.Evaluates (entryEnvironment type location actual) store (Core.LocalLoop.loopBody type condition body post selfReason) result finalStore ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

/-- Internal semantic induction, with body preservation supplied as the
statement-tree induction hypothesis. No next-loop evaluation is assumed. -/
theorem for_success
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {finalContext : Context} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.ForLoopExecutes program context evidence source environment heap condition post statements finalContext outcome after) :
    ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
      {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
      {body postBody : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
      {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
      {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
      PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
      NodeOccurrencesUnique source →
      Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
      BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location statements body →
      PostPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody →
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
      GeneralHeap.HeapRepresents mapping world heap store →
      Core.RuntimeEnvironmentHasTypes world actual actualContext →
      world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
      location ∉ mapping →
      store.read? location = some (.inRight .unit
        (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body postBody selfReason location actual)) →
      ForSuccessResult type (conditionCode.rename ξ) body postBody selfReason location actual mapping world store outcome after := by
  refine @for_induction program
    (fun context evidence source environment heap condition post statements _ outcome after =>
      ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
        {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
        {body postBody : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
        {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
        {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
        PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
        NodeOccurrencesUnique source → Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
        BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
          type location statements body →
      PostPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody →
        GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
        GeneralHeap.HeapRepresents mapping world heap store →
        Core.RuntimeEnvironmentHasTypes world actual actualContext →
        world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) → location ∉ mapping →
        store.read? location = some (.inRight .unit
          (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body postBody selfReason location actual)) →
        ForSuccessResult type (conditionCode.rename ξ) body postBody selfReason location actual mapping world store outcome after)
    ?_ ?_ ?_ ?_ ?_ context evidence source environment heap condition post statements finalContext outcome after execution
  · intro context evidence source environment before after condition post statements conditionEvaluation
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect postCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    exact ⟨_, store, mapping, world, .fallthrough environment, Core.LoopExecution.condition_false conditionCore, heaps,
      .refl _, .refl _, .refl _ _⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect postCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | fallthrough =>
        obtain ⟨postStore, postMap, postWorld, postCore, postHeaps, postMaps, postWorlds, postFrame⟩ :=
          postCorrect (environments.extend mapsExtended worldsExtended) nextHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
            (worldsExtended.lookup selfTyped) postEvaluation false
        obtain ⟨stillUnmapped, stillInstalled⟩ := self_retained unmapped installed (bodyFrame.trans postFrame)
        obtain ⟨result, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique agree bodyCorrect postCorrect
            (environments.extend (mapsExtended.trans postMaps) (worldsExtended.trans postWorlds)) postHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken (worldsExtended.trans postWorlds) actualTyped)
            ((worldsExtended.trans postWorlds).lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨result, finalStore, finalMapping, finalWorld, resultRelated,
          CoreProof.ForLoop.body_fallthrough conditionCore bodyCore postCore stillInstalled trace, finalHeaps,
          (mapsExtended.trans postMaps).trans mapsAgain, (worldsExtended.trans postWorlds).trans worldsAgain,
          (bodyFrame.trans postFrame).trans nextFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect postCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | continuing =>
        obtain ⟨postStore, postMap, postWorld, postCore, postHeaps, postMaps, postWorlds, postFrame⟩ :=
          postCorrect (environments.extend mapsExtended worldsExtended) nextHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
            (worldsExtended.lookup selfTyped) postEvaluation true
        obtain ⟨stillUnmapped, stillInstalled⟩ := self_retained unmapped installed (bodyFrame.trans postFrame)
        obtain ⟨result, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique agree bodyCorrect postCorrect
            (environments.extend (mapsExtended.trans postMaps) (worldsExtended.trans postWorlds)) postHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken (worldsExtended.trans postWorlds) actualTyped)
            ((worldsExtended.trans postWorlds).lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨result, finalStore, finalMapping, finalWorld, resultRelated,
          CoreProof.ForLoop.body_continuing conditionCore bodyCore postCore stillInstalled trace, finalHeaps,
          (mapsExtended.trans postMaps).trans mapsAgain, (worldsExtended.trans postWorlds).trans worldsAgain,
          (bodyFrame.trans postFrame).trans nextFrame⟩
  · intro context evidence source environment before conditionHeap after condition post statements bodyFinalContext bodyEnvironment
      conditionEvaluation bodyEvaluation
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect postCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, finalStore, finalMapping, finalWorld, related, bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | breaking => exact ⟨_, finalStore, finalMapping, finalWorld, .fallthrough environment,
        Core.LoopExecution.body_breaking conditionCore bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩
  · intro context evidence source environment before conditionHeap after condition post statements bodyFinalContext returned
      conditionEvaluation bodyEvaluation
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect postCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, finalStore, finalMapping, finalWorld, related, bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | returned value typed => exact ⟨_, finalStore, finalMapping, finalWorld, .returned value typed,
        Core.LoopExecution.body_returned conditionCore bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩


end Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal
