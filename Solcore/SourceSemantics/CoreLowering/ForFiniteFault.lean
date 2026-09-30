import Solcore.SourceSemantics.CoreLowering.ForFiniteSuccess

/-! Forward simulation of every supplied finite for-loop fault, including
post faults and successful body/post prefixes before a later fault. The
post contracts are structural induction interfaces, not compiler axioms. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal

open Frontend Frontend.SourceInference TypeSystem LocalCell
open Core.LoopExecution

def PostFaultPreserves (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (canonical actual : Core.Environment) (actualContext : Core.Context)
    (type : Core.Ty) (location : Core.Location) (items : List ForItemForm) (code : Core.Expr)
    (reasonAt : ExpressionId → Core.Word) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap}
    {store : Core.Store} {finalContext : Context} {reason : Dynamic.SemanticFault},
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Core.RuntimeEnvironmentHasTypes world actual actualContext →
    world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
    Dynamic.ForItemsFault program context evidence source environment heap items finalContext reason after →
    ∀ continued : Bool, ∃ token finalStore finalMap finalWorld,
      FaultRepresents program evidence source reasonAt reason token ∧
      Core.Evaluates ((if continued then CoreProof.ForLoop.continuingPrefix type else CoreProof.ForLoop.fallthroughPrefix type) ++
        entryEnvironment type location actual) store (CoreProof.ForLoop.postCode code)
        (.inLeft (Core.LocalLoop.controlType type) (.word token)) finalStore ∧
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

def ForFaultResult (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) (condition body postBody : Core.Expr) (selfReason : Core.Word)
    (location : Core.Location) (actual : Core.Environment)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) : Prop :=
  ∃ resultReason finalStore finalMapping finalWorld,
    FaultRepresents program evidence source reasonAt reason resultReason ∧
    Core.Evaluates (entryEnvironment type location actual) store (Core.LocalLoop.loopBody type condition body postBody selfReason)
      (.inLeft (Core.LocalLoop.controlType type) (.word resultReason)) finalStore ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

/-- Internal fault composition, including earlier successful iterations. The
body contracts remain explicit induction hypotheses, not compiler properties. -/
theorem for_fault
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (execution : Dynamic.ForLoopFaults program context evidence source environment heap condition post statements reason after) :
    ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
      {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
      {body postBody : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
      {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
      {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
      PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
      NodeOccurrencesUnique source → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
      Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
      BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location statements body →
      BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location statements body reasonAt →
      PostPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody →
      PostFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody reasonAt →
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
      GeneralHeap.HeapRepresents mapping world heap store →
      Core.RuntimeEnvironmentHasTypes world actual actualContext →
      world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
      location ∉ mapping →
      store.read? location = some (.inRight .unit
        (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body postBody selfReason location actual)) →
      ForFaultResult program evidence source reasonAt type (conditionCode.rename ξ) body postBody selfReason location actual
        mapping world store reason after := by
  refine @for_fault_induction program
    (fun context evidence source environment heap condition post statements reason after =>
      ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
        {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
        {body postBody : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
        {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
        {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
        PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
        NodeOccurrencesUnique source → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
        Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
        BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
          type location statements body →
        BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
          type location statements body reasonAt →
      PostPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody →
      PostFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody reasonAt →
        GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
        GeneralHeap.HeapRepresents mapping world heap store →
        Core.RuntimeEnvironmentHasTypes world actual actualContext →
        world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) → location ∉ mapping →
        store.read? location = some (.inRight .unit
          (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body postBody selfReason location actual)) →
        ForFaultResult program evidence source reasonAt type (conditionCode.rename ξ) body postBody selfReason location actual
          mapping world store reason after)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ context evidence source environment heap condition post statements reason after execution
  · intro context evidence source environment before after condition post statements reason conditionFault
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, site, faultLocation, rfl, origin, core⟩ := ScalarExpressionReflection.Primitive.source_fault
      conditionTree unique valid covers environments heaps conditionFault
    have restricted := GeneralExpressions.Primitive.readOnly conditionTree
    have renamed := restricted.evaluation_rename core agree
    have shifted := (restricted.rename ξ).evaluation_weakenAt_zero renamed
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)
    have shiftedAgain := ((restricted.rename ξ).weakenAt 0).evaluation_weakenAt_zero shifted .unit
    exact ⟨_, store, mapping, world, .uninitialized site faultLocation origin,
      Core.LoopExecution.condition_failure shiftedAgain, heaps, .refl _, .refl _, .refl _ _⟩
  · intro context evidence source environment before after condition post statements value actualType evaluation notBool actualTypeProof
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨_, staged, rfl, typed, _⟩ := ScalarExpressionReflection.Primitive.source_success
      conditionTree unique environments heaps evaluation
    obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
    exact False.elim (notBool trivial)
  · intro context evidence source environment before conditionHeap after condition post statements finalContext reason
      conditionEvaluation bodyFault
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨resultReason, finalStore, finalMapping, finalWorld, related, bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyFaultCorrect environments heaps actualTyped selfTyped bodyFault
    exact ⟨_, finalStore, finalMapping, finalWorld, related, Core.LoopExecution.body_failure conditionCore bodyCore,
      finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postFault
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | fallthrough =>
      obtain ⟨token, postStore, postMap, postWorld, postRelated, postCore, postHeaps, postMaps, postWorlds, postFrame⟩ :=
        postFaultCorrect (environments.extend mapsExtended worldsExtended) nextHeaps
          (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
          (worldsExtended.lookup selfTyped) postFault false
      exact ⟨token, postStore, postMap, postWorld, postRelated,
        CoreProof.ForLoop.body_fallthrough_post_fault conditionCore bodyCore postCore,
        postHeaps, mapsExtended.trans postMaps, worldsExtended.trans postWorlds, bodyFrame.trans postFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postFault
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | continuing =>
      obtain ⟨token, postStore, postMap, postWorld, postRelated, postCore, postHeaps, postMaps, postWorlds, postFrame⟩ :=
        postFaultCorrect (environments.extend mapsExtended worldsExtended) nextHeaps
          (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
          (worldsExtended.lookup selfTyped) postFault true
      exact ⟨token, postStore, postMap, postWorld, postRelated,
        CoreProof.ForLoop.body_continuing_post_fault conditionCore bodyCore postCore,
        postHeaps, mapsExtended.trans postMaps, worldsExtended.trans postWorlds, bodyFrame.trans postFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
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
        obtain ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect
            (environments.extend (mapsExtended.trans postMaps) (worldsExtended.trans postWorlds)) postHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken (worldsExtended.trans postWorlds) actualTyped)
            ((worldsExtended.trans postWorlds).lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated,
          CoreProof.ForLoop.body_fallthrough conditionCore bodyCore postCore stillInstalled trace, finalHeaps,
          (mapsExtended.trans postMaps).trans mapsAgain, (worldsExtended.trans postWorlds).trans worldsAgain,
          (bodyFrame.trans postFrame).trans nextFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
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
        obtain ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect
            (environments.extend (mapsExtended.trans postMaps) (worldsExtended.trans postWorlds)) postHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken (worldsExtended.trans postWorlds) actualTyped)
            ((worldsExtended.trans postWorlds).lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated,
          CoreProof.ForLoop.body_continuing conditionCore bodyCore postCore stillInstalled trace, finalHeaps,
          (mapsExtended.trans postMaps).trans mapsAgain, (worldsExtended.trans postWorlds).trans worldsAgain,
          (bodyFrame.trans postFrame).trans nextFrame⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal
