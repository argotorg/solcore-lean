import Solcore.SourceSemantics.CoreLowering.ScalarExpressionReflection
import Solcore.SourceSemantics.CoreLowering.LoopSourceInduction
import Solcore.SourceSemantics.CoreLowering.LoopExecution
import Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame

/-! Internal finite-loop composition. The explicit body simulation argument is
an induction hypothesis to be discharged by a statement-tree theorem. This
module does not claim that compiler acceptance alone supplies that argument. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal

open Frontend Frontend.SourceInference TypeSystem LocalCell
open Core.LoopExecution

inductive ControlRepresents (type : Core.Ty) : Dynamic.ControlOutcome → Core.Value → Prop where
  | fallthrough (environment : Dynamic.Environment) :
      ControlRepresents type (.fallthrough environment) (Core.LocalLoop.fallthroughValue type)
  | returned (value : SourceStagedValue.Value) (typed : SourceStagedValue.coreType value = type) :
      ControlRepresents type (.returned (StagedValue.toSource value)) (Core.LocalLoop.returnedValue (SourceStagedValue.toCore value))
  | breaking (environment : Dynamic.Environment) :
      ControlRepresents type (.breaking environment) (Core.LocalLoop.breakingValue type)
  | continuing (environment : Dynamic.Environment) :
      ControlRepresents type (.continuing environment) (Core.LocalLoop.continuingValue type)

/-- The induction hypothesis for a source body at any represented heap. The
actual generated body and captured lexical environment are fixed; mapped
source cells and administrative cells may grow during its execution. -/
def BodyPreserves (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (canonical actual : Core.Environment) (actualContext : Core.Context)
    (type : Core.Ty) (location : Core.Location) (statements : List StatementId) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap}
    {store : Core.Store} {finalContext : Context} {outcome : Dynamic.ControlOutcome},
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Core.RuntimeEnvironmentHasTypes world actual actualContext →
    world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
    Dynamic.StatementsExecute program context evidence source environment heap statements finalContext outcome after →
    ∃ result finalStore finalMapping finalWorld,
      ControlRepresents type outcome result ∧
      Core.Evaluates (bodyEnvironment type location actual) store (bodyCode code) result finalStore ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

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

/-- Result supplied by one finite source while derivation after self-cell
installation. The closure identity in every recursive edge is exact. -/
def WhileResult (type : Core.Ty) (condition body : Core.Expr) (selfReason : Core.Word)
    (location : Core.Location) (actual : Core.Environment)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ result finalStore finalMapping finalWorld,
    ControlRepresents type outcome result ∧
    Core.LoopExecution.WhileTrace type condition body selfReason location actual store result finalStore ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

/-- Internal semantic induction, with body preservation supplied as the
statement-tree induction hypothesis. No next-loop evaluation is assumed. -/
theorem while_success
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {finalContext : Context} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.WhileExecutes program context evidence source environment heap condition statements finalContext outcome after) :
    ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
      {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
      {body : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
      {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
      {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
      PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
      NodeOccurrencesUnique source →
      Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
      BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location statements body →
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
      GeneralHeap.HeapRepresents mapping world heap store →
      Core.RuntimeEnvironmentHasTypes world actual actualContext →
      world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
      location ∉ mapping →
      store.read? location = some (.inRight .unit
        (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body (Core.LocalLoop.fallthrough type) selfReason location actual)) →
      WhileResult type (conditionCode.rename ξ) body selfReason location actual mapping world store outcome after := by
  refine @while_induction program
    (fun context evidence source environment heap condition statements _ outcome after =>
      ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
        {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
        {body : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
        {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
        {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
        PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
        NodeOccurrencesUnique source → Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
        BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
          type location statements body →
        GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
        GeneralHeap.HeapRepresents mapping world heap store →
        Core.RuntimeEnvironmentHasTypes world actual actualContext →
        world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) → location ∉ mapping →
        store.read? location = some (.inRight .unit
          (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body (Core.LocalLoop.fallthrough type) selfReason location actual)) →
        WhileResult type (conditionCode.rename ξ) body selfReason location actual mapping world store outcome after)
    ?_ ?_ ?_ ?_ ?_ context evidence source environment heap condition statements finalContext outcome after execution
  · intro context evidence source environment before after condition statements conditionEvaluation
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    exact ⟨_, store, mapping, world, .fallthrough environment, .done conditionCore, heaps,
      .refl _, .refl _, .refl _ _⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment outcome
      conditionEvaluation bodyEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | fallthrough =>
        obtain ⟨stillUnmapped, stillInstalled⟩ := self_retained unmapped installed bodyFrame
        obtain ⟨result, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique agree bodyCorrect (environments.extend mapsExtended worldsExtended) nextHeaps (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
            (worldsExtended.lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨result, finalStore, finalMapping, finalWorld, resultRelated,
          .nextFallthrough conditionCore bodyCore stillInstalled trace, finalHeaps,
          mapsExtended.trans mapsAgain, worldsExtended.trans worldsAgain, bodyFrame.trans nextFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment outcome
      conditionEvaluation bodyEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | continuing =>
        obtain ⟨stillUnmapped, stillInstalled⟩ := self_retained unmapped installed bodyFrame
        obtain ⟨result, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique agree bodyCorrect (environments.extend mapsExtended worldsExtended) nextHeaps (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
            (worldsExtended.lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨result, finalStore, finalMapping, finalWorld, resultRelated,
          .nextContinue conditionCore bodyCore stillInstalled trace, finalHeaps,
          mapsExtended.trans mapsAgain, worldsExtended.trans worldsAgain, bodyFrame.trans nextFrame⟩
  · intro context evidence source environment before conditionHeap after condition statements bodyFinalContext bodyEnvironment
      conditionEvaluation bodyEvaluation
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, finalStore, finalMapping, finalWorld, related, bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | breaking => exact ⟨_, finalStore, finalMapping, finalWorld, .fallthrough environment,
        .breaks conditionCore bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩
  · intro context evidence source environment before conditionHeap after condition statements bodyFinalContext returned
      conditionEvaluation bodyEvaluation
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique agree bodyCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, finalStore, finalMapping, finalWorld, related, bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | returned value typed => exact ⟨_, finalStore, finalMapping, finalWorld, .returned value typed,
        .returns conditionCore bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩

/-- The source location and the provider occurrence are retained separately
from the Word carried by Core. No injective reason provider is required. -/
inductive FaultRepresents (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) : Dynamic.SemanticFault → Core.Word → Prop where
  | uninitialized (site : ExpressionId) (location : Dynamic.Location)
      {context : Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {root : ExpressionId}
      (origin : PrimitiveExpressions.UninitializedAt program context evidence source environment heap root site location) :
      FaultRepresents program evidence source reasonAt (.uninitializedLocation location) (reasonAt site)

def BodyFaultPreserves (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (canonical actual : Core.Environment) (actualContext : Core.Context)
    (type : Core.Ty) (location : Core.Location) (statements : List StatementId) (code : Core.Expr)
    (reasonAt : ExpressionId → Core.Word) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap}
    {store : Core.Store} {finalContext : Context} {reason : Dynamic.SemanticFault},
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Core.RuntimeEnvironmentHasTypes world actual actualContext →
    world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
    Dynamic.StatementsFault program context evidence source environment heap statements finalContext reason after →
    ∃ resultReason finalStore finalMapping finalWorld,
      FaultRepresents program evidence source reasonAt reason resultReason ∧
      Core.Evaluates (bodyEnvironment type location actual) store (bodyCode code)
        (.inLeft (Core.LocalLoop.controlType type) (.word resultReason)) finalStore ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

def WhileFaultResult (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) (condition body : Core.Expr) (selfReason : Core.Word)
    (location : Core.Location) (actual : Core.Environment)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) : Prop :=
  ∃ resultReason finalStore finalMapping finalWorld,
    FaultRepresents program evidence source reasonAt reason resultReason ∧
    Core.LoopExecution.WhileTrace type condition body selfReason location actual store
      (.inLeft (Core.LocalLoop.controlType type) (.word resultReason)) finalStore ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

/-- Internal fault composition, including earlier successful iterations. The
body contracts remain explicit induction hypotheses, not compiler properties. -/
theorem while_fault
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (execution : Dynamic.WhileFaults program context evidence source environment heap condition statements reason after) :
    ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
      {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
      {body : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
      {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
      {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
      PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
      NodeOccurrencesUnique source → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
      Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
      BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location statements body →
      BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location statements body reasonAt →
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
      GeneralHeap.HeapRepresents mapping world heap store →
      Core.RuntimeEnvironmentHasTypes world actual actualContext →
      world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
      location ∉ mapping →
      store.read? location = some (.inRight .unit
        (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body (Core.LocalLoop.fallthrough type) selfReason location actual)) →
      WhileFaultResult program evidence source reasonAt type (conditionCode.rename ξ) body selfReason location actual
        mapping world store reason after := by
  refine @while_fault_induction program
    (fun context evidence source environment heap condition statements reason after =>
      ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
        {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
        {body : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
        {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
        {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
        PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
        NodeOccurrencesUnique source → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
        Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
        BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
          type location statements body →
        BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
          type location statements body reasonAt →
        GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
        GeneralHeap.HeapRepresents mapping world heap store →
        Core.RuntimeEnvironmentHasTypes world actual actualContext →
        world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) → location ∉ mapping →
        store.read? location = some (.inRight .unit
          (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body (Core.LocalLoop.fallthrough type) selfReason location actual)) →
        WhileFaultResult program evidence source reasonAt type (conditionCode.rename ξ) body selfReason location actual
          mapping world store reason after)
    ?_ ?_ ?_ ?_ ?_ context evidence source environment heap condition statements reason after execution
  · intro context evidence source environment before after condition statements reason conditionFault
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, site, faultLocation, rfl, origin, core⟩ := ScalarExpressionReflection.Primitive.source_fault
      conditionTree unique valid covers environments heaps conditionFault
    have restricted := GeneralExpressions.Primitive.readOnly conditionTree
    have renamed := restricted.evaluation_rename core agree
    have shifted := (restricted.rename ξ).evaluation_weakenAt_zero renamed
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)
    have shiftedAgain := ((restricted.rename ξ).weakenAt 0).evaluation_weakenAt_zero shifted .unit
    exact ⟨_, store, mapping, world, .uninitialized site faultLocation origin,
      .conditionFault shiftedAgain, heaps, .refl _, .refl _, .refl _ _⟩
  · intro context evidence source environment before after condition statements value actualType evaluation notBool actualTypeProof
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨_, staged, rfl, typed, _⟩ := ScalarExpressionReflection.Primitive.source_success
      conditionTree unique environments heaps evaluation
    obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
    exact False.elim (notBool trivial)
  · intro context evidence source environment before conditionHeap after condition statements finalContext reason
      conditionEvaluation bodyFault
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨resultReason, finalStore, finalMapping, finalWorld, related, bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyFaultCorrect environments heaps actualTyped selfTyped bodyFault
    exact ⟨_, finalStore, finalMapping, finalWorld, related, .bodyFault conditionCore bodyCore,
      finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment reason
      conditionEvaluation bodyEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | fallthrough =>
        obtain ⟨stillUnmapped, stillInstalled⟩ := self_retained unmapped installed bodyFrame
        obtain ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect
            (environments.extend mapsExtended worldsExtended) nextHeaps (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
            (worldsExtended.lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated,
          .nextFallthrough conditionCore bodyCore stillInstalled trace, finalHeaps,
          mapsExtended.trans mapsAgain, worldsExtended.trans worldsAgain, bodyFrame.trans nextFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition statements bodyFinalContext bodyEnvironment reason
      conditionEvaluation bodyEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | continuing =>
        obtain ⟨stillUnmapped, stillInstalled⟩ := self_retained unmapped installed bodyFrame
        obtain ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect
            (environments.extend mapsExtended worldsExtended) nextHeaps (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
            (worldsExtended.lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated,
          .nextContinue conditionCore bodyCore stillInstalled trace, finalHeaps,
          mapsExtended.trans mapsAgain, worldsExtended.trans worldsAgain, bodyFrame.trans nextFrame⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal
