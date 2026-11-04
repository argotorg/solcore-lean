import Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame
import Solcore.Core.LocalLoop
import Solcore.SourceSemantics.Dynamic
import Solcore.SourceSemantics.CoreLowering.ScalarExpressionReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.BasicStatementTreeCertificates
import Solcore.Frontend.SourceCoreLoops

/-!
# Loop certificates

Trees and certificates of loops and `for` headers, administration and Source induction.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopAdministration
/-! Install the actual generated loop closure in an administrative optional
cell. Captured environments and generated bodies are supplied concretely;
there is no assertion that renamed closure captures are equal. The source
heap and source-to-Core location map remain unchanged. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopAdministration

open GeneralHeap

def installedStore (store : Core.Store) (type : Core.Ty) (condition body post : Core.Expr)
    (reason : Core.Word) (environment : Core.Environment) : Core.Store :=
  store ++ [.inRight .unit (Core.LocalLoop.installedClosure type condition body post reason store.length environment)]

def installedWorld (world : Core.StoreTyping) (type : Core.Ty) : Core.StoreTyping :=
  world ++ [Core.OptionalCell.cellType (Core.LocalLoop.functionType type)]

/-- Ordinary finite-world typing validates a self-referential closure after
allocating its absent optional cell. Filling that cell leaves all source cells
and every earlier administrative cell unchanged. -/
theorem install
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    {environment : Core.Environment} {context : Core.Context} {type : Core.Ty}
    {condition body post : Core.Expr} (reason : Core.Word)
    (heaps : HeapRepresents mapping world heap store)
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment context)
    (wellFormed : Core.Ty.WellFormed [] type)
    (conditionTyped : Core.HasType context condition (Core.LanguageResult.resultType .bool))
    (bodyTyped : Core.HasType context body (Core.LocalLoop.resultType type))
    (postTyped : Core.HasType context post (Core.LocalLoop.resultType type)) :
    HeapRepresents mapping (installedWorld world type) heap (installedStore store type condition body post reason environment) ∧
    Core.WorldExtends world (installedWorld world type) ∧
    store.length ∉ mapping ∧
    (installedWorld world type)[store.length]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) ∧
    (installedStore store type condition body post reason environment).read? store.length =
      some (.inRight .unit (Core.LocalLoop.installedClosure type condition body post reason store.length environment)) ∧
    AdministrativePreserved mapping store mapping (installedStore store type condition body post reason environment) := by
  have worldExtension : Core.WorldExtends world (installedWorld world type) := ⟨_, rfl⟩
  have found : (installedWorld world type)[store.length]? =
      some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) := by
    rw [← heaps.runtime_hasTypes.length_eq]
    simp [installedWorld]
  have typed : Core.RuntimeValueHasType (installedWorld world type)
      (Core.LocalLoop.installedClosure type condition body post reason store.length environment)
      (Core.LocalLoop.functionType type) :=
    .closure (.cons (.cellRef found) (Core.RuntimeEnvironmentHasTypes.weaken worldExtension environmentTyped))
      (Core.LocalLoop.loopBody_hasType reason wellFormed conditionTyped bodyTyped postTyped)
  have absentTyped : Core.RuntimeValueHasType world (.inLeft (Core.LocalLoop.functionType type) .unit)
      (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) :=
    .inLeft .unit
  have allocated := heaps.allocate_administrative absentTyped
  have written : (store.allocate (.inLeft (Core.LocalLoop.functionType type) .unit)).1.write? store.length
      (.inRight .unit (Core.LocalLoop.installedClosure type condition body post reason store.length environment)) =
      some (installedStore store type condition body post reason environment) := by
    simp [Core.Store.allocate, Core.Store.write?, installedStore]
  have filled := allocated.write_administrative heaps.fresh_unmapped found (.inRight typed) written
  refine ⟨filled, worldExtension, ?_, found, ?_, ?_⟩
  · intro member
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
    exact heaps.fresh_unmapped lookup
  · simp [installedStore, Core.Store.read?]
  · exact AdministrativePreserved.allocate_administrative _ _ _

/-- Any later represented source computation preserves this installed loop
code whenever it supplies the administrative frame property. -/
theorem retained
    {mapping futureMapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store futureStore : Core.Store}
    {environment : Core.Environment} {type : Core.Ty} {condition body post : Core.Expr} {reason : Core.Word}
    (heaps : HeapRepresents mapping world heap store)
    (frame : AdministrativePreserved mapping (installedStore store type condition body post reason environment)
      futureMapping futureStore) :
    store.length ∉ futureMapping ∧ futureStore.read? store.length =
      some (.inRight .unit (Core.LocalLoop.installedClosure type condition body post reason store.length environment)) := by
  have unmapped : store.length ∉ mapping := by
    intro member
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
    exact heaps.fresh_unmapped lookup
  obtain ⟨futureUnmapped, same⟩ := frame store.length unmapped (by simp [installedStore])
  exact ⟨futureUnmapped, same.trans (by simp [installedStore, Core.Store.read?])⟩

end Solcore.SourceSemantics.CoreLowering.LoopAdministration
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopSourceInduction
/-! A focused induction principle derived from the independent, mutually
inductive source semantics. The source judgments and their constructors are
unchanged; unrelated expression/call premises receive the trivial motive. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements

open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

/-- Induction on finite source while derivations, retaining the successful
body derivations and the induction hypothesis for each next iteration. -/
theorem while_induction {program : Program}
    (motive : Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      ExpressionId → List StatementId → Context → ControlOutcome → Heap → Prop)
    (done : ∀ {context evidence source environment before after condition body},
      ExpressionEvaluates program context evidence source environment before condition (.bool false) after →
      motive context evidence source environment before condition body context (.fallthrough environment) after)
    (nextFallthrough : ∀ {context evidence source environment before conditionHeap bodyHeap after
        condition body bodyFinalContext bodyEnvironment outcome},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.fallthrough bodyEnvironment) bodyHeap →
      WhileExecutes program context evidence source environment bodyHeap condition body context outcome after →
      motive context evidence source environment bodyHeap condition body context outcome after →
      motive context evidence source environment before condition body context outcome after)
    (nextContinue : ∀ {context evidence source environment before conditionHeap bodyHeap after
        condition body bodyFinalContext bodyEnvironment outcome},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.continuing bodyEnvironment) bodyHeap →
      WhileExecutes program context evidence source environment bodyHeap condition body context outcome after →
      motive context evidence source environment bodyHeap condition body context outcome after →
      motive context evidence source environment before condition body context outcome after)
    (breaks : ∀ {context evidence source environment before conditionHeap after condition body bodyFinalContext bodyEnvironment},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.breaking bodyEnvironment) after →
      motive context evidence source environment before condition body context (.fallthrough environment) after)
    (returns : ∀ {context evidence source environment before conditionHeap after condition body bodyFinalContext result},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext (.returned result) after →
      motive context evidence source environment before condition body context (.returned result) after)
    {context evidence source environment before condition body finalContext outcome after}
    (execution : WhileExecutes program context evidence source environment before condition body finalContext outcome after) :
    motive context evidence source environment before condition body finalContext outcome after := by
  apply WhileExecutes.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_17 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_18 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_19 := fun context evidence source environment before condition body finalContext outcome after _ =>
      motive context evidence source environment before condition body finalContext outcome after)
    (motive_20 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (t := execution)
  all_goals intros
  all_goals first
    | exact True.intro
    | solve | apply done; assumption
    | solve | apply nextFallthrough <;> assumption
    | solve | apply nextContinue <;> assumption
    | solve | apply breaks <;> assumption
    | solve | apply returns <;> assumption

/-- Fault induction retains successful prefixes and follows only the first
faulting iteration. -/
theorem while_fault_induction {program : Program}
    (motive : Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      ExpressionId → List StatementId → SemanticFault → Heap → Prop)
    (conditionFault : ∀ {context evidence source environment before after condition body reason},
      ExpressionFaults program context evidence source environment before condition reason after →
      motive context evidence source environment before condition body reason after)
    (conditionType : ∀ {context evidence source environment before after condition body value actual},
      ExpressionEvaluates program context evidence source environment before condition value after →
      (¬ BooleanValue value) → ValueRuntimeType value actual →
      motive context evidence source environment before condition body (.typeMismatch .bool actual) after)
    (bodyFault : ∀ {context evidence source environment before conditionHeap after condition body finalContext reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsFault program context evidence source environment conditionHeap body finalContext reason after →
      motive context evidence source environment before condition body reason after)
    (nextFallthrough : ∀ {context evidence source environment before conditionHeap bodyHeap after
        condition body bodyFinalContext bodyEnvironment reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.fallthrough bodyEnvironment) bodyHeap →
      WhileFaults program context evidence source environment bodyHeap condition body reason after →
      motive context evidence source environment bodyHeap condition body reason after →
      motive context evidence source environment before condition body reason after)
    (nextContinue : ∀ {context evidence source environment before conditionHeap bodyHeap after
        condition body bodyFinalContext bodyEnvironment reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.continuing bodyEnvironment) bodyHeap →
      WhileFaults program context evidence source environment bodyHeap condition body reason after →
      motive context evidence source environment bodyHeap condition body reason after →
      motive context evidence source environment before condition body reason after)
    {context evidence source environment before condition body reason after}
    (execution : WhileFaults program context evidence source environment before condition body reason after) :
    motive context evidence source environment before condition body reason after := by
  apply WhileFaults.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_17 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_18 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_19 := fun context evidence source environment before condition body reason after _ =>
      motive context evidence source environment before condition body reason after)
    (motive_20 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (t := execution)
  all_goals intros
  all_goals first
    | exact True.intro
    | solve | apply conditionFault; assumption
    | solve | apply conditionType <;> assumption
    | solve | apply bodyFault <;> assumption
    | solve | apply nextFallthrough <;> assumption
    | solve | apply nextContinue <;> assumption

end Solcore.SourceSemantics.CoreLowering.LoopStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopFiniteComposition
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopStatementTree
/-! Static certificates for the default scalar/product while-loop profile.
The source tree describes syntax and checked metadata, not termination.
Finite executions will be related through independent source derivations.
For-header traversal is a separate extension; this initial grammar has while
loops, break and continue, without named calls or source closures. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- A finite control statement tree. `tailReturns` marks function sequencing;
nested blocks and conditional branches use ordinary statement sequencing. -/
inductive Tree (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (selfReason : Core.Word) :
    SourceCoreLocalCell.Scope → Context → Bool → List StatementId → Core.Ty → Core.Expr → Prop where
  | nil {scope context tailReturns type} :
      Tree compilation source reasonAt selfReason scope context tailReturns [] type (Core.LocalLoop.fallthrough type)
  | letUninitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType body}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder none)
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.letUninitialized payloadType body)
  | letInitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType
        initializer initializerCode body initializerDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder (some initializer))
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payloadType initializerCode initializerDepth)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) payloadType initializerCode body)
  | assign
      {scope context tailReturns id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .assignValue assignment .equal rhs)
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payloadType rhsCode rhsDepth)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType) (.var index) rhsCode body)
  | discard
      {scope context tailReturns id rest node nodeType valueId valueType resultType valueCode body valueDepth semicolon}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .expression valueId semicolon)
      (notTail : (!semicolon && tailReturns && rest.isEmpty) = false)
      (statementType : if semicolon then nodeType = .unit else nodeType = valueType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId valueType valueCode valueDepth)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.discard (Core.LocalLoop.controlType resultType) valueCode body)
  | returnValue
      {scope context tailReturns id node valueId resultType valueCode valueDepth}
      (rest : List StatementId)
      (metadata : Metadata source id node resultType)
      (form : node.form = .returnStmt (some valueId))
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.returnValue resultType valueCode)
  | returnUnit {scope context tailReturns id node}
      (rest : List StatementId)
      (metadata : Metadata source id node .unit)
      (form : node.form = .returnStmt none) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) .unit (Core.LocalLoop.returned .unit)
  | tailExpression
      {scope context id node valueId resultType valueCode valueDepth}
      (metadata : Metadata source id node resultType)
      (form : node.form = .expression valueId false)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree compilation source reasonAt selfReason scope context true [id] resultType (Core.LocalLoop.returnValue resultType valueCode)
  | block
      {scope context tailReturns id rest node nodeType statements resultType blockCode body}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .block statements)
      (block : Tree compilation source reasonAt selfReason scope context false statements resultType blockCode)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.sequence resultType blockCode body)
  | ifThen
      {scope context tailReturns id rest node nodeType condition thenBody elseBody resultType
        conditionCode thenCode elseCode body conditionDepth}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .ifThen condition thenBody elseBody)
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
      (thenTree : Tree compilation source reasonAt selfReason scope context false thenBody resultType thenCode)
      (elseTree : Tree compilation source reasonAt selfReason scope context false (elseBody.getD []) resultType elseCode)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.sequence resultType
          (Core.LocalLoop.conditional resultType conditionCode thenCode elseCode) body)

  | whileLoop
      {scope context tailReturns id rest node condition statements resultType conditionCode bodyCode body conditionDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .whileLoop condition statements)
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
      (loopBody : Tree compilation source reasonAt selfReason scope context false statements resultType bodyCode)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.sequence resultType (Core.LocalLoop.whileLoop resultType conditionCode bodyCode selfReason) body)
  | breaking {scope context tailReturns id node resultType}
      (rest : List StatementId) (metadata : Metadata source id node .unit) (form : node.form = .breakStmt) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.breaking resultType)
  | continuing {scope context tailReturns id node resultType}
      (rest : List StatementId) (metadata : Metadata source id node .unit) (form : node.form = .continueStmt) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.continuing resultType)

theorem Tree.hasType
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context tailReturns statements type code)
    (wellFormed : Core.Ty.WellFormed [] type) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LocalLoop.resultType type) := by
  induction tree with
  | nil => exact Core.LocalLoop.fallthrough_hasType wellFormed
  | returnUnit => exact Core.LocalLoop.returned_hasType .unit
  | breaking => exact Core.LocalLoop.breaking_hasType wellFormed
  | continuing => exact Core.LocalLoop.continuing_hasType wellFormed
  | returnValue _ _ _ value | tailExpression _ _ value =>
      exact Core.LocalLoop.returnValue_hasType wellFormed value.hasType
  | letUninitialized _ _ binding _ _ tail =>
      exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) (tail wellFormed)
  | letInitialized _ _ _ _ value _ tail =>
      exact Core.LocalSequence.letInitialized_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)
  | assign _ _ target value _ tail =>
      exact Core.LocalSequence.assign_hasType (Core.LocalLoop.controlType_wellFormed wellFormed)
        (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType (tail wellFormed)
  | discard _ _ _ _ value _ tail =>
      exact Core.LocalSequence.discard_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)
  | block _ _ _ _ block tail => exact Core.LocalLoop.sequence_hasType wellFormed (block wellFormed) (tail wellFormed)
  | ifThen _ _ condition _ _ _ thenTree elseTree tail =>
      exact Core.LocalLoop.sequence_hasType wellFormed
        (Core.LocalLoop.conditional_hasType wellFormed condition.hasType (thenTree wellFormed) (elseTree wellFormed))
        (tail wellFormed)

  | whileLoop _ _ condition _ _ loopBody tail =>
      exact Core.LocalLoop.sequence_hasType wellFormed
        (Core.LocalLoop.whileLoop_hasType selfReason wellFormed condition.hasType (loopBody wellFormed))
        (tail wellFormed)

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForHeaderTree
/-! Static certificates for the default scalar/product `for` header compiler.
A header threads binder scope and source context into a static continuation.
The continuation predicate contains syntax certificates only; no source/Core
execution or termination witness is part of this tree. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- A header can allocate ordinary scalar/product locals, assign a bare local
with `=`, or discard a primitive expression. Its continuation is indexed by
the resulting lexical scope and context, so initializer bindings remain in
scope for the loop and post bindings can be discharged after each iteration. -/
inductive Tree (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (resultType : Core.Ty)
    (continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop) :
    SourceCoreLocalCell.Scope → Context → List ForItemForm → Core.Expr → Prop where
  | nil {scope context code}
      (next : continuation scope context code) :
      Tree compilation source reasonAt resultType continuation scope context [] code
  | letUninitialized {scope context middleContext binder rest payloadType body}
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree compilation source reasonAt resultType continuation
        ((binder.id, payloadType) :: scope) middleContext rest body) :
      Tree compilation source reasonAt resultType continuation scope context (.letDecl binder none :: rest)
        (Core.LocalSequence.letUninitialized payloadType body)
  | letInitialized {scope context middleContext binder rest payloadType initializer initializerCode body depth}
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payloadType initializerCode depth)
      (tail : Tree compilation source reasonAt resultType continuation
        ((binder.id, payloadType) :: scope) middleContext rest body) :
      Tree compilation source reasonAt resultType continuation scope context (.letDecl binder (some initializer) :: rest)
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) payloadType initializerCode body)
  | assign {scope context assignment index payloadType rhs rhsCode rest body depth}
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payloadType rhsCode depth)
      (tail : Tree compilation source reasonAt resultType continuation scope context rest body) :
      Tree compilation source reasonAt resultType continuation scope context (.assignValue assignment .equal rhs :: rest)
        (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType) (.var index) rhsCode body)
  | discard {scope context expression expressionType expressionCode rest body depth}
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt expression expressionType expressionCode depth)
      (tail : Tree compilation source reasonAt resultType continuation scope context rest body) :
      Tree compilation source reasonAt resultType continuation scope context (.expression expression :: rest)
        (Core.LocalSequence.discard (Core.LocalLoop.controlType resultType) expressionCode body)

/-- The post-vector finishes normally. Its final lexical names are intentionally
absent from the next iteration's source scope. -/
def Fallthrough (type : Core.Ty) (_scope : SourceCoreLocalCell.Scope) (_context : Context) (code : Core.Expr) : Prop :=
  code = Core.LocalLoop.fallthrough type

theorem Tree.hasType
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType continuation scope context items code)
    (wellFormed : Core.Ty.WellFormed [] resultType)
    (nextTyped : ∀ {scope context code}, continuation scope context code →
      Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LocalLoop.resultType resultType)) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LocalLoop.resultType resultType) := by
  induction tree with
  | nil next => exact nextTyped next
  | letUninitialized binding _ _ tail =>
    exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) tail
  | letInitialized _ _ value _ tail =>
    exact Core.LocalSequence.letInitialized_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType tail
  | assign target value _ tail =>
    exact Core.LocalSequence.assign_hasType (Core.LocalLoop.controlType_wellFormed wellFormed)
      (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType tail
  | discard value _ tail =>
    exact Core.LocalSequence.discard_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType tail

theorem Tree.map
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {left right : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType left scope context items code)
    (next : ∀ {scope context code}, left scope context code → right scope context code) :
    Tree compilation source reasonAt resultType right scope context items code := by
  induction tree with
  | nil certificate => exact .nil (next certificate)
  | letUninitialized binding extension _ tail => exact .letUninitialized binding extension tail
  | letInitialized binding extension value _ tail => exact .letInitialized binding extension value tail
  | assign target value _ tail => exact .assign target value tail
  | discard value _ tail => exact .discard value tail

end Solcore.SourceSemantics.CoreLowering.ForHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopStatementCertificates
/-! Extract scoped default while-loop statement trees from the actual successful compiler.
The ambient context/scope alignment and unique source occurrences are static
premises. For-header traversal is explicitly excluded by syntax. Neither child
trees nor source/Core evaluations are assumed; no termination is concluded. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- This certificate grammar covers while loops. Exclusion of for headers is
a static source-table condition, including nested statement occurrences. -/
def NoForLoops (source : TypedSource) : Prop :=
  ∀ {id : StatementId} {node : StatementNode}, source.lookupStatement? id = some node →
    ∀ initializer condition post body, node.form ≠ .forLoop initializer condition post body

/-- The default compiler policy authenticated by this certificate. -/
def defaultPolicy (compilation : SourceCorePrimitive.Context) : SourceCoreLoops.Policy :=
  { lowerExpression := fun fuel source scope id reasonAt =>
      SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt }

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok
    {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Function and nested-list tail conventions are both recovered from
successful lowering. Branch/block binders remain local to their child tree. -/
theorem tree_of_lowerFlowStatements
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (defaultPolicy compilation)
      fuel source scope statements resultType reasonAt tailReturns selfReason = .ok code) :
    Tree compilation source reasonAt selfReason scope context tailReturns statements resultType code := by
  induction fuel generalizing scope context statements code tailReturns with
  | zero =>
      cases statements with
      | nil =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
          cases accepted; exact .nil
      | cons =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
          cases accepted
  | succ fuel ih =>
      cases statements with
      | nil =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
          cases accepted; exact .nil
      | cons id rest =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, defaultPolicy] at accepted
          obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
          have metadata := (readStatement_certificate read).2
          cases form : node.form with
          | letDecl binder initializer =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
              have certificate := lowerBinder_certificate binding
              have extension := certificate.extends aligned
              cases initializer with
              | none =>
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .letUninitialized metadata form certificate extension
                    (ih (aligned.bind binder payload) compiledBody)
              | some initializer =>
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  simp only [certificate.monomorphic, List.isEmpty_nil, ↓reduceIte] at accepted
                  cases accepted
                  obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .letInitialized metadata form certificate extension valueTree
                    (ih (aligned.bind binder payload) compiledBody)
          | assignValue assignment operator rhs =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              let assignmentStep := fun operator => do
                let (index, payload) ← SourceCoreBasic.lowerAssignment source scope assignment operator
                let value ← SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope rhs reasonAt
                SourceCoreBasic.ensureType (.binder assignment.target.root) payload value.type
                pure (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType)
                  (.var index) value.expression body)
              change (match operator, (defaultPolicy compilation).assignValue with
                | .equal, _ | _, none => assignmentStep operator
                | _, some callback => callback (defaultPolicy compilation).lowerExpression fuel source scope
                    (.occurrence id.occurrence) assignment operator rhs (Core.LocalLoop.controlType resultType)
                    body reasonAt) = .ok code at accepted
              cases operator <;> dsimp only [defaultPolicy, assignmentStep] at accepted
              all_goals
                obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
                have targetCertificate := lowerAssignment_certificate target
                have equal := targetCertificate.equal
                cases equal
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              cases accepted
              obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
              rw [← ensureType_ok checked] at valueTree
              exact .assign metadata form targetCertificate valueTree (ih aligned compiledBody)
          | returnStmt value =>
              cases value with
              | none =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultUnit : resultType = .unit :=
                    (ensureType_ok resultChecked).trans (ensureType_ok unitChecked).symm
                  rw [← ensureType_ok unitChecked] at metadata
                  cases accepted
                  rw [resultUnit]
                  exact .returnUnit rest metadata form
              | some value =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  rw [← ensureType_ok resultChecked] at metadata
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  cases accepted
                  obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .returnValue rest metadata form valueTree
          | expression value semicolon =>
              simp only [form] at accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
              split at accepted
              · rename_i isTail
                have shape : semicolon = false ∧ tailReturns = true ∧ rest = [] := by
                  cases semicolon <;> cases tailReturns <;> cases rest <;> simp_all
                obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                cases checkedUnit
                rw [← ensureType_ok resultChecked] at metadata
                obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                cases checkedUnit
                cases accepted
                rw [← ensureType_ok checked] at valueTree
                rcases shape with ⟨rfl, rfl, rfl⟩
                exact .tailExpression metadata form valueTree
              · rename_i notTail
                have notTail : (!semicolon && tailReturns && rest.isEmpty) = false := by simpa using notTail
                cases semicolon with
                | true =>
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                    cases accepted
                    exact .discard metadata form notTail (ensureType_ok checked).symm
                      valueTree (ih aligned compiledBody)
                | false =>
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                    cases accepted
                    exact .discard metadata form notTail (ensureType_ok checked)
                      valueTree (ih aligned compiledBody)
          | block statements =>
              simp only [form] at accepted
              obtain ⟨block, compiledBlock, accepted⟩ := bind_ok accepted
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              exact .block metadata form (ih aligned compiledBlock) (ih aligned compiledBody)
          | ifThen condition thenBody elseBody =>
              simp only [form] at accepted
              obtain ⟨condition, compiledCondition, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨thenBranch, compiledThen, accepted⟩ := bind_ok accepted
              obtain ⟨_, _, conditionTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledCondition
              rw [← ensureType_ok checked] at conditionTree
              cases elseBody with
              | none =>
                  obtain ⟨elseBranch, compiledElse, accepted⟩ := bind_ok accepted
                  cases compiledElse
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .ifThen metadata form conditionTree (ih aligned compiledThen) .nil (ih aligned compiledBody)
              | some statements =>
                  obtain ⟨elseBranch, compiledElse, accepted⟩ := bind_ok accepted
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .ifThen metadata form conditionTree (ih aligned compiledThen)
                    (ih aligned compiledElse) (ih aligned compiledBody)
          | whileLoop condition statements =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok unitChecked] at metadata
              obtain ⟨condition, compiledCondition, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨loopBody, compiledLoopBody, accepted⟩ := bind_ok accepted
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              obtain ⟨_, _, conditionTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledCondition
              rw [← ensureType_ok checked] at conditionTree
              exact .whileLoop metadata form conditionTree (ih aligned compiledLoopBody) (ih aligned compiledBody)
          | breakStmt =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              cases accepted
              exact .breaking rest metadata form
          | continueStmt =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              cases accepted
              exact .continuing rest metadata form
          | forLoop initializer condition post statements =>
              exact False.elim (noFor (readStatement_certificate read).1 initializer condition post statements form)
          | assignBitNot =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases accepted
          | matchWith => simp [form] at accepted

/-- Recover the default flow tree through the expression-policy compatibility
wrapper used by the public default statement compiler. -/
theorem tree_of_lowerFlowStatementsWithExpression
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {statements : List StatementId}
    {resultType : Core.Ty} {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word}
    {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasonAt => SourceCorePrimitive.lowerExpressionWithReasons
        fuel compilation source scope id reasonAt)
      fuel source scope statements resultType reasonAt tailReturns selfReason = .ok code) :
    Tree compilation source reasonAt selfReason scope context tailReturns statements resultType code :=
  tree_of_lowerFlowStatements aligned unique noFor accepted

/-- The actual function compiler supplies its complete flow tree and precise
finish expression. Escaped loop control and non-Unit fallthrough keep their
separate supplied language failure tokens. -/
theorem tree_of_lowerStatements
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {statements : List StatementId}
    {resultType : Core.Ty} {reasonAt : ExpressionId → Core.Word}
    {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements
      resultType reasonAt fellThroughReason escapedReason = .ok code) :
    ∃ flow, code = Core.LocalControl.finish resultType
        (Core.LocalLoop.toControl resultType flow escapedReason)
        (if resultType = .unit then Core.LanguageResult.success .unit
         else Core.LanguageResult.failure resultType (.word fellThroughReason)) ∧
      Tree compilation source reasonAt escapedReason scope context true statements resultType flow := by
  unfold SourceCoreLoops.lowerStatementsWithReasons SourceCoreLoops.lowerStatementsWithExpression
    SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, compiledFlow, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨flow, rfl, tree_of_lowerFlowStatements aligned unique noFor compiledFlow⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForHeaderCertificates
/-! Recover a static default header tree from actual compiler success. The
continuation hypothesis authenticates successful continuation code using only
its static scope/context alignment; no evaluation premise is accepted. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements
open LoopStatements.Default

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok
    {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

theorem tree_of_lowerForItems
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {site : SourceCoreElaboration.ErrorSite} {code : Core.Expr}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Core.Expr}
    {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (nextCertificate : ∀ {scope context code}, ScopeContextAligned scope context →
      next scope = .ok code → continuation scope context code)
    (accepted : SourceCoreLoops.lowerForItems (defaultPolicy compilation) site fuel source scope items type reasonAt next = .ok code) :
    Tree compilation source reasonAt type continuation scope context items code := by
  induction fuel generalizing scope context items code with
  | zero =>
    cases items with
    | nil => exact .nil (nextCertificate aligned accepted)
    | cons => cases accepted
  | succ fuel ih =>
    cases items with
    | nil => exact .nil (nextCertificate aligned accepted)
    | cons item rest =>
      simp only [SourceCoreLoops.lowerForItems, defaultPolicy] at accepted
      cases item with
      | letDecl binder initializer =>
        obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
        have certificate := lowerBinder_certificate binding
        have extension := certificate.extends aligned
        obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
        have tail := ih (aligned.bind binder payload) compiledBody
        cases initializer with
        | none => cases accepted; exact .letUninitialized certificate extension tail
        | some initializer =>
          obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
          obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          simp only [certificate.monomorphic, List.isEmpty_nil, ↓reduceIte] at accepted
          cases accepted
          obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
          rw [← ensureType_ok checked] at valueTree
          exact .letInitialized certificate extension valueTree tail
      | expression expression =>
        obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
        exact .discard valueTree (ih aligned compiledBody)
      | assignValue assignment operator rhs =>
        obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
        let assignmentStep := fun operator => do
          let (index, payload) ← SourceCoreBasic.lowerAssignment source scope assignment operator
          let value ← SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope rhs reasonAt
          SourceCoreBasic.ensureType (.binder assignment.target.root) payload value.type
          pure (Core.LocalSequence.assign (Core.LocalLoop.controlType type) (.var index) value.expression body)
        change (match operator, (defaultPolicy compilation).assignValue with
          | .equal, _ | _, none => assignmentStep operator
          | _, some callback => callback (defaultPolicy compilation).lowerExpression fuel source scope site
              assignment operator rhs (Core.LocalLoop.controlType type) body reasonAt) = .ok code at accepted
        cases operator <;> dsimp only [defaultPolicy, assignmentStep] at accepted
        all_goals
          obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
          have certificate := lowerAssignment_certificate target
          have equal := certificate.equal
          cases equal
        obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
        obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
        cases checkedUnit
        cases accepted
        obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
        rw [← ensureType_ok checked] at valueTree
        exact .assign certificate valueTree (ih aligned compiledBody)
      | assignBitNot assignment => cases accepted

theorem tree_of_lowerPost
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {site : SourceCoreElaboration.ErrorSite} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerForItems (defaultPolicy compilation) site fuel source scope items type reasonAt
      (fun _ => .ok (Core.LocalLoop.fallthrough type)) = .ok code) :
    Tree compilation source reasonAt type (Fallthrough type) scope context items code :=
  tree_of_lowerForItems aligned unique (fun _ accepted => Except.ok.inj accepted.symm) accepted

end Solcore.SourceSemantics.CoreLowering.ForHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForLoopStatementTree
/-! Static certificates for the complete default scalar/product loop profile.
Statement lists and initializer vectors are separate indices of one tree, so
structural induction traverses a nested loop body without any evaluation
hypothesis or an additional mutually recursive semantics. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

inductive Position where
  | statements (tailReturns : Bool) (statements : List StatementId)
  | initializers (items : List ForItemForm) (condition : ExpressionId)
      (post : List ForItemForm) (statements : List StatementId)

/-- A finite control statement tree. `tailReturns` marks function sequencing;
nested blocks and conditional branches use ordinary statement sequencing. -/
inductive Tree (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (selfReason : Core.Word) :
    SourceCoreLocalCell.Scope → Context → Position → Core.Ty → Core.Expr → Prop where
  | nil {scope context tailReturns type} :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns []) type (Core.LocalLoop.fallthrough type)
  | letUninitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType body}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder none)
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalSequence.letUninitialized payloadType body)
  | letInitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType
        initializer initializerCode body initializerDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder (some initializer))
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payloadType initializerCode initializerDepth)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) payloadType initializerCode body)
  | assign
      {scope context tailReturns id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .assignValue assignment .equal rhs)
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payloadType rhsCode rhsDepth)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType) (.var index) rhsCode body)
  | discard
      {scope context tailReturns id rest node nodeType valueId valueType resultType valueCode body valueDepth semicolon}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .expression valueId semicolon)
      (notTail : (!semicolon && tailReturns && rest.isEmpty) = false)
      (statementType : if semicolon then nodeType = .unit else nodeType = valueType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId valueType valueCode valueDepth)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalSequence.discard (Core.LocalLoop.controlType resultType) valueCode body)
  | returnValue
      {scope context tailReturns id node valueId resultType valueCode valueDepth}
      (rest : List StatementId)
      (metadata : Metadata source id node resultType)
      (form : node.form = .returnStmt (some valueId))
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.returnValue resultType valueCode)
  | returnUnit {scope context tailReturns id node}
      (rest : List StatementId)
      (metadata : Metadata source id node .unit)
      (form : node.form = .returnStmt none) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) .unit (Core.LocalLoop.returned .unit)
  | tailExpression
      {scope context id node valueId resultType valueCode valueDepth}
      (metadata : Metadata source id node resultType)
      (form : node.form = .expression valueId false)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree compilation source reasonAt selfReason scope context (.statements true [id]) resultType (Core.LocalLoop.returnValue resultType valueCode)
  | block
      {scope context tailReturns id rest node nodeType statements resultType blockCode body}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .block statements)
      (block : Tree compilation source reasonAt selfReason scope context (.statements false statements) resultType blockCode)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.sequence resultType blockCode body)
  | ifThen
      {scope context tailReturns id rest node nodeType condition thenBody elseBody resultType
        conditionCode thenCode elseCode body conditionDepth}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .ifThen condition thenBody elseBody)
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
      (thenTree : Tree compilation source reasonAt selfReason scope context (.statements false thenBody) resultType thenCode)
      (elseTree : Tree compilation source reasonAt selfReason scope context (.statements false (elseBody.getD [])) resultType elseCode)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.sequence resultType
          (Core.LocalLoop.conditional resultType conditionCode thenCode elseCode) body)

  | whileLoop
      {scope context tailReturns id rest node condition statements resultType conditionCode bodyCode body conditionDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .whileLoop condition statements)
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
      (loopBody : Tree compilation source reasonAt selfReason scope context (.statements false statements) resultType bodyCode)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.sequence resultType (Core.LocalLoop.whileLoop resultType conditionCode bodyCode selfReason) body)
  | forLoop
      {scope context tailReturns id rest node initializer condition post statements resultType loopCode body}
      (metadata : Metadata source id node .unit)
      (form : node.form = .forLoop initializer condition post statements)
      (initialTree : Tree compilation source reasonAt selfReason scope context
        (.initializers initializer condition post statements) resultType loopCode)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.sequence resultType loopCode body)
  | initializersDone
      {scope context condition post statements resultType conditionCode bodyCode postCode depth}
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
      (bodyTree : Tree compilation source reasonAt selfReason scope context (.statements false statements) resultType bodyCode)
      (postTree : ForHeaders.Tree compilation source reasonAt resultType (ForHeaders.Fallthrough resultType) scope context post postCode) :
      Tree compilation source reasonAt selfReason scope context (.initializers [] condition post statements) resultType
        (Core.LocalLoop.iterate resultType conditionCode bodyCode postCode selfReason)
  | initializerUninitialized
      {scope context middleContext binder rest condition post statements payloadType resultType body}
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        (.initializers rest condition post statements) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.initializers (.letDecl binder none :: rest) condition post statements) resultType
        (Core.LocalSequence.letUninitialized payloadType body)
  | initializerInitialized
      {scope context middleContext binder rest condition post statements payloadType resultType initializer initializerCode body depth}
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payloadType initializerCode depth)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        (.initializers rest condition post statements) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) resultType
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) payloadType initializerCode body)
  | initializerAssign
      {scope context assignment index payloadType rhs rhsCode rest condition post statements resultType body depth}
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payloadType rhsCode depth)
      (tail : Tree compilation source reasonAt selfReason scope context (.initializers rest condition post statements) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.initializers (.assignValue assignment .equal rhs :: rest) condition post statements) resultType
        (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType) (.var index) rhsCode body)
  | initializerDiscard
      {scope context expression expressionType expressionCode rest condition post statements resultType body depth}
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt expression expressionType expressionCode depth)
      (tail : Tree compilation source reasonAt selfReason scope context (.initializers rest condition post statements) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.initializers (.expression expression :: rest) condition post statements) resultType
        (Core.LocalSequence.discard (Core.LocalLoop.controlType resultType) expressionCode body)
  | breaking {scope context tailReturns id node resultType}
      (rest : List StatementId) (metadata : Metadata source id node .unit) (form : node.form = .breakStmt) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.breaking resultType)
  | continuing {scope context tailReturns id node resultType}
      (rest : List StatementId) (metadata : Metadata source id node .unit) (form : node.form = .continueStmt) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.continuing resultType)

theorem Tree.hasType
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code)
    (wellFormed : Core.Ty.WellFormed [] type) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LocalLoop.resultType type) := by
  induction tree with
  | nil => exact Core.LocalLoop.fallthrough_hasType wellFormed
  | returnUnit => exact Core.LocalLoop.returned_hasType .unit
  | breaking => exact Core.LocalLoop.breaking_hasType wellFormed
  | continuing => exact Core.LocalLoop.continuing_hasType wellFormed
  | returnValue _ _ _ value | tailExpression _ _ value =>
      exact Core.LocalLoop.returnValue_hasType wellFormed value.hasType
  | letUninitialized _ _ binding _ _ tail =>
      exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) (tail wellFormed)
  | letInitialized _ _ _ _ value _ tail =>
      exact Core.LocalSequence.letInitialized_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)
  | assign _ _ target value _ tail =>
      exact Core.LocalSequence.assign_hasType (Core.LocalLoop.controlType_wellFormed wellFormed)
        (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType (tail wellFormed)
  | discard _ _ _ _ value _ tail =>
      exact Core.LocalSequence.discard_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)
  | block _ _ _ _ block tail => exact Core.LocalLoop.sequence_hasType wellFormed (block wellFormed) (tail wellFormed)
  | ifThen _ _ condition _ _ _ thenTree elseTree tail =>
      exact Core.LocalLoop.sequence_hasType wellFormed
        (Core.LocalLoop.conditional_hasType wellFormed condition.hasType (thenTree wellFormed) (elseTree wellFormed))
        (tail wellFormed)

  | whileLoop _ _ condition _ _ loopBody tail =>
      exact Core.LocalLoop.sequence_hasType wellFormed
        (Core.LocalLoop.whileLoop_hasType selfReason wellFormed condition.hasType (loopBody wellFormed))
        (tail wellFormed)

  | forLoop _ _ _ _ initial tail =>
      exact Core.LocalLoop.sequence_hasType wellFormed (initial wellFormed) (tail wellFormed)
  | initializersDone condition _ post body =>
      apply Core.LocalLoop.iterate_hasType selfReason wellFormed condition.hasType (body wellFormed)
      apply post.hasType wellFormed
      intro scope context code endpoint
      cases endpoint
      exact Core.LocalLoop.fallthrough_hasType wellFormed
  | initializerUninitialized binding _ _ tail =>
      exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) (tail wellFormed)
  | initializerInitialized _ _ value _ tail =>
      exact Core.LocalSequence.letInitialized_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)
  | initializerAssign target value _ tail =>
      exact Core.LocalSequence.assign_hasType (Core.LocalLoop.controlType_wellFormed wellFormed)
        (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType (tail wellFormed)
  | initializerDiscard value _ tail =>
      exact Core.LocalSequence.discard_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)

/-- Generic header acceptance can authenticate the empty-header continuation
first, then reconstruct every initializer binder and expression around it. -/
theorem Tree.ofHeader
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {items post : List ForItemForm}
    {condition : ExpressionId} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (header : ForHeaders.Tree compilation source reasonAt type
      (fun scope context code => Tree compilation source reasonAt selfReason scope context (.initializers [] condition post statements) type code)
      scope context items code) :
    Tree compilation source reasonAt selfReason scope context (.initializers items condition post statements) type code := by
  induction header with
  | nil next => exact next
  | letUninitialized binding extension _ tail => exact .initializerUninitialized binding extension tail
  | letInitialized binding extension value _ tail => exact .initializerInitialized binding extension value tail
  | assign target value _ tail => exact .initializerAssign target value tail
  | discard value _ tail => exact .initializerDiscard value tail


end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForLoopStatementCertificates
/-! Actual default loop compiler success yields a complete static certificate,
including initializer scopes and post vectors. Nested while/for bodies use
the same smaller compiler fuel; no source/Core execution is assumed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements
open Default (defaultPolicy)

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok
    {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Function and nested-list tail conventions are both recovered from
successful lowering. Branch/block binders remain local to their child tree. -/
theorem tree_of_lowerFlowStatements
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (defaultPolicy compilation)
      fuel source scope statements resultType reasonAt tailReturns selfReason = .ok code) :
    Tree compilation source reasonAt selfReason scope context (.statements tailReturns statements) resultType code := by
  induction fuel generalizing scope context statements code tailReturns with
  | zero =>
      cases statements with
      | nil =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
          cases accepted; exact .nil
      | cons =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
          cases accepted
  | succ fuel ih =>
      cases statements with
      | nil =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
          cases accepted; exact .nil
      | cons id rest =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, defaultPolicy] at accepted
          obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
          have metadata := (readStatement_certificate read).2
          cases form : node.form with
          | letDecl binder initializer =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
              have certificate := lowerBinder_certificate binding
              have extension := certificate.extends aligned
              cases initializer with
              | none =>
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .letUninitialized metadata form certificate extension
                    (ih (aligned.bind binder payload) compiledBody)
              | some initializer =>
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  simp only [certificate.monomorphic, List.isEmpty_nil, ↓reduceIte] at accepted
                  cases accepted
                  obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .letInitialized metadata form certificate extension valueTree
                    (ih (aligned.bind binder payload) compiledBody)
          | assignValue assignment operator rhs =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              let assignmentStep := fun operator => do
                let (index, payload) ← SourceCoreBasic.lowerAssignment source scope assignment operator
                let value ← SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope rhs reasonAt
                SourceCoreBasic.ensureType (.binder assignment.target.root) payload value.type
                pure (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType)
                  (.var index) value.expression body)
              change (match operator, (defaultPolicy compilation).assignValue with
                | .equal, _ | _, none => assignmentStep operator
                | _, some callback => callback (defaultPolicy compilation).lowerExpression fuel source scope
                    (.occurrence id.occurrence) assignment operator rhs (Core.LocalLoop.controlType resultType)
                    body reasonAt) = .ok code at accepted
              cases operator <;> dsimp only [defaultPolicy, assignmentStep] at accepted
              all_goals
                obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
                have targetCertificate := lowerAssignment_certificate target
                have equal := targetCertificate.equal
                cases equal
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              cases accepted
              obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
              rw [← ensureType_ok checked] at valueTree
              exact .assign metadata form targetCertificate valueTree (ih aligned compiledBody)
          | returnStmt value =>
              cases value with
              | none =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultUnit : resultType = .unit :=
                    (ensureType_ok resultChecked).trans (ensureType_ok unitChecked).symm
                  rw [← ensureType_ok unitChecked] at metadata
                  cases accepted
                  rw [resultUnit]
                  exact .returnUnit rest metadata form
              | some value =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  rw [← ensureType_ok resultChecked] at metadata
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  cases accepted
                  obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .returnValue rest metadata form valueTree
          | expression value semicolon =>
              simp only [form] at accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
              split at accepted
              · rename_i isTail
                have shape : semicolon = false ∧ tailReturns = true ∧ rest = [] := by
                  cases semicolon <;> cases tailReturns <;> cases rest <;> simp_all
                obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                cases checkedUnit
                rw [← ensureType_ok resultChecked] at metadata
                obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                cases checkedUnit
                cases accepted
                rw [← ensureType_ok checked] at valueTree
                rcases shape with ⟨rfl, rfl, rfl⟩
                exact .tailExpression metadata form valueTree
              · rename_i notTail
                have notTail : (!semicolon && tailReturns && rest.isEmpty) = false := by simpa using notTail
                cases semicolon with
                | true =>
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                    cases accepted
                    exact .discard metadata form notTail (ensureType_ok checked).symm
                      valueTree (ih aligned compiledBody)
                | false =>
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                    cases accepted
                    exact .discard metadata form notTail (ensureType_ok checked)
                      valueTree (ih aligned compiledBody)
          | block statements =>
              simp only [form] at accepted
              obtain ⟨block, compiledBlock, accepted⟩ := bind_ok accepted
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              exact .block metadata form (ih aligned compiledBlock) (ih aligned compiledBody)
          | ifThen condition thenBody elseBody =>
              simp only [form] at accepted
              obtain ⟨condition, compiledCondition, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨thenBranch, compiledThen, accepted⟩ := bind_ok accepted
              obtain ⟨_, _, conditionTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledCondition
              rw [← ensureType_ok checked] at conditionTree
              cases elseBody with
              | none =>
                  obtain ⟨elseBranch, compiledElse, accepted⟩ := bind_ok accepted
                  cases compiledElse
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .ifThen metadata form conditionTree (ih aligned compiledThen) .nil (ih aligned compiledBody)
              | some statements =>
                  obtain ⟨elseBranch, compiledElse, accepted⟩ := bind_ok accepted
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .ifThen metadata form conditionTree (ih aligned compiledThen)
                    (ih aligned compiledElse) (ih aligned compiledBody)
          | whileLoop condition statements =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok unitChecked] at metadata
              obtain ⟨condition, compiledCondition, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨loopBody, compiledLoopBody, accepted⟩ := bind_ok accepted
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              obtain ⟨_, _, conditionTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledCondition
              rw [← ensureType_ok checked] at conditionTree
              exact .whileLoop metadata form conditionTree (ih aligned compiledLoopBody) (ih aligned compiledBody)
          | breakStmt =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              cases accepted
              exact .breaking rest metadata form
          | continueStmt =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              cases accepted
              exact .continuing rest metadata form
          | forLoop initializer condition post statements =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok unitChecked] at metadata
              obtain ⟨loopCode, compiledInitializers, accepted⟩ := bind_ok accepted
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              refine .forLoop metadata form (Tree.ofHeader (ForHeaders.tree_of_lowerForItems aligned unique ?_ compiledInitializers))
                (ih aligned compiledBody)
              intro loopScope loopContext loopCode loopAligned compiledIteration
              obtain ⟨conditionValue, compiledCondition, compiledIteration⟩ := bind_ok compiledIteration
              obtain ⟨checkedUnit, checked, compiledIteration⟩ := bind_ok compiledIteration
              cases checkedUnit
              obtain ⟨loopBody, compiledLoopBody, compiledIteration⟩ := bind_ok compiledIteration
              obtain ⟨postCode, compiledPost, compiledIteration⟩ := bind_ok compiledIteration
              cases compiledIteration
              obtain ⟨_, _, conditionTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledCondition
              rw [← ensureType_ok checked] at conditionTree
              exact .initializersDone conditionTree (ih loopAligned compiledLoopBody)
                (ForHeaders.tree_of_lowerPost loopAligned unique compiledPost)
          | assignBitNot =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases accepted
          | matchWith => simp [form] at accepted

/-- Recover the default flow tree through the expression-policy compatibility
wrapper used by the public default statement compiler. -/
theorem tree_of_lowerFlowStatementsWithExpression
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {statements : List StatementId}
    {resultType : Core.Ty} {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word}
    {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasonAt => SourceCorePrimitive.lowerExpressionWithReasons
        fuel compilation source scope id reasonAt)
      fuel source scope statements resultType reasonAt tailReturns selfReason = .ok code) :
    Tree compilation source reasonAt selfReason scope context (.statements tailReturns statements) resultType code :=
  tree_of_lowerFlowStatements aligned unique accepted

/-- The actual function compiler supplies its complete flow tree and precise
finish expression. Escaped loop control and non-Unit fallthrough keep their
separate supplied language failure tokens. -/
theorem tree_of_lowerStatements
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {statements : List StatementId}
    {resultType : Core.Ty} {reasonAt : ExpressionId → Core.Word}
    {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements
      resultType reasonAt fellThroughReason escapedReason = .ok code) :
    ∃ flow, code = Core.LocalControl.finish resultType
        (Core.LocalLoop.toControl resultType flow escapedReason)
        (if resultType = .unit then Core.LanguageResult.success .unit
         else Core.LanguageResult.failure resultType (.word fellThroughReason)) ∧
      Tree compilation source reasonAt escapedReason scope context (.statements true statements) resultType flow := by
  unfold SourceCoreLoops.lowerStatementsWithReasons SourceCoreLoops.lowerStatementsWithExpression
    SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, compiledFlow, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨flow, rfl, tree_of_lowerFlowStatements aligned unique compiledFlow⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end
