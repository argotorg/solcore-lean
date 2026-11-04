import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperativeFor
import Solcore.Frontend.SourceCoreCompatibleDataPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopLayouts
import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews
import Solcore.SourceSemantics.CoreLowering.ScalarAssignmentReflection

/-!
# Finite loops

Finite success and reflection of loops, and the statement bridge.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForHeaderNativeBounds
/-! Bounds obtained from the original emitted Core derivation. Known phase
executions align values and stores by determinism; every remaining size comes
from an actual child derivation. No continuation equivalence is assigned a
cost, and renaming beneath the six post values keeps the original size. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ForHeaderNativeBounds
open Core Frontend CoreProof
open SourceCoreCompatibleDataPlaces
open DataPlaceExecution (referenceEnvironment keysEnvironment snapshotEnvironment rhsEnvironment modifiedEnvironment writtenEnvironment)

/-- A marked allocation is a real let node, so its remaining body is smaller. -/
theorem allocation_body {size : Nat} {environment : Environment} {before middle after : Store}
    {allocation body : Expr} {reference value : Value}
    (completed : EvaluationSize size environment before (.letE allocation body) value after)
    (allocated : Evaluates environment before allocation reference middle) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize (reference :: environment) middle body value after :=
  completed.let_body allocated

/-- Initialized headers retain both inserted values and both real boundaries. -/
theorem initialized_body {size : Nat} {environment : Environment} {before middle written after : Store}
    {output : Ty} {initializer allocation body : Expr} {input reference value : Value}
    (completed : EvaluationSize size environment before
      (LanguageResult.bind output initializer (.letE allocation body)) value after)
    (initialized : Evaluates environment before initializer (.inRight .word input) middle)
    (allocated : Evaluates (input :: environment) middle allocation reference written) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize (reference :: input :: environment) written body value after := by
  obtain ⟨initialSize, first, initial⟩ := completed.bind_success initialized
  obtain ⟨remainingSize, second, remaining⟩ := initial.let_body allocated
  exact ⟨remainingSize, Nat.lt_trans second first, remaining⟩

/-- The discarded payload is an actual temporary slot, not a capture cast. -/
theorem discard_body {size : Nat} {environment : Environment} {before middle after : Store}
    {output : Ty} {computation body : Expr} {input value : Value}
    (completed : EvaluationSize size environment before (LocalSequence.discard output computation body) value after)
    (computed : Evaluates environment before computation (.inRight .word input) middle) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize (input :: environment) middle (body.weakenAt 0) value after :=
  completed.bind_success computed

/-- Success through the seven actual assignment slots exposes a strict native
continuation. The premises are the same phase executions as execute_success,
with the actual compatible getter and setter. No child source meaning is used. -/
theorem execute_continuation {size : Nat} {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore modifiedStore setterStore written finalStore : Store}
    {location : Location} {keyValue snapshot right changed updated old result : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType location keyValue snapshot right changed environment) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word updated) setterStore)
    (read : setterStore.read? location = some old)
    (write : setterStore.write? location (.inRight .unit updated) = some written)
    (completed : EvaluationSize size environment before
      (execute prepared reference keys rhs next outputType operator bitNot invalidOperand) result finalStore) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize
        (writtenEnvironment prepared.route.rootType location keyValue snapshot right changed updated environment)
        written (shift 7 next) result finalStore := by
  obtain ⟨referenceSize, first, referenceRest⟩ := completed.let_body (referenceSelected.evaluates before)
  obtain ⟨keysSize, second, keysRest⟩ := referenceRest.bind_success keysEvaluated
  obtain ⟨snapshotSize, third, snapshotRest⟩ := keysRest.bind_success snapshotEvaluated
  obtain ⟨rhsSize, fourth, rhsRest⟩ := snapshotRest.bind_success rhsEvaluated
  obtain ⟨modifiedSize, fifth, modifiedRest⟩ := rhsRest.bind_success modifiedEvaluated
  obtain ⟨setterSize, sixth, setterRest⟩ := modifiedRest.bind_success setterEvaluated
  obtain ⟨remainingSize, seventh, remaining⟩ := setterRest.let_body
    (.storeCell (.var rfl) read (.inRight (.var rfl)) write)
  exact ⟨remainingSize, by omega, remaining⟩

/-- Moving into the actual six-value post environment changes syntax only.
It does not change or regenerate the supplied Core size. -/
theorem post_rename_size {size : Nat} {actual : Environment} {before after : Store}
    {type : Ty} {location : Location} {continued : Bool} {code : Expr} {ξ : Renaming} {value : Value} :
    EvaluationSize size (TypedImperativeFor.postValues type location continued ++ actual) before
      (ForLoop.postCode (code.rename ξ)) value after ↔
    EvaluationSize size (TypedImperativeFor.postValues type location continued ++ actual) before
      (code.rename ((fun index => index + 6).comp ξ)) value after := by
  rw [TypedImperativeFor.post_rename]

open TypedImperativeFor (postValues)

private theorem insertion_zero : Renaming.insertion 0 = (fun index => index + 1) := by
  funext index
  simp [Renaming.insertion]

private theorem shift_comp (left right : Nat) :
    Renaming.comp (fun index => index + left) (fun index => index + right) =
      (fun index => index + (right + left)) := by
  funext index
  simp [Renaming.comp, Nat.add_assoc]

set_option maxRecDepth 3000 in
/-- Inversion of the actual body envelope exposes the actual post computation.
The four branch temporaries and Unit/self slots retain their concrete values. -/
theorem post_computation_sized {size : Nat} {actual : Environment} {before bodyStore after : Store}
    {type : Ty} {location : Location} {body post : Expr} {reason : Word} {value : Value}
    (continued : Bool)
    (evaluation : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) before
      (LocalLoop.advance type (Core.LoopExecution.bodyCode body)
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).weakenAt 0)) value after)
    (bodyEval : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) before
      (Core.LoopExecution.bodyCode body) (if continued then LocalLoop.continuingValue type else LocalLoop.fallthroughValue type) bodyStore) :
    ∃ postSize postStore postValue, postSize < size ∧
      EvaluationSize postSize (postValues type location continued ++ actual) bodyStore (ForLoop.postCode post) postValue postStore := by
  cases continued
  · obtain ⟨next, nextSmaller, postAdvance⟩ := evaluation.advance_fallthrough bodyEval
    have renamed : EvaluationSize next
        (ForLoop.fallthroughPrefix type ++ Core.LoopExecution.entryEnvironment type location actual) bodyStore
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).rename
          (fun index => index + 4)) value after := by
      simpa only [← Expr.rename_insertion, Expr.rename_comp, insertion_zero, shift_comp, Nat.reduceAdd, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, ForLoop.fallthroughPrefix, ForLoop.continuingPrefix, List.cons_append, List.nil_append] using postAdvance
    rw [LoopRenaming.advance] at renamed
    obtain ⟨postSize, store, result, postSmaller, evaluated⟩ := renamed.bind_computation
    exact ⟨postSize, store, result, Nat.lt_trans postSmaller nextSmaller, evaluated⟩
  · obtain ⟨next, nextSmaller, postAdvance⟩ := evaluation.advance_continuing bodyEval
    have renamed : EvaluationSize next
        (ForLoop.continuingPrefix type ++ Core.LoopExecution.entryEnvironment type location actual) bodyStore
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).rename
          (fun index => index + 4)) value after := by
      simpa only [← Expr.rename_insertion, Expr.rename_comp, insertion_zero, shift_comp, Nat.reduceAdd, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, ForLoop.fallthroughPrefix, ForLoop.continuingPrefix, List.cons_append, List.nil_append] using postAdvance
    rw [LoopRenaming.advance] at renamed
    obtain ⟨postSize, store, result, postSmaller, evaluated⟩ := renamed.bind_computation
    exact ⟨postSize, store, result, Nat.lt_trans postSmaller nextSmaller, evaluated⟩

end Solcore.SourceSemantics.CoreLowering.ForHeaderNativeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForFiniteSuccess
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopStatementSuccess
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopStatementFault
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopReflectionInterfaces
/-! Proof contracts for reconstruction of independent source executions from
finite generated Core executions. These contracts are internal induction
hypotheses; compiler acceptance will supply them through the static tree. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal

def Executes (functionMode : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (finalContext : Context)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  if functionMode then Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after
  else Dynamic.StatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after

inductive OutcomeRepresents (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) : Dynamic.ControlOutcome → Core.Value → Prop where
  | control {outcome value} (related : ControlRepresents type outcome value) :
      OutcomeRepresents program evidence source reasonAt type outcome value
  | fault {reason word} (related : FaultRepresents program evidence source reasonAt reason word) :
      OutcomeRepresents program evidence source reasonAt type (.fault reason) (.inLeft (Core.LocalLoop.controlType type) (.word word))

/-- Pair each source judgment with its corresponding result constructor. This
prevents a fault witness from being supplied through the successful judgment. -/
inductive Meaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (functionMode : Bool)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (statements : List StatementId) (type : Core.Ty) :
    Context → Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {finalContext outcome after result}
      (execution : ScalarStatementViews.ListExecutes functionMode program context evidence source environment before statements finalContext outcome after)
      (related : ControlRepresents type outcome result) :
      Meaning program context evidence source reasonAt functionMode environment before statements type finalContext outcome after result
  | fault {finalContext reason after word}
      (execution : ScalarStatementViews.ListFaults functionMode program context evidence source environment before statements finalContext reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      Meaning program context evidence source reasonAt functionMode environment before statements type finalContext (.fault reason) after
        (.inLeft (Core.LocalLoop.controlType type) (.word word))

theorem Meaning.source
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {mode : Bool} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {statements : List StatementId} {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (meaning : Meaning program context evidence source reasonAt mode environment before statements type finalContext outcome after result) :
    Executes mode program context evidence source environment before statements finalContext outcome after := by
  cases meaning with
  | control execution _ => cases mode <;> exact .control execution
  | fault execution _ => cases mode <;> exact .fault execution

theorem Meaning.related
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {mode : Bool} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {statements : List StatementId} {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (meaning : Meaning program context evidence source reasonAt mode environment before statements type finalContext outcome after result) :
    OutcomeRepresents program evidence source reasonAt type outcome result := by
  cases meaning with
  | control _ related => exact .control related
  | fault _ related => exact .fault related

def Result (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (functionMode : Bool) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ finalContext outcome after finalMapping finalWorld,
    Meaning program context evidence source reasonAt functionMode environment before statements type finalContext outcome after result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

def Reflects (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (functionMode : Bool) (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store finalStore : Core.Store} {result : Core.Value},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Core.Evaluates actual store (code.rename ξ) result finalStore →
    Result program context evidence source reasonAt functionMode environment heap statements type mapping world store result finalStore

/-- Reconstruct one loop body's finite source execution from its actual Core
execution, including the three temporary binders at loop entry. -/
def BodyReflects (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word)
    (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (canonical actual : Core.Environment) (actualContext : Core.Context)
    (type : Core.Ty) (location : Core.Location) (statements : List StatementId) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap}
    {store finalStore : Core.Store} {result : Core.Value},
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Core.RuntimeEnvironmentHasTypes world actual actualContext →
    world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
    Core.Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode code) result finalStore →
    Result program context evidence source reasonAt false environment heap statements type mapping world store result finalStore

theorem Reflects.body
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {statements : List StatementId} {code : Core.Expr} {ξ : Core.Renaming}
    (correct : Reflects compilation program evidence source reasonAt scope context false statements type code)
    (wellFormed : Core.Ty.WellFormed [] type) (valid : PrimitiveExpressions.ContextValid compilation context)
    (respects : Core.Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope) actualContext)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    BodyReflects program context evidence source reasonAt scope administrativeContext environment canonical actual actualContext
      type location statements (code.rename ξ) := by
  intro mapping world heap store finalStore result environments heaps actualTyped locationTyped evaluation
  have layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ := ⟨respects, agree, actualTyped⟩
  have shifted := ((layout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert Core.RuntimeValueHasType.unit).insert
    (Core.RuntimeValueHasType.bool (value := true))
  apply correct wellFormed valid environments heaps shifted
  simpa only [rename_insert, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, Core.LoopExecution.bodyCode] using evaluation

inductive WhileMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (statements : List StatementId) (type : Core.Ty) :
    Context → Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {finalContext outcome after result}
      (execution : Dynamic.WhileExecutes program context evidence source environment before condition statements finalContext outcome after)
      (related : ControlRepresents type outcome result) :
      WhileMeaning program context evidence source reasonAt environment before condition statements type finalContext outcome after result
  | fault {reason after word}
      (fault : Dynamic.WhileFaults program context evidence source environment before condition statements reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      WhileMeaning program context evidence source reasonAt environment before condition statements type context (.fault reason) after
        (.inLeft (Core.LocalLoop.controlType type) (.word word))

def WhileResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ finalContext outcome after finalMapping finalWorld,
    WhileMeaning program context evidence source reasonAt environment before condition statements type finalContext outcome after result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopFiniteReflection
/-! Reconstruct a finite independent while execution from a finite execution
of its installed Core closure. Body reflection is the structural child-tree
induction hypothesis; the next iteration is proved by decreasing Core
execution size, never assumed as an external source execution. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof
open Core.LoopExecution

private theorem self_retained
    {mapping futureMapping : GeneralHeap.LocationMap} {before after : Core.Store}
    {location : Core.Location} {value : Core.Value}
    (unmapped : location ∉ mapping) (read : before.read? location = some value)
    (frame : GeneralHeap.AdministrativePreserved mapping before futureMapping after) :
    location ∉ futureMapping ∧ after.read? location = some value := by
  have bounded : location < before.length := (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨unmapped, same⟩ := frame location unmapped bounded
  exact ⟨unmapped, same.trans read⟩

private theorem while_context
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.WhileExecutes program context evidence source environment before condition statements finalContext outcome after) :
    finalContext = context := by cases execution <;> rfl

/-- The static condition constructs its source execution without any source
trace premise. The body contract is discharged by the statement-tree theorem. -/
theorem while_reflect
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {condition : ExpressionId} {conditionCode : Core.Expr} {conditionDepth : Nat}
    {statements : List StatementId} {body : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {administrativeContext : Core.Context}
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual)
    (bodyCorrect : BodyReflects program context evidence source reasonAt scope administrativeContext
      environment canonical actual actualContext type location statements body) :
    ∀ (size : Nat) {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap}
      {store finalStore : Core.Store} {result : Core.Value},
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
      GeneralHeap.HeapRepresents mapping world heap store →
      Core.RuntimeEnvironmentHasTypes world actual actualContext →
      world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
      location ∉ mapping →
      store.read? location = some (.inRight .unit
        (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body (Core.LocalLoop.fallthrough type) selfReason location actual)) →
      EvaluationSize size (entryEnvironment type location actual) store
        (Core.LocalLoop.loopBody type (conditionCode.rename ξ) body (Core.LocalLoop.fallthrough type) selfReason) result finalStore →
      WhileResult program context evidence source reasonAt environment heap condition statements type mapping world store result finalStore := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro mapping world heap store finalStore result environments heaps actualTyped locationTyped unmapped installed evaluation
    obtain ⟨conditionOutcome, conditionValue, conditionSource, related, conditionCore⟩ :=
      GeneralExpressions.Primitive.preserves conditionTree program context evidence valid environments heaps
    have restricted := GeneralExpressions.Primitive.readOnly conditionTree
    have renamed := restricted.evaluation_rename conditionCore agree
    have first := (restricted.rename ξ).evaluation_weakenAt_zero renamed
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)
    have shifted := ((restricted.rename ξ).weakenAt 0).evaluation_weakenAt_zero first .unit
    cases related with
    | uninitialized site faultLocation origin =>
      cases conditionSource with
      | fault sourceFault =>
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure shifted)
        exact ⟨context, _, heap, mapping, world,
          .fault (.condition sourceFault) (.uninitialized site faultLocation origin), heaps, .refl _, .refl _, .refl _ _⟩
    | value staged typed =>
      obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
      cases conditionSource with
      | value sourceCondition =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false shifted)
          exact ⟨context, _, heap, mapping, world,
            .control (.done sourceCondition) (.fallthrough environment), heaps, .refl _, .refl _, .refl _ _⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch shifted
          obtain ⟨bodySize, bodyStore, bodyValue, _, bodyEvaluation⟩ := branch.bind_computation
          obtain ⟨bodyContext, bodyOutcome, bodyHeap, bodyMapping, bodyWorld, bodyMeaning,
            bodyHeaps, maps, worlds, frame⟩ :=
            bodyCorrect environments heaps actualTyped locationTyped bodyEvaluation.sound
          cases bodyMeaning with
          | fault sourceFault related =>
            obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
              (Core.LoopExecution.body_failure shifted bodyEvaluation.sound)
            exact ⟨context, _, bodyHeap, bodyMapping, bodyWorld,
              .fault (.body sourceCondition sourceFault) related, bodyHeaps, maps, worlds, frame⟩
          | control sourceBody related =>
            cases related with
            | returned staged typed =>
              obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned shifted bodyEvaluation.sound)
              exact ⟨context, _, bodyHeap, bodyMapping, bodyWorld,
                .control (.returns sourceCondition sourceBody) (.returned staged typed), bodyHeaps, maps, worlds, frame⟩
            | breaking bodyEnvironment =>
              obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking shifted bodyEvaluation.sound)
              exact ⟨context, _, bodyHeap, bodyMapping, bodyWorld,
                .control (.breaks sourceCondition sourceBody) (.fallthrough environment), bodyHeaps, maps, worlds, frame⟩
            | fallthrough bodyEnvironment =>
              obtain ⟨unmappedAgain, installedAgain⟩ := self_retained unmapped installed frame
              obtain ⟨nextSize, nextSmaller, nextEvaluation⟩ := branch.loop_next_fallthrough bodyEvaluation.sound installedAgain
              obtain ⟨nextContext, nextOutcome, after, finalMapping, finalWorld, nextMeaning,
                finalHeaps, mapsAgain, worldsAgain, frameAgain⟩ :=
                ih nextSize (Nat.lt_trans nextSmaller branchSmaller)
                  (environments.extend maps worlds) bodyHeaps (Core.RuntimeEnvironmentHasTypes.weaken worlds actualTyped)
                  (worlds.lookup locationTyped) unmappedAgain installedAgain nextEvaluation
              cases nextMeaning with
              | control nextSource nextRelated =>
                have sameContext := while_context nextSource
                subst nextContext
                exact ⟨context, _, after, finalMapping, finalWorld,
                  .control (.nextFallthrough sourceCondition sourceBody nextSource) nextRelated,
                  finalHeaps, maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩
              | fault nextFault nextRelated =>
                exact ⟨context, _, after, finalMapping, finalWorld,
                  .fault (.nextFallthrough sourceCondition sourceBody nextFault) nextRelated,
                  finalHeaps, maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩
            | continuing bodyEnvironment =>
              obtain ⟨unmappedAgain, installedAgain⟩ := self_retained unmapped installed frame
              obtain ⟨nextSize, nextSmaller, nextEvaluation⟩ := branch.loop_next_continuing bodyEvaluation.sound installedAgain
              obtain ⟨nextContext, nextOutcome, after, finalMapping, finalWorld, nextMeaning,
                finalHeaps, mapsAgain, worldsAgain, frameAgain⟩ :=
                ih nextSize (Nat.lt_trans nextSmaller branchSmaller)
                  (environments.extend maps worlds) bodyHeaps (Core.RuntimeEnvironmentHasTypes.weaken worlds actualTyped)
                  (worlds.lookup locationTyped) unmappedAgain installedAgain nextEvaluation
              cases nextMeaning with
              | control nextSource nextRelated =>
                have sameContext := while_context nextSource
                subst nextContext
                exact ⟨context, _, after, finalMapping, finalWorld,
                  .control (.nextContinue sourceCondition sourceBody nextSource) nextRelated,
                  finalHeaps, maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩
              | fault nextFault nextRelated =>
                exact ⟨context, _, after, finalMapping, finalWorld,
                  .fault (.nextContinue sourceCondition sourceBody nextFault) nextRelated,
                  finalHeaps, maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForInitializerHeader
/-! Forget the loop continuation while retaining the actual initializer
compiler tree. This projection is used only for faults within initializers. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference

def HeaderPosition (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (position : Position) (type : Core.Ty) (code : Core.Expr) : Prop :=
  match position with
  | .statements _ _ => True
  | .initializers items _ _ _ => ForHeaders.Tree compilation source reasonAt type (fun _ _ _ => True) scope context items code

theorem Tree.header
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code) :
    HeaderPosition compilation source reasonAt scope context position type code := by
  induction tree with
  | initializersDone => exact .nil trivial
  | initializerUninitialized binding extension _ ih => exact .letUninitialized binding extension ih
  | initializerInitialized binding extension value _ ih => exact .letInitialized binding extension value ih
  | initializerAssign target value _ ih => exact .assign target value ih
  | initializerDiscard value _ ih => exact .discard value ih
  | nil | letUninitialized | letInitialized | assign | discard | returnValue | returnUnit | tailExpression
  | block | ifThen | whileLoop | forLoop | breaking | continuing => exact trivial

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopStatementBridge
/-! Accepted default while lowering preserves supplied finite source success
and fault derivations. The source trace is the only termination witness. This
does not assert termination of every checked loop or general source fault
completeness. All completed Core runs agree with the preserved finite trace. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference BasicStatements Internal ScalarStatementViews

private theorem identity_respects (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context) :
    Core.Renaming.Respects Core.Renaming.id (SourceCoreLocalCell.coreContext scope)
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) := by
  intro index foundType found
  change (SourceCoreLocalCell.coreContext scope ++ administrativeContext)[index]? = some foundType
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem canonical_layout
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
    Layout world (SourceCoreLocalCell.coreContext scope) coreEnvironment
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) coreEnvironment Core.Renaming.id :=
  ⟨identity_respects scope administrativeContext, fun found => found, environments.runtime_hasTypes⟩

theorem Tree.hasType_with_administrative
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {mode : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context mode statements type code)
    (wellFormed : Core.Ty.WellFormed [] type) (administrativeContext : Core.Context) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code (Core.LocalLoop.resultType type) := by
  simpa only [Core.Expr.rename_id] using (tree.hasType wellFormed).rename (identity_respects scope administrativeContext)

/-- A successful source trace determines a finite executable Core result,
including the allocated administrative cells and the source-location map. -/
theorem lowerFlowStatements_source_success_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context finalContext : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source) (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasons)
      fuel source scope statements type reasonAt tailReturns selfReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (execution : ListExecutes tailReturns program context evidence source environment heap statements finalContext outcome after) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalLoop.resultType type) ∧
    ∃ result finalStore finalMapping finalWorld required,
      ControlRepresents type outcome result ∧ GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  have tree := tree_of_lowerFlowStatementsWithExpression aligned unique noFor accepted
  obtain ⟨result, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
    tree.source_success unique program evidence wellFormed environments heaps (canonical_layout environments) execution
  simp only [Core.Expr.rename_id] at evaluated
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
  refine ⟨Core.infer_complete (tree.hasType_with_administrative wellFormed administrativeContext),
    result, finalStore, finalMapping, finalWorld, required, related, finalHeaps, maps, worlds, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) evaluated

theorem lowerFlowStatements_source_fault_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context finalContext : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source) (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasons)
      fuel source scope statements type reasonAt tailReturns selfReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (fault : ListFaults tailReturns program context evidence source environment heap statements finalContext reason after) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalLoop.resultType type) ∧
    ∃ word finalStore finalMapping finalWorld required,
      FaultRepresents program evidence source reasonAt reason word ∧ GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) =
        .done (.inLeft (Core.LocalLoop.controlType type) (.word word)) finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = .inLeft (Core.LocalLoop.controlType type) (.word word) ∧ actualStore = finalStore) := by
  have tree := tree_of_lowerFlowStatementsWithExpression aligned unique noFor accepted
  obtain ⟨word, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
    tree.source_fault unique program evidence wellFormed valid covers environments heaps (canonical_layout environments) fault
  simp only [Core.Expr.rename_id] at evaluated
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
  refine ⟨Core.infer_complete (tree.hasType_with_administrative wellFormed administrativeContext),
    word, finalStore, finalMapping, finalWorld, required, related, finalHeaps, maps, worlds, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) evaluated

inductive FinishedControlRepresents (type : Core.Ty) (fellThroughReason escapedReason : Core.Word) :
    Dynamic.ControlOutcome → Core.Value → Prop where
  | fallthrough (environment : Dynamic.Environment) :
      FinishedControlRepresents type fellThroughReason escapedReason (.fallthrough environment)
        (if type = .unit then .inRight .word .unit else .inLeft type (.word fellThroughReason))
  | returned (value : SourceStagedValue.Value) (typed : SourceStagedValue.coreType value = type) :
      FinishedControlRepresents type fellThroughReason escapedReason (.returned (StagedValue.toSource value))
        (.inRight .word (SourceStagedValue.toCore value))
  | breaking (environment : Dynamic.Environment) :
      FinishedControlRepresents type fellThroughReason escapedReason (.breaking environment) (.inLeft type (.word escapedReason))
  | continuing (environment : Dynamic.Environment) :
      FinishedControlRepresents type fellThroughReason escapedReason (.continuing environment) (.inLeft type (.word escapedReason))

def fallback (type : Core.Ty) (reason : Core.Word) : Core.Expr :=
  if type = .unit then Core.LanguageResult.success .unit else Core.LanguageResult.failure type (.word reason)

private theorem finish_success
    {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    {environment : Core.Environment} {before after : Core.Store} {code : Core.Expr}
    (related : ControlRepresents type outcome result)
    (evaluated : Core.Evaluates environment before code result after) (fellThrough escaped : Core.Word) :
    ∃ finished, FinishedControlRepresents type fellThrough escaped outcome finished ∧
      Core.Evaluates environment before
        (Core.LocalControl.finish type (Core.LocalLoop.toControl type code escaped) (fallback type fellThrough)) finished after := by
  cases related with
  | fallthrough sourceEnv =>
    refine ⟨_, .fallthrough sourceEnv, Core.LocalControl.finish_fallthrough type
      (Core.LocalLoop.toControl_normal type escaped evaluated) ?_⟩
    by_cases unit : type = .unit
    · simp [fallback, unit, Core.LanguageResult.success, Core.Expr.weakenAt]
      exact .inRight .unit
    · simp [fallback, unit, Core.LanguageResult.failure, Core.Expr.weakenAt]
      exact .inLeft .word
  | returned value typed =>
    exact ⟨_, .returned value typed, Core.LocalControl.finish_returned type
      (Core.LocalLoop.toControl_normal type escaped evaluated)⟩
  | breaking sourceEnv =>
    exact ⟨_, .breaking sourceEnv, Core.LocalControl.finish_failure type
      (Core.LocalLoop.toControl_transfer type escaped evaluated)⟩
  | continuing sourceEnv =>
    exact ⟨_, .continuing sourceEnv, Core.LocalControl.finish_failure type
      (Core.LocalLoop.toControl_transfer type escaped evaluated)⟩

private theorem finish_hasType
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    {reasonAt : ExpressionId → Core.Word} {escaped : Core.Word}
    (tree : Tree compilation source reasonAt escaped scope context true statements type flow)
    (wellFormed : Core.Ty.WellFormed [] type) (admin : Core.Context) (fellThrough : Core.Word) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ admin)
      (Core.LocalControl.finish type (Core.LocalLoop.toControl type flow escaped) (fallback type fellThrough))
      (Core.LanguageResult.resultType type) := by
  apply Core.LocalControl.finish_hasType wellFormed
    (Core.LocalLoop.toControl_hasType escaped wellFormed (tree.hasType_with_administrative wellFormed admin))
  by_cases unit : type = .unit
  · simpa [fallback, unit] using Core.LanguageResult.success_hasType (context := SourceCoreLocalCell.coreContext scope ++ admin) Core.HasType.unit
  · simpa [fallback, unit] using Core.LanguageResult.failure_hasType wellFormed (Core.HasType.word (value := fellThrough))

inductive FinishedOutcomeRepresents (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty)
    (fellThrough escaped : Core.Word) : Dynamic.ControlOutcome → Core.Value → Prop where
  | control {outcome value} (related : FinishedControlRepresents type fellThrough escaped outcome value) :
      FinishedOutcomeRepresents program evidence source reasonAt type fellThrough escaped outcome value
  | fault {reason word} (related : FaultRepresents program evidence source reasonAt reason word) :
      FinishedOutcomeRepresents program evidence source reasonAt type fellThrough escaped (.fault reason) (.inLeft type (.word word))

/-- Actual accepted function lowering preserves a supplied finite source
outcome. Fallthrough, return, escaped control and semantic faults retain their
separate boundary meanings. Fuel exhaustion is never a completed result. -/
theorem lowerStatements_source_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context finalContext : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source) (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements type reasonAt fellThroughReason escapedReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (execution : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LanguageResult.resultType type) ∧
    ∃ result finalStore finalMapping finalWorld required,
      FinishedOutcomeRepresents program evidence source reasonAt type fellThroughReason escapedReason outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  obtain ⟨flow, same, tree⟩ := tree_of_lowerStatements aligned unique noFor accepted
  change code = Core.LocalControl.finish type (Core.LocalLoop.toControl type flow escapedReason) (fallback type fellThroughReason) at same
  subst code
  refine ⟨Core.infer_complete (finish_hasType tree wellFormed administrativeContext fellThroughReason), ?_⟩
  cases execution with
  | control execution =>
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
      tree.source_success unique program evidence wellFormed environments heaps (canonical_layout environments) execution
    simp only [Core.Expr.rename_id] at evaluated
    obtain ⟨finished, related, finishedEval⟩ := finish_success related evaluated fellThroughReason escapedReason
    obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel finishedEval
    refine ⟨finished, finalStore, finalMapping, finalWorld, required, .control related, finalHeaps, maps, worlds, frame, completes, ?_⟩
    intro runtimeFuel actual actualStore completed
    exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) finishedEval
  | fault fault =>
    obtain ⟨word, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
      tree.source_fault unique program evidence wellFormed valid covers environments heaps (canonical_layout environments) fault
    simp only [Core.Expr.rename_id] at evaluated
    have finishedEval := Core.LocalControl.finish_failure (fallback := fallback type fellThroughReason) type
      (Core.LocalLoop.toControl_failure type escapedReason evaluated)
    obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel finishedEval
    refine ⟨_, finalStore, finalMapping, finalWorld, required, .fault related, finalHeaps, maps, worlds, frame, completes, ?_⟩
    intro runtimeFuel actual actualStore completed
    exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) finishedEval

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
end
