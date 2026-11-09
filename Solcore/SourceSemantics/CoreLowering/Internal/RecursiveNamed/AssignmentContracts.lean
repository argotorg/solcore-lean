import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions

/-!
# Recursive named rows: assignment contracts

Contracts of bare and place assignments, bit-not updates and place keys, with expression Source bounds and compositions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedBareAssignmentContracts
/-! Dynamic receipts for a bare assignment prefix. Source sizes and the
original Core size are independent. Prefix inversion retains the actual
seven bound values; a terminal Unit execution identifies the commit store
only, and supplies no size bound. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedBareAssignmentContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleBareAssignment
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open GenericExpressionMeaning (FaultRep)

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}

/-- An empty projection spine has its own independent source derivation. -/
theorem resolves_sized
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world index)
    (bare : place.projections = []) :
    SourceExecutionSize.SourcePlaceResolves program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize []])
      context evidence source environment heap place snapshot.resolved heap :=
  .intro snapshot.lookup snapshot.read (bare ▸ .nil) snapshot.read snapshot.root .nil

/-- The reference, empty keys, and getter are three actual prefix nodes. -/
theorem snapshot_prefix_sized
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word}
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) rhs next outputType operator false invalid).rename ξ) value finalStore) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize
        (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual) store
        (LanguageResult.bind outputType (shift 3 (rhs.rename ξ))
          (CompatiblePlaceRhsReflection.remainder prepared .unit (next.rename ξ) outputType operator invalid)) value finalStore := by
  rw [execute_rename layout] at completed
  obtain ⟨first, firstBound, firstEval⟩ := completed.let_body (.var snapshot.nativeLookup)
  obtain ⟨second, secondBound, secondEval⟩ := firstEval.bind_success (keys_evaluates _ store)
  obtain ⟨third, thirdBound, thirdEval⟩ := secondEval.bind_success (snapshot.getter layout)
  exact ⟨third, by omega, thirdEval⟩

/-- A completed run whose right-hand side is Unit passes the modifier's check. -/
theorem execute_unit_passes_sized {prepared : Prepared} {reference rhs next : Expr}
    {keys : SourceCoreBasic.LoweredExpr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier}
    {bitNot : Bool} {invalid : Word} {actual : Environment}
    {before keyStore snapshotStore rhsStore modifiedStore setterStore finalStore : Store}
    {target : Location} {keyValue saved changed updated value : Value}
    (referenceSelected : DataEquality.Selects actual reference (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType target actual) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType target keyValue actual) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word saved) snapshotStore)
    (rightEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType target keyValue saved actual) snapshotStore
      (shift 3 rhs) (.inRight .word .unit) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType target keyValue saved .unit actual) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalid) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType target keyValue saved .unit changed actual) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.inRight .word updated) setterStore)
    {size : Nat}
    (completed : EvaluationSize size actual before
      (execute prepared reference keys rhs next outputType operator bitNot invalid) value finalStore) :
    SourceCoreDataPlaces.Passes operator .unit := by
  obtain ⟨_, _, firstEval⟩ := completed.let_body (referenceSelected.evaluates before)
  obtain ⟨_, _, secondEval⟩ := firstEval.bind_success keysEvaluated
  obtain ⟨_, _, thirdEval⟩ := secondEval.bind_success snapshotEvaluated
  obtain ⟨_, _, fourthEval⟩ := thirdEval.bind_success rightEvaluated
  obtain ⟨_, _, fifthEval⟩ := fourthEval.bind_success modifiedEvaluated
  obtain ⟨_, _, sixthEval⟩ := fifthEval.bind_success setterEvaluated
  rcases DataPlaceGuard.inv_sized sixthEval with ⟨passes, _⟩ | ⟨_, _, zero, _, _⟩
  · exact passes
  · cases zero

/-- One inversion for the actual emitted prefix. The six supplied phase
executions align values/stores; all costs come from the original derivation.
The terminal Unit execution identifies only the store after its real write. -/
theorem execute_continuation_sized {prepared : Prepared} {reference rhs next : Expr}
    {keys : SourceCoreBasic.LoweredExpr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier}
    {bitNot : Bool} {invalid : Word} {actual : Environment}
    {before keyStore snapshotStore rhsStore modifiedStore setterStore commitStore finalStore : Store}
    {target : Location} {keyValue saved right changed updated value : Value}
    (referenceSelected : DataEquality.Selects actual reference (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType target actual) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType target keyValue actual) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word saved) snapshotStore)
    (rightEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType target keyValue saved actual) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType target keyValue saved right actual) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalid) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType target keyValue saved right changed actual) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.inRight .word updated) setterStore)
    (terminal : Evaluates actual before
      (execute prepared reference keys rhs .unit outputType operator bitNot invalid) .unit commitStore)
    {size : Nat}
    (completed : EvaluationSize size actual before
      (execute prepared reference keys rhs next outputType operator bitNot invalid) value finalStore) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize (writtenEnvironment prepared.route.rootType target keyValue saved right changed updated actual)
        commitStore (shift 7 next) value finalStore := by
  obtain ⟨first, firstBound, firstEval⟩ := completed.let_body (referenceSelected.evaluates before)
  obtain ⟨second, secondBound, secondEval⟩ := firstEval.bind_success keysEvaluated
  obtain ⟨third, thirdBound, thirdEval⟩ := secondEval.bind_success snapshotEvaluated
  obtain ⟨fourth, fourthBound, fourthEval⟩ := thirdEval.bind_success rightEvaluated
  obtain ⟨fifth, fifthBound, fifthEval⟩ := fourthEval.bind_success modifiedEvaluated
  obtain ⟨sixth, sixthBound, sixthEval⟩ := fifthEval.bind_success setterEvaluated
  rcases DataPlaceGuard.inv_sized sixthEval with ⟨passes, seventh, seventhBound, seventhEval⟩ |
    ⟨operation, selected, zero, _, _⟩
  case inr =>
    -- The terminal run meets the same check, which fails.
    subst selected zero
    have failed : Evaluates actual before
        (execute prepared reference keys rhs .unit outputType (some ⟨operation, true⟩) bitNot invalid)
        (.inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero))) setterStore :=
      .letE (referenceSelected.evaluates before)
        (LanguageResult.bind_success _ keysEvaluated
          (LanguageResult.bind_success _ snapshotEvaluated
            (LanguageResult.bind_success _ rightEvaluated
              (LanguageResult.bind_success _ modifiedEvaluated
                (LanguageResult.bind_success _ setterEvaluated SourceCoreDataPlaces.guard_panic)))))
    cases (evaluation_deterministic terminal failed).1
  cases seventhEval with
  | @letE writeSize remainingSize _ _ writtenStore _ _ _ _ _ write remaining =>
    cases write with
    | storeCell referenceEval read input written =>
      have nativePrefix : Evaluates actual before
          (execute prepared reference keys rhs .unit outputType operator bitNot invalid) .unit writtenStore := by
        exact .letE (referenceSelected.evaluates before)
          (LanguageResult.bind_success _ keysEvaluated
            (LanguageResult.bind_success _ snapshotEvaluated
              (LanguageResult.bind_success _ rightEvaluated
                (LanguageResult.bind_success _ modifiedEvaluated
                  (LanguageResult.bind_success _ setterEvaluated
                    (SourceCoreDataPlaces.guard_passes passes
                    (.letE (.storeCell referenceEval.sound read input.sound written)
                      (by simpa [shift, Expr.rename, List.range, List.range.loop, List.foldl, Expr.weakenAt] using
                        (Evaluates.unit (environment := .unit :: updated :: changed :: right :: saved :: keyValue ::
                          .cellRef (OptionalCell.cellType prepared.route.rootType) target :: actual) (store := writtenStore))))))))))
      obtain ⟨_, sameStore⟩ := evaluation_deterministic nativePrefix terminal
      cases sameStore
      exact ⟨_, by omega, remaining⟩

/-- Every bound comes from the original completed derivation. The terminal
prefix is used solely to identify its write store with the semantic commit. -/
theorem continuation_sized
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word}
    {right changed : Value} {rhsStore commitStore : Store} {optional : Value}
    (rightEvaluated : Evaluates
      (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual) store
      (shift 3 (rhs.rename ξ)) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates
      (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value right actual) rhsStore
      (modified prepared.route.leafType operator false (.var 1) (.var 0) invalid) (.inRight .word changed) rhsStore)
    (latestRead : rhsStore.read? snapshot.target = some optional)
    (terminal : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) rhs .unit outputType operator false invalid).rename ξ)
      .unit commitStore)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) rhs next outputType operator false invalid).rename ξ) value finalStore) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value right changed changed actual)
        commitStore (shift 7 (next.rename ξ)) value finalStore := by
  rw [execute_rename layout] at completed terminal
  exact execute_continuation_sized (.var snapshot.nativeLookup) (keys_evaluates _ store)
    (snapshot.getter layout) rightEvaluated modifiedEvaluated
    (setter_evaluates layout snapshot.value right changed latestRead) terminal completed

inductive ResultAt (size : Nat) (compilation : SourceCoreCompatibleDataPlaces.Context) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} (functions : FunctionModel compilation.checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (faults : FaultRep) (prepared : Prepared) (place : PlaceResolution) (operator : Syntax.ValueAssignOp)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (actual : Environment) (actualContext : Core.Context) (ξ : Renaming)
    (next : Expr) (outputType : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap} {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (result : value = .inLeft outputType (.word token)) (represented : faults reason token)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      ResultAt size compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
        rhs actual actualContext ξ next outputType value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {updatedValue : Value} {after : Dynamic.Heap} {commitStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (represented : ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after commitStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap commitStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ actual) commitStore (shift 7 (next.rename ξ)) value finalStore) :
      ResultAt size compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
        rhs actual actualContext ξ next outputType value finalStore


/-- Erasure preserves all source outcomes, actual slots, and heap receipts. -/
theorem ResultAt.erase {size : Nat} {faults : FunctionCalls.FaultRep} {operator : Syntax.ValueAssignOp}
    {rhs : ExpressionId} {actualContext : Core.Context} {next : Expr} {outputType : Ty}
    {value : Value} {finalStore : Store}
    (result : ResultAt size compilation registry functions program context evidence source faults prepared place operator
      environment heap store mapping world rhs actual actualContext ξ next outputType value finalStore) :
    CompatibleBareAssignment.Result compilation registry functions program context evidence source faults prepared place operator
      environment heap store mapping world rhs actual actualContext ξ next outputType value finalStore := by
  cases result with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace.sound same represented heaps maps worlds frame metadata
  | success trace represented heaps maps worlds frame metadata count typed _ remaining =>
    exact .success trace.sound represented heaps maps worlds frame metadata count typed remaining.sound

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedBareAssignmentContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts
/-! Measured ordered keys keep the actual projection derivation. Member steps
add source cost without evaluating an expression; index steps retain source
order and repetitions. Native bundle sizes are independent of these source
sizes. The adapters only restrict pointwise expression meanings. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open DataPlaceKeyOrder

variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}

/-- Removing member-only steps cannot increase the actual source size. -/
theorem projections_values {size : Nat} {projections : List PlaceProjection} {evaluated : List Dynamic.EvaluatedProjection}
    (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before projections evaluated after) :
    ∃ values vectorSize, Values projections values evaluated ∧
      SourceExecutionSize.ExpressionsEvaluate program vectorSize context evidence source environment before (sourceKeys projections) values after ∧
      vectorSize ≤ size := by
  induction projections generalizing size before evaluated with
  | nil => cases trace; exact ⟨[], _, .nil, .nil, Nat.le_refl _⟩
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      cases trace with
      | member tail =>
        obtain ⟨values, vectorSize, shaped, executed, bound⟩ := ih tail
        exact ⟨values, vectorSize, .member shaped, executed,
          Nat.le_trans bound (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp)))⟩
    | index key =>
      cases trace with
      | index head tail =>
        obtain ⟨values, vectorSize, shaped, executed, bound⟩ := ih tail
        refine ⟨_ :: values, _, .index shaped, .cons head executed, ?_⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *
        omega

theorem projections_fault {size : Nat} {projections : List PlaceProjection} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before projections reason after) :
    ∃ vectorSize, SourceExecutionSize.ExpressionsFault program vectorSize context evidence source environment before (sourceKeys projections) reason after ∧
      vectorSize ≤ size := by
  induction projections generalizing size before with
  | nil => cases trace
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      cases trace with
      | memberTail failed =>
        obtain ⟨vectorSize, failed, bound⟩ := ih failed
        exact ⟨vectorSize, failed, Nat.le_trans bound
          (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp)))⟩
    | index key =>
      cases trace with
      | indexHead failed => exact ⟨_, .head failed, Nat.le_refl _⟩
      | indexTail head failed =>
        obtain ⟨vectorSize, failed, bound⟩ := ih failed
        refine ⟨_, .tail head failed, ?_⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *
        omega

/-- Reflection reconstructs a source size; it makes no comparison to Core cost. -/
theorem values_projections {size : Nat} {projections : List PlaceProjection} {values : List Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before (sourceKeys projections) values after) :
    ∃ sourceSize evaluated, Values projections values evaluated ∧
      SourceExecutionSize.SourceProjectionsEvaluate program sourceSize context evidence source environment before projections evaluated after := by
  induction projections generalizing size before values with
  | nil => cases trace; exact ⟨_, [], .nil, .nil⟩
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      obtain ⟨sourceSize, evaluated, shaped, executed⟩ := ih trace
      exact ⟨_, _, .member shaped, .member executed⟩
    | index key =>
      cases trace with
      | cons head tail =>
        obtain ⟨sourceSize, evaluated, shaped, executed⟩ := ih tail
        exact ⟨_, _, .index shaped, .index head executed⟩

theorem fault_projections {size : Nat} {projections : List PlaceProjection} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ExpressionsFault program size context evidence source environment before (sourceKeys projections) reason after) :
    ∃ sourceSize, SourceExecutionSize.SourceProjectionsFault program sourceSize context evidence source environment before projections reason after := by
  induction projections generalizing size before with
  | nil => cases trace
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      obtain ⟨sourceSize, failed⟩ := ih trace
      exact ⟨_, .memberTail failed⟩
    | index key =>
      cases trace with
      | head failed => exact ⟨_, .indexHead failed⟩
      | tail head failed =>
        obtain ⟨sourceSize, failed⟩ := ih failed
        exact ⟨_, .indexTail head failed⟩

inductive OutcomeAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (projections : List PlaceProjection) : DataExpressionSequence.Outcome → Dynamic.Heap → Prop where
  | values {values evaluated after} (shaped : Values projections values evaluated)
      (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before projections evaluated after) :
      OutcomeAt program size context evidence source environment before projections (.ok values) after
  | fault {reason after} (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before projections reason after) :
      OutcomeAt program size context evidence source environment before projections (.error reason) after

theorem OutcomeAt.sound {size projections outcome}
    (trace : OutcomeAt program size context evidence source environment before projections outcome after) :
    OutcomeTrace program context evidence source environment before projections outcome after := by
  cases trace with
  | values shaped trace => exact .values shaped trace.sound
  | fault trace => exact .fault trace.sound

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {entry : ProtectedExpressionMeaning.Entry}

/-- The higher-level named contract supplies the same measured source child. -/
theorem preserves_at {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults entry) :
    ProtectedDataExpressionSequence.ExpressionPreservesAt size model program context evidence source certificate faults entry := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed installed trace
  apply meaning generated found environments heaps locals agrees typed installed
  cases trace with
  | value trace => exact .value trace
  | fault trace => exact .fault trace

theorem reflects_at {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults entry) :
    ProtectedDataExpressionSequence.ExpressionReflectsAt size model program context evidence source certificate faults entry := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning generated found environments heaps locals agrees typed installed evaluated
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, rest⟩
  cases trace with
  | value trace => exact .value trace
  | fault trace => exact .fault trace

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceAssignmentContracts
/-! Dynamic projected-assignment receipts retain the original native tail and
independent source measurements. These receipts are semantic outputs, never
static compiler evidence. The seven written values are typed directly from
the reflected setter/write phases. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceAssignmentContracts
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

inductive KeyResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping) (index : Nat)
    (rhs next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceFaults program sourceSize context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      KeyResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore
  | keys {sourceSize remainingSize : Nat} {location : Dynamic.Location} {resolved : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (trace : SourceExecutionSize.SourceProjectionsEvaluate program sourceSize context evidence source environment before place.projections resolved after)
      (execution : CompatiblePlaceTargetKeys.Execution checked registry functions prepared place codes sourceTypes location resolved
        coreEnvironment before after store mapping world index)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (keysEnvironment prepared.route.rootType execution.target (packValues execution.values) coreEnvironment)
        execution.keyStore (CompatiblePlaceKeyReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore) :
      KeyResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore


inductive PrefixResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceFaults program sourceSize context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      PrefixResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore
  | resolved {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
      (sourceTrace : SourceExecutionSize.SourcePlaceResolves program sourceSize context evidence source environment before place target after)
      (execution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before after)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (snapshotEnvironment prepared.route.rootType execution.target (packValues execution.values)
        (.inRight .unit execution.snapshot) coreEnvironment) execution.store
        (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore) :
      PrefixResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore


inductive RhsResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr) (next : Expr) (outputType : Ty)
    (operator : Syntax.ValueAssignOp) (invalid : Word) (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      RhsResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore
  | ready {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
      (sourceTrace : SourceExecutionSize.SourcePlaceResolves program sourceSize context evidence source environment before place target targetHeap)
      (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap)
      (right : CompatiblePlaceRhsReflection.Execution checked registry functions program context evidence source faults environment prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
      {rhsSize : Nat}
      (rhsTrace : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right.right right.heap)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
        (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
      RhsResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore


inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (keyType : Ty) (actualContext : Core.Context)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      ResultAt size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore
  | committed {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleRenamedPlaceSuccess.writtenContext prepared keyType actualContext) ambient.definitions)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      ResultAt size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore


theorem KeyResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word}
    {result : Value} {finalStore : Store}
    (receipt : KeyResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore) :
    CompatiblePlaceKeyReflection.Result checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace.sound same represented heaps maps worlds frame metadata
  | keys lookup trace execution _ remaining =>
    exact .keys lookup trace.sound execution remaining.sound

theorem PrefixResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {leaf : TypeSystem.Ty} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word}
    {result : Value} {finalStore : Store}
    (receipt : PrefixResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore) :
    CompatiblePlacePrefixReflection.Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace.sound same represented heaps maps worlds frame metadata
  | resolved trace execution _ remaining =>
    exact .resolved trace.sound execution remaining.sound

theorem RhsResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {leaf : TypeSystem.Ty} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {next : Expr} {outputType : Ty}
    {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value} {finalStore : Store}
    (receipt : RhsResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore) :
    CompatiblePlaceRhsReflection.Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace.sound same represented heaps maps worlds frame metadata
  | ready trace execution right _ _ remaining =>
    exact .ready trace.sound execution right remaining.sound

theorem ResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {keyType : Ty} {actualContext : Core.Context} {place : PlaceResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {environment : Dynamic.Environment} {actual : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs
      environment actual before store mapping world next output value finalStore) :
    CompatiblePlaceTailReflection.Result checked registry functions program context evidence source faults place operator rhs
      environment actual before store mapping world next output value finalStore := by
  cases result with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace.sound same represented heaps maps worlds frame metadata
  | committed trace heaps maps worlds frame metadata count _ _ remaining =>
    exact .committed trace.sound heaps maps worlds frame metadata count remaining.sound

theorem ResultAt.weaken_bound {size larger : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {keyType : Ty} {actualContext : Core.Context} {place : PlaceResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {environment : Dynamic.Environment} {actual : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs
      environment actual before store mapping world next output value finalStore) (bound : size ≤ larger) :
    ResultAt larger checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs
      environment actual before store mapping world next output value finalStore := by
  cases result with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace same represented heaps maps worlds frame metadata
  | committed trace heaps maps worlds frame metadata count typed smaller remaining =>
    exact .committed trace heaps maps worlds frame metadata count typed (Nat.lt_of_lt_of_le smaller bound) remaining

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceAssignmentContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedBareBitNotContracts
/-! A numeric bare snapshot creates a real mapped commit and an exact typed
seven-slot continuation in the actual renamed environment. Its Unit RHS has
no source child. Every native phase is constructed from a represented live cell. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {location : Dynamic.Location} {target : Location} {sourceValue : Dynamic.Value} {value : Value}
  {actual : Environment} {actualContext : Core.Context} {index : Nat} {ξ : Renaming}

/-! The actual six phases and write expose a strict child of the original
Core derivation. Source updates have no expression child; continuation
agreement transports results but supplies no execution-size bound. -/
theorem initialized_prefix_sized (layout : Layout prepared)

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨prepared.route.rootSourceType, some sourceValue, none⟩)
    (nativeRead : store.read? target = some (.inRight .unit value))
    (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType sourceValue value prepared.route.rootType)
    (lookup : actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    ∃ updated replacement after finalStore slots,
      Dynamic.BitNotSnapshot (some sourceValue) updated ∧
      Dynamic.Heap.Writes heap location (some updated) after ∧
      ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      HeapRepresents checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      (SourceCoreDataPlaces.Passes operator .unit → ∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ))) ∧
      ∀ {next : Expr} {output : Ty} {result : Value} {after : Store} {size : Nat},
        CoreProof.EvaluationSize size actual store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
            next output operator true invalid).rename ξ) result after →
        ∃ remainingSize, remainingSize < size ∧ CoreProof.EvaluationSize remainingSize (slots ++ actual)
          finalStore (shift 7 (next.rename ξ)) result after := by
  obtain ⟨updated, replacement, related, applies, modified, _⟩ :=
    CompatiblePlaceNumericBitNotModifier.success profile represented
      (environment := rhsEnvironment prepared.route.rootType target .unit (.inRight .unit value) .unit actual)
      (snapshot := .var 1) (rhs := .var 0) (.var rfl) operator store invalid
  have written := DataPlaceCommitReflection.source_writes read updated
  obtain ⟨finalStore, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read related written
  let slots : Environment := [.unit, replacement, replacement, .unit, .inRight .unit value, .unit,
    .cellRef (OptionalCell.cellType prepared.route.rootType) target]
  have rhs : Evaluates (snapshotEnvironment prepared.route.rootType target .unit (.inRight .unit value) actual)
      store (shift 3 (LanguageResult.success .unit)) (.inRight .word .unit) store := by
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
    exact .inRight .unit
  have modifier : Evaluates (rhsEnvironment prepared.route.rootType target .unit (.inRight .unit value) .unit actual)
      store (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType operator true (.var 1) (.var 0) invalid)
      (.inRight .word replacement) store := by simpa only [← layout.sameType] using modified
  have agreement : SourceCoreDataPlaces.Passes operator .unit → ∀ next output, ContinuationAgreement actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ)
      (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
    intro passes next output
    rw [execute_rename layout]
    exact (ContinuationAgreement.letE (.var lookup)).trans
      ((ContinuationAgreement.bind (CompatibleBareBitNotNative.keys_evaluates _ _)).trans
        ((ContinuationAgreement.bind (CompatibleBareBitNotNative.getter_evaluates layout nativeRead)).trans
          ((ContinuationAgreement.bind rhs).trans
            ((ContinuationAgreement.bind modifier).trans
              ((ContinuationAgreement.bind (CompatibleBareBitNotNative.setter_evaluates layout
                (.inRight .unit value) replacement nativeRead)).trans
                ((DataPlaceGuard.agreement passes).trans
                  (ContinuationAgreement.letE (.storeCell (.var rfl) nativeRead (.inRight (.var rfl)) coreWritten))))))))

  refine ⟨updated, replacement, _, finalStore, slots, applies, written, related, finalHeaps, frame,
    .of_write written, rfl, ?_, agreement, ?_⟩
  ·
    exact .cons .unit (.cons related.runtime_hasType (.cons related.runtime_hasType
      (.cons .unit (.cons (.inRight represented.runtime_hasType) (.cons .unit (.cons (.cellRef reference.typed) actualTyped))))))
  · intro next output result after size completed
    rw [execute_rename layout] at completed
    have passes := RecursiveNamedBareAssignmentContracts.execute_unit_passes_sized
      (.var lookup) (CompatibleBareBitNotNative.keys_evaluates _ _)
      (CompatibleBareBitNotNative.getter_evaluates layout nativeRead) rhs modifier
      (CompatibleBareBitNotNative.setter_evaluates layout (.inRight .unit value) replacement nativeRead) completed
    have terminal := (agreement passes .unit output).wrap
      (by simpa [shift, Expr.rename, List.range, List.range.loop, List.foldl, Expr.weakenAt] using
        (Evaluates.unit (environment := slots ++ actual) (store := finalStore)))
    rw [execute_rename layout] at terminal
    exact RecursiveNamedBareAssignmentContracts.execute_continuation_sized
      (.var lookup) (CompatibleBareBitNotNative.keys_evaluates _ _)
      (CompatibleBareBitNotNative.getter_evaluates layout nativeRead) rhs modifier
      (CompatibleBareBitNotNative.setter_evaluates layout (.inRight .unit value) replacement nativeRead)
      terminal completed

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
/-! Original source children for ordinary composition heads. Each size refers
 to the retained source derivation. Native branch bounds are extracted from
 their original completion, independently of the source cost. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
open Core Frontend SourceInference GeneralHeap CompatiblePayload CoreProof
open CompatibleExpressionPrimitives RecursiveNamedCallBounds

private theorem node_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

theorem evaluation_raw_sized
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value} {size : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (evaluation : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id value after) :
    ∃ child, SourceExecutionSize.ExpressionFormEvaluates program child context evidence source environment before
      node.form node.requirements node.coercions value after ∧ child < size := by
  cases evaluation with
  | intro found raw coercions =>
    have same := node_unique unique found contains
    subst same
    rw [empty] at coercions
    cases coercions
    exact ⟨_, raw, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := node_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

theorem fault_raw_sized
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {size : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (fault : SourceExecutionSize.ExpressionFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.ExpressionFormFaults program child context evidence source environment before
      node.form node.requirements node.coercions reason after ∧ child < size := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form found raw =>
    exact ⟨_, node_unique unique found contains ▸ raw, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | coercion found _ failed =>
    have same := node_unique unique found contains
    subst same
    rw [empty] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := node_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {size : Nat}

theorem group_inv (metadata : Metadata checked source id node type) {inner : ExpressionId}
    (form : node.form = .group inner) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ child, ExpressionOutcome program child context evidence source environment before inner outcome after ∧ child < size := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with
    | group _ child => exact ⟨_, .value child, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with
    | group _ child => exact ⟨_, .fault child, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩

theorem pair_inv (metadata : Metadata checked source id node type) {left right : ExpressionId}
    (form : node.form = .tuple [left, right]) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ child sequence, ProtectedDataExpressionSequence.TraceAt program child context evidence source environment before
      [left, right] sequence after ∧ CompatibleExpressionProducts.PacksOutcome sequence outcome ∧ child < size := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with
    | tuple _ children pack => exact ⟨_, _, .values children, .values pack,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with
    | tuple _ children => exact ⟨_, _, .fault children, .fault _,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩

inductive UnaryTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (operand : ExpressionId) (operator : Syntax.UnaryOp) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {childSize input output after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before operand input after)
      (applies : Dynamic.UnaryPrimitiveApplies operator input output)
      (childSizeSmaller : childSize < size) : UnaryTrace program size context evidence source environment before operand operator (.value output) after
  | fault {childSize reason after}
      (child : SourceExecutionSize.ExpressionFaults program childSize context evidence source environment before operand reason after)
      (childSizeSmaller : childSize < size) :
      UnaryTrace program size context evidence source environment before operand operator (.fault reason) after
  | invalid {childSize input reason middle after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before operand input middle)
      (fault : Dynamic.UnaryOperationFaults program context evidence middle operator [] input reason after)
      (childSizeSmaller : childSize < size) :
      UnaryTrace program size context evidence source environment before operand operator (.fault reason) after

theorem unary_inv {operator : Syntax.UnaryOp} {operand : ExpressionId} (metadata : Metadata checked source id node type)
    (form : node.form = .unary operator operand) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    UnaryTrace program size context evidence source environment before operand operator outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | unary layout child applies =>
      have empty := no_owned layout
      subst empty
      cases applies with
      | primitive applied => refine .value child applied ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
      | method _ selected _ => cases selected
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | unaryOperand _ child => refine .fault child ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | unaryApply layout child failed =>
      have empty := no_owned layout
      subst empty
      refine .invalid child failed.sound ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

inductive BinaryTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) (operator : Syntax.BinaryOp) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | leftFault {childSize reason after}
      (child : SourceExecutionSize.ExpressionFaults program childSize context evidence source environment before left reason after)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.fault reason) after
  | leftInvalid {childSize input after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before left input after)
      (invalid : Dynamic.BinaryLeftOperandInvalid operator input)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.fault (.invalidBinaryOperands operator)) after
  | short {childSize input output after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before left input after)
      (circuit : Dynamic.ShortCircuits operator input output)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.value output) after
  | rightFault {firstSize secondSize input reason middle after}
      (first : SourceExecutionSize.ExpressionEvaluates program firstSize context evidence source environment before left input middle)
      (continues : Dynamic.EvaluatesRightOperand operator input)
      (second : SourceExecutionSize.ExpressionFaults program secondSize context evidence source environment middle right reason after)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.fault reason) after
  | value {firstSize secondSize a b output middle after}
      (first : SourceExecutionSize.ExpressionEvaluates program firstSize context evidence source environment before left a middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : SourceExecutionSize.ExpressionEvaluates program secondSize context evidence source environment middle right b after)
      (applies : Dynamic.BinaryPrimitiveApplies operator a b output)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.value output) after
  | invalid {firstSize secondSize a b reason middle operated after}
      (first : SourceExecutionSize.ExpressionEvaluates program firstSize context evidence source environment before left a middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : SourceExecutionSize.ExpressionEvaluates program secondSize context evidence source environment middle right b operated)
      (failed : Dynamic.BinaryOperationFaults program context evidence operated operator [] a b reason after)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.fault reason) after

theorem binary_inv {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (metadata : Metadata checked source id node type)
    (form : node.form = .binary left operator right) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    BinaryTrace program size context evidence source environment before left right operator outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | binaryShortCircuit _ child circuit _ => refine .short child circuit ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | binaryEvaluateRight layout first continues second applies =>
      have empty := no_owned layout
      subst empty
      cases applies with
      | primitive applied => refine .value first continues second applied ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
      | method _ selected _ => cases selected
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | binaryLeft _ child => refine .leftFault child ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | binaryLeftOperand _ child invalid => refine .leftInvalid child invalid ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | binaryRight _ first continues second => refine .rightFault first continues second ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | binaryApply layout first continues second failed =>
      have empty := no_owned layout
      subst empty
      refine .invalid first continues second failed.sound ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

inductive ConditionalTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition thenId elseId : ExpressionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | fault {childSize reason after}
      (child : SourceExecutionSize.ExpressionFaults program childSize context evidence source environment before condition reason after)
      (childSizeSmaller : childSize < size) :
      ConditionalTrace program size context evidence source environment before condition thenId elseId (.fault reason) after
  | branch {childSize branchSize flag middle outcome after}
      (conditionTrace : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before condition (.bool flag) middle)
      (branchTrace : ExpressionOutcome program branchSize context evidence source environment middle
        (if flag then thenId else elseId) outcome after)
      (childSizeSmaller : childSize < size)
      (branchSizeSmaller : branchSize < size) :
      ConditionalTrace program size context evidence source environment before condition thenId elseId outcome after
  | invalid {childSize value actual after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before condition value after)
      (invalid : ¬ Dynamic.BooleanValue value) (runtimeType : Dynamic.ValueRuntimeType value actual)
      (childSizeSmaller : childSize < size) :
      ConditionalTrace program size context evidence source environment before condition thenId elseId (.fault (.typeMismatch .bool actual)) after

theorem conditional_inv {condition thenId elseId : ExpressionId} (metadata : Metadata checked source id node type)
    (form : node.form = .conditional condition thenId elseId) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ConditionalTrace program size context evidence source environment before condition thenId elseId outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | conditionalTrue _ first second => refine .branch first (.value second) ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | conditionalFalse _ first second => refine .branch first (.value second) ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | conditionalCondition _ child => refine .fault child ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | conditionalTrueBranch _ first second => refine .branch first (.fault second) ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | conditionalFalseBranch _ first second => refine .branch first (.fault second) ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | conditionalType _ child invalid runtimeType => refine .invalid child invalid runtimeType ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

/-- The chosen right branch retains its original native child witness. -/
theorem right_evaluated {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {operator : Syntax.BinaryOp}
    {operand result : TypeSystem.Ty} {mode : Mode} {a : Dynamic.Value} {x : Value}
    {actual : Environment} {store finalStore : Store} {right : Expr} {value : Value}
    (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (original : EvaluationSize size (x :: actual) store (mode.tail operator right) value finalStore) :
    ∃ child rightValue rightStore, EvaluationSize child (x :: actual) store
      (right.weakenAt 0) rightValue rightStore ∧ child < size := by
  cases profile with
  | word strict => cases strict <;> cases original <;> refine ⟨_, _, _, by assumption, ?_⟩ <;> omega
  | integer strict => cases strict <;> cases original <;> refine ⟨_, _, _, by assumption, ?_⟩ <;> omega
  | panicking panicking => cases panicking <;> cases original <;> refine ⟨_, _, _, by assumption, ?_⟩ <;> omega
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict | panicking strict => cases strict
    | andTrue =>
      cases original with
      | ifTrue condition right =>
        obtain ⟨_, rfl⟩ := evaluation_deterministic condition.sound (Evaluates.var rfl)
        exact ⟨_, _, _, right, by omega⟩
      | ifFalse condition right =>
        have same := (evaluation_deterministic condition.sound (Evaluates.var rfl)).1
        cases same
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict | panicking strict => cases strict
    | orFalse =>
      cases original with
      | ifFalse condition right =>
        obtain ⟨_, rfl⟩ := evaluation_deterministic condition.sound (Evaluates.var rfl)
        exact ⟨_, _, _, right, by omega⟩
      | ifTrue condition right =>
        have same := (evaluation_deterministic condition.sound (Evaluates.var rfl)).1
        cases same

theorem choose_branch_evaluated {actual : Environment} {store finalStore : Store}
    {flag : Bool} {thenCode elseCode : Expr} {value : Value}
    (original : EvaluationSize size (.bool flag :: actual) store
      (.ifE (.var 0) (thenCode.weakenAt 0) (elseCode.weakenAt 0)) value finalStore) :
    ∃ child, EvaluationSize child (.bool flag :: actual) store
      ((if flag then thenCode else elseCode).weakenAt 0) value finalStore ∧ child < size := by
  cases original with
  | ifTrue condition branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic condition.sound (Evaluates.var rfl)
    cases same
    exact ⟨_, branch, by omega⟩
  | ifFalse condition branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic condition.sound (Evaluates.var rfl)
    cases same
    exact ⟨_, branch, by omega⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedAssignmentHeadContracts
/-! One dynamic result for bare and projected assignment heads. Source costs
remain independent of the original Core continuation size. Real entry, heap,
and slot receipts are outputs of execution reflection, never static Head fields. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedAssignmentHeadContracts
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (faults : FunctionCalls.FaultRep) (entry : ProtectedExpressionMeaning.Entry) (scope : Scope) (writtenContext : Core.Context)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (same : value = .inLeft output (.word token)) (matched : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (installed : entry scope finalMap finalWorld after finalStore canonical) :
      ResultAt size checked registry functions program context evidence source faults entry scope writtenContext place operator rhs
        environment canonical actual before store mapping world next output value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (installed : entry scope finalMap finalWorld after written canonical)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions program context evidence source faults entry scope writtenContext place operator rhs
        environment canonical actual before store mapping world next output value finalStore

theorem ResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry} {scope : Scope} {writtenContext : Core.Context}
    {place : PlaceResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt size checked registry functions program context evidence source faults entry scope writtenContext place operator rhs
      environment canonical actual before store mapping world next output value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      HeapRepresents checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions ∧
      entry scope finalMap finalWorld after written canonical ∧
      Evaluates (slots ++ actual) written (shift 7 next) value finalStore) := by
  cases result with
  | fault trace same matched heaps maps worlds frame metadata installed =>
    exact .inl ⟨_, _, _, _, _, trace.sound, same, matched, heaps, maps, worlds, frame, metadata, installed⟩
  | success trace heaps maps worlds frame metadata count typed installed _ remaining =>
    exact .inr ⟨_, _, _, _, _, _, trace.sound, heaps, maps, worlds, frame, metadata, count, typed, installed, remaining.sound⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedAssignmentHeadContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
/-! Pointwise composition of the existing static heads. Structural children
may use the same budget (group and singleton code are unchanged). Real call
body children remain subject to the separate strict bound of their call leaf.
This layer composes finite obligations; it does not close the recursive Tree. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives CoreProof
open RecursiveNamedBoundedContracts RecursiveNamedCallBounds
open CompatibleExpressionConditionals
open CompatibleExpressionTypedCompositions (Head)


private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId) (first second : SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code =>
  current = scope ∧ ((id = left ∧ code = first) ∨ (id = right ∧ code = second))

private theorem two_tree {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {left right : ExpressionId}
    {leftNode rightNode : ExpressionNode} {first second : SourceCoreBasic.LoweredExpr}
    (leftFound : source.lookupExpression? left = some leftNode)
    (rightFound : source.lookupExpression? right = some rightNode) :
    DataExpressionSequence.Tree source (Two scope left right first second) scope
      [left, right] [leftNode.type, rightNode.type] [first, second] :=
  .cons leftFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ (.single rightFound ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

private theorem pair_result {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {leftType rightType : TypeSystem.Ty}
    {first second : SourceCoreBasic.LoweredExpr} {faults : FunctionCalls.FaultRep}
    {sequence : DataExpressionSequence.Outcome} {value : Value}
    (result : DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world [leftType, rightType] [first, second] faults sequence value) :
    ∃ outcome, CompatibleExpressionProducts.PacksOutcome sequence outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (.product leftType rightType) (.product first.type second.type) faults outcome value := by
  cases result with
  | values represented =>
    change DataExpressionSequence.Values _ _ _ [leftType, rightType] [first.type, second.type] _ _ at represented
    cases represented with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        cases tail
        exact ⟨_, .values (.cons (.singleton _)), .value (.product left right)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩


variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}

universe u v
namespace Stateful
open ProtectedStateTransition (Transition)
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)

private def ReflectsRawAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩


/-- The second child starts at the first child's concrete post-witness. -/
private theorem continue_transition {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {initial middle reached : ProtectedStateTransition.Index}
    {state : protocol.State initial} {middleState : protocol.State middle}
    (first : protocol.Relates state middleState)
    (second : Transition protocol middleState reached) :
    Transition protocol state reached := by
  obtain ⟨final, last⟩ := second
  exact ⟨final, protocol.trans first last⟩

namespace WithReady
open ProtectedStateExpressionOperandTyping
variable (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop)

private theorem pair_transition
    {initial final : ProtectedStateTransition.Index} {state : protocol.State initial}
    {sequence : DataExpressionSequence.Outcome} {outcome : Dynamic.ExpressionOutcome}
    (packed : CompatibleExpressionProducts.PacksOutcome sequence outcome)
    (transition : ∃ reached : protocol.State final, protocol.Relates state reached ∧
      ∀ sources, sequence = .ok sources → ready reached) :
    ProtectedStateTransition.WithReady.Reached protocol ready outcome state final := by
  obtain ⟨reached, related, successful⟩ := transition
  refine ⟨reached, related, ?_⟩
  cases packed with
  | values _ => exact fun _ _ => successful _ rfl
  | fault _ => intro value impossible; cases impossible

theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (tree : Head checked source certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    [FunctionCalls.FaultTokens faults] (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.PreservesAt protocol ready
        (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.WithReady.Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning inner (by rw [form]; change inner ∈ [inner]; simp) n bound _ _ _ ⟨rfl, child⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry initialReady trace
    obtain ⟨childSize, childTrace, childSmaller⟩ := RecursiveNamedExpressionSourceBounds.group_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      ih childSize (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) innerFound environments heaps locals agrees actualTyped installedEntry initialReady childTrace
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have leftIH := fun n (bound : n ≤ budget) => @meaning left (by rw [form]; change left ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have rightIH := fun n (bound : n ≤ budget) => @meaning right (by rw [form]; change right ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry initialReady trace
    -- The sequence uses a strict bound; its successor is exactly childSize ≤ budget.
    have children : ∀ childId, childId ∈ [left, right] → ∀ childSize, childSize < budget + 1 → ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionPreservesAt protocol ready childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (fun current expression code => expression = childId ∧ Two scope left right first second current expression code) faults := by
      intro childId member childSize bound
      apply ProtectedStateTransition.WithReady.PreservesAt.to_sequence protocol ready
      intro childScope childId childCode entry
      obtain ⟨sameId, rfl, alternatives⟩ := entry
      subst childId
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH childSize (by omega)
      · exact rightIH childSize (by omega)
    obtain ⟨sequenceSize, sequence, sourceTrace, packed, sequenceSmaller⟩ := RecursiveNamedExpressionSourceBounds.pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      ProtectedDataExpressionSequence.Stateful.WithReady.preserves_bounded protocol ready (budget + 1) (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry initialReady sourceTrace (by omega)
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata, pair_transition protocol ready packed transition⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning operand (by rw [form]; change operand ∈ [operand]; simp) n bound _ _ _ ⟨rfl, child⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have sourceStep := RecursiveNamedExpressionSourceBounds.unary_inv metadata form unique trace
    cases sourceStep with
    | value childTrace applied childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) childFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
        have same := actualApplied.functional applied
        subst sourceResult
        refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _⟩
        · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
        · exact .value (outputType ▸ resultRep)
    | fault childTrace childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) childFound environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | invalid childTrace failed childSmaller =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) childFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
        exact False.elim (unary_fault_excluded applied failed)
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have leftIH := fun n (bound : n ≤ budget) => @meaning left (by rw [form]; change left ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, leftTree⟩
    have rightIH := fun n (bound : n ≤ budget) => @meaning right (by rw [form]; change right ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, rightTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have sourceStep := RecursiveNamedExpressionSourceBounds.binary_inv metadata form unique trace
    cases sourceStep with
    | leftFault childTrace childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | leftInvalid childTrace invalid childSmaller =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        exact False.elim (profile.left_valid payload invalid)
    | short childTrace circuit childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
        exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
          .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _⟩
    | rightFault firstTrace continues secondTrace firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt firstSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value firstTrace)
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
          rightIH _ (Nat.le_trans (Nat.le_of_lt secondSmaller) bounded) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) (.fault secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
    | value firstTrace continues secondTrace applied firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt firstSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value firstTrace)
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
          rightIH _ (Nat.le_trans (Nat.le_of_lt secondSmaller) bounded) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨sourceResult, result, actualApplied, resultRep, combined⟩ := profile.right_success leftPayload rightPayload continues first second applied
          have same := actualApplied.functional applied
          subst sourceResult
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated
              (ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _)⟩
    | invalid firstTrace continues secondTrace failed firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt firstSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value firstTrace)
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
          rightIH _ (Nat.le_trans (Nat.le_of_lt secondSmaller) bounded) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          rcases profile.right_outcome leftPayload rightPayload continues first second with
            ⟨_, _, applied, _, _⟩ | ⟨code, panics, combined⟩
          · exact False.elim (binary_fault_excluded applied failed)
          · obtain ⟨rfl, rfl⟩ := binary_fault_panic panics failed
            exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
              .fault (FunctionCalls.FaultTokens.panic code), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated
                (ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _)⟩

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have conditionIH := fun n (bound : n ≤ budget) => @meaning condition (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, conditionTree⟩
    have thenIH := fun n (bound : n ≤ budget) => @meaning thenId (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, thenTree⟩
    have elseIH := fun n (bound : n ≤ budget) => @meaning elseId (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, elseTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have sourceStep := RecursiveNamedExpressionSourceBounds.conditional_inv metadata form unique trace
    cases sourceStep with
    | fault childTrace childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        conditionIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | @branch conditionSize branchSize flag middle outcome after conditionTrace branchTrace conditionSmaller branchSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        conditionIH _ (Nat.le_trans (Nat.le_of_lt conditionSmaller) bounded) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady (.value conditionTrace)
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | value payload =>
        obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
        cases sourceEq
        subst coreEq
        cases flag with
        | false =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
            elseIH _ (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded) elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
          · rw [choose_rename]; exact LocalControl.choose_false type first branch
          · simpa only [elseType] using represented
        | true =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
            thenIH _ (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded) thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
          · rw [choose_rename]; exact LocalControl.choose_true type first branch
          · simpa only [thenType] using represented
    | invalid childTrace invalid runtimeType childSmaller =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := conditionIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨flag, rfl, _⟩ := bool_fields payload
        exact False.elim (invalid trivial)



theorem Head.reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (tree : Head checked source certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    [FunctionCalls.FaultTokens faults] (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.ReflectsAt protocol ready
        (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.WithReady.Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning inner (by rw [form]; change inner ∈ [inner]; simp) n bound _ _ _ ⟨rfl, child⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      ih size bounded innerFound environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.group_intro metadata form trace.sound, ?_, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have leftIH := fun n (bound : n ≤ budget) => @meaning left (by rw [form]; change left ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have rightIH := fun n (bound : n ≤ budget) => @meaning right (by rw [form]; change right ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    -- The sequence uses a strict bound; its successor is exactly childSize ≤ budget.
    have children : ∀ childId, childId ∈ [left, right] → ∀ childSize, childSize < budget + 1 → ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionReflectsAt protocol ready childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (fun current expression code => expression = childId ∧ Two scope left right first second current expression code) faults := by
      intro childId member childSize bound
      apply ProtectedStateTransition.WithReady.ReflectsAt.to_sequence protocol ready
      intro childScope childId childCode entry
      obtain ⟨sameId, rfl, alternatives⟩ := entry
      subst childId
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH childSize (by omega)
      · exact rightIH childSize (by omega)
    obtain ⟨sequenceSize, sequence, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      ProtectedDataExpressionSequence.Stateful.WithReady.reflects_bounded protocol ready (budget + 1) (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry initialReady evaluated (by omega)
    obtain ⟨outcome, packed, payload⟩ := pair_result represented
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.pair_intro metadata form sourceTrace.sound packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata, pair_transition protocol ready packed transition⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning operand (by rw [form]; change operand ∈ [operand]; simp) n bound _ _ _ ⟨rfl, child⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    rw [unary_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) childFound environments heaps locals agrees actualTyped installedEntry initialReady childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation.sound) complete
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.fault failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) childFound environments heaps locals agrees actualTyped installedEntry initialReady childEvaluation
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation.sound coreApplied) complete
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.value childTrace.sound applied),
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _⟩
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have leftIH := fun n (bound : n ≤ budget) => @meaning left (by rw [form]; change left ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, leftTree⟩
    have rightIH := fun n (bound : n ≤ budget) => @meaning right (by rw [form]; change right ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, rightTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    rw [Mode.binary_rename] at evaluated
    have complete := evaluated.sound
    rw [Mode.binary_eq] at evaluated
    cases evaluated with
    | caseLeft leftEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        leftIH _ (by omega) leftFound environments heaps locals agrees actualTyped installedEntry initialReady leftEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation.sound)
          exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.leftFault failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | caseRight leftEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        leftIH _ (by omega) leftFound environments heaps locals agrees actualTyped installedEntry initialReady leftEvaluation
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | @value sourceValue coreValue payload =>
        rw [leftType] at payload
        cases trace with
        | value firstTrace =>
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation.sound
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, middle, middleMap, middleWorld, binary_intro metadata form (.short firstTrace.sound circuit),
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, ⟨middleState, firstRelated, fun _ _ => firstReady _ rfl⟩⟩
          · obtain ⟨rightSize, rightValue, rightStore, rightEvaluation, rightSmaller⟩ := RecursiveNamedExpressionSourceBounds.right_evaluated profile payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightSourceSize, rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
              rightIH rightSize (by omega) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) shifted
            cases represented with
            | fault matched =>
              cases trace with
              | fault failed =>
                have combined := profile.right_failure payload continues leftEvaluation.sound rightEvaluation.sound
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.rightFault firstTrace.sound continues failed.sound),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              rcases profile.right_outcome leftPayload rightPayload continues leftEvaluation.sound rightEvaluation.sound with
                ⟨sourceResult, result, applied, resultRep, combined⟩ | ⟨code, panics, combined⟩
              · obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                cases trace with
                | value secondTrace =>
                  exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.value firstTrace.sound continues secondTrace.sound applied),
                    .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                    firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated (ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _)⟩
              · obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                cases trace with
                | value secondTrace =>
                  exact ⟨_, after, finalMap, finalWorld,
                    binary_intro metadata form (.invalid firstTrace.sound continues secondTrace.sound (.panic panics)),
                    .fault (FunctionCalls.FaultTokens.panic code), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                    firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated (ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _)⟩

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have conditionIH := fun n (bound : n ≤ budget) => @meaning condition (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, conditionTree⟩
    have thenIH := fun n (bound : n ≤ budget) => @meaning thenId (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, thenTree⟩
    have elseIH := fun n (bound : n ≤ budget) => @meaning elseId (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, elseTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    rw [choose_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        conditionIH _ (by omega) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation.sound)
          exact ⟨_, after, finalMap, finalWorld, conditional_intro metadata form (.fault failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        conditionIH _ (by omega) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady childEvaluation
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | value payload =>
        obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
        subst sourceEq
        subst coreEq
        cases trace with
        | value conditionTrace =>
          obtain ⟨selectedSize, selected, selectedSmaller⟩ := RecursiveNamedExpressionSourceBounds.choose_branch_evaluated branch
          cases flag with
          | false =>
            change EvaluationSize selectedSize _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
              elseIH selectedSize (by omega) elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace.sound branchTrace.sound),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
            simpa only [elseType] using represented
          | true =>
            change EvaluationSize selectedSize _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
              thenIH selectedSize (by omega) thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace.sound branchTrace.sound),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
            simpa only [thenType] using represented



theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (tree : Head checked source certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    [FunctionCalls.FaultTokens faults] (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.ReflectsAt protocol ready
        (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.WithReady.Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial initialReady evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    Head.reflects_raw_at functions program evidence protocol ready budget size bounded tree found meaning
      environments heaps locals agrees actualTyped initial initialReady evaluated
  obtain ⟨sourceSize, sized⟩ := ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩

end WithReady

theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    [FunctionCalls.FaultTokens faults] (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults childSize) :
    ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults size := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _⟩ := WithReady.Head.preserves_at functions program evidence protocol (fun _ => True)
        budget size bounded unique tree found
        (fun child _ childSize bound => by
          intro current expression code certified
          exact ProtectedStateTransition.WithReady.PreservesAt.of_stateful protocol (meaning childSize bound) certified.2)
        environments heaps locals agrees actualTyped initial True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related⟩

private theorem Head.reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    [FunctionCalls.FaultTokens faults] (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults childSize) :
    ReflectsRawAt protocol size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _⟩ := WithReady.Head.reflects_raw_at functions program evidence protocol (fun _ => True)
        budget size bounded tree found
        (fun child _ childSize bound => by
          intro current expression code certified
          exact ProtectedStateTransition.WithReady.ReflectsAt.of_stateful protocol (meaning childSize bound) certified.2)
        environments heaps locals agrees actualTyped initial True.intro evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related⟩

/-- Finite native completion yields an independently sized source trace. -/
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    [FunctionCalls.FaultTokens faults] (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol
      (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source certificate faults childSize) :
    ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults size := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    Head.reflects_raw_at functions program evidence protocol budget size bounded meaning tree found environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨sourceSize, sized⟩ := ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩

end Stateful

/-- Legacy entries carry a proof witness and no runtime record data. -/
private def legacyProtocol (entry : ProtectedExpressionMeaning.Entry) :
    ProtectedStateTransition.Protocol Unit where
  State index := PLift (entry index.scope index.mapping index.world index.heap index.store index.canonical)
  records _ := ()
  Relates _ _ := True
  refl _ := True.intro
  trans _ _ := True.intro

variable {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

private theorem lift_preserves_at {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedStateTransition.PreservesAt (legacyProtocol entry) (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees actualTyped initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨PLift.up (transport.extend initial.down maps worlds frame metadata), True.intro⟩⟩

private theorem lift_reflects_at {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedStateTransition.ReflectsAt (legacyProtocol entry) (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees actualTyped initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨PLift.up (transport.extend initial.down maps worlds frame metadata), True.intro⟩⟩

theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    [FunctionCalls.FaultTokens faults] (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.PreservesAt childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installedEntry trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.Head.preserves_at functions program evidence (legacyProtocol entry) budget size bounded unique
      (fun childSize bound => lift_preserves_at functions program evidence transport (meaning childSize bound))
      tree found environments heaps locals agrees actualTyped (PLift.up installedEntry) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- Finite native completion yields an independently sized source trace. -/
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    [FunctionCalls.FaultTokens faults] (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt childSize
      (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.Head.reflects_at functions program evidence (legacyProtocol entry) budget size bounded
      (fun childSize bound => lift_reflects_at functions program evidence transport (meaning childSize bound))
      tree found environments heaps locals agrees actualTyped (PLift.up installedEntry) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
end
