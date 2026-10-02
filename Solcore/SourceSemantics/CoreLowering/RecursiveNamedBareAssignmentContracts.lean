import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts

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
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {invalid : Word}
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

/-- One inversion for the actual emitted prefix. The six supplied phase
executions align values/stores; all costs come from the original derivation.
The terminal Unit execution identifies only the store after its real write. -/
theorem execute_continuation_sized {prepared : Prepared} {reference rhs next : Expr}
    {keys : SourceCoreBasic.LoweredExpr} {outputType : Ty} {operator : Option BinaryOp}
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
  cases sixthEval with
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
                    (.letE (.storeCell referenceEval.sound read input.sound written)
                      (by simpa [shift, Expr.rename, List.range, List.range.loop, List.foldl, Expr.weakenAt] using
                        (Evaluates.unit (environment := .unit :: updated :: changed :: right :: saved :: keyValue ::
                          .cellRef (OptionalCell.cellType prepared.route.rootType) target :: actual) (store := writtenStore)))))))))
      obtain ⟨_, sameStore⟩ := evaluation_deterministic nativePrefix terminal
      cases sameStore
      exact ⟨_, by omega, remaining⟩

/-- Every bound comes from the original completed derivation. The terminal
prefix is used solely to identify its write store with the semantic commit. -/
theorem continuation_sized
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {invalid : Word}
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
