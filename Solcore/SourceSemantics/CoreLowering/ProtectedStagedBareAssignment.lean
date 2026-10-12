import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds

/-! A bare plain assignment runs its RHS through the same staged relation.
The native snapshot and seven-slot commit remain those emitted by the actual
compiler. Stage rejection stops before the write and retains the RHS heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof
open CompatibleBareAssignment
universe u v

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {faults : RecursiveStageMeaning.FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)

structure RhsResult
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
    (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop where
  trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id outcome after
  evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
    store (shift 3 (lowered.expression.rename ξ)) value finalStore
  represented : RecursiveStageMeaning.ResultRepresentsFor (payloadModel compilation.checked registry functions)
    finalMap finalWorld node.type lowered.type faults outcome value
  heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store finalMap finalStore
  metadata : Dynamic.HeapMetadataExtend before after
  sourcePost : ∀ right, outcome = .value right →
    Dynamic.ValueHasType context after right node.type ∧ Dynamic.HeapWellTyped context after

inductive ResultAt (size : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before place target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      ResultAt size initial next output value finalStore
  | success {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (snapshot : Staging.Recursive.BareTarget environment before place target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id (.value right) middle)
      (rightTyped : Dynamic.ValueHasType context middle right node.type)
      (middleTyped : Dynamic.HeapWellTyped context middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies .equal target.selected right replacement)
        middle target updated after)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, written, canonical⟩) :
      ResultAt size initial next output value finalStore

variable (transport : ProtectedStateTransition.AdministrativeTransport protocol)

include transport in
/-- Every recursive RHS bound comes from the completed native prefix.
Only the successful branch constructs an ordinary assignment erasure for the
existing pure commit lemma; staged faults stay in the staged result. -/
theorem reflects_with_rhs (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
      (child : Nat), child < budget → ∀ {value : Value} {finalStore : Store},
      EvaluationSize child (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
        store (shift 3 (lowered.expression.rename ξ)) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RhsResult (program := program) (context := context) (stages := stages) (invocation := invocation)
          (faults := faults) (id := id) (node := node) (lowered := lowered)
          snapshot sourceSize outcome after value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        none false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt (compilation := compilation) (registry := registry) (functions := functions) (program := program) (context := context) (stages := stages) (invocation := invocation)
      (prepared := prepared) (place := place) (environment := environment) (actual := actual)
      (faults := faults) (id := id) (node := node) (actualContext := actualContext)
      protocol size initial (next.rename ξ) outputType value finalStore := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  have bareSnapshot := (Staging.Recursive.BareTarget.of_resolves (program := program) (context := context) (evidence := invocation.evidence) (source := invocation.source) bare (snapshot.resolves bare)).2
  have phase := snapshot_prefix layout snapshot lowered.expression next outputType none invalid
  obtain ⟨prefixSize, prefixBound, remaining⟩ := RecursiveNamedBareAssignmentContracts.snapshot_prefix_sized layout snapshot completed
  cases remaining with
  | caseLeft evaluated _ =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ :=
        rhsMeaning snapshot _ (by omega) evaluated
      cases related : result.represented with
      | fault token =>
          have failed := phase.wrap (LanguageResult.bind_failure outputType result.evaluated)
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
          exact .fault bareSnapshot result.trace rfl token result.heaps result.maps result.worlds
            result.frame result.metadata rhsPost
  | caseRight evaluated retained =>
      rename_i rhsStore rightValue
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ :=
        rhsMeaning snapshot _ (by omega) evaluated
      cases related : result.represented with
      | value payload =>
          rename_i right
          rename_i rhsStore
          have rightRep : ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType right rightValue prepared.route.rootType :=
            .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
          obtain ⟨plain, _⟩ := ProtectedBareAssignment.rhs_of_expression snapshot protocol initial
            (faults := fun _ _ => False) (.value result.trace.sound.value_plain) result.evaluated
            (.value payload) result.heaps result.maps result.worlds result.frame result.metadata rhsPost
          obtain ⟨latest⟩ := plain.latest
          obtain ⟨initialValue, initialized⟩ := cell_initial latest.related
          have nativeModified : Evaluates
              (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
              (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType none false (.var 1) (.var 0) invalid)
              (.inRight .word rightValue) rhsStore := by
            simp only [SourceCoreCompatibleDataPlaces.modified]
            exact .inRight (.var rfl)
          obtain ⟨after, commitStore, _, written, finalHeaps, frame, metadata, typed, writeFrame, writeMetadata, agreement⟩ :=
            commit_with_write layout snapshot bare plain rightRep rightRep (.equal _ _) nativeModified actualTyped
          have terminal := (agreement .unit outputType).wrap
            (by simpa [shift, Expr.rename, List.range, List.range.loop, List.foldl, Expr.weakenAt] using
              (Evaluates.unit (environment := writtenEnvironment prepared.route.rootType snapshot.target .unit
                snapshot.value rightValue rightValue rightValue actual) (store := commitStore)))
          obtain ⟨remainingSize, remainingBound, remaining⟩ :=
            RecursiveNamedBareAssignmentContracts.continuation_sized layout snapshot result.evaluated nativeModified
              latest.nativeRead terminal completed
          obtain ⟨rhsState, rhsRelated⟩ := rhsPost
          obtain ⟨rightTyped, middleTyped⟩ := result.sourcePost _ rfl
          exact .success bareSnapshot result.trace rightTyped middleTyped
            (.intro latest.read (latest.type.trans snapshot.type.symm) initialized (.leaf (.equal _ _)) written)
            finalHeaps result.maps result.worlds frame metadata
            (slots := [.unit, rightValue, rightValue, rightValue, snapshot.value, .unit,
              .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target]) rfl typed remainingBound remaining
            ⟨transport.extend rhsState (.refl _) (.refl _) writeFrame writeMetadata,
              protocol.trans rhsRelated (transport.related rhsState (.refl _) (.refl _) writeFrame writeMetadata)⟩



private theorem writes_functional {heap left right : Dynamic.Heap} {location : Dynamic.Location}
    {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes heap location value left)
    (second : Dynamic.Heap.Writes heap location value right) : left = right := by
  have cells : ∀ {before first second : List Dynamic.Cell} {index : Nat} {value : Dynamic.Cell},
      Dynamic.Heap.CellsWrite before index value first → Dynamic.Heap.CellsWrite before index value second → first = second := by
    intro before first second index value left
    induction left generalizing second with
    | head => intro right; cases right; rfl
    | tail _ ih => intro right; cases right with | tail rest => exact congrArg (List.cons _) (ih rest)
  cases first with
  | intro firstRead firstWrite =>
    cases second with
    | intro secondRead secondWrite =>
      cases firstRead.functional secondRead
      exact congrArg Dynamic.Heap.mk (cells firstWrite secondWrite)

include transport in
theorem preserves_value_with_rhs
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {sourceSize : Nat} {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
    {target : Dynamic.ResolvedPlace}
    (targetSnapshot : Staging.Recursive.BareTarget environment before place target)
    (sourceTrace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id (.value right) middle)
    (sourceWrite : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies .equal target.selected right replacement)
      middle target updated after)
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index)),
      ∃ value finalStore finalMap finalWorld,
        RhsResult (program := program) (context := context) (stages := stages) (invocation := invocation)
          (faults := faults) (id := id) (node := node) (lowered := lowered)
          snapshot sourceSize (.value right) middle value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, middle, finalStore, canonical⟩)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (invalid : Word) :
    ∃ finalStore finalMap finalWorld slots,
      Dynamic.ValueHasType context middle right node.type ∧ Dynamic.HeapWellTyped context middle ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next output none false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  obtain ⟨_, sameTarget⟩ := snapshot.resolve_unique bare (targetSnapshot.resolves program context invocation.evidence invocation.source)
  subst target
  obtain ⟨value, rhsStore, rhsMap, rhsWorld, result, rhsPost⟩ := rhsMeaning snapshot
  cases related : result.represented with
  | value payload =>
    rename_i rightValue
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType right rightValue prepared.route.rootType :=
      .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
    obtain ⟨plain, _⟩ := ProtectedBareAssignment.rhs_of_expression snapshot protocol initial
      (faults := fun _ _ => False) (.value sourceTrace.sound.value_plain) result.evaluated
      (.value payload) result.heaps result.maps result.worlds result.frame result.metadata rhsPost
    cases sourceWrite with
    | intro latestRead sameType initialValue update written =>
      cases update with
      | leaf applied =>
        cases applied
        have nativeModified : Evaluates
            (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
            (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType none false (.var 1) (.var 0) invalid)
            (.inRight .word rightValue) rhsStore := by
          simp only [SourceCoreCompatibleDataPlaces.modified]
          exact .inRight (.var rfl)
        obtain ⟨generatedHeap, finalStore, _, generatedWrite, finalHeaps, frame, metadata, typed, writeFrame, writeMetadata, agreement⟩ :=
          commit_with_write layout snapshot bare plain rightRep rightRep (.equal _ _) nativeModified actualTyped
        have same := writes_functional generatedWrite written
        subst generatedHeap
        obtain ⟨rhsState, rhsRelated⟩ := rhsPost
        exact ⟨finalStore, rhsMap, rhsWorld,
          [.unit, rightValue, rightValue, rightValue, snapshot.value, .unit,
            .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target],
          (result.sourcePost _ rfl).1, (result.sourcePost _ rfl).2,
          finalHeaps, result.maps, result.worlds, frame, metadata, rfl, typed,
          ⟨transport.extend rhsState (.refl _) (.refl _) writeFrame writeMetadata,
            protocol.trans rhsRelated (transport.related rhsState (.refl _) (.refl _) writeFrame writeMetadata)⟩,
          agreement⟩

theorem preserves_fault_with_rhs
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared)
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {sourceSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index)),
      ∃ value finalStore finalMap finalWorld,
        RhsResult (program := program) (context := context) (stages := stages) (invocation := invocation)
          (faults := faults) (id := id) (node := node) (lowered := lowered)
          snapshot sourceSize (.fault failure) after value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (next : Expr) (output : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next output none false invalid).rename ξ)
        (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, result, post⟩ := rhsMeaning snapshot
  cases result.represented with
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      (snapshot_prefix layout snapshot lowered.expression next output none invalid).wrap
        (LanguageResult.bind_failure output result.evaluated),
      matched, result.heaps, result.maps, result.worlds, result.frame, result.metadata, post⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedBareAssignment
