import Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics
import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentRhs
import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentMeaning
import Solcore.SourceSemantics.CoreLowering.ProtectedStateBareAssignment

/-! Completed bare assignment code reconstructs the independent source
transaction or fault. RHS meaning is typed and instantiated in the actual
three temporary slots; successful continuation typing names its seven values.
A concrete expression-tree consumer discharges the child interface separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof
open CompatibleBareAssignment
universe u v

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {certificate : Certificate} {faults : FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp} {identities : Dynamic.Value → Word → Prop}
  {entry : ProtectedExpressionMeaning.Entry}

/- Finite reflection needs no source RHS trace and no chosen child execution.
The actual completed code is the sole runtime premise. -/
namespace Stateful
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)

include transport in
theorem reflects_reachable_bounded_with_rhs (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
      (child : Nat), child < budget → ∀ {value : Value} {finalStore : Store},
      EvaluationSize child (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
        store (shift 3 (lowered.expression.rename ξ)) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
        RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
          (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (_generated : certificate scope id lowered) (_found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ProtectedStateBareAssignment.ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator scope canonical environment before store mapping world
      id actual actualContext ξ initial next outputType value finalStore := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  have phase :=  snapshot_prefix layout snapshot lowered.expression next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) invalid
  obtain ⟨prefixSize, prefixBound, remaining⟩ := RecursiveNamedBareAssignmentContracts.snapshot_prefix_sized layout snapshot completed
  cases remaining with
  | caseLeft evaluated _ =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result, rhsPost⟩ :=
      rhsMeaning snapshot _ (by omega) evaluated
    cases related : result.represented with
    | fault token =>
      have failed := phase.wrap (LanguageResult.bind_failure outputType result.evaluated)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
      cases sourceTrace with
      | fault fault =>
        exact .fault (.rhs (RecursiveNamedBareAssignmentContracts.resolves_sized snapshot bare) fault) rfl token result.heaps result.maps result.worlds result.frame result.metadata rhsPost
  | caseRight evaluated remaining =>
    rename_i rhsStore rightValue
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result, rhsPost⟩ :=
      rhsMeaning snapshot _ (by omega) evaluated
    cases related : result.represented with
    | value payload =>
      rename_i right
      rename_i rhsStore
      have rightRep : ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType right rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      have saved := snapshot.represented.extend result.maps result.worlds
      have modifier := modifier_total observations profile saved rightRep
        (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid
      rcases modifier with ⟨invalidOperands, failed⟩ | ⟨updated, updatedValue, replacement, applied, modified⟩
      · have failed : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
            (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
            (.inLeft prepared.route.leafType (.word invalid)) rhsStore := by
          simpa only [layout.sameType] using failed
        have evaluation := phase.wrap (LanguageResult.bind_success outputType result.evaluated
          (LanguageResult.bind_failure outputType failed))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluation
        obtain ⟨latest⟩ := result.latest
        obtain ⟨initial, initialized⟩ := cell_initial latest.related
        cases sourceTrace with
        | value rhsTrace =>
          exact .fault (.operands (RecursiveNamedBareAssignmentContracts.resolves_sized snapshot bare) rhsTrace latest.read
            (latest.type.trans snapshot.type.symm) initialized .nil invalidOperands) rfl (invalidToken _ _ invalidOperands)
            result.heaps result.maps result.worlds result.frame result.metadata rhsPost
      · cases sourceTrace with
        | value rhsTrace =>
          obtain ⟨latest⟩ := result.latest
          obtain ⟨initial, initialValue⟩ := cell_initial latest.related
          have nativeModified : Evaluates
              (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
              (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
              (.inRight .word updatedValue) rhsStore := by simpa only [layout.sameType] using modified
          obtain ⟨after, commitStore, _, written, finalHeaps, frame, metadata, typed, writeFrame, writeMetadata, agreement⟩ :=
            commit_with_write layout snapshot bare result rightRep replacement applied nativeModified actualTyped
          have terminal := (agreement .unit outputType).wrap
            (by simpa [shift, Expr.rename, List.range, List.range.loop, List.foldl, Expr.weakenAt] using
              (Evaluates.unit (environment := writtenEnvironment prepared.route.rootType snapshot.target .unit
                snapshot.value rightValue updatedValue updatedValue actual) (store := commitStore)))
          obtain ⟨remainingSize, remainingBound, remaining⟩ :=
            RecursiveNamedBareAssignmentContracts.continuation_sized layout snapshot result.evaluated nativeModified
              latest.nativeRead terminal completed
          obtain ⟨rhsState, rhsRelated⟩ := rhsPost
          exact .success (.intro (RecursiveNamedBareAssignmentContracts.resolves_sized snapshot bare) rhsTrace
              (.intro latest.read (latest.type.trans snapshot.type.symm) initialValue (.leaf applied) written))
            replacement finalHeaps result.maps result.worlds frame metadata
            (slots := [.unit, updatedValue, updatedValue, rightValue, snapshot.value, .unit,
              .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target]) rfl typed remainingBound remaining
            ⟨transport.extend rhsState (.refl _) (.refl _) writeFrame writeMetadata,
              protocol.trans rhsRelated (transport.related rhsState (.refl _) (.refl _) writeFrame writeMetadata)⟩

include transport in
theorem reflects_reachable_bounded (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.ReflectsAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ProtectedStateBareAssignment.ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator scope canonical environment before store mapping world
      id actual actualContext ξ initial next outputType value finalStore := by
  exact reflects_reachable_bounded_with_rhs protocol transport budget initial layout bare extension
    (fun snapshot child smaller {_ _} evaluated => Stateful.rhs_reflects_at snapshot protocol child (meaning child smaller)
      generated found environments heaps locals agrees actualTyped initial evaluated)
    observations generated found rhsView rhsCore profile environments heaps locals agrees actualTyped slot rootTyped invalidToken completed bounded

end Stateful

theorem reflects_reachable_bounded (budget : Nat)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.ReflectsAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedBareAssignmentContracts.ResultAt size compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  exact (Stateful.reflects_reachable_bounded_with_rhs (scope := scope) (canonical := canonical)
    ProtectedStateBareAssignment.unitProtocol ProtectedStateBareAssignment.unitTransport budget () layout bare extension
    (fun snapshot child smaller {_ _} evaluated => by
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ := rhs_reflects_at snapshot child (meaning child smaller)
        generated found environments heaps locals agrees actualTyped installed evaluated
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, (), trivial⟩)
    observations generated found rhsView rhsCore profile environments heaps locals agrees actualTyped slot rootTyped invalidToken completed bounded).forget

theorem reflects_reachable
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) :
    CompatibleBareAssignment.Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size completed
  exact (reflects_reachable_bounded size layout bare extension
    (RecursiveNamedBoundedContracts.reflects_below_of_unbounded meaning size) observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped invalidToken sized (Nat.le_refl size)).erase

/-- Compatibility entry point retaining the original operand-token premise. -/
theorem reflects
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : faults (.invalidAssignmentOperands operator) invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) :
    CompatibleBareAssignment.Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  exact reflects_reachable layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped
    (AssignmentOperandDiagnostics.of_unconditional invalidToken) completed

end Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
