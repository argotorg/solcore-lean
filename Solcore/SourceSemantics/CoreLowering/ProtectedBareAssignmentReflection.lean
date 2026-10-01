import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentRhs
import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentMeaning

/-! Completed bare assignment code reconstructs the independent source
transaction or fault. RHS meaning is typed and instantiated in the actual
three temporary slots; successful continuation typing names its seven values.
A concrete expression-tree consumer discharges the child interface separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof
open CompatibleBareAssignment

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {certificate : Certificate} {faults : FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp} {identities : Dynamic.Value → Word → Prop}
  {entry : ProtectedExpressionMeaning.Entry}

/-- Finite reflection needs no source RHS trace and no chosen child execution.
The actual completed code is the sole runtime premise. -/
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
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  have phase :=  snapshot_prefix layout snapshot lowered.expression next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) invalid
  have remaining := phase.unwrap completed
  cases remaining with
  | caseLeft evaluated _ =>
    obtain ⟨outcome, after, finalMap, finalWorld, result⟩ :=
      ProtectedBareAssignment.rhs_reflects snapshot meaning generated found environments heaps locals agrees actualTyped installed evaluated
    cases related : result.represented with
    | fault token =>
      have failed := phase.wrap (LanguageResult.bind_failure outputType result.evaluated)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed failed
      cases result.trace with
      | fault fault =>
        exact .fault (.rhs (snapshot.resolves bare) fault) rfl token result.heaps result.maps result.worlds result.frame result.metadata
  | caseRight evaluated remaining =>
    rename_i rhsStore rightValue
    obtain ⟨outcome, after, finalMap, finalWorld, result⟩ :=
      ProtectedBareAssignment.rhs_reflects snapshot meaning generated found environments heaps locals agrees actualTyped installed evaluated
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
            (modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
            (.inLeft prepared.route.leafType (.word invalid)) rhsStore := by
          simpa only [layout.sameType] using failed
        have evaluation := phase.wrap (LanguageResult.bind_success outputType result.evaluated
          (LanguageResult.bind_failure outputType failed))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluation
        obtain ⟨latest⟩ := result.latest
        obtain ⟨initial, initialized⟩ := cell_initial latest.related
        cases result.trace with
        | value rhsTrace =>
          exact .fault (.operands (snapshot.resolves bare) rhsTrace latest.read
            (latest.type.trans snapshot.type.symm) initialized .nil invalidOperands) rfl invalidToken
            result.heaps result.maps result.worlds result.frame result.metadata
      · obtain ⟨after, commitStore, trace, _, finalHeaps, frame, metadata, typed, agreement⟩ :=
          commit layout snapshot bare result rightRep replacement applied (by simpa only [layout.sameType] using modified) actualTyped
        exact .success trace replacement finalHeaps result.maps result.worlds frame metadata
          (slots := [.unit, updatedValue, updatedValue, rightValue, snapshot.value, .unit,
            .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target]) rfl typed
          ((agreement next outputType).unwrap completed)

end Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
