import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaViewHeads

/-! A genuine formation fixes the stronger captured-prefix receipt at its
producer. Generic ValueRep inversion keeps an existential caller prefix, so
local storage must retain this original receipt when it is needed later. The
formation copies the captured cells, so the receipt describes the formed
closure over its copies in the formed state. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState RecursiveNamedCatalog RecursiveNamedLambdaFormationHeads
open CallableIndexedLambdaNestedRuntimeBodyMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled program} {rank : Nat}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
    source context evidence scope id lowered)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope canonical owner.key.frameLocation)
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
    (some (CallableIndexedNamedGeneration.state caller.named)))
  (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
    compiled.indexed.layouts.definitions}
  (heaps : GenericHeap.HeapRepresents model mapping world heap store)

/-- The formation records of the head's actual formation: the copies of its
captured cells, the formed closure over them and the formed state. -/
abbrev FormedRecord :=
  Formed model
    (captures_for complete globals
      (CallableIndexedOwnedLambdaViewHeads.nested_entry initial owner prefixZero observed history bundle globals)
      related agrees typed)
    (actualCode head environment)
    (historyAt head
      (CallableIndexedOwnedLambdaViewHeads.nested_entry initial owner prefixZero observed history bundle globals)
      environment)
    heap store owner.key.frameLocation

include slots heaps in
/-- The actual formation of the head copies its captured cells. -/
theorem formation_exists :
    Nonempty (FormedRecord head complete globals initial owner prefixZero observed history bundle related agrees typed
      (model := model)) := by
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial owner prefixZero observed history bundle globals
  let captured : Captures compiled.indexed mapping world scope environment actual :=
    captures_for complete globals entry related agrees typed
  have capturedGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    have capturedGlobals := capture_globals_for complete globals slots entry related agrees typed
    have frame : entry.catalog.authority.frameLocation = owner.key.frameLocation :=
      (initial.rows owner.position).frame_eq
    simpa only [frame] using capturedGlobals
  have reference : captured.canonical[(actualCode head environment).referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    have referenceEq : (actualCode head environment).referenceIndex =
        scope.length + 1 + compiled.indexed.base.globals.length := reference_index head
    rw [referenceEq]
    exact capturedGlobals.reference
  have read : store.read? owner.key.frameLocation = some (SourceCoreCallableIndexedFrames.encode
      compiled.indexed.ancestry.layout.frame (historyAt head entry environment).native) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  exact CallableIndexedLambdaValues.formation captured (actualCode head environment)
    (historyAt head entry environment) head.snapshots (reference_index head) heaps reference read

variable (formedRecord : FormedRecord head complete globals initial owner prefixZero observed history bundle related
  agrees typed (model := model))

include slots heaps in
/-- The same actual formation captures, code, history and support create the
selected closure receipt for a formed record, over its copies in the formed
state. -/
def of_formation :
    let code := actualCode head environment
    CallableIndexedOwnedIndirectExpressionHeads.ClosureAt (headers := headers) (keys := keys)
      (registry := registry) (faults := faults)
      formedRecord.finalMap formedRecord.finalWorld formedRecord.closure
      (FunctionValues.sourceType formedRecord.closure)
      (value code formedRecord.embedding (initial.rows owner.position).authority.current formedRecord.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial owner prefixZero observed history bundle globals
  let captured : Captures compiled.indexed mapping world scope environment actual :=
    captures_for complete globals entry related agrees typed
  let code : Code compiled.indexed (formed head environment) scope captured.administrative := actualCode head environment
  let currentHistory : History code := historyAt head entry environment
  let support : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code := actualSupport head environment
  have origin : CallableIndexedOwnedFunctionValues.ActualSourceOrigin code currentHistory support :=
    CallableIndexedOwnedFunctionValues.ActualSourceOrigin.of_nested head entry environment
  have capturedGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    have capturedGlobals := capture_globals_for complete globals slots entry related agrees typed
    have frame : entry.catalog.authority.frameLocation = owner.key.frameLocation :=
      (initial.rows owner.position).frame_eq
    simpa only [frame] using capturedGlobals
  have nativeTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formedRecord.represents heaps.runtime_hasTypes)
  exact {
    owner := owner
    scope := scope
    capturedActual := formedRecord.closureActual
    callerPrefix := 1
    captured := formedRecord.captures
    code := formedRecord.closureCode
    history := formedRecord.closureHistory
    support := support.recapture formedRecord.captured
    origin := origin.recapture formedRecord.captured
    globals := capturedGlobals.of_slots formedRecord.slots
    referenceIndex := reference_index head
    sourceView := rfl
    value_eq := rfl
    type_eq := rfl
    typed := nativeTyped }

include slots heaps in
/-- The prefix is fixed by the original producer, before any generic read. -/
theorem caller_prefix :
    (of_formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed
      heaps formedRecord).callerPrefix = 1 := rfl

include slots heaps in
/-- Selection retains the immutable logical owner from actual formation. -/
theorem owner_eq :
    (of_formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed
      heaps formedRecord).owner = owner := rfl

include slots heaps in
/-- The ranked body remains associated with the original full named principal. -/
theorem principal_eq :
    (of_formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed
      heaps formedRecord).support.1 = caller := rfl

include slots heaps in
/-- The actual formation history retains its authentic original Source seed. -/
theorem source_seed :
    (of_formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed
      heaps formedRecord).history.metadata = CallableIndexedNamedGeneration.state caller.named := rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaFormationReceipts
