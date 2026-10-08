import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRuntimeFamilyMembers

/-! A genuine formation attaches its actual prepared index to the unchanged
public model. Finite transports preserve this receipt; opaque heap/value
relations alone cannot recover it after it has been erased. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryFormedMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- One constructor names the exact formed value and its genuine prepared
index. It does not change the public model's prior alternatives. -/
inductive FormedAt (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    LocationMap → StoreTyping → TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | ordinary (i : OrdinaryIndex compiled) (owner : OwnedKey keys) (history : History i.code)
      (origin : SourceOrigin i.support history)
      (prefixContext : i.captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) i.support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 i.scope i.captured.canonical owner.key.frameLocation)
      (referenceIndex : i.code.referenceIndex = i.scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType i.world (value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      FormedAt headers keys registry faults i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
        (value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

/-- Inject only this actual formed branch into the unchanged model. -/
theorem FormedAt.represents (member : FormedAt headers keys registry faults mapping world raw source native type) :
    CallableIndexedOwnedPreparedOrdinaryLambdaValues.Represents headers keys registry faults mapping world raw source native type := by
  cases member with
  | ordinary i owner history origin prefixContext globals referenceIndex typed =>
    exact .prepared_ordinary owner i.captured i.code history i.support origin prefixContext globals referenceIndex typed i.prepared

/-- Selection follows the retained constructor, without an inverse on an
opaque representation or any promise about a prior branch. -/
theorem FormedAt.selection (member : FormedAt headers keys registry faults mapping world raw source native type) :
    CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selection headers keys registry faults mapping world raw source native type := by
  cases member with
  | ordinary i owner history origin prefixContext globals referenceIndex typed =>
    exact .prepared_ordinary owner i.captured i.code history i.support origin prefixContext globals referenceIndex typed i.prepared

/-- Expose the literal index only inside an existential Prop goal. -/
theorem FormedAt.has_index (member : FormedAt headers keys registry faults mapping world raw source native type) :
    ∃ i : OrdinaryIndex compiled, ∃ history : History i.code,
      i.mapping = mapping ∧ i.world = world ∧ raw = FunctionValues.sourceType i.function ∧
      source = .closure i.function ∧ native = value i.code i.captured.embedding history.native i.capturedActual ∧
      type = CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore := by
  cases member with
  | ordinary i owner history origin prefixContext globals referenceIndex typed =>
    exact ⟨i, history, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Map/world growth preserves the same closure, captured Source environment,
native value, history and static body. It performs no recapture. -/
theorem FormedAt.extend {futureMap : LocationMap} {futureWorld : StoreTyping}
    (member : FormedAt headers keys registry faults mapping world raw source native type)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld) :
    FormedAt headers keys registry faults futureMap futureWorld raw source native type := by
  cases member with
  | ordinary i owner history origin prefixContext globals referenceIndex typed =>
    let future : OrdinaryIndex compiled := {
      function := i.function, mapping := futureMap, world := futureWorld, scope := i.scope
      capturedActual := i.capturedActual, captured := i.captured.extend maps worlds
      code := i.code, support := i.support, prepared := i.prepared }
    exact .ordinary future owner history origin prefixContext globals referenceIndex (typed.weaken worlds)

/-- Genuine key embedding preserves the owner/frame observation and every
other capture/history/body field. -/
theorem FormedAt.map_keys {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (member : FormedAt headers keys registry faults mapping world raw source native type) :
    FormedAt headers futureKeys registry faults mapping world raw source native type := by
  cases member with
  | ordinary i owner history origin prefixContext globals referenceIndex typed =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations 1 i.scope i.captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .ordinary i (embedding.map owner) history origin prefixContext actualGlobals referenceIndex typed

section Formation
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (history_at source_origin reference_index)
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {heap : Dynamic.Heap} {store : Store} {actual canonical : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code) (prepared : PreparedAt code support)
  (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

include packet prepared prefixContext observed in
/-- One actual formation call at identity inclusion retains its complete
original tuple and constructs the known prepared member from the same inputs.
Typing comes from the returned relation; its branch is never inverted. -/
theorem formation_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual)) store ∧
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).Represents
      registry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) ∧
    FormedAt headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  obtain ⟨sourceTrace, evaluated, related, determined⟩ :=
    CallableIndexedOwnedPreparedOrdinaryLambdaFormation.formation captured code support prepared owner initial packet
      profile prefixContext observed (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      (fun related => related) stored ordinary coercions
  have typed := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).runtime_hasType
    (registry := registry) related
  let i : OrdinaryIndex compiled := ⟨function, mapping, world, scope, actual, captured, code, support, prepared⟩
  have member : FormedAt headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
    .ordinary i owner (history_at captured code support owner initial packet)
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) typed
  exact ⟨sourceTrace, evaluated, related, determined, member⟩
end Formation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryFormedMembers
