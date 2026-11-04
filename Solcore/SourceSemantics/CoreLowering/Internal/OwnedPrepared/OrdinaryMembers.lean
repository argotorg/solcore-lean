import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectApplication
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectCalls
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation
import Solcore.Frontend.SourceCoreUnifiedCompilation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues
import Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning
import Solcore.SourceSemantics.CoreLowering.BuiltinCallSource
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadFaultPolicies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinCertificates

/-!
# Prepared callables: ordinary members

Runtime family members, formed, stored and read members of ordinary rows, and stored indirect application.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRuntimeFamilyMembers
/-! Actual prepared ordinary indices and finite strict-child extraction.
The family records admitted expression members at their literal support
factory. Its two grades are used independently by the existing invocation
and typed-finish adapters. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRuntimeFamilyMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open RecursiveNamedCatalogInvocationBounds (Below)

/-- This index contains the actual captured environment and the static support
chosen for the same Code. Current caller state remains an invocation input. -/
structure OrdinaryIndex (compiled : SourceCoreUnifiedCompilation.Compiled) where
  function : Dynamic.Closure
  mapping : LocationMap
  world : StoreTyping
  scope : SourceCoreLocalCell.Scope
  capturedActual : Environment
  captured : Captures compiled.indexed mapping world scope function.captured capturedActual
  code : Code compiled.indexed function scope captured.administrative
  support : Support code
  prepared : PreparedAt code support

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- The certificate is the retained factory at the actual body read fuel. -/
def OrdinaryIndex.certificate (i : OrdinaryIndex compiled) (context : SourceSemantics.Context) :
    GenericExpressionMeaning.Certificate :=
  i.support.certificates i.support.body.readFuel i.function.source context

def PreservesAt (i : OrdinaryIndex compiled) (context : SourceSemantics.Context) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
    (bridge (headers := headers) (keys := keys))
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context i.function.evidence i.function.source (i.certificate context) faults size

def ReflectsAt (i : OrdinaryIndex compiled) (context : SourceSemantics.Context) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
    (bridge (headers := headers) (keys := keys))
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context i.function.evidence i.function.source (i.certificate context) faults size

/-- Each conjunct applies to its own actual Source or native run. -/
def Family (i : OrdinaryIndex compiled) (size : Nat) : Prop :=
  ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
    PreservesAt (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i context size ∧
    ReflectsAt (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i context size

/-- A real strict family child remains strict below the outer grade, including
when the head itself uses that outer grade. -/
theorem preserves_below (outer headBudget : Nat) (within : headBudget ≤ outer)
    (ih : ∀ i, Below outer (Family (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions i)) (i : OrdinaryIndex compiled) :
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
      Below headBudget (PreservesAt (headers := headers) (keys := keys)
        (registry := registry) (faults := faults) functions i context) := by
  intro context valid child strict
  exact (ih i child (Nat.lt_of_lt_of_le strict within) context valid).1

/-- Reflection selects the independent native conjunct at the same actual
support and context; it preserves the child's original strict grade. -/
theorem reflects_below (outer headBudget : Nat) (within : headBudget ≤ outer)
    (ih : ∀ i, Below outer (Family (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions i)) (i : OrdinaryIndex compiled) :
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
      Below headBudget (ReflectsAt (headers := headers) (keys := keys)
        (registry := registry) (faults := faults) functions i context) := by
  intro context valid child strict
  exact (ih i child (Nat.lt_of_lt_of_le strict within) context valid).2

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRuntimeFamilyMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryFormedMembers
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
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (history_at source_origin reference_index prepared_recapture)
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
original tuple and constructs the known prepared member of the formed closure
over the copies from the same inputs, at the recaptured index.
Typing comes from the returned relation; its branch is never inverted. -/
theorem formation_member
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).Represents
        registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function) (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      FormedAt headers keys registry faults formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  obtain ⟨formed, sourceTrace, evaluated, related, determined⟩ :=
    CallableIndexedOwnedPreparedOrdinaryLambdaFormation.formation captured code support prepared owner initial packet
      profile prefixContext observed (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      (fun related => related) heaps ordinary coercions
  have typed := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).runtime_hasType
    (registry := registry) related
  let i : OrdinaryIndex compiled := ⟨formed.closure, formed.finalMap, formed.finalWorld, scope, formed.closureActual,
    formed.captures, formed.closureCode, support.recapture formed.captured, prepared_recapture prepared formed.captured⟩
  have member : FormedAt headers keys registry faults formed.finalMap formed.finalWorld
      (FunctionValues.sourceType function) (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
    .ordinary i owner formed.closureHistory ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
  exact ⟨formed, sourceTrace, evaluated, related, determined, member⟩
end Formation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryFormedMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectParentPrefix
/-! The exact prepared model is observed at the one actual successful callee
post. Its prior branch remains a genuine General selection alternative. A
closure identity and attached Dispatch/Selected inputs are consumed only at
that post; no classifier existence or prepared origin for prior values is
asserted. The original ordered child proofs run once in the common core. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectParentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)

/-- Exact selection and the original conditional resolver share this same
actual post. The selected value may retain the unresolved prior branch. -/
def ValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee sourceValue after ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge functions compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore ∧
    ∀ (function : Dynamic.Closure), sourceValue = .closure function →
      CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
        (function := function) (native := carrier) (type := compiler.calleeCode.type) ∧
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
          (.closure function) carrier)
        (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
          compiler.original dispatch.row),
        CallableIndexedOwnedStoredIndirectParentPrefix.ForModel.ClosureResolutionWithEffects
          (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (calleeMap := finalMap) (calleeWorld := finalWorld) (calleeHeap := after)
          (calleeStore := calleeStore) (calleeSize := sourceSize) (sourceTypes := sourceTypes)
          bridge functions compiler prepared initial dispatch budget value finalStore

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource tree unique parent in
/-- Strict children of the same family construct the actual callee post.
Exact model inversion observes that post before any conditional closure resolver. -/
theorem reflects_parent (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.FaultPrefix
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge functions compiler initial budget value finalStore ∨
      ValuePrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        (sourceTypes := sourceTypes) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) := by
  obtain ⟨sameCaller, sameSource, produced⟩ :=
    CallableIndexedOwnedStoredIndirectParentPrefix.ForModel.reflects_parent_with_effects
      bridge functions compiler prepared certified found sourceTyped parentTyped wellFormed runtime covers
      environments heaps locals agrees typed initial admitted caller sidecarSource tree unique parent
      budget children completed within
  refine ⟨sameCaller, sameSource, ?_⟩
  rcases produced with failed | succeeded
  · exact Or.inl failed
  · right
    obtain ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, resolver⟩ := succeeded
    refine ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, ?_⟩
    intro function sameClosure
    have exactValue : ValueRep compiled.compatible.checked registry functions finalMap finalWorld
        calleeNode.type (.closure function) carrier compiler.calleeCode.type := sameClosure ▸ post.2.1
    exact ⟨CallableIndexedOwnedPreparedOrdinaryLambdaValues.selected_of_value profile exactValue,
      resolver function sameClosure⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectParentPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectApplication
/-! The actual prepared ordinary branch consumes the original successful
argument receipt and its intermediate effects. Native callable injectivity,
independent Source traces and actual physical arity construct its arguments.
Only strict children of the same expression family invoke the prepared body;
the original restoration returns the actual current caller pool. Prior
selections and principal population remain separate alternatives. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)


variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
    compiler.original dispatch.row)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {lambdaScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captured : CallableIndexedLambdaValues.Captures compiled.indexed calleeMap calleeWorld lambdaScope function.captured capturedActual)
  (code : CallableIndexedLambdaValues.Code compiled.indexed function lambdaScope captured.administrative)
  (history : CallableIndexedLambdaValues.History code)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (seed : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 lambdaScope captured.canonical owner.key.frameLocation)
  (referenceIndex : code.referenceIndex = lambdaScope.length + 1 + compiled.indexed.base.globals.length)
  (sameNative : calleeNative = CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
  (selectedType : RuntimeValueHasType calleeWorld calleeNative
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
  {table : SourceCoreFaultSites.Table}
  (rebuilt : support.issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep support.issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep support.issued.assignments reason token → faults reason token)
  (interprets : ∀ context, CallableIndexedOwnedTypedLambdaBodyContinuations.Validity
      (program := Program.ofChecked compiled.sourceProgram) captured code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := support.certificates support.body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory
        support.diagnosticPolicy function.source support.issued.invalidOperand)
      (faults := faults) (registry := registry) support.issued
      (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys)) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) table)

/-- Semantic callable outcomes retain their genuine staged counterpart.
Stage rejection is a separate earlier outcome. -/
def boundaryOutcome : Dynamic.ExpressionOutcome → Staging.CallBoundary.Outcome
  | .value value => .value value
  | .fault reason => .semanticFault reason

/-- The original successful prefix, actual intermediate effects and passed
fourth gate remain attached beside the complete Source and staged outcome. -/
def ResultAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (boundaryOutcome outcome) after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial outcome after value finalStore finalMap finalWorld

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  calleeTrace post accepted observed referenceIndex sameNative selectedType seed extension faithful observations
  rebuilt operandIncluded unaryIncluded interprets in
/-- The selected prepared packet constructs its own body continuation from
strict expression children, preserving the whole fourth-bind witness. -/
theorem reflects_selected (budget : Nat)
    (reflection : ∀ context, CallableIndexedOwnedTypedLambdaBodyContinuations.Validity
        (program := Program.ofChecked compiled.sourceProgram) captured code context →
      RecursiveNamedCatalogInvocationBounds.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context function.evidence function.source
          (support.certificates support.body.readFuel function.source context) faults size))
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    ResultAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld) (sidecar := sidecar)
      bridge profile compiler prepared initial dispatch budget value finalStore := by
  refine ⟨original, step, passed, ?_⟩
  obtain ⟨_nativeSize, argumentSize, sources, values, middle, argumentStore, argumentMap, argumentWorld,
    _argumentsNative, _argumentsStrict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, _stepFrame, _stepMetadata,
    maps, worlds, frame, metadataExtended, ⟨argumentState, related, argumentAdmission⟩,
    ⟨remainingSize, remaining, remainingStrict⟩⟩ := step
  have calleeRep := post.2.1
  have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code
  have sourceBinders : code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binding => binding.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binding : TypedBinder => binding.scheme.body)) parameters).symm
  have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormed runtime covers locals admitted.heap calleeTrace sourceBinders
  have actualType := calleeRep.runtime_hasType.type_eq
  have callableType := compiler.callableType
  rw [actualFunctionType] at callableType
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (callableType.trans (actualType.symm.trans selectedType.type_eq))
  have nativeBundle := (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
    (compiler.packedType.symm.trans nativeTypes.1)
  have nativeResult := nativeTypes.2
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals admitted.heap calleeTrace)
  have nativeCount : (compiler.codes.map (·.type)).length = function.parameters.length := by
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans passed.1.symm
  have arity : sources.length = function.parameters.length := represented.length.1.symm.trans nativeCount
  let futureCaptured := captured.extend stepMaps stepWorlds
  have representedArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
    futureCaptured code support seed (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) profile represented arity.symm
    (by simpa only [sourceBinders] using sourceBundle) nativeBundle
  obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application,
    calleeTyped, calleeHeapTyped, _calleeExtension, calleeLocals, rawTyped, _argumentHeapTyped,
    heapExtension, _argumentLocals, _fullExtension, rawArity, packed, packing, _packedTyped, raw⟩ :=
    CallableIndexedOwnedStoredCallSourcePrefix.from_admission_with_arity bridge initial wellFormed runtime covers locals admitted
      unique compiler.found compiler.originalForm parentTyped compiler.argumentCoercions arity calleeTrace argumentsTrace
  have rawArguments : Dynamic.ValuesHaveTypes function.context middle sources support.body.types := by
    simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
  have count : rawTypes.length = metadata.argumentCount := by
    cases application with | intro count _ _ _ => exact count.symm
  have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers calleeLocals calleeHeapTyped
    argumentsTyping count argumentsTrace
  have read : Evaluates (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
      (.second (.var 2)) (.word dispatch.contract) argumentStore :=
    .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have gate := prepared.site.dispatch_known .beforeApplication native.diagnostics.unknown
    dispatch.contract dispatch.row dispatch.found read
  rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication passed.2.1] at gate
  cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
  | failed failed _strict =>
    have same := (evaluation_deterministic failed.sound gate).1
    cases same
  | continued acceptedGate applicationTrace _gateStrict applicationStrict =>
    obtain ⟨same, stores⟩ := evaluation_deterministic acceptedGate.sound gate
    cases same
    subst stores
    have payloadTrace := CallableIndexedOwnedStoredApplicationProjection.to_payload applicationTrace
    rw [sameNative] at payloadTrace
    obtain ⟨currentMetadata, currentCarried⟩ := argumentAdmission.rows owner.position
    have reference : futureCaptured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have call := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.application_reflects
        futureCaptured code support history (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) extension faithful observations wellFormed
        rebuilt operandIncluded unaryIncluded interprets representedArguments owner (bridge.pool argumentState)
        argumentHeaps raw.captures reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        raw.heaps rawArguments argumentAdmission.rows budget
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
        reflection (callContext := context) (callerEvidence := evidence) payloadTrace (Nat.le_of_lt applicationStrict)
    obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps,
      lastMaps, lastWorlds, lastFrame, lastMetadata, transition⟩ := call
    obtain ⟨baseReached, baseRelated⟩ := transition
    obtain ⟨returned, samePool, lastRelated⟩ := bridge.restore argumentState baseReached
      lastMaps lastWorlds lastFrame lastMetadata baseRelated
    obtain ⟨sourceSize, sourceParent⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm
      parent.requirements parent.coercions compiler.argumentCoercions parent.arity wellFormed runtime covers
      calleeLocals calleeHeapTyped argumentsTyping count calleeTrace
      (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.called argumentsTrace called)
    have coercions : Dynamic.CoercionPathExecutes (Program.ofChecked compiled.sourceProgram) context evidence
        middle metadata.argumentCoercions packed packed middle := by
      rw [compiler.argumentCoercions]
      exact .nil
    have staged : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (boundaryOutcome outcome) after := by
      cases called with
      | value applied =>
        exact .applied calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
          packing coercions packing parent.arity argumentsCount applied.sound
      | fault failed =>
        exact .applicationFault calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
          packing coercions packing parent.arity argumentsCount failed.sound
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    have parentRep : GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) finalMap finalWorld
        compiler.original.type lowered.type faults outcome value := by
      rw [loweredType, nativeResult]
      cases resultRep with
      | value relatedPayload => exact .value (.compatible rawResult relatedPayload)
      | fault matched => exact .fault matched
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceParent, staged, parentRep, finalHeaps,
      maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadataExtended.trans lastMetadata,
      returned, callerProtocol.trans related lastRelated,
      after_expression_sized initial returned admitted wellFormed runtime covers locals parentTyped sourceParent
        (frame.trans lastFrame)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectApplication
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectPreservation
/-! Forward prepared calls use the actual callee post and independently typed
argument vector. The shared ordered suffix core invokes a prepared body leaf
built internally from strict children, then restores the current caller once.
Prior selection and physical arity rejection remain separate alternatives. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedStoredClosureArgumentReceipts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)


variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
    compiler.original dispatch.row)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {lambdaScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captured : CallableIndexedLambdaValues.Captures compiled.indexed calleeMap calleeWorld lambdaScope function.captured capturedActual)
  (code : CallableIndexedLambdaValues.Code compiled.indexed function lambdaScope captured.administrative)
  (history : CallableIndexedLambdaValues.History code)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (seed : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 lambdaScope captured.canonical owner.key.frameLocation)
  (referenceIndex : code.referenceIndex = lambdaScope.length + 1 + compiled.indexed.base.globals.length)
  (sameNative : calleeNative = CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
  (selectedType : RuntimeValueHasType calleeWorld calleeNative
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
  {table : SourceCoreFaultSites.Table}
  (rebuilt : support.issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep support.issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep support.issued.assignments reason token → faults reason token)
  (interprets : ∀ context, CallableIndexedOwnedTypedLambdaBodyContinuations.Validity
      (program := Program.ofChecked compiled.sourceProgram) captured code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := support.certificates support.body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory
        support.diagnosticPolicy function.source support.issued.invalidOperand)
      (faults := faults) (registry := registry) support.issued
      (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys)) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) table)

include certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The strict callee child constructs its actual value and reached state. -/
theorem preserves_callee_value (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context evidence source certificate faults size)
    {size : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee sourceValue after)
    (smaller : size < budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial sourceValue after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted (.value trace)
  cases represented with
  | value represented =>
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩

/-- Physical count is required only for the actual accepted application branch. -/
def PhysicalArity {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after) : Prop :=
  CallableIndexedOwnedStoredIndirectCallBounds.ForModel.CalledSuffix
    (context := context) (evidence := evidence) (environment := environment) suffix →
    function.parameters.length = ids.length

/-- The argument fault constructor needs no physical closure count. -/
theorem PhysicalArity.argumentFault {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (failed : SourceExecutionSize.ExpressionsFault (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment calleeHeap ids reason after) :
    PhysicalArity (context := context) (evidence := evidence) (source := source) (environment := environment)
      (function := function) (.argumentFault failed) := by
  rintro ⟨arguments, middle, argumentTrace, called, same⟩
  have positive := called.positive
  omega

/-- Accepted physical count is an independent actual compiler/closure receipt. -/
theorem PhysicalArity.called {argumentsSize callSize : Nat} {arguments : List Dynamic.Value}
    {middle after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments middle)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
      context evidence function.evidence middle (.closure function) arguments outcome after)
    (count : function.parameters.length = ids.length) :
    PhysicalArity (context := context) (evidence := evidence) (source := source) (environment := environment)
      (.called argumentsTrace called) := fun _ => count

include parentTyped wellFormed runtime covers locals admitted unique parent calleeTrace accepted post in
/-- Genuine Source suffix witnesses construct their exact staged counterpart. -/
theorem staged_of_suffix {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after) :
    Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata
      (CallableIndexedOwnedPreparedStoredIndirectApplication.boundaryOutcome outcome) after := by
  cases suffix with
  | argumentFault failed =>
    exact .argumentsFault calleeTrace.sound (by simpa only [prepared.call] using accepted) failed.sound
  | called argumentsTrace called =>
    rename_i arguments middle
    obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
      original_facts unique compiler.found compiler.originalForm parentTyped
    obtain ⟨_calleeTyped, calleeHeapTyped, _calleeExtension⟩ :=
      wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
        (.closure function) (.function parameter sourceResult) runtime covers locals admitted.heap calleeTyping calleeTrace.sound
    obtain ⟨packed, packing, _rawTyped, _heapTyped, _extension, _packedTyped⟩ :=
      after_trace wellFormed runtime covers (locals.mono post.2.2.2.2.2.2.1) calleeHeapTyped argumentsTyping argumentsTrace
    have count : rawTypes.length = metadata.argumentCount := by
      cases application with | intro count _ _ _ => exact count.symm
    have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers
      (locals.mono post.2.2.2.2.2.2.1) calleeHeapTyped argumentsTyping count argumentsTrace
    have coercions : Dynamic.CoercionPathExecutes (Program.ofChecked compiled.sourceProgram) context evidence
        middle metadata.argumentCoercions packed packed middle := by
      rw [compiler.argumentCoercions]; exact .nil
    cases called with
    | value applied =>
      exact .applied calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
        packing coercions packing parent.arity argumentsCount applied.sound
    | fault failed =>
      exact .applicationFault calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
        packing coercions packing parent.arity argumentsCount failed.sound

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  environments agrees typed calleeTrace post accepted observed referenceIndex sameNative selectedType seed
  dispatch selected extension faithful observations rebuilt operandIncluded unaryIncluded interprets in
/-- The true Source suffix constructs its native execution. Prepared body
meaning uses only strict children at the genuine parameter entry. -/
theorem preserves_selected (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (physicalCount : PhysicalArity (context := context) (evidence := evidence) (source := source)
      (environment := environment) suffix)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget)
    (meaning : CallableIndexedOwnedStoredIndirectCallBounds.ForModel.CalledSuffix
        (context := context) (evidence := evidence) (environment := environment) suffix → ∀ context, CallableIndexedOwnedTypedLambdaBodyContinuations.Validity
        (program := Program.ofChecked compiled.sourceProgram) captured code context →
      RecursiveNamedCatalogInvocationBounds.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context function.evidence function.source
          (support.certificates support.body.readFuel function.source context) faults size)) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata
        (CallableIndexedOwnedPreparedStoredIndirectApplication.boundaryOutcome outcome) after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial outcome after value finalStore finalMap finalWorld := by
  have calleePost := post
  obtain ⟨calleeEvaluation, calleeRep, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame, calleeMetadata,
    calleeState, calleeRelated, _calleePost⟩ := post
  have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code
  have sourceBinders : code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binding => binding.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binding : TypedBinder => binding.scheme.body)) parameters).symm
  have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormed runtime covers locals admitted.heap calleeTrace sourceBinders
  have actualType := calleeRep.runtime_hasType.type_eq
  have callableType := compiler.callableType
  rw [actualFunctionType] at callableType
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (callableType.trans (actualType.symm.trans selectedType.type_eq))
  have nativeBundle := (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
    (compiler.packedType.symm.trans nativeTypes.1)
  have nativeResult := nativeTypes.2
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals admitted.heap calleeTrace)
  have application : CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ApplicationPreserves
      (registry := registry) (faults := faults) bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared
      (context := context) (evidence := evidence) (environment := environment) (canonical := canonical)
      (mapping := calleeMap) (world := calleeWorld) (calleeHeap := calleeHeap) (store := calleeStore)
      (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (resultCore := code.receipt.resultCore) (dispatch := dispatch) budget suffix := by
    intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
      argumentState argumentAdmission stepMaps stepWorlds stepFrame stepMetadata calleeTyped heapExtension
      represented argumentHeaps rawTyped packing bundle argumentsSize callSize outcome after
      argumentsTrace called sameSuffix callWithin
    have physical := physicalCount sameSuffix
    have nativeCount : (compiler.codes.map (·.type)).length = function.parameters.length := by
      simpa only [List.length_map] using compiler.ordered_children.1.symm.trans physical.symm
    have arity : arguments.length = function.parameters.length := represented.length.1.symm.trans nativeCount
    let futureCaptured := captured.extend stepMaps stepWorlds
    have representedArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
      futureCaptured code support seed (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) profile represented arity.symm
      (by simpa only [sourceBinders] using sourceBundle) nativeBundle
    obtain ⟨raw, stable⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
      bridge argumentState runtime argumentAdmission calleeTyped heapExtension rawTyped packing bundle arity
    have rawArguments : Dynamic.ValuesHaveTypes function.context middle arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨currentMetadata, currentCarried⟩ := argumentAdmission.rows owner.position
    have reference : futureCaptured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps,
      lastMaps, lastWorlds, lastFrame, lastMetadata, transition⟩ :=
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.application_preserves
        futureCaptured code support history (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) extension faithful observations wellFormed
        rebuilt operandIncluded unaryIncluded interprets representedArguments owner (bridge.pool argumentState)
        argumentHeaps raw.captures reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        raw.heaps rawArguments stable budget (meaning sameSuffix) (callContext := context) (callerEvidence := evidence) called callWithin
    have evaluatedNative : Evaluates [calleeNative, DataPatternValues.packValues payloads]
        middleStore CallableIndexedLambdaCalls.applyPayload result finalStore := by
      simpa only [sameNative, futureCaptured, CallableIndexedLambdaValues.Captures.extend] using evaluated
    obtain ⟨baseReached, baseRelated⟩ := transition
    obtain ⟨returned, _samePool, lastRelated⟩ := bridge.restore argumentState baseReached
      lastMaps lastWorlds lastFrame lastMetadata baseRelated
    exact ⟨result, finalStore, finalMap, finalWorld,
      CallableIndexedOwnedStoredIndirectCallBounds.application_gate dispatch selected physical native.diagnostics.unknown,
      evaluatedNative, resultRep, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, lastRelated⟩
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceParent, evaluated, result⟩ :=
    CallableIndexedOwnedStoredIndirectCallBounds.ForModel.preserves_selected_with_application
    bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared parent tree unique parentTyped wellFormed runtime covers
    environments locals agrees typed initial admitted calleeState calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
    selectedType calleeHeaps rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation
    selected budget children suffix argumentsWithin callWithin application
  exact ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceParent, evaluated,
    staged_of_suffix bridge profile compiler prepared parentTyped wellFormed runtime covers locals initial admitted unique parent
      calleeTrace calleePost accepted suffix, result⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryStoredMembers
/-! A known formed member stays beside its literal initialized Source cell and
native optional payload. Heap representation alone does not recover this
qualification, and mutation transport requires the actual future reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryStoredMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedOrdinaryFormedMembers
open CallableIndexedOwnedFunctionValues (Header Key)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

/-- The actual initialized payload and its known formed constructor. The
location and native target are exposed only within proof goals. -/
def StoredAt (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (location : Dynamic.Location) (raw : TypeSystem.Ty) (source : Dynamic.Value)
    (native : Value) (type : Ty) : Prop :=
  FormedAt headers keys registry faults mapping world raw source native type ∧
  ∃ target, ReferenceRepresents mapping world location target type ∧
    Dynamic.Heap.Reads heap location ⟨raw, some source, none⟩ ∧
    store.read? target = some (.inRight .unit native)

/-- Inject the retained function constructor into the unchanged payload model. -/
theorem payload_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (member : FormedAt headers keys registry faults mapping world raw source native type) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world raw source native type := by
  cases member with
  | ordinary i owner history origin prefixContext globals referenceIndex typed =>
    exact .function (.prepared_ordinary owner i.captured i.code history i.support origin
      prefixContext globals referenceIndex typed i.prepared)

/-- Actual future reads are necessary when the heap or store may have changed. -/
theorem StoredAt.extend_with_reads {heap futureHeap : Dynamic.Heap} {store futureStore : Store}
    {location : Dynamic.Location} {futureMap : LocationMap} {futureWorld : StoreTyping}
    (stored : StoredAt headers keys registry faults mapping world heap store location raw source native type)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (reads : Dynamic.Heap.Reads futureHeap location ⟨raw, some source, none⟩)
    (nativeReads : ∀ target, ReferenceRepresents mapping world location target type →
      futureStore.read? target = some (.inRight .unit native)) :
    StoredAt headers keys registry faults futureMap futureWorld futureHeap futureStore location raw source native type := by
  obtain ⟨member, target, reference, _, _⟩ := stored
  exact ⟨member.extend maps worlds, target, reference.extend maps worlds, reads, nativeReads target reference⟩

/-- Key transport preserves the same owner/frame observation and stored value. -/
theorem StoredAt.map_keys {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw source native type) :
    StoredAt headers futureKeys registry faults mapping world heap store location raw source native type := by
  exact ⟨stored.1.map_keys embedding, stored.2⟩

/-- One real initialized write retains the same formed payload. Its nominal
Source declaration type is supplied independently of native projection. -/
theorem written_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {heap after : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {target : Location} {cell : Dynamic.Cell}
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell) (cellType : cell.type = raw)
    (member : FormedAt headers keys registry faults mapping world raw source native type)
    (written : Dynamic.Heap.Writes heap location (some source) after) :
    ∃ updated, store.write? target (.inRight .unit native) = some updated ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
        mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated ∧
      Dynamic.HeapMetadataExtend heap after ∧
      StoredAt headers keys registry faults mapping world after updated location raw source native type := by
  have represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world cell.type source native type := cellType.symm ▸ payload_member profile member
  obtain ⟨updated, coreWritten, finalHeaps, administrative⟩ :=
    GenericHeap.HeapRepresents.write_initialized heaps reference read represented written
  obtain ⟨old, oldValue, oldPayload, oldRead, _, _, oldRelated⟩ := heaps.cells reference.mapped
  have same := oldRead.functional read
  subst old
  have ordinary := oldRelated.ordinary
  obtain ⟨previous, previousRead, afterRead⟩ := written.reads_updated
  have same := previousRead.functional read
  subst previous
  have initialized : Dynamic.Heap.Reads after location ⟨raw, some source, none⟩ := by
    simpa only [cellType, ordinary] using afterRead
  exact ⟨updated, coreWritten, finalHeaps, administrative, .of_write written,
    member, target, reference, initialized, Store.write?_reads_written coreWritten⟩

open CallableIndexedHistory CallableIndexedAllocationCompletion

/-- The actual marked allocation runs once and retains its complete snapshot,
marker, capture, heap and frame receipts beside the new initialized member. -/
theorem allocated_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = compiled.indexed.layouts.definitions)
    (frameRegistered : layout.Registered compiled.indexed.layouts.definitions)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location}
    {frame : NativeFrame} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative request.scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout frame))
    (payloadAt : PayloadAt request actual (some native))
    (payloadType : request.payloadType = type)
    (member : FormedAt headers keys registry faults mapping world raw source native type)
    (allocated : Dynamic.Heap.Allocates before raw (some source) sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native]) ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
        (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native]) ∧
      StoredAt headers keys registry faults (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native])
        sourceLocation raw source native type := by
  subst type
  have cell : GenericHeap.CellRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      mapping world ⟨raw, some source, none⟩ (optionalValue request.payloadType (some native)) request.payloadType :=
    .initialized (payload_member profile member)
  obtain ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative⟩ :=
    CallableIndexedOrdinaryAllocation.preserves_with_captures_for_type allocation annotation same definitions
      frameRegistered environments agrees heaps reference read payloadAt cell allocated
  have maps : LocationMap.Extends mapping (mapping ++ [store.length + 2]) := ⟨_, rfl⟩
  have worlds : WorldExtends world
      (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType]) := ⟨_, rfl⟩
  have stored : StoredAt headers keys registry faults (mapping ++ [store.length + 2])
      (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
      after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native])
      sourceLocation raw source native request.payloadType := by
    refine ⟨member.extend maps worlds, store.length + 2, finalReference, allocated.reads_new, ?_⟩
    simp [Store.read?]
  exact ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative, stored⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryStoredMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds
/-! The builtin alternative of the accepted indirect payload invocation uses
the literal contracted builtin carrier and ordered represented scalar inputs.
The actual primitive body runs once at the argument store. It has no F child,
and preserves that whole store and the original Source heap. The enclosing
parent supplies the two genuine dispatch gates and ordered E children. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open BuiltinBodyMeaning CallableIndexedBuiltinValues BuiltinCalls

private theorem payload_evaluates {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (inputs : InputRep function arguments input)
    (identity contract : Word) (captured : Environment) (store : Store) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates [BuiltinCalls.Protocol.contractedValue function identity contract captured, input]
        store CallableIndexedLambdaCalls.applyPayload (.inRight .word nativeResult) store := by
  obtain ⟨sourceResult, nativeResult, applied, represented, body⟩ := inputs.body_meaning captured store
  exact ⟨sourceResult, nativeResult, applied, represented,
    .apply (.second (.first (.var rfl))) (.var rfl) body⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : BuiltinFunctionId}
  {native : Value} {nativeType : Ty}
  (builtin : Represents compiled.indexed world function.type (.builtin ⟨function⟩) native nativeType)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : ValuesRep compiled.compatible.checked registry functions mapping world
    function.parameterTypes arguments payloads (CompatibleBuiltinMeaning.argumentTypes function))
  {program : Program} {context : SourceSemantics.Context}
  {caller invocation : Dynamic.EvidenceEnvironment} {before : Dynamic.Heap} {store : Store}

include observations builtin represented in
/-- Invalid builtin application is excluded by its actual ordered scalar
inputs. The original Source application fixes the result; native execution
uses the same real contracted carrier rather than a reconstructed closure. -/
theorem preserves {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome program size context caller invocation
      before (.builtin ⟨function⟩) arguments outcome after) :
    ∃ value,
      Evaluates [native, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value store ∧
      FunctionCalls.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world function.returnType (SourceCoreInteger.builtinResult function) faults outcome value ∧
      after = before := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  cases called with
  | value applied =>
    cases applied with
    | builtin applied =>
      generalize typeEq : function.type = sourceType at builtin
      cases builtin with
      | builtin selected number descriptor typed =>
        obtain ⟨sourceResult, nativeResult, actual, related, evaluated⟩ :=
          payload_evaluates inputs _ descriptor.id _ store
        have same := actual.functional applied
        subst sourceResult
        exact ⟨_, evaluated, .value (CompatibleBuiltinMeaning.result_represents inputs applied related), rfl⟩
  | fault failed =>
    exact False.elim (InputRep.excludes_callable_fault inputs failed.sound)

include observations builtin represented in
/-- Native completion determines the same primitive result and store. Its
Source application has its own genuine constant grade; reflection uses no
preservation theorem or semantic body callback. -/
theorem reflects {size : Nat} {value : Value} {finalStore : Store}
    (completed : CoreProof.EvaluationSize size [native, DataPatternValues.packValues payloads]
      store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceSize outcome,
      RecursiveNamedCallBounds.CallOutcome program sourceSize context caller invocation
        before (.builtin ⟨function⟩) arguments outcome before ∧
      FunctionCalls.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world function.returnType (SourceCoreInteger.builtinResult function) faults outcome value ∧
      finalStore = store := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  generalize typeEq : function.type = sourceType at builtin
  cases builtin with
  | builtin selected number descriptor typed =>
    obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ :=
      payload_evaluates inputs _ descriptor.id _ store
    obtain ⟨same, sameStore⟩ := evaluation_deterministic completed.sound evaluated
    subst value
    exact ⟨_, .value sourceResult, .value (.builtin applied),
      .value (CompatibleBuiltinMeaning.result_represents inputs applied related), sameStore⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryReadMembers
/-! Initialized local reads retain a known prepared member at the genuine raw
cell type. The reported occurrence type remains its own runtime view. Actual
callee traces are associated by determinism without rerunning their producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryReadMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionReads
open CallableIndexedOwnedPreparedOrdinaryFormedMembers
open CallableIndexedOwnedPreparedOrdinaryStoredMembers
open CallableIndexedOwnedFunctionValues (Header Key)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {sourceValue : Dynamic.Value} {nativeValue : Value} {type : Ty}
  {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : Certificate fuel (.initial compiled.compatible.checked) source scope id reason code)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}

/-- The real binder and initialized cell exclude the reached empty witness. -/
theorem initialized_policy
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    UninitializedPolicy certificate context environment heap faults := by
  intro other cell witness
  have same := witness.lookup.functional lookup
  subst other
  obtain ⟨_, target, reference, read, nativeRead⟩ := stored
  have same := witness.read.functional read
  subst cell
  cases witness.empty

/-- Genuine lexical and stored receipts construct the exact initialized
Source/native read; no heap-relation inverse supplies the qualified member. -/
theorem initialized_traces
    (binding : StaticBinding certificate context)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    type = certificate.type ∧
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence source environment heap
      id sourceValue heap ∧
    Evaluates actual store (code.rename ξ) (.inRight .word nativeValue) store := by
  rcases certificate with ⟨node, readType, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  dsimp only at *
  obtain ⟨member, target, reference, read, nativeRead⟩ := stored
  obtain ⟨other, cell, otherLookup, otherRead, cellType, _⟩ := locals.lookup binding.declared
  have same := otherLookup.functional lookup
  subst other
  have same := otherRead.functional read
  subst cell
  have nominal : raw = declared.scheme.body := cellType
  have notMapping : ¬ ∃ key value, declared.scheme.body = .mapping key value := by
    intro ⟨key, value, mapped⟩
    have mapped : raw = .mapping key value := nominal.trans mapped
    cases member with
    | ordinary i owner history origin prefixContext globals referenceIndex typed => cases mapped
  obtain ⟨selectedTarget, nativeLookup, selectedReference⟩ := environments.lookup_visible lookup slot
  have same : selectedTarget = target := Option.some.inj (selectedReference.mapped.symm.trans reference.mapped)
  subst selectedTarget
  have sameType : type = readType := by
    exact (Ty.sum.inj (Option.some.inj (reference.typed.symm.trans selectedReference.typed))).2
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id sourceValue heap := by
    have formTrace : Dynamic.ExpressionFormEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
        source environment heap node.form [] [] sourceValue heap :=
      form ▸ Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup read rfl rfl
    exact .intro (lookupExpression?_sound metadata.found)
      (by rw [metadata.requirements, metadata.coercions]; exact formTrace)
      (by rw [metadata.coercions]; exact .nil)
  refine ⟨sameType, sourceTrace, ?_⟩
  cases emitted with
  | ordinary _ =>
    change Evaluates actual store (OptionalCell.read readType (.var (ξ index)) reason)
      (.inRight .word nativeValue) store
    exact OptionalCell.read_success reason (.var (agrees nativeLookup)) nativeRead
  | mapping declared _ => exact False.elim (notMapping ⟨_, _, declared⟩)

/-- One original read producer retains its broad result, heap/frame/metadata
and the same initialized qualifier. Its empty-cell policy is derived above. -/
theorem read_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id (.value sourceValue) heap ∧
    Evaluates actual store (code.rename ξ) (.inRight .word nativeValue) store ∧
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      mapping world certificate.node.type certificate.type faults (.value sourceValue) (.inRight .word nativeValue) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world heap store ∧
    AdministrativePreserved mapping store mapping store ∧ Dynamic.HeapMetadataExtend heap heap ∧
    StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type := by
  obtain ⟨_, sourceTrace, nativeTrace⟩ := initialized_traces certificate binding environments locals agrees stored lookup
  obtain ⟨outcome, after, result, finalStore, actualSource, actualNative, related, finalHeaps, frame, metadata⟩ :=
    certificate.evaluates_with_diagnostics
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      extension (Program.ofChecked compiled.sourceProgram) context evidence binding environments heaps locals agrees
      (initialized_policy certificate stored lookup)
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic actualNative nativeTrace
  subst result
  subst finalStore
  obtain ⟨sameOutcome, sameHeap⟩ := source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup stored.2.choose_spec.2.1 rfl actualSource (.value sourceTrace)
  subst outcome
  subst after
  exact ⟨actualSource, actualNative, related, finalHeaps, frame, metadata, stored⟩

section Parent
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {childFuel : Nat}
  {compilation : SourceCoreFunctions.Context} {parentId : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body childFuel compilation source scope parentId id ids metadata reasonAt lowered)
  {calleeNode : ExpressionNode}
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)

/-- Associate the same already-produced callee tuple with the initialized read.
This constructs no second first-child producer and keeps the original post. -/
theorem at_value_post
    (sameCode : compiler.calleeCode.expression = code)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    {sourceSize : Nat} {calleeValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {calleeMap : LocationMap} {calleeWorld : StoreTyping}
    (sourceTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment heap id calleeValue after)
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld) :
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld ∧
    calleeValue = sourceValue ∧ after = heap ∧ carrier = nativeValue ∧ calleeStore = store ∧
    FormedAt headers keys registry faults calleeMap calleeWorld raw calleeValue carrier type := by
  obtain ⟨_, expectedSource, expectedNative⟩ :=
    initialized_traces certificate binding environments locals agrees stored lookup
  have actualNative := post.1
  rw [sameCode] at actualNative
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic actualNative expectedNative
  have sameNative : carrier = nativeValue := (Value.inRight.inj sameResult).2
  obtain ⟨sameOutcome, sameHeap⟩ := source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup stored.2.choose_spec.2.1 rfl (.value sourceTrace.sound) (.value expectedSource)
  have sameSource : calleeValue = sourceValue := Dynamic.ExpressionOutcome.value.inj sameOutcome
  have member : FormedAt headers keys registry faults calleeMap calleeWorld raw calleeValue carrier type := by
    rw [sameSource, sameNative]
    exact stored.1.extend post.2.2.2.1 post.2.2.2.2.1
  exact ⟨post, sameSource, sameHeap, sameNative, sameStore, member⟩

variable {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : Prepared compiler native)
  {sidecar : SourceCoreStageContracts.Sidecar} {sourceTypes : List TypeSystem.Ty}

/-- This is the original full callee tuple, with a known member beside that
same tuple. Its strict native/Source witnesses, gate and conditional resolver
are retained literally, including the unresolved prior alternatives. -/
def QualifiedValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize calleeValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment heap id calleeValue after ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore ∧
    (∀ (function : Dynamic.Closure), calleeValue = .closure function →
      CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
        (function := function) (native := carrier) (type := compiler.calleeCode.type) ∧
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
          (.closure function) carrier)
        (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site id ids metadata
          compiler.original dispatch.row),
        CallableIndexedOwnedStoredIndirectParentPrefix.ForModel.ClosureResolutionWithEffects
          (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (calleeMap := finalMap) (calleeWorld := finalWorld) (calleeHeap := after)
          (calleeStore := calleeStore) (calleeSize := sourceSize) (sourceTypes := sourceTypes)
          bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
          compiler prepared initial dispatch budget value finalStore) ∧
    FormedAt headers keys registry faults finalMap finalWorld raw calleeValue carrier type

/-- Retain the genuine parent prefix and attach its known initialized member
at the very same native/Source post; the callee producer is not rerun. -/
theorem at_value_prefix
    (sameCode : compiler.calleeCode.expression = code)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    {budget : Nat} {value : Value} {finalStore : Store}
    (produced : CallableIndexedOwnedPreparedStoredIndirectParentPrefix.ValuePrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      (sourceTypes := sourceTypes) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedPreparedStoredIndirectParentPrefix.ValuePrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      (sourceTypes := sourceTypes) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore ∧
    QualifiedValuePrefix (registry := registry) (faults := faults) (raw := raw) (type := type) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      (sourceTypes := sourceTypes) (sidecar := sidecar)
      bridge profile compiler initial prepared budget value finalStore := by
  obtain ⟨nativeSize, sourceSize, calleeValue, after, carrier, calleeStore, finalMap, finalWorld,
    completed, smaller, sourceTrace, post, gate, resolver⟩ := produced
  obtain ⟨samePost, _, _, _, _, member⟩ := at_value_post certificate bridge profile compiler initial
    sameCode binding unique environments locals agrees stored lookup sourceTrace post
  exact ⟨⟨nativeSize, sourceSize, calleeValue, after, carrier, calleeStore, finalMap, finalWorld,
      completed, smaller, sourceTrace, post, gate, resolver⟩,
    nativeSize, sourceSize, calleeValue, after, carrier, calleeStore, finalMap, finalWorld,
      completed, smaller, sourceTrace, samePost, gate, resolver, member⟩
end Parent

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryReadMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueSourceSuffix
/-! The ordinary accepted indirect suffix is indexed by its actual Source
callee value and invocation dictionary. Closure, global and builtin branches
use this one parent constructor. The retained CallableValue witness is supplied
by the positive callee relation. Stage rejection belongs to the separate
staged boundary, and no guard acceptance follows from declarative typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueSourceSuffix
open Core Frontend SourceInference
open CallableIndexedOwnedIndirectSourceAdapters

/-- The same ordered Source argument and application derivations retain their
independent sizes. No body outcome is stored in the compiler certificate. -/
inductive Suffix (program : Program) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (ids : List ExpressionId) (function : Dynamic.Value) :
    Nat → Nat → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentFault {size reason after}
      (failed : SourceExecutionSize.ExpressionsFault program size context caller source
        environment before ids reason after) :
      Suffix program context caller invocation source environment before ids function
        size 0 (.fault reason) after
  | called {argumentsSize callSize arguments middle outcome after}
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context caller
        source environment before ids arguments middle)
      (called : RecursiveNamedCallBounds.CallOutcome program callSize context caller invocation
        middle function arguments outcome after) :
      Suffix program context caller invocation source environment before ids function
        argumentsSize callSize outcome after

variable {program : Program} {context : SourceSemantics.Context}
  {caller invocation : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before calleeHeap after : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId} {function : Dynamic.Value}
  {node : ExpressionNode} {metadata : IndirectCallResolution}

/-- The real accepted parent rule wraps exactly these measured children. Its
Source arity comes from actual argument preservation, with no body premise. -/
theorem Suffix.to_expression
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (argumentCoercions : metadata.argumentCoercions = [])
    (sourceArity : ids.length = metadata.argumentCount)
    (callable : Dynamic.CallableValue function)
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : caller.Covers context)
    (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context calleeHeap)
    {types : List TypeSystem.Ty} (typed : ExpressionsHaveTypes source context ids types)
    (count : types.length = metadata.argumentCount)
    {calleeSize argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context caller source
      environment before callee function calleeHeap)
    (suffix : Suffix program context caller invocation source environment calleeHeap ids function
      argumentsSize callSize outcome after) :
    ∃ size, RecursiveNamedCallBounds.ExpressionOutcome program size context caller source
      environment before call outcome after := by
  cases suffix with
  | argumentFault failed =>
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize]],
      .fault (.form (lookupExpression?_sound found) ?_)⟩
    rw [form]
    exact .indirectArguments calleeTrace callable failed
  | called argumentsTrace called =>
    rename_i arguments middle
    have appliedArity := arguments_count_of_source_admission wellFormed runtime covers locals
      heapTyped typed count argumentsTrace
    obtain ⟨packed, pack⟩ := Dynamic.ValuesPack.exists_pack arguments
    cases called with
    | @value result _ applied =>
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize
        [calleeSize, argumentsSize, SourceExecutionSize.stepSize [], callSize],
        SourceExecutionSize.stepSize []],
        .value (.intro (raw := result) (middle := after) (lookupExpression?_sound found) ?_ ?_)⟩
      · rw [form]
        refine .indirectCall ?_ calleeTrace argumentsTrace pack ?_ pack sourceArity appliedArity applied
        · simp [requirements, argumentCoercions, coercions, coercionRequirementIds]
        · rw [argumentCoercions]; exact .nil
      · rw [coercions]; exact .nil
    | fault failed =>
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize
        [calleeSize, argumentsSize, SourceExecutionSize.stepSize [], callSize]],
        .fault (.form (lookupExpression?_sound found) ?_)⟩
      rw [form]
      refine .indirectApply calleeTrace argumentsTrace pack ?_ pack sourceArity appliedArity failed
      rw [argumentCoercions]; exact .nil

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueSourceSuffix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueParentBounds
/-! One accepted indirect parent at the literal callee value. The actual
positive callee relation selects closure/global/builtin payload application;
the same ordered E argument fold and original four-bind inversion retain all
reached states and independent grades. Application ports are instantiated by
that concrete dispatcher, not stored in static qualification.

The gate inputs are the exact two native acceptance conclusions of the
authentic user/builtin boundary decision, with the same contracted carrier.
Stage/arity rejection have separate boundary outcomes. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredClosureArgumentReceipts CallableIndexedOwnedStoredIndirectCallBounds
open CallableIndexedOwnedPreparedIndirectValueSourceSuffix
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section Selected
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (firstAdmission : Admission bridge context first)
  (calleeState : callerProtocol.State ⟨scope, mapping, world, calleeHeap, store, canonical⟩)
  (calleeRelated : callerProtocol.Relates first calleeState)
  (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
  (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
  (calleeMetadata : Dynamic.HeapMetadataExtend before calleeHeap)
  {function : Dynamic.Value} {invocation : Dynamic.EvidenceEnvironment} {sourceResultType : TypeSystem.Ty} {calleeNative : Value}
  (callable : Dynamic.CallableValue function)
  {parameterCore resultCore : Ty}
  (nativeTyped : RuntimeValueHasType world calleeNative (CallableContract.functionType parameterCore resultCore) compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world calleeHeap store)
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType sourceResultType)
  (nativeResult : compiler.resultType = resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}
  {calleePayload : Value} {contract : Word}
  (shape : calleeNative = .pair calleePayload (.word contract))
  (firstGate : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown contract = none)
  (secondGate : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown contract = none)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee function calleeHeap)
  (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- The whole parent keeps the actual returned caller witness and success-only
Source admission. Its native and Source result types remain independent receipts. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type outcome reached

include rawResult nativeResult in
theorem parent_result {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (related : FunctionCalls.ResultRepresents model finalMap finalWorld sourceResultType resultCore faults outcome value) :
    GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value := by
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [loweredType, nativeResult]
  cases related with
  | value payload => exact .value (.compatible rawResult payload)
  | fault matched => exact .fault matched

/-- A genuine called constructor at the same Source suffix and its exact grade. -/
def CalledSuffix {suffixArgumentsSize suffixCallSize : Nat}
    {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment calleeHeap ids function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) : Prop :=
  ∃ (arguments : List Dynamic.Value) (middle : Dynamic.Heap),
    ∃ argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) suffixArgumentsSize
      context evidence source environment calleeHeap ids arguments middle,
    ∃ called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) suffixCallSize
      context evidence invocation middle function arguments suffixOutcome suffixAfter,
      suffix = .called argumentsTrace called

/-- An intermediate leaf at the actual admitted argument state. The final
prepared endpoint constructs this leaf from strict body children. -/
def ApplicationPreserves (budget : Nat)
    {suffixArgumentsSize suffixCallSize : Nat} {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment calleeHeap ids function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) : Prop :=
  ∀ {middleMap : LocationMap} {middleWorld : StoreTyping} {middle : Dynamic.Heap} {middleStore : Store}
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter sourceResult : TypeSystem.Ty} {packed : Dynamic.Value},
    (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩) →
    Admission bridge context argumentState →
    LocationMap.Extends mapping middleMap → WorldExtends world middleWorld →
    AdministrativePreserved mapping store middleMap middleStore → Dynamic.HeapMetadataExtend calleeHeap middle →
    Dynamic.ValueHasType context calleeHeap function (.function parameter sourceResult) →
    Dynamic.HeapTypesExtend calleeHeap middle →
    DataExpressionSequence.Values model middleMap middleWorld sourceTypes (compiler.codes.map (·.type)) arguments payloads →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions middleMap middleWorld middle middleStore →
    Dynamic.ValuesHaveTypes context middle arguments types → Dynamic.ValuesPack arguments packed →
    TypeSystem.Ty.productMany types = parameter →
    ∀ {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize context evidence
      source environment calleeHeap ids arguments middle) →
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize context evidence
      invocation middle function arguments outcome after) →
    CalledSuffix (context := context) (evidence := evidence) (environment := environment) suffix →
    callSize ≤ budget →
    ∃ result finalStore finalMap finalWorld,
      Evaluates [calleeNative, DataPatternValues.packValues payloads] middleStore
        CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld sourceResultType resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends middleMap finalMap ∧ WorldExtends middleWorld finalWorld ∧
      AdministrativePreserved middleMap middleStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend middle after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates argumentState returned

/-- The native application port is instantiated by the same concrete value
dispatcher. This is a strict F induction step at the actual argument state. -/
def ApplicationReflects (budget : Nat) : Prop :=
  ∀ {middleMap : LocationMap} {middleWorld : StoreTyping} {middle : Dynamic.Heap} {middleStore : Store}
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter sourceResult : TypeSystem.Ty} {packed : Dynamic.Value},
    (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩) →
    Admission bridge context argumentState →
    LocationMap.Extends mapping middleMap → WorldExtends world middleWorld →
    AdministrativePreserved mapping store middleMap middleStore → Dynamic.HeapMetadataExtend calleeHeap middle →
    Dynamic.ValueHasType context calleeHeap function (.function parameter sourceResult) →
    Dynamic.HeapTypesExtend calleeHeap middle →
    DataExpressionSequence.Values model middleMap middleWorld sourceTypes (compiler.codes.map (·.type)) arguments payloads →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions middleMap middleWorld middle middleStore →
    Dynamic.ValuesHaveTypes context middle arguments types → Dynamic.ValuesPack arguments packed →
    TypeSystem.Ty.productMany types = parameter →
    ∀ {size : Nat} {value : Value} {finalStore : Store},
    EvaluationSize size [calleeNative, DataPatternValues.packValues payloads] middleStore
      CallableIndexedLambdaCalls.applyPayload value finalStore → size ≤ budget →
    ∃ callSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize context evidence
        invocation middle function arguments outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld sourceResultType resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends middleMap finalMap ∧ WorldExtends middleWorld finalWorld ∧
      AdministrativePreserved middleMap middleStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend middle after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates argumentState returned


include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata nativeTyped heaps
  rawResult nativeResult callable shape firstGate secondGate calleeTrace calleeEvaluation in
/-- A real successful callee post feeds ordered admitted arguments, the exact
parameter continuation and the original whole call. Only strict child IH remains. -/
theorem preserves_with_application
    (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget)
    (applicationPreserves : ApplicationPreserves (registry := registry) (faults := faults) bridge functions compiler
      (context := context) (evidence := evidence) (environment := environment) (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := resultCore) (sourceResultType := sourceResultType) budget suffix) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (context := context) bridge functions compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  obtain ⟨calleeTyped, calleeHeapTyped, calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
      function (.function parameter sourceResult) runtime covers locals firstAdmission.heap calleeTyping calleeTrace.sound
  have calleeAdmission : Admission bridge context calleeState :=
    ⟨calleeHeapTyped, StableRows.after_administrative (bridge.pool first) (bridge.pool calleeState) firstAdmission.rows calleeFrame⟩
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  obtain ⟨sourceSize, original⟩ := Suffix.to_expression (invocation := invocation) compiler.found compiler.originalForm parent.requirements parent.coercions
    compiler.argumentCoercions parent.arity callable wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
    argumentsTyping count calleeTrace suffix
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons nativeTyped (typed.weaken calleeWorlds))
  cases suffix with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        frame, metadata, reached, related, _stable⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_fault_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission failed argumentsWithin
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
    have whole := call_argument_fault (resultType := resultCore) shape calleeEvaluation firstGate evaluated
    rw [← emitted] at whole
    exact ⟨sourceSize, _, finalStore, finalMap, finalWorld, original, whole,
      parent_result functions compiler rawResult nativeResult (.fault matched), finalHeaps,
      calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans metadata,
      reached, callerProtocol.trans calleeRelated related,
      after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | called argumentsTrace called =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentEvaluation, represented, middleHeaps,
        maps, worlds, frame, metadata, argumentState, related, argumentAdmission⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace argumentsWithin
    obtain ⟨packed, packing, rawTyped, _heapTyped, extension, _packedTyped⟩ :=
      after_trace wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped argumentsTyping argumentsTrace
    obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, returned, lastRelated⟩ :=
      applicationPreserves argumentState argumentAdmission maps worlds frame metadata calleeTyped extension
        represented middleHeaps rawTyped packing (empty_bundle application compiler.argumentCoercions)
        argumentsTrace called ⟨_, _, argumentsTrace, called, rfl⟩ callWithin
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    have whole := call_payload_success (resultType := resultCore) shape calleeEvaluation firstGate
      argumentEvaluation secondGate evaluated
    rw [← emitted] at whole
    exact ⟨sourceSize, result, finalStore, finalMap, finalWorld, original, whole,
      parent_result functions compiler rawResult nativeResult resultRep, finalHeaps,
      (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
      (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
      returned, callerProtocol.trans (callerProtocol.trans calleeRelated related) lastRelated,
      after_expression_sized first returned firstAdmission wellFormed runtime covers locals parentTyped original
        ((calleeFrame.trans frame).trans lastFrame)⟩

include unique parentTyped in
/-- The original finite whole-call inversion retains independent Source/native
grades. Argument faults keep the actual child post; successful arguments call the
receiving-model payload reflector once at their genuine reached state. -/
theorem reflects_with_application
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
    (firstAdmission : Admission bridge context first)
    (calleeRelated : callerProtocol.Relates first calleeState)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend before calleeHeap)
    (nativeTyped : RuntimeValueHasType world calleeNative (CallableContract.functionType parameterCore resultCore) compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world calleeHeap store)
    (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType sourceResultType)
    (nativeResult : compiler.resultType = resultCore)
    (callable : Dynamic.CallableValue function)
    (shape : calleeNative = .pair calleePayload (.word contract))
    (firstGate : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown contract = none)
    (secondGate : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown contract = none)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee function calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)
    (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar prepared.site callee ids metadata compiler.original row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (applicationReflects : ApplicationReflects (registry := registry) (faults := faults)
      (context := context) (evidence := evidence) (invocation := invocation) (function := function)
      (scope := scope) (canonical := canonical) (mapping := mapping) (world := world) (store := store)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := sourceResultType) (resultCore := resultCore)
      bridge functions compiler budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      ResultAt
        (registry := registry) (faults := faults) (context := context)
        bridge functions compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  obtain ⟨calleeTyped, calleeHeapTyped, _calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
      function (.function parameter sourceResult) runtime covers locals firstAdmission.heap calleeTyping calleeTrace.sound
  have calleeAdmission : Admission bridge context calleeState :=
    ⟨calleeHeapTyped, StableRows.after_administrative (bridge.pool first) (bridge.pool calleeState) firstAdmission.rows calleeFrame⟩
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  rw [emitted] at completed
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons nativeTyped (typed.weaken calleeWorlds))
  cases accepted_completed shape calleeEvaluation firstGate secondGate completed within with
  | failed argumentsTrace smaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, after, finalMap, finalWorld, sourceArguments, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | fault matched =>
      cases sourceArguments with
      | fault failed =>
        obtain ⟨sourceSize, original⟩ := Suffix.to_expression (invocation := invocation) compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity callable wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (Suffix.argumentFault failed)
        exact ⟨sourceSize, _, after, finalMap, finalWorld, original,
          parent_result functions compiler rawResult nativeResult (.fault matched), finalHeaps,
          calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans metadata,
          reached, callerProtocol.trans calleeRelated related,
          after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | applied argumentsTrace applicationTrace smaller applicationSmaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, middle, middleMap, middleWorld, sourceArguments, represented, middleHeaps,
        maps, worlds, frame, metadata, argumentState, related, argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | values represented =>
      cases sourceArguments with
      | values sourceArguments =>
        obtain ⟨packed, packing, rawTyped, _heapTyped, extension, _packedTyped⟩ :=
          after_trace wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped argumentsTyping sourceArguments
        obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps, lastMaps, lastWorlds,
            lastFrame, lastMetadata, returned, lastRelated⟩ :=
          applicationReflects argumentState (argumentPost.successful _ rfl) maps worlds frame metadata
            calleeTyped extension represented middleHeaps rawTyped packing
            (empty_bundle application compiler.argumentCoercions) applicationTrace (Nat.le_of_lt applicationSmaller)
        obtain ⟨sourceSize, original⟩ := Suffix.to_expression (invocation := invocation) compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity callable wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (Suffix.called sourceArguments called)
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original,
          parent_result functions compiler rawResult nativeResult resultRep, finalHeaps,
          (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
          (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
          returned, callerProtocol.trans (callerProtocol.trans calleeRelated related) lastRelated,
          after_expression_sized first returned firstAdmission wellFormed runtime covers locals parentTyped original
            ((calleeFrame.trans frame).trans lastFrame)⟩
end Selected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectCalleeReflection
/-! The actual strict callee child reflects at the complete function model.
A value retains its original Source trace and reached post. An ordinary child
fault stops the whole indirect call at that same post, before the gates and
arguments. Source and native grades are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectCalleeReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functionModel mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Native reflection recovers the independently sized original callee
trace and the same exact reached value post. -/
theorem reflects_value (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word value) finalStore)
    (smaller : size < budget) :
    ∃ sourceSize sourceValue after finalMap finalWorld,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before callee sourceValue after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge functionModel compiler initial
        sourceValue after value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted completed
  cases represented with
  | value represented =>
    cases trace with
    | value trace =>
      exact ⟨sourceSize, _, after, finalMap, finalWorld, trace, completed.sound, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩

include compiler in
private theorem source_callee_fault {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee reason after) :
    ∃ parentSize, RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) parentSize
      context evidence source environment before id (.fault reason) after := by
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [size]],
    .fault (.form (size_fault := SourceExecutionSize.stepSize [size]) (lookupExpression?_sound compiler.found) ?_)⟩
  rw [compiler.originalForm]
  exact .indirectCallee fault

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted in
/-- A native first-bind fault reflects only its exact strict callee child.
The enclosing Source fault has an independent grade and the same post. -/
theorem reflects_fault (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {token : Word} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore)
    (smaller : size < budget) :
    ∃ sourceSize reason after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
        bridge functionModel compiler initial (.fault reason) after (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted completed
  cases represented with
  | fault matched =>
    cases trace with
    | fault failed =>
      obtain ⟨parentSize, original⟩ := source_callee_fault compiler failed
      have whole := CallableContract.call_callee_failure (result := compiler.resultType)
        (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
        prepared.site.gates native.diagnostics.unknown completed.sound
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      exact ⟨parentSize, _, after, finalMap, finalWorld, original, whole, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped original frame⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectCalleeReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveBodyBounds
/-! Primitive bodies close admitted expression members using the existing
builtin producer. Static coverage retains ordinary context validity at the
actual certified expression; runtime validity alone cannot supply that fact.
The prepared flow and typed parameter continuations are then derived internally.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex PreservesAt ReflectsAt Family)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity FlowPreserves FlowReflects)
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- All four static facts concern the same actual certified context and code.
The ordinary ledger receipt is independent of the weaker runtime ledger. -/
structure StaticAt (i : OrdinaryIndex compiled) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop where
  tree : CompatibleExpressionBuiltins.Tree i.support.body.readFuel (.initial compiled.compatible.checked)
    i.function.source context i.code.compilation.solvedRequirements i.code.reasonAt scope id lowered
  valid : CompatibleExpressionLiterals.ContextValid i.code.compilation.solvedRequirements context i.function.evidence
  reads : ReachedLoweredReadOutcomePorts.ReadPolicies i.support.body.readFuel (.initial compiled.compatible.checked)
    i.function.source context i.code.reasonAt faults
  missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) i.function.source
    functions registry (Program.ofChecked compiled.sourceProgram) context i.function.evidence i.code.reasonAt faults

/-- Coverage is requested only for an actual certificate at its genuine valid
context. It contains static and diagnostic receipts, with no execution law. -/
def StaticCoverage (i : OrdinaryIndex compiled) : Prop :=
  ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
    ∀ scope id lowered, i.certificate context scope id lowered →
      StaticAt (registry := registry) (faults := faults) functions i context scope id lowered

/-- The existing accepted compiler producer supplies the literal builtin Tree.
Independent syntax, policy, Source typing and ordinary validity remain inputs. -/
theorem StaticAt.of_functions (i : OrdinaryIndex compiled) (context : SourceSemantics.Context)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilerContext : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (sameLedger : compilerContext.solvedRequirements = i.code.compilation.solvedRequirements)
    (declarations : CompatibleExpressionReads.ScopeDeclarations i.function.source scope context)
    (signatures : context.signatures = compiled.compatible.checked.signatures)
    (constructors : CompatibleExpressionInstantiationLaws.ConstructorLaw i.function.source context
      (CompatibleExpressionBuiltins.Syntax i.function.source))
    (policyFor : CompatibleExpressionBuiltins.PolicyFor policy compilerContext i.support.body.readFuel
      (.initial compiled.compatible.checked) i.function.source scope i.code.reasonAt)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (coercions : ∀ id node, CompatibleExpressionBuiltins.Syntax i.function.source id →
      i.function.source.lookupExpression? id = some node → node.coercions = [])
    (syntaxTree : CompatibleExpressionBuiltins.Syntax i.function.source id)
    (found : i.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType i.function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilerContext
      i.function.source scope id i.code.reasonAt = .ok lowered)
    (valid : CompatibleExpressionLiterals.ContextValid i.code.compilation.solvedRequirements context i.function.evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies i.support.body.readFuel (.initial compiled.compatible.checked)
      i.function.source context i.code.reasonAt faults)
    (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) i.function.source
      functions registry (Program.ofChecked compiled.sourceProgram) context i.function.evidence i.code.reasonAt faults) :
    StaticAt (registry := registry) (faults := faults) functions i context scope id lowered := by
  have tree := CompatibleExpressionBuiltins.tree_of_functions_with_validity
    i.support.unique declarations signatures constructors policyFor native active profile coercions
    syntaxTree found typed accepted
  rw [sameLedger] at tree
  exact ⟨tree, valid, reads, missing⟩

variable (i : OrdinaryIndex compiled)
  (coverage : StaticCoverage (registry := registry) (faults := faults) functions i)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include coverage extension faithful observations functionTypes wellFormed in
/-- The builtin producer runs once. Only its extra primitive fault post is
forgotten; the same semantic tuple and admitted reached state are returned. -/
theorem preserves_at (size : Nat) :
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
      PreservesAt (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i context size := by
  intro context valid scope id lowered certified node found sourceTyped mapping world administrative environment
    canonical actual actualContext before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  have packet := coverage context valid scope id lowered certified
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves
      (bridge := bridge (headers := headers) (keys := keys)) (functions := functions) (evidence := i.function.evidence)
      (transport := administrativeTransport headers keys) (extension := extension) (faithful := faithful)
      (observations := observations) (functionTypes := functionTypes) (valid := packet.valid)
      (reads := packet.reads) (missing := packet.missing) (unique := i.support.unique)
      (wellFormed := wellFormed) (runtime := valid.2) (covers := valid.1.covers)
      packet.tree found sourceTyped environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post.1⟩

include coverage extension faithful observations functionTypes wellFormed in
/-- Reflection keeps the independently returned Source grade and the exact
native completion's returned state when forgetting that extra post. -/
theorem reflects_at (size : Nat) :
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
      ReflectsAt (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i context size := by
  intro context valid scope id lowered certified node found sourceTyped mapping world administrative environment
    canonical actual actualContext before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  have packet := coverage context valid scope id lowered certified
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects
      (bridge := bridge (headers := headers) (keys := keys)) (functions := functions) (evidence := i.function.evidence)
      (transport := administrativeTransport headers keys) (extension := extension) (faithful := faithful)
      (observations := observations) (functionTypes := functionTypes) (valid := packet.valid)
      (reads := packet.reads) (missing := packet.missing) (unique := i.support.unique)
      (wellFormed := wellFormed) (runtime := valid.2) (covers := valid.1.covers)
      packet.tree found sourceTyped environments heaps locals agrees typed initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post.1⟩

include coverage extension faithful observations functionTypes wellFormed in
/-- Primitive coverage closes this literal expression family directly. -/
theorem family_at (size : Nat) :
    Family (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i size := by
  intro context valid
  exact ⟨preserves_at functions i coverage extension faithful observations functionTypes wellFormed size context valid,
    reflects_at functions i coverage extension faithful observations functionTypes wellFormed size context valid⟩

variable {table : SourceCoreFaultSites.Table}
  (rebuilt : i.support.issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep i.support.issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep i.support.issued.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := i.support.certificates i.support.body.readFuel i.function.source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory
        i.support.diagnosticPolicy i.function.source i.support.issued.invalidOperand)
      (faults := faults) (registry := registry) i.support.issued
      (bridge (headers := headers) (keys := keys)) functions table)

include coverage extension faithful observations functionTypes wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- The prepared head and loop recipes derive actual Source flow internally. -/
theorem preserves_flow (size : Nat) :
    FlowPreserves i.captured i.code i.support.body.toBody functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size := by
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.preserves_flow
    i.support.namedCompilation i.captured i.code i.support.issued i.support.body functions
    extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets size
    (fun context valid child _ =>
      preserves_at functions i coverage extension faithful observations functionTypes wellFormed child context valid)
    size (Nat.le_refl size)

include coverage extension faithful observations functionTypes wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Exact native flow grade uses the original Below result at size+1. No
Source grade is equated with that native grade. -/
theorem reflects_flow (size : Nat) :
    FlowReflects i.captured i.code i.support.body.toBody functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size := by
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.reflects_flow
    i.support.namedCompilation i.captured i.code i.support.issued i.support.body functions
    extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets (size + 1) functionTypes
    (fun context valid child _ =>
      reflects_at functions i coverage extension faithful observations functionTypes wellFormed child context valid)
    size (Nat.lt_succ_self size)

variable (history : History i.code) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, i.mapping, i.world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped i.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes i.function.context before arguments i.support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include coverage extension faithful observations functionTypes wellFormed rebuilt operandIncluded unaryIncluded interprets beforeTyped argumentsTyped stable in
/-- Actual Source parameter entry, flow and typed finish are closed here. -/
theorem source_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      i.captured i.code history i.support.body.toBody.toContext functions owner caller budget := by
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.source_continuation
    i.support.namedCompilation i.captured i.code i.support.issued i.support.body functions
    extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets
    history owner caller beforeTyped argumentsTyped stable budget
    (fun context valid child _ =>
      preserves_at functions i coverage extension faithful observations functionTypes wellFormed child context valid)

include coverage extension faithful observations functionTypes wellFormed rebuilt operandIncluded unaryIncluded interprets beforeTyped argumentsTyped stable in
/-- The same native parameter prefix uses genuine allocation and typed finish. -/
theorem native_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      i.captured i.code history i.support.body.toBody.toContext functions owner caller budget := by
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.native_continuation
    i.support.namedCompilation i.captured i.code i.support.issued i.support.body functions
    extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets
    history owner caller beforeTyped argumentsTyped stable budget functionTypes
    (fun context valid child _ =>
      reflects_at functions i coverage extension faithful observations functionTypes wellFormed child context valid)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveBodyBounds
end
