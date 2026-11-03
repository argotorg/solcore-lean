import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol

/-! Selected indirect heads retain the original callsite and a genuine lambda
callee occurrence. Selection contains static code, ordered binders and parsed
guards; it stores no child or body execution law. Body continuations are supplied
only at the real ordered-argument post, for use by the shared mutual closer. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedIndirectSourceAdapters
open RecursiveNamedCatalogInvocationBounds (Below)
universe u

/-- An authentic original lambda occurrence, including its empty raw coercion
path. The policy-read compiler node remains a separate receipt. -/
structure LambdaCallee (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  form : node.form = .lambda parameters result body
  coercions : node.coercions = []

def LambdaCallee.function {source : TypedSource} {id : ExpressionId}
    (callee : LambdaCallee source id) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) : Dynamic.Closure :=
  ⟨callee.parameters, callee.result, callee.body, source, environment, context, evidence⟩

/-- Direct case inversion retains the actual formation environment: the
closure captures the copies of its captured cells, made in the reached heap. -/
theorem LambdaCallee.source_value {source : TypedSource} {id : ExpressionId}
    (callee : LambdaCallee source id) (unique : NodeOccurrencesUnique source)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    ∃ captured, value = .closure (callee.function context evidence captured) ∧
      Dynamic.EnvironmentCopies source environment before captured after := by
  have contains := lookupExpression?_sound callee.found
  cases evaluated with
  | intro found raw coercions =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.coercions] at coercions
    cases coercions
    rw [callee.form] at raw
    cases raw with
    | lambda _ snapshot => exact ⟨_, rfl, snapshot⟩
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.form] at form
    cases form

/-- The original lambda form and empty coercions exclude every callee fault. -/
theorem LambdaCallee.excludes_fault {source : TypedSource} {id : ExpressionId}
    (callee : LambdaCallee source id) (unique : NodeOccurrencesUnique source)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before id reason after) : False := by
  have contains := lookupExpression?_sound callee.found
  cases failed with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent contains
  | form found raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.form] at raw
    cases raw
  | coercion found _ failed =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.coercions] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.form] at form
    cases form

/-- The original sized indirect rule supplies only successful lambda callees
and its genuine argument/application suffix. Arity and coercion faults are
excluded by the authentic empty-path parent receipt. -/
theorem suffix_of_source
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata)) (coercions : node.coercions = [])
    (argumentCoercions : metadata.argumentCoercions = []) (arity : ids.length = metadata.argumentCount)
    (lambda : LambdaCallee source callee) (unique : NodeOccurrencesUnique source)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    {types : List TypeSystem.Ty} (sourceArguments : ExpressionsHaveTypes source context ids types)
    (sourceCount : types.length = metadata.argumentCount)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ calleeSize argumentsSize callSize captured calleeHeap,
      SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee
        (.closure (lambda.function context evidence captured)) calleeHeap ∧
      Dynamic.EnvironmentCopies source environment before captured calleeHeap ∧
      SourceSuffix program context evidence source environment calleeHeap ids (lambda.function context evidence captured)
        argumentsSize callSize outcome after ∧ calleeSize < size ∧ argumentsSize < size ∧ callSize ≤ size := by
  have independent := CallableIndirectCallSourceBounds.indirect_inv_sized found form coercions unique trace
  cases independent with
  | calleeFault child smaller => exact False.elim (lambda.excludes_fault unique child.sound)
  | notCallable child invalid smaller =>
    obtain ⟨_, same, _⟩ := lambda.source_value unique child.sound
    rw [same] at invalid
    exact False.elim (invalid trivial)
  | argumentsFault first callable children firstSmall childrenSmall =>
    obtain ⟨captured, same, copy⟩ := lambda.source_value unique first.sound
    cases same
    exact ⟨_, _, 0, captured, _, first, copy, .argumentFault children, firstSmall, childrenSmall, Nat.zero_le _⟩
  | sourceArity first children mismatch firstSmall childrenSmall => exact False.elim (mismatch arity.symm)
  | argumentCoercionFault first children sameArity pack failed firstSmall childrenSmall coercionSmall =>
    rw [argumentCoercions] at failed
    cases failed
  | applied layout first children packed converted unpacked sameArity appliedArity called firstSmall childrenSmall coercionSmall callSmall =>
    obtain ⟨captured, same, copy⟩ := lambda.source_value unique first.sound
    cases same
    rw [argumentCoercions] at converted
    cases converted
    have sameArguments := Dynamic.ValuesPack.injective_of_length_eq packed unpacked
      ((arguments_count_of_source_admission wellFormed runtime covers (locals.mono copy.metadata_extends)
        (heapTyped.copy copy) sourceArguments sourceCount children).trans appliedArity.symm)
    cases sameArguments
    exact ⟨_, _, _, captured, _, first, copy, SourceSuffix.of_call children (.value called), firstSmall, childrenSmall,
      Nat.le_of_lt callSmall⟩
  | applicationFault first children packed converted unpacked sameArity appliedArity called firstSmall childrenSmall coercionSmall callSmall =>
    obtain ⟨captured, same, copy⟩ := lambda.source_value unique first.sound
    cases same
    rw [argumentCoercions] at converted
    cases converted
    have sameArguments := Dynamic.ValuesPack.injective_of_length_eq packed unpacked
      ((arguments_count_of_source_admission wellFormed runtime covers (locals.mono copy.metadata_extends)
        (heapTyped.copy copy) sourceArguments sourceCount children).trans appliedArity.symm)
    cases sameArguments
    exact ⟨_, _, _, captured, _, first, copy, SourceSuffix.of_call children (.fault called), firstSmall, childrenSmall,
      Nat.le_of_lt callSmall⟩



open CallableIndexedLambdaNestedRuntimeBodyMeaning
open CallableIndexedOwnedLambdaFormationReceipts (FormedRecord of_formation formation_exists)
section Certificates
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- Pure obligations on the exact original formation Code. Ordered argument
certificates retain duplicates, and both parsed decisions use its descriptor. -/
structure Selection
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
    {function : Dynamic.Closure} {calleeScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function calleeScope administrative) : Prop where
  children : DataExpressionSequence.Tree source certificate scope ids
    (code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) compiler.codes
  nativeTypes : compiler.codes.map (·.type) = code.receipt.loweredParameters.map Prod.snd
  escaped : faults .controlEscapedFunction code.compilation.internalReason
  rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType
  nativeResult : compiler.resultType = code.receipt.resultCore
  stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown code.descriptor.id = none
  arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown code.descriptor.id = none

/-- The original callsite and authentic literal producer remain complete.
Selection checks that producer's Code, not every generic ValueRep witness. -/
structure Receipt (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
    (certificate : GenericExpressionMeaning.Certificate)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  policy : SourceCoreFunctions.Policy
  body : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  compilation : SourceCoreFunctions.Context
  callee : ExpressionId
  ids : List ExpressionId
  metadata : IndirectCallResolution
  reasonAt : ExpressionId → Word
  compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered
  native : SourceCoreGeneralFunctions.CallableContext
  prepared : Prepared compiler native
  parent : SourceParent compiler
  rank : Nat
  formation : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
    source context evidence scope callee compiler.calleeCode
  sameSource : source = CallableIndexedNamedGeneration.source caller.named
  calleeCertified : certificate scope callee compiler.calleeCode
  sourceTyped : ExpressionHasType source context callee (.function compiler.parameter compiler.result)
  sourceTypes : List TypeSystem.Ty
  sourceArguments : ExpressionsHaveTypes source context ids sourceTypes
  sourceCount : sourceTypes.length = metadata.argumentCount
  selected : ∀ environment, Selection (faults := faults) (certificate := certificate) compiler prepared (actualCode formation environment)

/-- The same authentic node creates the raw Source formation packet. -/
def Receipt.lambda {caller : CallableIndexedOwnedFunctionValues.Header compiled program}
    (head : Receipt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered) :
    LambdaCallee source head.callee where
  node := head.formation.code.sourceNode
  found := head.formation.found
  parameters := head.formation.parameters
  result := head.formation.result
  body := head.formation.statements
  form := head.formation.code.sourceForm
  coercions := head.formation.coercions

/-- Original source/dictionary/captured locations are exactly the formed ones. -/
theorem Receipt.function_eq {caller : CallableIndexedOwnedFunctionValues.Header compiled program}
    (head : Receipt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered)
    (environment : Dynamic.Environment) :
    head.lambda.function context evidence environment = formed head.formation environment := by
  simp only [Receipt.lambda, LambdaCallee.function, formed, CallableIndexedLambdaGeneration.closure, head.sameSource]

/-- Actual selected literal grammar for the existing generic Calls/Tree fold. -/
def Head (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
    (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (Receipt (headers := headers) (registry := registry) (faults := faults)
    (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered)
end Certificates

section Formation
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Receipt (headers := headers) (registry := registry) (faults := faults)
    (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ (bridge.pool initial))
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)

/-- The formation records of the literal callee: its copies, closure and formed
state. -/
abbrev CalleeRecord :=
  FormedRecord head.formation complete globals (bridge.pool initial) owner prefixZero packet.observed packet.carried
    packet.bundle related agrees typed
    (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))

local notation "Record" => CalleeRecord owner caller prefixZero profile complete globals head bridge initial packet related
  agrees typed

/-- This exact producer retains prefix one, immutable owner, full captures and
original named history, for a formed closure over its copies. No generic model
witness is substituted. -/
def formedReceipt (formedRecord : Record) :=
  of_formation head.formation profile complete globals slots (bridge.pool initial) owner prefixZero packet.observed
    packet.carried packet.bundle related agrees typed heaps formedRecord

local notation "C" => formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed heaps

/-- The actual producer evaluates its own complete emitted callee expression,
copying the captured cells. Native determinism in the existing parent inversion
matches this exact carrier. -/
theorem formed_receipts (formedRecord : Record) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap head.callee
      (.closure (formed head.formation formedRecord.captured)) formedRecord.finalHeap ∧
    Dynamic.EnvironmentCopies source environment heap formedRecord.captured formedRecord.finalHeap ∧
    Evaluates actual store (head.compiler.calleeCode.expression.rename ξ)
      (.inRight .word (value (C formedRecord).code (C formedRecord).captured.embedding (C formedRecord).history.native
        (C formedRecord).capturedActual)) formedRecord.finalStore := by
  have sourceValue := formedRecord.source program
    (by change Dynamic.OrdinaryRequirementLayout head.formation.code.sourceNode.requirements head.formation.code.sourceNode.coercions []
        rw [head.formation.requirements, head.formation.coercions]; rfl) head.formation.coercions
  refine ⟨?_, ?_, ?_⟩
  · change Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap head.formation.code.id (.closure (formed head.formation formedRecord.captured)) formedRecord.finalHeap at sourceValue
    simpa only [head.sameSource, head.formation.identifier] using sourceValue
  · have copy := formedRecord.copy
    change Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment heap formedRecord.captured
      formedRecord.finalHeap at copy
    simpa only [head.sameSource] using copy
  · exact Eq.mp (congrArg (fun expression => Evaluates actual store expression
      (.inRight .word (value (actualCode head.formation environment) formedRecord.embedding
        (historyAt head.formation (CallableIndexedOwnedLambdaViewHeads.nested_entry (bridge.pool initial) owner prefixZero
          packet.observed packet.carried packet.bundle globals) environment).native formedRecord.closureActual)) formedRecord.finalStore)
      (congrArg (fun output : SourceCoreBasic.LoweredExpr => output.expression.rename ξ) head.formation.emitted)) formedRecord.evaluated

include bridge in
/-- The caller witness reaches every administrative extension through the owned
pool and its returned wrapper. -/
theorem caller_transition {index : ProtectedStateTransition.Index} (state : callerProtocol.State index)
    {nextMap : LocationMap} {nextWorld : StoreTyping} {nextHeap : Dynamic.Heap} {nextStore : Store}
    (maps : LocationMap.Extends index.mapping nextMap) (worlds : WorldExtends index.world nextWorld)
    (frame : AdministrativePreserved index.mapping index.store nextMap nextStore)
    (metadata : Dynamic.HeapMetadataExtend index.heap nextHeap) :
    ProtectedStateTransition.Transition callerProtocol state (index.extend nextMap nextWorld nextHeap nextStore) := by
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedFunctionState.protocol headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys) (bridge.pool state)
    maps worlds frame metadata
  obtain ⟨returned, _, callerRelated⟩ := bridge.restore state reached maps worlds frame metadata related
  exact ⟨returned, callerRelated⟩

local notation "P" => callerProtocol
local notation "B" => bridge
local notation "F" => CallableIndexedOwnedFunctionValues.model headers keys registry faults profile

include prefixZero complete globals slots related agrees typed heaps in
/-- Pointwise Source head: genuine initial Source typing and all-row stability
remain real input receipts. The literal callee copies its captured cells and
the caller witness follows to the formed state; then ordered arguments,
parameter allocation, body and restoration return their exact reached
witnesses. -/
theorem preserves_bounded
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context heap) (stable : StableRows (bridge.pool initial))
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
    (budget : Nat)
    (arguments : Below budget (ProtectedStateTransition.PreservesAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source certificate faults))
    (bodies : ∀ formedRecord : Record,
      ∀ reached : (P).State ⟨scope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap,
        formedRecord.finalStore, canonical⟩,
      (P).Relates initial reached →
      SourceContinuations (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := head.ids) profile (C formedRecord) (head.selected environment).escaped B
        reached budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition P initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨calleeSize, argumentsSize, callSize, calleeCaptured, calleeHeap, calleeTrace, calleeCopy, suffix,
      calleeSmall, argumentsSmall, callWithin⟩ :=
    suffix_of_source head.compiler.found head.compiler.originalForm head.parent.coercions
      head.compiler.argumentCoercions head.parent.arity head.lambda unique wellFormed runtime covers locals heapTyped
      head.sourceArguments head.sourceCount trace
  obtain ⟨formedRecord⟩ := formation_exists head.formation complete globals slots (bridge.pool initial) owner prefixZero
    packet.observed packet.carried packet.bundle related agrees typed heaps
  obtain ⟨_sourceCallee, sourceCopy, nativeCallee⟩ := formed_receipts owner caller prefixZero profile complete globals slots
    head bridge initial packet related agrees typed heaps formedRecord
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional calleeCopy sourceCopy
  rw [head.function_eq] at calleeTrace suffix
  obtain ⟨reached, reachedRelated⟩ := caller_transition bridge initial formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
  have captures : FunctionValues.SourceCapturesValid formedRecord.finalHeap (.closure (formed head.formation formedRecord.captured)) :=
    formedRecord.copy.agrees locals
  let selected := head.selected environment
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceParent, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, transition⟩ :=
    preserves_bounded_with_continuations profile head.compiler head.prepared head.parent (C formedRecord)
      selected.children selected.nativeTypes selected.escaped selected.rawResult selected.nativeResult
      (related.extend formedRecord.maps formedRecord.worlds) formedRecord.heaps (locals.mono formedRecord.copy.metadata_extends) captures agrees
      (typed.weaken formedRecord.worlds) wellFormed runtime covers (heapTyped.copy formedRecord.copy) head.sourceArguments head.sourceCount
      B reached (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) stable formedRecord.frame) budget
      arguments (bodies formedRecord reached reachedRelated) initial reachedRelated formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
      calleeTrace nativeCallee selected.stageAccepted selected.arityAccepted suffix
      (Nat.le_trans (Nat.le_of_lt argumentsSmall) within) (Nat.le_trans callWithin within)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩

include prefixZero complete globals slots related agrees typed heaps in
/-- Native reflection uses the real literal producer's evaluation in the
original parent completion inversion. It retains original strict native
argument/body children and an independently graded whole Source trace. -/
theorem reflects_bounded
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context heap) (stable : StableRows (bridge.pool initial))
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (budget : Nat)
    (arguments : Below budget (ProtectedStateTransition.ReflectsAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source certificate faults))
    (bodies : ∀ formedRecord : Record,
      ∀ reached : (P).State ⟨scope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap,
        formedRecord.finalStore, canonical⟩,
      (P).Relates initial reached →
      NativeContinuations (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := head.ids) profile (C formedRecord) (head.selected environment).escaped B
        reached budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition P initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨formedRecord⟩ := formation_exists head.formation complete globals slots (bridge.pool initial) owner prefixZero
    packet.observed packet.carried packet.bundle related agrees typed heaps
  obtain ⟨sourceCallee, _sourceCopy, nativeCallee⟩ := formed_receipts owner caller prefixZero profile complete globals
    slots head bridge initial packet related agrees typed heaps formedRecord
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size sourceCallee
  obtain ⟨reached, reachedRelated⟩ := caller_transition bridge initial formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
  have captures : FunctionValues.SourceCapturesValid formedRecord.finalHeap (.closure (formed head.formation formedRecord.captured)) :=
    formedRecord.copy.agrees locals
  let selected := head.selected environment
  exact reflects_bounded_with_continuations profile head.compiler head.prepared head.parent (C formedRecord)
    selected.children selected.nativeTypes selected.escaped selected.rawResult selected.nativeResult
    (related.extend formedRecord.maps formedRecord.worlds) formedRecord.heaps (locals.mono formedRecord.copy.metadata_extends) captures agrees
    (typed.weaken formedRecord.worlds) wellFormed runtime covers (heapTyped.copy formedRecord.copy) head.sourceArguments head.sourceCount
    B reached (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) stable formedRecord.frame) budget
    arguments (bodies formedRecord reached reachedRelated) initial reachedRelated formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
    calleeTrace nativeCallee selected.stageAccepted selected.arityAccepted completed within

end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectHeads
