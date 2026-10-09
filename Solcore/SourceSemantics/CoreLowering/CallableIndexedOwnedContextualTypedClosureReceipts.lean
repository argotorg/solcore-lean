import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedLambdaReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation

/-! Retained contextual static receipts provide genuine owner, Code, captures,
history and Syntax independently of an escaped-control diagnostic. Their typed
invocations use the original SourceReceipt/no-escape finish core and actual
saved-frame restoration. StaticMember is the Prop-facing witness factor for
the existing positive-cell backend; no General representation is inverted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedOrdinaryLambdaSupport (Support SourceOrigin)
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt PrincipalAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The exact ordinary/principal static receipt is retained before erasure.
Its real factory fields determine the typed body; no diagnostic row is added. -/
inductive Association
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : Support code registry faults) (origin : SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions)
      (provenance : OrdinaryAt code support) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions)
      (provenance : PrincipalAt code support) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Forward selection keeps the genuine contextual branch and all its fields. -/
theorem Association.selection
    (member : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    exact .contextual_ordinary_lambda owner captured code history support origin prefixContext globals referenceIndex typed provenance
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact .contextual_principal_lambda owner captured code history support origin globals leading referenceIndex typed provenance

/-- Only forward projection to the exact general relation is needed. -/
theorem Association.represents
    (member : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) :=
  CallableIndexedOwnedGeneralFunctionSelection.represents member.selection

/-- Actual map/world growth changes only capture and runtime typing indices.
The original code, owner, history and same-body syntax stay the same. -/
def Association.extend
    (member : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association headers keys registry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    exact .ordinary owner (captured.extend maps worlds) code history support origin prefixContext globals
      referenceIndex (typed.weaken worlds) provenance
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact .principal owner (captured.extend maps worlds) code history support origin globals leading
      referenceIndex (typed.weaken worlds) provenance

/-- Model leaves retain a real typed association under Prop, without exposing
an operational Code getter or recovering authority from representation. -/
abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameterCore resultCore : Ty) : Prop :=
  Nonempty (Association headers keys registry faults mapping world function native bindings parameterCore resultCore)

theorem StaticMember.selection
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) := by
  obtain ⟨association⟩ := member
  exact association.selection

theorem StaticMember.represents
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) :=
  CallableIndexedOwnedGeneralFunctionSelection.represents member.selection

theorem StaticMember.extend
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys registry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

/-- The original Source support authenticates the actual native carrier.
No escaped-control row is used by this static stage observation. -/
theorem Association.stage_origin
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases association with
  | ordinary _owner captured code history support _origin _prefix _globals _reference _typed _provenance =>
    exact CallableIndexedOwnedOrdinaryLambdaSupport.Support.stage_origin captured code support history
  | principal _owner captured code history support _origin _globals _leading _reference _typed _provenance =>
    exact CallableIndexedOwnedMethodLambdaSupport.Support.stage_origin captured code support history

theorem StaticMember.stage_origin
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  obtain ⟨association⟩ := member
  exact association.stage_origin

section Formation
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults) (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : OrdinaryAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

include profile prefixContext observed provenance inclusion in
/-- One original contextual formation retains its complete traces and
represented value, plus the same static member for later initialized reads.
The factory is used once, without an escaped-token hypothesis. -/
theorem formation_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual)) store ∧
    functions.Represents registry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) ∧
    StaticMember headers keys registry faults mapping world function
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨sourceTrace, nativeTrace, related, determined⟩ :=
    CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.formation captured code support owner initial packet
      profile prefixContext observed provenance functions inclusion stored ordinary coercions
  have typed : RuntimeValueHasType world
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions := functions.runtime_hasType (registry := registry) related
  exact ⟨sourceTrace, nativeTrace, related, determined,
    ⟨.ordinary owner captured code (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) typed provenance⟩⟩

end Formation

section PrincipalFormation
variable {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
  (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (provenance : PrincipalAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)

include packet profile provenance inclusion in
/-- One original contextual principal formation retains its genuine leading
bundle, owner and history with the exact static member. No escaped-control diagnostic is required. -/
theorem principal_formation_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)) store ∧
    functions.Represents registry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) ∧
    StaticMember headers keys registry faults mapping world function
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨sourceTrace, nativeTrace, related, determined⟩ :=
    CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.formation captured code support owner initial packet
      profile functions inclusion provenance stored ordinary coercions
  have typed : RuntimeValueHasType world
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions := functions.runtime_hasType (registry := registry) related
  exact ⟨sourceTrace, nativeTrace, related, determined,
    ⟨.principal owner captured code
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) support
      (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet)
      packet.observed (CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet)
      (CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support) typed provenance⟩⟩

end PrincipalFormation

section Invocation
open RecursiveNamedCatalogInvocationBounds (Below)
open CallableIndexedOwnedTypedLambdaStaticBody (Body)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

/-- The strict flow child is indexed by this receipt's real retained Code.
An old BodyOrigin child cannot be substituted for this typed flow contract. -/
def Association.FlowPreserves
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (size : Nat) : Prop :=
  match association with
  | .ordinary _ captured code _ support _ _ _ _ _ provenance =>
    CallableIndexedOwnedTypedLambdaBodyContinuations.FlowPreserves captured code
      (Body.of_body_with support.body provenance.syntax) functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size
  | .principal _ captured code _ support _ _ _ _ _ provenance =>
    CallableIndexedOwnedTypedLambdaBodyContinuations.FlowPreserves captured code
      (Body.of_body_with support.body provenance.syntax) functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size

def Association.FlowReflects
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (size : Nat) : Prop :=
  match association with
  | .ordinary _ captured code _ support _ _ _ _ _ provenance =>
    CallableIndexedOwnedTypedLambdaBodyContinuations.FlowReflects captured code
      (Body.of_body_with support.body provenance.syntax) functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size
  | .principal _ captured code _ support _ _ _ _ _ provenance =>
    CallableIndexedOwnedTypedLambdaBodyContinuations.FlowReflects captured code
      (Body.of_body_with support.body provenance.syntax) functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size

variable (functions : FunctionModel compiled.compatible.checked.catalog
  (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

variable {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
  (initial : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
    (function.parameters.map (fun binding => binding.scheme.body)))
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (stable : StableRows initial)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include represented heaps beforeTyped argumentsTyped locals stable wellFormed in
/-- The actual typed flow callback, parameter action and saved-frame restore
run through their original cores. The final pool comes from that transition. -/
theorem preserves_at (budget : Nat)
    (below : Below budget (association.FlowPreserves functions))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedStoredClosureInvocation.ResultAt (registry := registry) (faults := faults)
        functions initial function resultCore outcome after value finalStore := by
  cases association with
  | ordinary owner captured code history support _origin _prefixContext globals referenceIndex _typed provenance =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨_currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedTypedLambdaInvocationBounds.application_preserves_bounded
        captured code history (Body.of_body_with support.body provenance.syntax) functions represented owner
        initial heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        beforeTyped raw stable wellFormed budget below trace within
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame,
      metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support _origin globals _leading referenceIndex _typed provenance =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨_currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedTypedLambdaInvocationBounds.application_preserves_bounded
        captured code history (Body.of_body_with support.body provenance.syntax) functions represented owner
        initial heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        beforeTyped raw stable wellFormed budget below trace within
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame,
      metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

include represented heaps beforeTyped argumentsTyped locals stable wellFormed in
theorem reflects_at (budget : Nat)
    (below : Below budget (association.FlowReflects functions))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedStoredClosureInvocation.ResultAt (registry := registry) (faults := faults)
        functions initial function resultCore outcome after value finalStore := by
  cases association with
  | ordinary owner captured code history support _origin _prefixContext globals referenceIndex _typed provenance =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨_currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedTypedLambdaInvocationBounds.application_reflects_bounded
        captured code history (Body.of_body_with support.body provenance.syntax) functions represented owner
        initial heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        beforeTyped raw stable wellFormed budget below completed within
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame,
      metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support _origin globals _leading referenceIndex _typed provenance =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨_currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedTypedLambdaInvocationBounds.application_reflects_bounded
        captured code history (Body.of_body_with support.body provenance.syntax) functions represented owner
        initial heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        beforeTyped raw stable wellFormed budget below completed within
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame,
      metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

end Invocation
/-- The actual Code's accepted parameter compilation retains the ordered raw
Source binders. Packing or native tags do not determine this Source row. -/
theorem Association.source_binders
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  cases association with
  | ordinary _owner _captured code _history _support _origin _prefix _globals _reference _typed _provenance =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm
  | principal _owner _captured code _history _support _origin _globals _leading _reference _typed _provenance =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

/-- Runtime typing already retained by the same Association fixes only its
native carrier type. Its genuine Source binder row is a separate projection. -/
theorem Association.native_type
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    native.type = CallableContract.functionType parameterCore resultCore := by
  cases association with
  | ordinary _owner _captured _code _history _support _origin _prefix _globals _reference typed _provenance =>
    exact typed.type_eq
  | principal _owner _captured _code _history _support _origin _globals _leading _reference typed _provenance =>
    exact typed.type_eq

/-- Genuine contextual provenance retains the canonical projection of every
ordered binder, for both ordinary and principal static receipts. -/
theorem Association.projected_bindings
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases association with
  | ordinary _owner _captured _code _history _support _origin _prefix _globals _reference _typed provenance =>
    exact CallableIndexedOwnedContextualTypedLambdaReceipts.ordinary_projected_bindings provenance
  | principal _owner _captured _code _history _support _origin _globals _leading _reference _typed provenance =>
    exact CallableIndexedOwnedContextualTypedLambdaReceipts.principal_projected_bindings provenance

/-- The real binder projections and same typed body's result projection fix
this Code's packed native parameter type. No diagnostic receipt is used. -/
theorem Association.parameter_core
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameterCore = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  cases association with
  | ordinary _owner _captured _code _history _support _origin _prefix _globals _reference _typed provenance =>
    exact CallableIndexedOwnedContextualTypedLambdaReceipts.ordinary_binding_pack provenance profile
  | principal _owner _captured _code _history _support _origin _globals _leading _reference _typed provenance =>
    exact CallableIndexedOwnedContextualTypedLambdaReceipts.principal_binding_pack provenance profile

/-- Prop-facing projections eliminate the actual retained Association only
inside the proof; no operational Code getter or classical choice is introduced. -/
theorem StaticMember.source_binders
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  obtain ⟨association⟩ := member
  exact association.source_binders

theorem StaticMember.native_type
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    native.type = CallableContract.functionType parameterCore resultCore := by
  obtain ⟨association⟩ := member
  exact association.native_type

theorem StaticMember.projected_bindings
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  obtain ⟨association⟩ := member
  exact association.projected_bindings

theorem StaticMember.parameter_core
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameterCore = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  obtain ⟨association⟩ := member
  exact association.parameter_core profile

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts
