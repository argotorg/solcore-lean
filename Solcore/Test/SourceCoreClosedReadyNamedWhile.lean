import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceOrigin
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
import Solcore.Test.SourceCoreClosedOwnedExpressionHead
import Solcore.Test.SourceCoreClosedOwnedWhile

/-! A real named parameter receipt and a literal-false while body exercise
actual loop activation, Source admission and the reached owned records.
The literal and body callbacks are derived internally from authentic static
receipts and the shared Ready family; no execution family is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreClosedReadyNamedWhile
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open Tests.SourceCoreClosedOwnedWhile (booleans boolean_preserves_at boolean_reflects_at)
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)
open Tests.SourceCoreClosedOwnedExpressionHead (PreparedReceipts layouts PoolObservations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- Full original parameter, hook, Source and compiler receipts stay together.
The certificate admits only the compiler's ordinary Boolean literal leaf. -/
abbrev Receipt {index : Index} (argumentsPool : State headers keys index)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (arguments : List Dynamic.Value) :=
  CallableIndexedOwnedAdmittedNamedExpressionHeads.ParameterReceipt
    (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := fun header _ => booleans header.function.source)
    (expressionSyntax := fun _ _ => True) (diagnosticPolicy := .reachable) (runtime := true)
    argumentsPool header arguments

/-- This bounded Source body contains a real while condition, and both its
loop body and the remaining Unit fallthrough are empty. -/
structure FalseWhile (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  statement : StatementId
  node : StatementNode
  condition : ExpressionId
  conditionNode : ExpressionNode
  body : header.function.body = [statement]
  found : header.function.source.lookupStatement? statement = some node
  form : node.form = .whileLoop condition []
  conditionFound : header.function.source.lookupExpression? condition = some conditionNode
  literal : CompatibleExpressionLiterals.Literal [] conditionNode .bool (LanguageResult.success (.bool false))
  unitResult : header.function.resultType = .unit

private theorem literal_fields {node : ExpressionNode}
    (literal : CompatibleExpressionLiterals.Literal [] node .bool (LanguageResult.success (.bool false))) :
    ∃ name, node.form = .reference name (.builtinBoolean false) ∧ node.type = .bool ∧
      node.requirements = [] ∧ node.coercions = [] := by
  cases literal with
  | bool value form type requirements coercions => exact ⟨_, form, type, requirements, coercions⟩

variable {index : Index} {argumentsPool : State headers keys index}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) (faults := faults) functions owner argumentsPool header arguments)
  (body : FalseWhile header)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include receipt body wellFormed in
/-- Authentic Source body typing supplies the condition judgment; the
independent literal/form receipts build the same original compiler Syntax. -/
theorem body_syntax : GenericImperativeMatch.Syntax header.function.source (fun _ => True) header.context
    (.statements true header.function.body) header.function.resultType := by
  have original := receipt.admitted_entry wellFormed
  have statements : ProtectedStateImperativeTypedSourceSites.Statements header.function.source header.context header.function.body :=
    CallableIndexedOwnedBodyTypedFacts.statements original.source
  rw [body.body] at statements
  have head := ProtectedStateImperativeTypedSourceSites.head statements
  have unique := header.unique
  obtain ⟨conditionTyped, _bodyTyped⟩ := ProtectedStateImperativeTypedSourceSites.while_loop unique head body.found body.form
  obtain ⟨_name, _form, conditionType, _requirements, _coercions⟩ := literal_fields body.literal
  rw [body.body]
  exact .whileLoop body.found body.form body.conditionFound conditionType
    (by simpa only [conditionType] using conditionTyped) True.intro
    (.body (.nil (.inl rfl))) (.body (.nil (.inr body.unitResult)))

include body in
/-- Construct the original false condition and Unit body trace. No Source or
native execution premise is needed to obtain this genuine finite body run. -/
theorem actual_source {environment : Dynamic.Environment} {before : Dynamic.Heap} :
    ∃ size, RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size
      header.function header.context environment before (.value .unit) before := by
  obtain ⟨name, form, _type, requirements, coercions⟩ := literal_fields body.literal
  have condition : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []])
      header.context header.function.evidence header.function.source environment before body.condition (.bool false) before := by
    refine .intro (raw := .bool false) (middle := before) (lookupExpression?_sound body.conditionFound) ?_ ?_
    · rw [form]
      exact .builtinBoolean (by simp [Dynamic.OrdinaryRequirementLayout, requirements, coercions, coercionRequirementIds])
    · rw [coercions]
      exact .nil
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [SourceExecutionSize.stepSize
    [SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []]]]],
    .unit (finalContext := header.context) (finalEnvironment := environment) body.unitResult ?_⟩
  rw [body.body]
  exact .singleton (lookupStatement?_sound body.found)
    (by intro expression impossible; rw [body.form] at impossible; cases impossible)
    (.whileLoop (lookupStatement?_sound body.found) body.form (.done condition))

private abbrev bridge := CallableIndexedOwnedIndirectCallerProtocol.of_legacy
  (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

private def actual_origin := CallableIndexedOwnedBodySourceOrigin.source_origin
  (CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
  (receipt.admitted_entry wellFormed).source.runtime

private def actual_entry : CallableRuntimeBodyReadyOrigins.Entry (protocol headers keys)
    (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (fun _ => True))
    (actual_origin functions owner receipt wellFormed) functions :=
  CallableIndexedOwnedBodySourceOrigin.ready_entry (bridge (headers := headers) (keys := keys))
    (receipt.admitted_entry wellFormed) (body_syntax functions owner receipt body wellFormed)

variable (prepared : PreparedReceipts (headers := headers)) (member : header ∈ headers)

private def marked : MarkedAllocation.Producer (protocol headers keys)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (layouts prepared member).symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    (same : first = second)
    (producer : MarkedAllocation.Producer (protocol headers keys)
      second compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    {location : Location} {native : NativeFrame}
    (ready : OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (marked (headers := headers) (keys := keys) (registry := registry) functions prepared member).toOrdinary location native :=
  ready_layout (keys := keys) functions (layouts prepared member)
    (CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include wellFormed in
private theorem literals_preserve (context : SourceSemantics.Context)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : header.function.evidence.Covers context) (size : Nat) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt
      (protocol headers keys)
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (Program.ofChecked compiled.sourceProgram) header.function.evidence
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (booleans header.function.source)
      (source := header.function.source) (context := context) (faults := faults) size :=
  CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at (bridge (headers := headers) (keys := keys))
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful wellFormed runtime covers
      (boolean_preserves_at (headers := headers) (keys := keys) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) (registry := registry) (context := context) (faults := faults) functions header.function.evidence size header.unique))

include wellFormed in
private theorem literals_reflect (context : SourceSemantics.Context)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : header.function.evidence.Covers context) (size : Nat) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt
      (protocol headers keys)
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (Program.ofChecked compiled.sourceProgram) header.function.evidence
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (booleans header.function.source)
      (source := header.function.source) (context := context) (faults := faults) size :=
  CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at (bridge (headers := headers) (keys := keys))
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful wellFormed runtime covers
      (boolean_reflects_at (headers := headers) (keys := keys) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) (registry := registry) (context := context) (faults := faults) functions header.function.evidence size))

private def actual_inputs := CallableIndexedOwnedBodyReadyCatalog.inputs
  (bridge (headers := headers) (keys := keys))
  (CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
  (receipt.admitted_entry wellFormed).source.runtime (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys) wellFormed

variable (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)

include prepared member extension faithful observations wellFormed in
private theorem family_preserves (size : Nat) :
    CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (actual_inputs functions owner receipt wellFormed).facts functions (Program.ofChecked compiled.sourceProgram)
      (actual_origin functions owner receipt wellFormed) size := by
  have closed := CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.preserves_at
    (ι := Unit) (origins := fun _ => actual_origin functions owner receipt wellFormed)
    (functions := functions) (program := Program.ofChecked compiled.sourceProgram) (observations := observations)
    (protocols := fun _ => protocol headers keys)
    (conditionGate := fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producers := fun _ => marked (headers := headers) (keys := keys) functions prepared member)
    (acquire := fun _ => acquire functions prepared member)
    (stateTransport := fun _ => administrativeTransport headers keys) (stateBindings := fun _ => CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (readinesses := fun _ => CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
    (inputs := fun _ => actual_inputs functions owner receipt wellFormed)
    (expressionMeaning := fun _ context valid _ child _ _ =>
      literals_preserve functions wellFormed context valid.2
        ((CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped).runtimeOf valid.1).covers child)
    (kitsFor := fun _ budget children => CallableIndexedOwnedBodyReadyCatalog.preserving_ready_kits
      (bridge (headers := headers) (keys := keys))
      (CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
      (receipt.admitted_entry wellFormed).source.runtime (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys) wellFormed
      functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (marked (headers := headers) (keys := keys) functions prepared member) (acquire functions prepared member)
      (administrativeTransport headers keys) budget
      children) size
  exact closed ()

include prepared member extension faithful observations wellFormed in
private theorem family_reflects (functionTypes : FunctionRuntimeViews functions) (size : Nat) :
    CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (actual_inputs functions owner receipt wellFormed).facts functions (Program.ofChecked compiled.sourceProgram)
      (actual_origin functions owner receipt wellFormed) size := by
  have closed := CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.reflects_at
    (ι := Unit) (origins := fun _ => actual_origin functions owner receipt wellFormed)
    (functions := functions) (program := Program.ofChecked compiled.sourceProgram) (observations := observations)
    (protocols := fun _ => protocol headers keys)
    (conditionGate := fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producers := fun _ => marked (headers := headers) (keys := keys) functions prepared member)
    (acquire := fun _ => acquire functions prepared member)
    (stateTransport := fun _ => administrativeTransport headers keys) (stateBindings := fun _ => CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (readinesses := fun _ => CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
    (inputs := fun _ => actual_inputs functions owner receipt wellFormed)
    (expressionMeaning := fun _ context valid _ child _ _ =>
      literals_reflect functions wellFormed context valid.2
        ((CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped).runtimeOf valid.1).covers child)
    (kitsFor := fun _ budget children => CallableIndexedOwnedBodyReadyCatalog.reflecting_ready_kits
      (bridge (headers := headers) (keys := keys))
      (CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
      (receipt.admitted_entry wellFormed).source.runtime (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys) wellFormed
      functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (marked (headers := headers) (keys := keys) functions prepared member) (acquire functions prepared member)
      (administrativeTransport headers keys) budget functionTypes
      children) size
  exact closed ()

/-- Full body semantics and observations refer to one actual returned pool.
The parameter receipt fixes the physical frame and all original entry data. -/
def BodyPost (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates receipt.body.actualBody receipt.body.store (header.body.rename receipt.body.embedding) value finalStore ∧
  FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld header.function.resultType header.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
  AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
  Dynamic.HeapMetadataExtend receipt.body.heap after ∧
  TypedMixedNamedBody.ReachedExit compiled.compatible.checked
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions finalMap finalWorld
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: receipt.administrative)
    (Program.ofChecked compiled.sourceProgram) header.function header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    receipt.body.environment receipt.body.heap after outcome ∧
  receipt.frameLocation ∉ finalMap ∧
  finalStore.read? receipt.frameLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state receipt.index)) ∧
  ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
    Relates receipt.reached reached ∧
    PoolObservations receipt.reached reached ∧ PoolObservations argumentsPool reached ∧
    ProtectedStateTransition.FunctionFinish.PostReady
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      header.context outcome reached ∧
    CallableIndexedOwnedSourceAdmission.PostAdmission (bridge (headers := headers) (keys := keys))
      header.context header.function.resultType outcome reached

private theorem frame_kept {finalMap : LocationMap} {finalStore : Store}
    (preserved : AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore) :
    receipt.frameLocation ∉ finalMap ∧
      finalStore.read? receipt.frameLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state receipt.index)) := by
  have unmapped : receipt.frameLocation ∉ receipt.body.mapping :=
    Eq.mp (congrArg (fun location => location ∉ receipt.body.mapping) receipt.body.catalog_frame)
      receipt.body.catalog.authority.unmapped
  have retained := preserved receipt.frameLocation unmapped (List.getElem?_eq_some_iff.mp receipt.body.state.read).1
  exact ⟨retained.1, retained.2.trans receipt.body.state.read⟩

include body wellFormed prepared member extension faithful observations in
/-- A genuine false-while Source trace is constructed internally, then the
shared Ready Family returns complete semantics and the actual reached pool. -/
theorem source_post :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize
        header.function header.context receipt.body.environment receipt.body.heap (.value .unit) receipt.body.heap ∧
      BodyPost functions owner receipt (.value .unit) receipt.body.heap value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, trace⟩ := actual_source body (environment := receipt.body.environment) (before := receipt.body.heap)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      preserved, metadata, exit, reached, related, post⟩ :=
    family_preserves functions owner receipt wellFormed prepared member extension faithful observations sourceSize
      (actual_entry functions owner receipt body wellFormed) trace
  have frame := frame_kept functions owner receipt preserved
  refine ⟨sourceSize, value, finalStore, finalMap, finalWorld, trace,
    evaluated, represented, heaps, maps, worlds, preserved, metadata, exit, frame.1, frame.2,
    reached, related, reached_pool_observations related,
    reached_pool_observations ((protocol headers keys).trans receipt.related related), post, ?_⟩
  exact CallableIndexedOwnedAdmittedBodyEntries.after_body
    (bridge (headers := headers) (keys := keys)) wellFormed (receipt.admitted_entry wellFormed) reached trace preserved

include body wellFormed prepared member extension faithful observations in
/-- Native reflection calls the shared Ready Family independently. Its Source
grade, whole result and post admission accompany the same actual native post. -/
theorem native_post (functionTypes : FunctionRuntimeViews functions) (size : Nat)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize
        header.function header.context receipt.body.environment receipt.body.heap outcome after ∧
      BodyPost functions owner receipt outcome after value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      preserved, metadata, exit, reached, related, post⟩ :=
    family_reflects functions owner receipt wellFormed prepared member extension faithful observations functionTypes size
      (actual_entry functions owner receipt body wellFormed) completed
  have frame := frame_kept functions owner receipt preserved
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    completed.sound, represented, heaps, maps, worlds, preserved, metadata, exit, frame.1, frame.2,
    reached, related, reached_pool_observations related,
    reached_pool_observations ((protocol headers keys).trans receipt.related related), post, ?_⟩
  exact CallableIndexedOwnedAdmittedBodyEntries.after_body
    (bridge (headers := headers) (keys := keys)) wellFormed (receipt.admitted_entry wellFormed) reached trace preserved

end Tests.SourceCoreClosedReadyNamedWhile
