import Solcore.Test.SourceCoreClosedOwnedLexicalBody
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeNamedBodyFamily
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedHeaderReceipts

/-! Full prepared Header receipts close nil Unit bodies through the actual
named mutual family. The selected argument/callee head then retains its real
returned pool, without an assumed expression or body meaning. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedExpressionHead
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds ProtectedStateTransition
open Tests.SourceCoreClosedOwnedLexicalBody (noExpressions noExpressionSyntax reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- The complete factory attribution is retained as the static test premise. -/
def PreparedReceipts : Prop :=
  ∀ header, header ∈ headers → ∃ row, ∃ prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row,
    ∃ instantiation, RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header

variable (receipts : PreparedReceipts (headers := headers))
  (body_nil : ∀ header, header ∈ headers → header.function.body = [])
  (unit_result : ∀ header, header ∈ headers → header.function.resultType = .unit)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)

include receipts in
theorem layouts {header} (member : header ∈ headers) : header.layouts = compiled.indexed.layouts := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.layouts

include receipts in
private theorem accepted {header} (member : header ∈ headers) :
    SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.accepted

include receipts in
private theorem projection {header} (member : header ∈ headers) :
    compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.projection

private def nilProfile {header} (member : header ∈ headers) (administrative : Core.Context) :
    MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
      noExpressions .reachable header noExpressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) header.function.source noExpressions header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
      header.function.resultType header.output (LocalLoop.fallthrough header.output) := by
    rw [body_nil header member]
    exact .nil (Or.inr (unit_result header member))
  let admission : GenericLexicalStatements.Syntax header.function.source noExpressionSyntax header.context true
      header.function.body header.function.resultType := by
    rw [body_nil header member]
    exact .nil (Or.inr (unit_result header member))
  let tree := GenericImperativeMatch.Tree.body
    (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) admission lexical
  have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok (LocalLoop.fallthrough header.output) := by
    rw [body_nil header member]
    cases header.fuel <;> rfl
  exact MatchProfileWith.of_extracted header.valid (accepted receipts member) (projection receipts member) generated tree
    (.body (syntaxTree := admission) (body := lexical))

private def producer {header} (member : header ∈ headers) : MarkedAllocation.Producer (protocol headers keys)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (layouts receipts member).symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (same : first = second) (marked : MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame} (ready : OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ marked).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire {header} (member : header ∈ headers) (location : Location) (native : NativeFrame)
    (seed : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (producer (functions := functions) (registry := registry) (keys := keys) receipts member).toOrdinary location native := by
  intro index reached read
  exact (ready_layout (headers := headers) (keys := keys) (layouts receipts member)
    (CallableIndexedOwnedMarkedAllocation.producer headers keys (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) seed)) reached read

def conditions (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :
    BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header :=
  CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
    (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header

include extension faithful observations receipts body_nil unit_result escaped in
/-- The actual named family closes the bodies; only impossible expression
certificate leaves are discharged. No body law is a test premise. -/
theorem bodies_preserve (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions functions owner header) size := by
  exact CallableRuntimeNamedBodyFamily.preserves_at (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) true functions extension faithful observations escaped
    (protocol headers keys) (conditions functions owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun header member => producer (functions := functions) (registry := registry) (keys := keys) receipts member)
    (fun header member => acquire functions receipts member)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (fun _ => noExpressions)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact nilProfile (registry := registry) (faults := faults) receipts body_nil unit_result member administrative)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact aligned)
    (by intro header member context valid budget child within below scope id lowered impossible; cases impossible) size

include extension faithful observations functionTypes receipts body_nil unit_result escaped in
theorem bodies_reflect (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions functions owner header) size := by
  exact CallableRuntimeNamedBodyFamily.reflects_at (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) true functions extension faithful observations functionTypes escaped
    (protocol headers keys) (conditions functions owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun header member => producer (functions := functions) (registry := registry) (keys := keys) receipts member)
    (fun header member => acquire functions receipts member)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (fun _ => noExpressions)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact nilProfile (registry := registry) (faults := faults) receipts body_nil unit_result member administrative)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact aligned)
    (by intro header member context valid budget child within below scope id lowered impossible; cases impossible) size


open CallableIndexedOwnedExpressionHeads
variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {compilation : SourceCoreFunctions.Context}

include extension faithful observations receipts body_nil unit_result escaped in
/-- Real ordinary/direct metadata chooses the callee; its nil Unit body is
closed by the named family above, with no semantic child assumption. -/
theorem closed_head_preserves (size : Nat)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup) :
    PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence (noExpressions context)) size := by
  exact CallableIndexedOwnedExpressionHeads.preserves_at_with functions owner (fun header member => layouts receipts member)
    (conditions functions owner)
    (fun header _member => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
    size size (Nat.le_refl _) idsUnique unique owners
    (by intro child smaller scope id lowered impossible; cases impossible)
    (by
      intro header member child smaller
      exact bodies_preserve functions extension faithful observations owner receipts body_nil unit_result escaped child header member)

include extension faithful observations functionTypes receipts body_nil unit_result escaped in
/-- Native reflection derives its source grade independently and uses the
same real metadata, actual body family and reached caller pool. -/
theorem closed_head_reflects (size : Nat) :
    ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence (noExpressions context)) size := by
  exact CallableIndexedOwnedExpressionHeads.reflects_at_with functions owner (fun header member => layouts receipts member)
    (conditions functions owner)
    (fun header _member => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
    size size (Nat.le_refl _)
    (by intro child smaller scope id lowered impossible; cases impossible)
    (by
      intro header member child smaller
      exact bodies_reflect functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped child header member)


/-- Every observation is made on the actual returned pool, including all
ordered rows and readable snapshot records. -/
def PoolObservations {initialIndex reachedIndex : Index}
    (initial : State headers keys initialIndex) (reached : State headers keys reachedIndex) : Prop :=
  (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
  (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
    compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame reachedIndex.mapping reachedIndex.store record) ∧
  (∀ row record, record ∈ records initial row → record ∈ records reached row)

section Drivers
variable {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr}
  (head : RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers compilation source context evidence (noExpressions context) scope id lowered)
  (found : source.lookupExpression? id = some node)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
    administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (globals : Globals (headers := headers) owner compilation.administrativePrefix scope canonical)

include extension faithful observations receipts body_nil unit_result escaped head found environments heaps locals agrees typed initial globals in
/-- A genuine source call trace drives the actual argument, parameter and body
receipts. The caller is restored in that returned pool. -/
theorem closed_head_source_post (size : Nat)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size context evidence source
      environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    closed_head_preserves functions extension faithful observations owner receipts body_nil unit_result escaped size idsUnique unique owners
      head found environments heaps locals agrees typed initial globals trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, reached_pool_observations related⟩

include extension faithful observations functionTypes receipts body_nil unit_result escaped head found environments heaps locals agrees typed initial globals in
/-- The original measured native completion reconstructs full source evidence
at its independent grade, retaining the exact returned caller pool. -/
theorem closed_head_native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    closed_head_reflects functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped size
      head found environments heaps locals agrees typed initial globals completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, reached_pool_observations related⟩
end Drivers

end Tests.SourceCoreClosedOwnedExpressionHead


